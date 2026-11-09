// Skate pose sync for SA:COOP (adapting GTSkate).
//
// GTSkate does not play GTA animations: its Skate-engine poses CJ's skeleton bone by bone every frame. So there is no
// animation id to send. This module sends the bones' local rotations (G_SKATE_POSE, ~20 Hz, CH_STATE) of the local
// player while it skates, and writes them into the bones of its copy on the other games.
//
// Placement: src/client/features/skate/Skate.cpp (tools/build.py globs src/client/**/*.cpp: no build file to edit).
// FSD: this slice includes only shared/ and entities/ (tools/fsd_check.py).
//
// UNVERIFIED (nothing here was compiled or run) - see "CONFIRM" and "TODO" below.
#include <algorithm>
#include <cmath>
#include <map>

#include "common/api/protocol/Protocol.h"
#include "common/lib/log/Log.h"
#include "common/lib/util/Util.h"
#include "entities/player/Players.h"
#include "shared/api/net-session/Session.h"
#include "shared/game/Game.h"
#include "shared/lib/core/Core.h"

namespace coop::skate {
namespace {
using namespace game;

// TODO: true while the LOCAL player is on the board. Use the same condition your board-object sync already uses.
// (FSD: do not include another features/ slice for it; put the flag in shared/ or an entity if it lives elsewhere.)
bool IsSkating() { return false; }

struct RwMat {  // RwMatrix (the same as AnimPreview.cpp's)
    CVector right;
    uint32_t flags;
    CVector up;
    uint32_t pad1;
    CVector at;
    uint32_t pad2;
    CVector pos;
    uint32_t pad3;
};
static_assert(sizeof(RwMat) == 0x40);

// eBoneTag of the bones that carry the pose (the fingers, toes and the rest follow their parents when the hierarchy is
// updated). CONFIRM against eBoneTag: 5 (head), 41 and 51 (thighs) already appear in ScenePartner.cpp / AnimPreview.cpp.
constexpr int kBones[] = {0, 1, 2, 3, 4, 5, 21, 22, 23, 24, 31, 32, 33, 34, 41, 42, 43, 51, 52, 53};
constexpr int NB = (int)(sizeof(kBones) / sizeof(kBones[0]));
constexpr int kPosBones = 2;  // bones 0 (root) and 1 (pelvis) also carry their translation

// ---- rotation <-> quaternion (the two are inverses of each other, whatever the matrix convention) ----
void ToQuat(const RwMat& M, float q[4]) {
    const float m[3][3] = {{M.right.x, M.right.y, M.right.z}, {M.up.x, M.up.y, M.up.z}, {M.at.x, M.at.y, M.at.z}};
    float t = m[0][0] + m[1][1] + m[2][2];
    if (t > 0) {
        float s = sqrtf(t + 1) * 2;
        q[3] = s / 4; q[0] = (m[2][1] - m[1][2]) / s; q[1] = (m[0][2] - m[2][0]) / s; q[2] = (m[1][0] - m[0][1]) / s;
    } else if (m[0][0] > m[1][1] && m[0][0] > m[2][2]) {
        float s = sqrtf(1 + m[0][0] - m[1][1] - m[2][2]) * 2;
        q[3] = (m[2][1] - m[1][2]) / s; q[0] = s / 4; q[1] = (m[0][1] + m[1][0]) / s; q[2] = (m[0][2] + m[2][0]) / s;
    } else if (m[1][1] > m[2][2]) {
        float s = sqrtf(1 + m[1][1] - m[0][0] - m[2][2]) * 2;
        q[3] = (m[0][2] - m[2][0]) / s; q[0] = (m[0][1] + m[1][0]) / s; q[1] = s / 4; q[2] = (m[1][2] + m[2][1]) / s;
    } else {
        float s = sqrtf(1 + m[2][2] - m[0][0] - m[1][1]) * 2;
        q[3] = (m[1][0] - m[0][1]) / s; q[0] = (m[0][2] + m[2][0]) / s; q[1] = (m[1][2] + m[2][1]) / s; q[2] = s / 4;
    }
}

void FromQuat(const float q[4], RwMat& M) {
    float x = q[0], y = q[1], z = q[2], w = q[3];
    M.right = {1 - 2 * (y * y + z * z), 2 * (x * y - z * w), 2 * (x * z + y * w)};
    M.up = {2 * (x * y + z * w), 1 - 2 * (x * x + z * z), 2 * (y * z - x * w)};
    M.at = {2 * (x * z - y * w), 2 * (y * z + x * w), 1 - 2 * (x * x + y * y)};
}

// smallest-three: 2 bits for the index of the largest component, 10 bits for each of the other three
uint32_t Pack(const float q[4]) {
    int big = 0;
    for (int i = 1; i < 4; i++)
        if (fabsf(q[i]) > fabsf(q[big])) big = i;
    float sign = q[big] < 0 ? -1.f : 1.f;
    uint32_t out = (uint32_t)big;
    for (int i = 0, shift = 2; i < 4; i++) {
        if (i == big) continue;
        float v = q[i] * sign * 1.41421356f;  // in [-1, 1]
        out |= (uint32_t)lroundf((v * 0.5f + 0.5f) * 1023.f) << shift;
        shift += 10;
    }
    return out;
}

void Unpack(uint32_t p, float q[4]) {
    int big = (int)(p & 3);
    float sum = 0;
    for (int i = 0, shift = 2; i < 4; i++) {
        if (i == big) continue;
        q[i] = (((p >> shift) & 1023) / 1023.f * 2.f - 1.f) / 1.41421356f;
        sum += q[i] * q[i];
        shift += 10;
    }
    q[big] = sqrtf(std::max(0.f, 1.f - sum));
}

// a bone's translation relative to its parent: millimetres in an i16 (+-32 m is far more than a skeleton needs)
void PutPos(Writer& w, const CVector& v) {
    auto q = [](float f) { return (int16_t)std::clamp(lroundf(f * 1000.f), -32767L, 32767L); };
    w.I16(q(v.x)); w.I16(q(v.y)); w.I16(q(v.z));
}
CVector GetPos(Reader& r) {
    float x = r.I16() / 1000.f, y = r.I16() / 1000.f, z = r.I16() / 1000.f;
    return CVector{x, y, z};
}

// ---- the ped's skeleton ----
void* HierOf(CPed* ped) {
    auto* clump = (uint8_t*)ped->RwObject();
    return clump && clump[0] == 2 ? Call<0x734A40, void*>(clump) : nullptr;  // GetAnimHierarchyFromSkinClump (Props.cpp)
}

// the RwFrame of a bone, from the hierarchy's node info
void* FrameOf(void* hier, int tag) {
    int i = Call<0x7C51A0, int>(hier, tag);  // RpHAnimIDGetIndex (Props.cpp)
    if (i < 0) return nullptr;
    auto* info = Field<uint8_t*>(hier, 0x1C);          // RpHAnimHierarchy::pNodeInfo   CONFIRM (RenderWare layout)
    if (!info) return nullptr;
    return Field<void*>(info + (size_t)i * 16, 0x0C);  // RpHAnimNodeInfo::pFrame        CONFIRM
}

// ---- remote state ----
struct Snap {
    uint64_t t = 0;  // local time of reception
    float q[NB][4] = {};
    CVector pos[kPosBones];
};
struct Remote {
    Snap a, b;  // the two latest snapshots: shown ~100 ms behind, between them
    bool active = false;
    uint16_t seq = 0;
};
std::map<uint8_t, Remote> g_remote;

constexpr uint64_t kSendEveryMs = 50;  // 20 Hz
constexpr uint64_t kDelayMs = 100;     // interpolation delay
constexpr uint64_t kStaleMs = 1500;    // no pose for so long (a lost "stop"): the copy is let go

class Skate : public Module {
public:
    const char* Name() const override { return "Skate"; }

    void OnInstallHooks() override {
        Net().SetHandler(proto::G_SKATE_POSE, [](uint8_t from, Reader& r) { Instance().Handle(from, r); });
    }

    void OnPeerLeave(uint8_t id) override { Release(id); }
    void OnSessionEnd() override { g_remote.clear(); }
    void OnGameShutdown() override { m_wasSkating = false; }

    // TODO(timing): if the pose flickers or never shows, the game's own animation update is overwriting it after this
    // point. Then move ApplyRemote() into a hook of CPed::PreRender (mem::HookFn), as Anims.cpp hooks its functions.
    void OnPostProcess() override {
        if (!Net().Online() || !core::IsPlayerReady()) return;
        SendLocal();
        for (auto it = g_remote.begin(); it != g_remote.end();) {
            RemotePlayer* rp = Players::Instance().Get(it->first);
            Remote& s = it->second;
            if (s.active && NowMs() - s.b.t > kStaleMs) s.active = false;
            if (!s.active) {
                if (rp) Let(*rp);
                it = g_remote.erase(it);
                continue;
            }
            if (rp && rp->ped) ApplyRemote(*rp, s);
            ++it;
        }
    }

    static Skate& Instance() {
        static Skate s;
        return s;
    }

private:
    bool m_wasSkating = false;
    uint16_t m_seq = 0;
    uint64_t m_lastSend = 0;

    // the copy goes back to its own tasks (Anims.cpp recomputes animHeld every frame for the players it follows)
    static void Let(RemotePlayer& rp) {
        rp.skateHeld = false;
        rp.animHeld = false;
    }

    void Release(uint8_t id) {
        if (RemotePlayer* rp = Players::Instance().Get(id)) Let(*rp);
        g_remote.erase(id);
    }

    // ---- local: read the pose GTSkate gave our CJ and send it ----
    void SendLocal() {
        bool skating = IsSkating();
        if (!skating) {
            if (m_wasSkating) {  // the end goes reliably: a lost one would freeze the pose on the others
                Writer w(proto::G_SKATE_POSE);
                w.U8(0);
                w.U16(++m_seq);
                Net().Send(proto::CH_RELIABLE, w);
            }
            m_wasSkating = false;
            return;
        }
        m_wasSkating = true;
        if (NowMs() - m_lastSend < kSendEveryMs) return;
        m_lastSend = NowMs();

        CPlayerPed* me = FindPlayerPed(0);
        void* hier = me ? HierOf(me) : nullptr;
        if (!hier) return;

        Writer w(proto::G_SKATE_POSE);
        w.U8(1);  // flags: 1 = skating
        w.U16(++m_seq);
        for (int i = 0; i < kPosBones; i++) {
            void* f = FrameOf(hier, kBones[i]);
            PutPos(w, f ? Field<RwMat>(f, 0x10).pos : CVector{});  // RwFrame::modelling
        }
        for (int i = 0; i < NB; i++) {
            float q[4] = {0, 0, 0, 1};
            if (void* f = FrameOf(hier, kBones[i])) ToQuat(Field<RwMat>(f, 0x10), q);
            w.U32(Pack(q));
        }
        Net().Send(proto::CH_STATE, w);
    }

    // ---- remote: receive ----
    void Handle(uint8_t from, Reader& r) {
        uint8_t flags = r.U8();
        uint16_t seq = r.U16();
        if (!r.Ok()) return;
        if (!(flags & 1)) {
            Release(from);
            return;
        }
        Remote& s = g_remote[from];
        if (s.active && (int16_t)(seq - s.seq) <= 0) return;  // an old or repeated one
        Snap n;
        n.t = NowMs();
        for (int i = 0; i < kPosBones; i++) n.pos[i] = GetPos(r);
        for (int i = 0; i < NB; i++) Unpack(r.U32(), n.q[i]);
        if (!r.Ok()) return;
        s.a = s.active ? s.b : n;
        s.b = n;
        s.seq = seq;
        s.active = true;
    }

    // ---- remote: write the pose into the copy's bones ----
    void ApplyRemote(RemotePlayer& rp, Remote& s) {
        void* hier = HierOf(rp.ped);
        if (!hier) return;
        rp.skateHeld = true;  // Anims.cpp ORs this into animHeld, which it recomputes every frame
        rp.animHeld = true;   // its own tasks keep off it (Players.cpp, Peds.cpp read this)

        float span = (float)std::max<int64_t>(1, (int64_t)(s.b.t - s.a.t));
        float t = std::clamp((float)((int64_t)(NowMs() - kDelayMs) - (int64_t)s.a.t) / span, 0.f, 1.f);

        for (int i = 0; i < NB; i++) {
            void* f = FrameOf(hier, kBones[i]);
            if (!f) continue;
            float dot = 0;
            for (int k = 0; k < 4; k++) dot += s.a.q[i][k] * s.b.q[i][k];
            float sign = dot < 0 ? -1.f : 1.f, q[4], len = 0;
            for (int k = 0; k < 4; k++) {
                q[k] = s.a.q[i][k] * (1 - t) + s.b.q[i][k] * sign * t;  // nlerp
                len += q[k] * q[k];
            }
            len = sqrtf(len);
            if (len < 1e-6f) continue;
            for (float& v : q) v /= len;

            RwMat m = Field<RwMat>(f, 0x10);  // keeps the frame's own translation (except the root and pelvis)
            FromQuat(q, m);
            if (i < kPosBones) {
                const CVector &p0 = s.a.pos[i], &p1 = s.b.pos[i];
                m.pos = CVector{p0.x + (p1.x - p0.x) * t, p0.y + (p1.y - p0.y) * t, p0.z + (p1.z - p0.z) * t};
            }
            Field<RwMat>(f, 0x10) = m;
            Call<0x7F0910>(f);  // RwFrameUpdateObjects (as AnimPreview.cpp's SetFrame)
        }
        Call<0x7C51D0>(hier);  // RpHAnimHierarchyUpdateMatrices
    }
};

struct Reg {
    Reg() { core::RegisterModule(&Skate::Instance()); }
} g_reg;

}  // namespace
}  // namespace coop::skate
