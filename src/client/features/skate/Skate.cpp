// Skate pose sync for SA:COOP (adapting GTSkate Standalone).
//
// What gtskate.asi does (read from its binary, build TimeDateStamp 0x6ACAD69E, SizeOfImage 0x114000):
//  - It plays no GTA animation. A Skate-engine port (skate_ffi.dll) computes a pose for CJ's whole skeleton.
//  - On every CPed render callback, for ONE ped (the skater) and only while its "skating" flag is set, it copies that
//    pose over the hierarchy's matrix array: RpHAnimHierarchyGetMatrixArray(hier) (0x7C5120), 0x40 bytes per node, ALL
//    nodes, world space, clearing bit 0x20000 of each matrix's flags (not identity any more). The frames' own local
//    matrices are never touched, so reading bone frames sees nothing of the pose.
//  - Its board is not a game object: it builds the mesh itself and draws it with D3D, on its own game only.
//  - Its state lives in its .data, at fixed offsets from the module base (see gt:: below).
//
// So this module:
//  LOCAL  : while the skater is on the board, after the ped renders, reads GTSkate's pose buffer and sends it (G_SKATE_POSE,
//           ~30 Hz, CH_STATE): the ped's own transform plus every node in the ped's space.
//  REMOTE : on every render of the partner's copy, writes the interpolated pose over that ped's matrix array, the same way
//           GTSkate does, from the SAME snapshot's transform (so a jump is not split between the synced ped position and a
//           pose of another moment). The partner does not need GTSkate installed to SEE the skater.
//           It also puts the modloader "skateboard" model (skate.ide, id 340) under the partner's feet, if that model exists.
//
// Placement: src/client/features/skate/Skate.cpp (tools/build.py globs src/client/**/*.cpp: no build file to edit).
// FSD: only shared/ and entities/ are included (tools/fsd_check.py).
//
// NOT compiled with the project toolchain and NOT run in the game. Marked CONFIRM: things taken from memory.
#include <windows.h>
#undef GetObject  // wingdi.h: GetObject -> GetObjectA, and game::GetObject(int) would not be found by the linker

#include <algorithm>
#include <cmath>
#include <cstring>
#include <map>

#include "common/api/protocol/Protocol.h"
#include "common/lib/log/Log.h"
#include "common/lib/util/Util.h"
#include "entities/player/Players.h"
#include "shared/api/net-session/Session.h"
#include "shared/game/Game.h"
#include "shared/game/Script.h"
#include "shared/lib/core/Core.h"
#include "shared/lib/memory/Memory.h"

namespace coop::skate {
namespace {
using namespace game;
using game::script::Cmd;

struct RwMat {  // RwMatrix (the same as AnimPreview.cpp's); also the first 0x40 bytes of a CMatrix
    CVector right;
    uint32_t flags;
    CVector up;  // RW "up" is SA's forward (Y); "at" is SA's up (Z)
    uint32_t pad1;
    CVector at;
    uint32_t pad2;
    CVector pos;
    uint32_t pad3;
};
static_assert(sizeof(RwMat) == 0x40);

// ---------------------------------------------------------------------------------------------------------------
// gtskate.asi: where its state is. These are offsets into THAT build only: the module is checked before any is read.
// To use another GTSkate build, find the same spots again (the render callback tests them in this order:
// enabled, skating, ped == skater, pose ready) and change the numbers, or the check below will say so in the log.
// ---------------------------------------------------------------------------------------------------------------
namespace gt {
constexpr uint32_t kStamp = 0x6ACAD69E;  // IMAGE_FILE_HEADER::TimeDateStamp
constexpr uint32_t kImage = 0x114000;    // IMAGE_OPTIONAL_HEADER::SizeOfImage
constexpr uint32_t kEnabled = 0x0C3CDD;  // u8  : the mod is on
constexpr uint32_t kCount = 0x105E34;    // i32 : number of nodes in the pose (the hierarchy's numNodes)
constexpr uint32_t kReady = 0x105E38;    // u8  : a pose has been published
constexpr uint32_t kPose = 0x105E3C;     // RwMat* : count x 0x40 bytes, world space
constexpr uint32_t kSkating = 0x105E58;  // u8  : 1 from getting on the board to getting off
constexpr uint32_t kPed = 0x105E5C;      // CPed* the pose is applied to

const uint8_t* Base() {
    static const uint8_t* base = []() -> const uint8_t* {
        auto* m = (const uint8_t*)GetModuleHandleA("gtskate.asi");
        if (!m) {
            LOGD("Skate: gtskate.asi is not loaded; this game will not send a skate pose (it still shows the others')");
            return nullptr;
        }
        auto* nt = m + *(const uint32_t*)(m + 0x3C);
        uint32_t stamp = *(const uint32_t*)(nt + 8), image = *(const uint32_t*)(nt + 0x50);
        if (stamp != kStamp || image != kImage) {
            LOGD("Skate: gtskate.asi is another build (stamp %08X, size %X): the offsets in Skate.cpp do not apply", stamp,
                 image);
            return nullptr;
        }
        return m;
    }();
    return base;
}
template <typename T>
T Get(uint32_t off) {
    return *(const T*)(Base() + off);
}

// the local player is on the board and a pose is ready
bool Active() {
    if (!Base() || !Get<uint8_t>(kEnabled) || !Get<uint8_t>(kSkating) || !Get<uint8_t>(kReady)) return false;
    return Get<uint32_t>(kPed) == (uint32_t)(uintptr_t)FindPlayerPed(0);
}
}  // namespace gt

constexpr int kMaxNodes = 64;  // a ped's hierarchy has far fewer; the packet carries 10 bytes per node

// the board under the partner's feet
constexpr int kBoardModel = 340;      // skate.ide (modloader\SkateMod): "340, skateboard, skateboard"
constexpr float kBoardDrop = 0.22f;   // ankle -> the model's origin: the ankle is ~0.09 over the sole, and skateboard.dff's deck
                                      // top is 0.128 over its origin (bbox x +-0.113, y +-0.45, z 0..0.128: the length is Y)
constexpr int kFootL = 43, kFootR = 53;  // eBoneTag, CONFIRM (thighs 41/51 are the ones the sa-coop code already uses)

// ---- rotation <-> quaternion (inverses of each other, whatever the matrix convention) ----
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

void Nlerp(const float a[4], const float b[4], float t, float out[4]) {
    float dot = a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
    float sign = dot < 0 ? -1.f : 1.f, len = 0;
    for (int k = 0; k < 4; k++) {
        out[k] = a[k] * (1 - t) + b[k] * sign * t;
        len += out[k] * out[k];
    }
    len = sqrtf(len);
    if (len < 1e-6f) {
        for (int k = 0; k < 4; k++) out[k] = a[k];
        return;
    }
    for (int k = 0; k < 4; k++) out[k] /= len;
}

// ---- world <-> the ped's own space (the ped matrix's rows are its right/up/at axes in the world) ----
float Dot(const CVector& a, const CVector& b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
CVector Cross(const CVector& a, const CVector& b) {
    return CVector{a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}

// a bone's world matrix -> rotation relative to the ped (as a matrix, for ToQuat) and offset from it, in the ped's axes
void ToLocal(const RwMat& ped, const RwMat& bone, RwMat& rel, CVector& off) {
    rel.right = {Dot(bone.right, ped.right), Dot(bone.right, ped.up), Dot(bone.right, ped.at)};
    rel.up = {Dot(bone.up, ped.right), Dot(bone.up, ped.up), Dot(bone.up, ped.at)};
    rel.at = {Dot(bone.at, ped.right), Dot(bone.at, ped.up), Dot(bone.at, ped.at)};
    CVector d = bone.pos - ped.pos;
    off = {Dot(d, ped.right), Dot(d, ped.up), Dot(d, ped.at)};
}

CVector Mix(const CVector& c, const RwMat& ped) {  // c.x * right + c.y * up + c.z * at
    return ped.right * c.x + ped.up * c.y + ped.at * c.z;
}

void ToWorld(const RwMat& ped, const RwMat& rel, const CVector& off, RwMat& bone) {
    bone.right = Mix(rel.right, ped);
    bone.up = Mix(rel.up, ped);
    bone.at = Mix(rel.at, ped);
    bone.pos = ped.pos + Mix(off, ped);
}

// the packet's numbers
void PutF(Writer& w, float f) {
    uint32_t u;
    memcpy(&u, &f, 4);
    w.U32(u);
}
float GetF(Reader& r) {
    uint32_t u = r.U32();
    float f;
    memcpy(&f, &u, 4);
    return f;
}
// a node's offset: millimetres in an i16 (+-32 m is far more than a skeleton needs)
void PutOff(Writer& w, const CVector& v) {
    auto q = [](float f) { return (int16_t)std::clamp(lroundf(f * 1000.f), -32767L, 32767L); };
    w.I16(q(v.x)); w.I16(q(v.y)); w.I16(q(v.z));
}
CVector GetOff(Reader& r) {
    float x = r.I16() / 1000.f, y = r.I16() / 1000.f, z = r.I16() / 1000.f;
    return CVector{x, y, z};
}

// ---- the ped's skeleton (the same calls as Props.cpp) ----
void* HierOf(CPed* ped) {
    auto* clump = (uint8_t*)ped->RwObject();
    return clump && clump[0] == 2 ? Call<0x734A40, void*>(clump) : nullptr;  // GetAnimHierarchyFromSkinClump
}
RwMat* MatrixArray(void* hier) { return (RwMat*)Call<0x7C5120, uint8_t*>(hier); }  // RpHAnimHierarchyGetMatrixArray
int NumNodes(void* hier) { return Field<int32_t>(hier, 4); }                        // as ScenePartner.cpp, and GTSkate
int NodeOf(void* hier, int boneTag) { return Call<0x7C51A0, int>(hier, boneTag); }  // RpHAnimIDGetIndex

struct Pose {  // a skeleton in its ped's own space, and that ped's transform in the world
    uint64_t t = 0;
    int n = 0;
    CVector pedPos;
    float pedQ[4] = {0, 0, 0, 1};
    float q[kMaxNodes][4] = {};
    CVector off[kMaxNodes];
};
struct Remote {
    Pose a, b;  // the two latest: shown a little behind, between them
    bool active = false;
    uint16_t seq = 0;
};
std::map<uint8_t, Remote> g_remote;
std::map<uint8_t, int> g_board;        // the partner's board: its object's handle
std::map<uint8_t, CVector> g_boardAxis;  // its last length axis (the board's two ends look alike: keep one)
Pose g_local;
bool g_localFresh = false;

constexpr uint64_t kSendEveryMs = 33;  // ~30 Hz, as the on-foot state (Players.cpp)
constexpr uint64_t kDelayMs = 70;      // shown this far behind: two packets
constexpr uint64_t kStaleMs = 1500;    // no pose for so long (a lost "stop"): the copy is let go

// where between the two latest snapshots "now - delay" falls
float Phase(const Remote& s) {
    float span = (float)std::max<int64_t>(1, (int64_t)(s.b.t - s.a.t));
    return std::clamp((float)((int64_t)(NowMs() - kDelayMs) - (int64_t)s.a.t) / span, 0.f, 1.f);
}
// the skater's transform at that moment: what the body is drawn around
void InterpPed(const Remote& s, float t, RwMat& pm) {
    float q[4];
    Nlerp(s.a.pedQ, s.b.pedQ, t, q);
    pm = RwMat{};
    FromQuat(q, pm);
    pm.pos = s.a.pedPos * (1 - t) + s.b.pedPos * t;
}
void InterpNode(const Remote& s, int i, float t, const RwMat& pm, RwMat& world) {
    float q[4];
    Nlerp(s.a.q[i], s.b.q[i], t, q);
    RwMat rel{};
    FromQuat(q, rel);
    CVector off = s.a.off[i] * (1 - t) + s.b.off[i] * t;
    ToWorld(pm, rel, off, world);
}

using PedRenderFn = void(__fastcall*)(CPed*, void*);
PedRenderFn g_origPedRender = nullptr;
void __fastcall HookPedRender(CPed* self, void* edx);

class Skate : public Module {
public:
    const char* Name() const override { return "Skate"; }

    void OnInstallHooks() override {
        Net().SetHandler(proto::G_SKATE_POSE, [](uint8_t from, Reader& r) { Instance().Handle(from, r); });
        // CONFIRM: 0x5E7680 = CPed::Render (from gta-reversed, not checked in a binary). GTSkate does its work in a
        // per-ped render callback, and this is the same moment. If this fails or never runs, the log says so.
        if (!mem::HookFn(0x5E7680, &HookPedRender, &g_origPedRender, "CPed::Render"))
            LOGD("Skate: could not hook CPed::Render; partners will not see the skate pose");
    }

    void OnPeerLeave(uint8_t id) override { Release(id); }
    void OnSessionEnd() override {
        for (auto& [id, h] : g_board)
            if (GetObject(h)) Cmd(0x0108).I(h).Run();  // DELETE_OBJECT
        g_board.clear();
        g_boardAxis.clear();
        g_remote.clear();
    }

    void OnPostProcess() override {
        if (!Net().Online() || !core::IsPlayerReady()) return;
        SendLocal();
        for (auto it = g_remote.begin(); it != g_remote.end();) {
            uint8_t id = it->first;
            RemotePlayer* rp = Players::Instance().Get(id);
            Remote& s = it->second;
            if (s.active && NowMs() - s.b.t > kStaleMs) s.active = false;
            if (!s.active) {
                if (rp) Let(*rp);
                DropBoard(id);
                it = g_remote.erase(it);
                continue;
            }
            if (rp) {
                rp->skateHeld = true;  // Anims.cpp ORs this into animHeld, which it recomputes every frame
                rp->animHeld = true;   // its own tasks keep off it (Players.cpp, Peds.cpp read this)
                if (rp->ped) PlaceBoard(id, *rp, s);
            }
            ++it;
        }
    }

    static Skate& Instance() {
        static Skate s;
        return s;
    }

    // ---- from the CPed::Render hook ----
    void BeforeRender(CPed* ped) {  // the partner's copy: write the pose over its matrix array, as GTSkate does
        if (g_remote.empty()) return;
        RemotePlayer* rp = Players::Instance().FindByPed(ped);
        if (!rp) return;
        auto it = g_remote.find(rp->id);
        if (it != g_remote.end() && it->second.active) ApplyRemote(ped, it->second);
    }

    void AfterRender(CPed* ped) {  // our own skater: GTSkate has published this frame's pose by now
        if (ped != (CPed*)FindPlayerPed(0) || !gt::Active()) return;
        Capture(ped);
    }

private:
    bool m_wasSkating = false;
    uint16_t m_seq = 0;
    uint64_t m_lastSend = 0;
    bool m_boardWarned = false;

    // the copy goes back to its own tasks (Anims.cpp recomputes animHeld every frame for the players it follows)
    static void Let(RemotePlayer& rp) {
        rp.skateHeld = false;
        rp.animHeld = false;
    }

    void Release(uint8_t id) {
        if (RemotePlayer* rp = Players::Instance().Get(id)) Let(*rp);
        DropBoard(id);
        g_remote.erase(id);
    }

    // ---- local: GTSkate's published pose (world space) -> the ped's space ----
    void Capture(CPed* ped) {
        auto* pm = Field<RwMat*>(ped, 0x14);  // CEntity::m_matrix
        auto* pose = gt::Get<RwMat*>(gt::kPose);
        int n = gt::Get<int32_t>(gt::kCount);
        if (!pm || !pose || n < 1 || n > kMaxNodes) return;
        g_local.n = n;
        g_local.pedPos = pm->pos;
        ToQuat(*pm, g_local.pedQ);
        // the nodes are taken against the ped as the packet will give it back (its rotation goes through the packing)
        float pq[4];
        Unpack(Pack(g_local.pedQ), pq);
        RwMat ref{};
        FromQuat(pq, ref);
        ref.pos = pm->pos;
        for (int i = 0; i < n; i++) {
            RwMat rel;
            ToLocal(ref, pose[i], rel, g_local.off[i]);
            ToQuat(rel, g_local.q[i]);
        }
        g_localFresh = true;
    }

    void SendLocal() {
        bool skating = gt::Active();
        if (!skating) {
            if (m_wasSkating) {  // the end goes reliably: a lost one would freeze the pose on the others
                Writer w(proto::G_SKATE_POSE);
                w.U8(0);
                w.U16(++m_seq);
                Net().Send(proto::CH_RELIABLE, w);
            }
            m_wasSkating = false;
            g_localFresh = false;
            return;
        }
        m_wasSkating = true;
        if (!g_localFresh || NowMs() - m_lastSend < kSendEveryMs) return;
        m_lastSend = NowMs();
        g_localFresh = false;

        Writer w(proto::G_SKATE_POSE);
        w.U8(1);  // flags: 1 = skating
        w.U16(++m_seq);
        w.U8((uint8_t)g_local.n);
        PutF(w, g_local.pedPos.x); PutF(w, g_local.pedPos.y); PutF(w, g_local.pedPos.z);
        w.U32(Pack(g_local.pedQ));
        for (int i = 0; i < g_local.n; i++) {
            w.U32(Pack(g_local.q[i]));
            PutOff(w, g_local.off[i]);
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
        int n = r.U8();
        if (!r.Ok() || n < 1 || n > kMaxNodes) return;
        Remote& s = g_remote[from];
        if (s.active && (int16_t)(seq - s.seq) <= 0) return;  // an old or repeated one
        Pose p;
        p.t = NowMs();
        p.n = n;
        p.pedPos.x = GetF(r); p.pedPos.y = GetF(r); p.pedPos.z = GetF(r);
        Unpack(r.U32(), p.pedQ);
        for (int i = 0; i < n; i++) {
            Unpack(r.U32(), p.q[i]);
            p.off[i] = GetOff(r);
        }
        if (!r.Ok()) return;
        s.a = s.active && s.b.n == n ? s.b : p;
        s.b = p;
        s.seq = seq;
        s.active = true;
    }

    // ---- remote: write the pose over the copy's matrix array ----
    void ApplyRemote(CPed* ped, Remote& s) {
        void* hier = HierOf(ped);
        if (!hier) return;
        RwMat* arr = MatrixArray(hier);
        int n = std::min({s.b.n, s.a.n, NumNodes(hier), kMaxNodes});
        if (!arr || n < 1) return;

        float t = Phase(s);
        RwMat pm;
        InterpPed(s, t, pm);
        for (int i = 0; i < n; i++) {
            RwMat bone = arr[i];  // keeps the flags words
            InterpNode(s, i, t, pm, bone);
            bone.flags &= ~0x20000u;  // not an identity matrix any more (GTSkate does the same)
            arr[i] = bone;
        }
    }

    // ---- remote: the board under its feet ----
    int MakeBoard(CPed* holder) {
        if (!IsObjectModel(kBoardModel)) {
            if (!m_boardWarned) LOGD("Skate: model %d (modloader\\SkateMod\\skate.ide) is not here: no board for the partner", kBoardModel);
            m_boardWarned = true;
            return -1;
        }
        if (!IsModelLoaded(kBoardModel)) {
            RequestModel(kBoardModel);
            return -1;
        }
        if (!HasRoom(ObjectPool(), kKeepObjects, "object")) return -1;
        CVector at = holder->GetPosition();
        int h = -1;
        Cmd(0x029B).I(kBoardModel).F(at.x).F(at.y).F(at.z).Out(&h).Run();  // CREATE_OBJECT_NO_OFFSET
        CObject* o = h >= 0 ? GetObject(h) : nullptr;
        if (!o) return -1;
        Field<uint8_t>(o, 0x13C) = 6;  // OBJECT_MISSION2, as Props.cpp: saves and snapshots do not keep it
        Cmd(0x0382).I(h).I(0).Run();   // SET_OBJECT_COLLISION: only to be seen
        Cmd(0x0550).I(h).I(1).Run();   // FREEZE_OBJECT_POSITION: it goes where PlaceBoard puts it
        MarkModelNotNeeded(kBoardModel);
        return h;
    }

    void DropBoard(uint8_t id) {
        auto it = g_board.find(id);
        if (it != g_board.end()) {
            if (GetObject(it->second)) Cmd(0x0108).I(it->second).Run();  // DELETE_OBJECT
            g_board.erase(it);
        }
        g_boardAxis.erase(id);
    }

    void PlaceBoard(uint8_t id, RemotePlayer& rp, Remote& s) {
        void* hier = HierOf(rp.ped);
        if (!hier) return;
        int iL = NodeOf(hier, kFootL), iR = NodeOf(hier, kFootR);
        int n = std::min({s.a.n, s.b.n});
        if (iL < 0 || iR < 0 || iL >= n || iR >= n) return;

        auto bit = g_board.find(id);
        if (bit == g_board.end() || !GetObject(bit->second)) {
            int h = MakeBoard(rp.ped);
            if (h < 0) return;
            g_board[id] = h;
            bit = g_board.find(id);
        }
        CObject* o = GetObject(bit->second);
        CMatrix* m = o ? o->Matrix() : nullptr;
        if (!m) return;

        float t = Phase(s);
        RwMat pm, fl, fr;
        InterpPed(s, t, pm);
        InterpNode(s, iL, t, pm, fl);
        InterpNode(s, iR, t, pm, fr);

        // the board lies under both feet: its length is the line between them (flattened against the ped's up)
        CVector up = pm.at;
        CVector axis = fl.pos - fr.pos;
        axis = axis - up * Dot(axis, up);
        float len = sqrtf(Dot(axis, axis));
        axis = len > 0.05f ? axis * (1.0f / len) : pm.up;
        auto last = g_boardAxis.find(id);
        if (last != g_boardAxis.end() && Dot(last->second, axis) < 0) axis = axis * -1.0f;
        g_boardAxis[id] = axis;
        CVector right = Cross(axis, up);

        WorldRemove(o);
        m->right = right;
        m->forward = axis;
        m->up = up;
        m->pos = (fl.pos + fr.pos) * 0.5f - up * kBoardDrop;
        CallMethod<0x446F90>(o);  // CEntity::UpdateRW
        CallMethod<0x532B00>(o);  // CEntity::UpdateRwFrame
        WorldAdd(o);
    }
};

void __fastcall HookPedRender(CPed* self, void* edx) {
    Skate::Instance().BeforeRender(self);
    g_origPedRender(self, edx);
    Skate::Instance().AfterRender(self);
}

struct Reg {
    Reg() { core::RegisterModule(&Skate::Instance()); }
} g_reg;

}  // namespace
}  // namespace coop::skate
