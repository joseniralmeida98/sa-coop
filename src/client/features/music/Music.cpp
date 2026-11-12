// Music from a URL, out of a car's trunk (the idea of MDPM, made for SA:COOP).
//
//   /music <link to an MP3>   the music starts in YOUR car's trunk (or around you, on foot); every player hears it
//                             by the distance to that car: louder near it, quieter far, left or right by where it is
//   /music stop               stops yours;   /music vol <0-100>   your volume;   /music hear <on|off>   others' links
//
// Only the link and the moment it started cross the network (G_MUSIC, reliable, again every 5 s so whoever comes late
// joins in): every game downloads the file itself (WinHTTP), decodes it (minimp3) and mixes it (waveOut), and
// finds its place in the song by the clock, so the games play the same second. No audio is sent between players.
//
// Limits: a direct link to an MP3 file (or a podcast/MP3 download), up to 40 MB. Not YouTube, Spotify or the like (they are
// pages, not audio), not live radio (a stream with no end is not a file), not AAC/M3U8.
//
// Needs third_party/minimp3/minimp3.h (one file, CC0: github.com/lieff/minimp3). Without it this module builds and says so.
//
// Placement: src/client/features/music/Music.cpp (tools/build.py globs src/client/**/*.cpp).
// FSD: only common/, shared/ and entities/ are included (tools/fsd_check.py).
//
// NOT compiled with the project toolchain and NOT run in the game.
#include <windows.h>
#undef GetObject

#include <mmsystem.h>
#include <winhttp.h>

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstring>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#include "common/api/protocol/Protocol.h"
#include "common/lib/log/Log.h"
#include "common/lib/util/Util.h"
#include "entities/player/Players.h"
#include "shared/api/net-session/Session.h"
#include "shared/config/Config.h"
#include "shared/game/Game.h"
#include "shared/lib/core/Core.h"
#include "shared/ui/chat/Chat.h"

#if __has_include(<minimp3.h>)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#define MINIMP3_IMPLEMENTATION
#include <minimp3.h>
#pragma clang diagnostic pop
#define MUSIC_HAVE_MP3 1
#endif

namespace coop::music {
namespace {
using namespace game;

constexpr int kRate = 44100;                 // what the mixer plays
constexpr int kBlock = 1024;                 // frames per waveOut buffer (~23 ms)
constexpr int kBufs = 4;                     // buffers in flight (~93 ms)
constexpr size_t kMaxBytes = 40u << 20;      // the largest file taken
constexpr size_t kMaxUrl = 500;
constexpr uint64_t kBeatMs = 5000;           // the owner says again what it plays
constexpr int64_t kResync = kRate * 3 / 2;   // out of step by more than this (frames): look for the place again
constexpr float kFullM = 4.0f;               // full volume up to here (metres) ...
constexpr float kFarM = 70.0f;               // ... fading to silence here
constexpr float kTrunkM = 2.2f;              // the trunk: behind the car's centre by this much
constexpr float kPi = 3.14159265f;

enum State : int { kLoading, kReady, kSeeking, kFailed, kEnded, kStopped };

#ifdef MUSIC_HAVE_MP3
// ---- an MP3 file in memory, decoded a frame at a time and resampled to kRate ----
struct Decoder {
    std::vector<uint8_t> data;
    mp3dec_t dec{};
    size_t pos = 0;             // the next byte for the decoder
    int hz = 0;                 // the file's rate, known from its first frame
    std::vector<float> q;       // decoded stereo (L, R, L, R ...) at the file's rate
    size_t head = 0;            // the frame of q being read
    double frac = 0;            // between q[head] and q[head + 1]
    int64_t out = 0;            // frames given out (at kRate) since the song's start
    bool ended = false;

    void Reset() {
        mp3dec_init(&dec);
        pos = 0;
        q.clear();
        head = 0;
        frac = 0;
        out = 0;
        ended = false;
    }

    // one more frame into q; false when the file has no more
    bool DecodeFrame() {
        mp3d_sample_t pcm[MINIMP3_MAX_SAMPLES_PER_FRAME];
        while (pos < data.size()) {
            mp3dec_frame_info_t info{};
            int left = (int)std::min<size_t>(data.size() - pos, (size_t)1 << 30);
            int n = mp3dec_decode_frame(&dec, data.data() + pos, left, pcm, &info);
            if (info.frame_bytes <= 0) {
                pos = data.size();
                return false;
            }
            pos += (size_t)info.frame_bytes;
            if (n <= 0) continue;  // a tag or a damaged frame: skipped
            if (!hz) hz = info.hz;
            const float k = 1.0f / 32768.0f;
            if (info.channels == 1) {
                for (int i = 0; i < n; i++) {
                    float v = (float)pcm[i] * k;
                    q.push_back(v);
                    q.push_back(v);
                }
            } else {
                for (int i = 0; i < n; i++) {
                    q.push_back((float)pcm[2 * i] * k);
                    q.push_back((float)pcm[2 * i + 1] * k);
                }
            }
            return true;
        }
        return false;
    }

    // stereo float at kRate; once the file is over, silence
    void Read(float* o, int frames) {
        if (!hz) DecodeFrame();
        if (!hz) {
            ended = true;
            std::fill(o, o + frames * 2, 0.0f);
            return;
        }
        const double step = (double)hz / kRate;
        for (int i = 0; i < frames; i++) {
            while (q.size() / 2 < head + 2 && DecodeFrame()) {
            }
            if (q.size() / 2 < head + 2) {
                ended = true;
                o[2 * i] = o[2 * i + 1] = 0.0f;
                continue;
            }
            const float t = (float)frac;
            const float* a = &q[2 * head];
            o[2 * i] = a[0] + (a[2] - a[0]) * t;
            o[2 * i + 1] = a[1] + (a[3] - a[1]) * t;
            frac += step;
            size_t adv = (size_t)frac;
            frac -= (double)adv;
            head += adv;
            out++;
        }
        if (head > 16384) {
            size_t drop = std::min(head, q.size() / 2);
            q.erase(q.begin(), q.begin() + (ptrdiff_t)(drop * 2));
            head -= drop;
        }
    }

    // to the place `target` frames (at kRate) into the song, by decoding up to it
    void SeekFrames(int64_t target) {
        Reset();
        if (!hz && !DecodeFrame()) {
            ended = true;
            return;
        }
        if (!hz) return;
        q.clear();
        pos = 0;
        mp3dec_init(&dec);
        int64_t skip = (int64_t)((double)target * hz / kRate);
        while (skip > 0) {
            if (!DecodeFrame()) {  // the file is shorter than that
                ended = true;
                return;
            }
            int64_t got = (int64_t)(q.size() / 2);
            if (got <= skip) {
                skip -= got;
                q.clear();
            } else {
                head = (size_t)skip;
                skip = 0;
            }
        }
        out = target;
    }
};
#else
struct Decoder {};
#endif

struct Source {
    uint8_t owner = 0;
    uint32_t serial = 0;
    std::string url;
    uint64_t startMs = 0;               // our clock at the song's second 0
    std::atomic<int> state{kLoading};
    std::atomic<bool> cancel{false};
    std::string err;                    // why it failed (written before state says so)
    std::shared_ptr<Decoder> dec;       // made by the loader; the mixer reads it once state is kReady
    std::atomic<float> gL{0.0f}, gR{0.0f};  // the game thread's: how loud on each side
    float curL = 0.0f, curR = 0.0f;     // the mixer's, smoothed
    uint64_t lastBeat = 0;
};

std::mutex g_mu;
std::vector<std::shared_ptr<Source>> g_src;
std::atomic<float> g_vol{0.7f};
std::atomic<bool> g_mixRun{false}, g_mixAlive{false};
std::thread g_mixThread;

int64_t PosAt(const Source& s, uint64_t t) { return t <= s.startMs ? 0 : (int64_t)(t - s.startMs) * kRate / 1000; }

// ---- the download ----
bool Download(Source& s, std::vector<uint8_t>& out, std::string& err) {
    std::wstring w = Utf8ToWide(s.url);
    URL_COMPONENTSW uc{};
    uc.dwStructSize = sizeof(uc);
    uc.dwHostNameLength = (DWORD)-1;
    uc.dwUrlPathLength = (DWORD)-1;
    uc.dwExtraInfoLength = (DWORD)-1;
    if (!WinHttpCrackUrl(w.c_str(), (DWORD)w.size(), 0, &uc) || !uc.lpszHostName) {
        err = "bad link";
        return false;
    }
    std::wstring host(uc.lpszHostName, uc.dwHostNameLength);
    std::wstring path(uc.lpszUrlPath ? uc.lpszUrlPath : L"", uc.lpszUrlPath ? uc.dwUrlPathLength : 0);
    if (uc.lpszExtraInfo) path.append(uc.lpszExtraInfo, uc.dwExtraInfoLength);
    if (path.empty()) path = L"/";
    const bool tls = uc.nScheme == INTERNET_SCHEME_HTTPS;

    HINTERNET ses = WinHttpOpen(L"SA-COOP/1.0", WINHTTP_ACCESS_TYPE_AUTOMATIC_PROXY, WINHTTP_NO_PROXY_NAME,
                                WINHTTP_NO_PROXY_BYPASS, 0);
    if (!ses) ses = WinHttpOpen(L"SA-COOP/1.0", WINHTTP_ACCESS_TYPE_DEFAULT_PROXY, WINHTTP_NO_PROXY_NAME,
                                WINHTTP_NO_PROXY_BYPASS, 0);
    if (!ses) {
        err = "no network";
        return false;
    }
    WinHttpSetTimeouts(ses, 10000, 10000, 15000, 30000);
    HINTERNET con = WinHttpConnect(ses, host.c_str(), uc.nPort, 0);
    HINTERNET req = con ? WinHttpOpenRequest(con, L"GET", path.c_str(), nullptr, WINHTTP_NO_REFERER,
                                             WINHTTP_DEFAULT_ACCEPT_TYPES, tls ? WINHTTP_FLAG_SECURE : 0)
                        : nullptr;
    bool ok = false;
    if (req && WinHttpSendRequest(req, WINHTTP_NO_ADDITIONAL_HEADERS, 0, WINHTTP_NO_REQUEST_DATA, 0, 0, 0) &&
        WinHttpReceiveResponse(req, nullptr)) {
        DWORD status = 0, sz = sizeof(status);
        WinHttpQueryHeaders(req, WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER, WINHTTP_HEADER_NAME_BY_INDEX, &status,
                            &sz, WINHTTP_NO_HEADER_INDEX);
        if (status != 200) {
            err = Format("the server answered %lu", (unsigned long)status);
        } else {
            ok = true;
            std::vector<uint8_t> buf(64 * 1024);
            for (;;) {
                if (s.cancel) {
                    ok = false;
                    err = "stopped";
                    break;
                }
                DWORD got = 0;
                if (!WinHttpReadData(req, buf.data(), (DWORD)buf.size(), &got)) {
                    ok = false;
                    err = "the download broke off";
                    break;
                }
                if (got == 0) break;
                out.insert(out.end(), buf.begin(), buf.begin() + got);
                if (out.size() > kMaxBytes) {
                    ok = false;
                    err = "the file is over 40 MB";
                    break;
                }
            }
        }
    } else if (err.empty()) {
        err = "could not reach the server";
    }
    if (req) WinHttpCloseHandle(req);
    if (con) WinHttpCloseHandle(con);
    WinHttpCloseHandle(ses);
    return ok;
}

#ifdef MUSIC_HAVE_MP3
// to where the song is now on everyone's clock; leaves the state kReady (or kEnded / kStopped)
void SeekToNow(Source& s) {
    Decoder& d = *s.dec;
    int64_t lead = 0;
    for (int i = 0; i < 4 && !s.cancel; i++) {
        uint64_t t0 = NowMs();
        d.SeekFrames(PosAt(s, t0) + lead);
        if (d.ended) {
            s.state = kEnded;
            return;
        }
        int64_t took = (int64_t)(NowMs() - t0) * kRate / 1000;  // the song moved on meanwhile
        if (lead >= took - kRate / 10) break;                   // within a tenth of a second of it
        lead = took + took / 5;
    }
    s.state = s.cancel ? kStopped : kReady;
}

void StartSeek(const std::shared_ptr<Source>& s) {
    int expected = kReady;
    if (!s->state.compare_exchange_strong(expected, kSeeking)) return;
    std::thread([s] { SeekToNow(*s); }).detach();
}

void LoadMain(std::shared_ptr<Source> s) {
    std::vector<uint8_t> data;
    std::string err;
    if (!Download(*s, data, err)) {
        s->err = err;
        s->state = s->cancel ? kStopped : kFailed;
        return;
    }
    auto d = std::make_shared<Decoder>();
    d->data = std::move(data);
    d->Reset();
    if (!d->DecodeFrame() || !d->hz) {
        s->err = "that is not an MP3 file";
        s->state = kFailed;
        return;
    }
    LOGI("Music: %s: %u bytes, %d Hz", s->url.c_str(), (unsigned)d->data.size(), d->hz);
    d->Reset();
    s->dec = d;
    SeekToNow(*s);
}
#endif

// ---- the mixer: every playing song, by the side and the distance ----
void MixBlock(int16_t* pcm) {
    std::vector<std::shared_ptr<Source>> list;
    {
        std::lock_guard<std::mutex> lk(g_mu);
        list = g_src;
    }
    float acc[kBlock * 2] = {};
#ifdef MUSIC_HAVE_MP3
    float tmp[kBlock * 2];
    for (auto& s : list) {
        if (s->state != kReady) continue;
        Decoder& d = *s->dec;
        int64_t want = PosAt(*s, NowMs());
        int64_t diff = want - d.out;
        if (diff > kResync || diff < -kResync) {
            StartSeek(s);
            continue;
        }
        for (int k = 0; k < 4 && want - d.out > kBlock * 2; k++) d.Read(tmp, kBlock);  // behind: catch up
        if (want - d.out < -kBlock / 2) continue;  // ahead: wait in silence
        d.Read(tmp, kBlock);
        if (d.ended) s->state = kEnded;
        const float tl = s->gL, tr = s->gR;
        for (int i = 0; i < kBlock; i++) {
            float f = (float)(i + 1) / kBlock;
            float gl = s->curL + (tl - s->curL) * f, gr = s->curR + (tr - s->curR) * f;
            acc[2 * i] += tmp[2 * i] * gl;
            acc[2 * i + 1] += tmp[2 * i + 1] * gr;
        }
        s->curL = tl;
        s->curR = tr;
    }
#endif
    for (int i = 0; i < kBlock * 2; i++) pcm[i] = (int16_t)(std::clamp(acc[i], -1.0f, 1.0f) * 32767.0f);
}

void MixerMain() {
    WAVEFORMATEX f{};
    f.wFormatTag = WAVE_FORMAT_PCM;
    f.nChannels = 2;
    f.nSamplesPerSec = kRate;
    f.wBitsPerSample = 16;
    f.nBlockAlign = 4;
    f.nAvgBytesPerSec = kRate * 4;
    HWAVEOUT out = nullptr;
    if (waveOutOpen(&out, WAVE_MAPPER, &f, 0, 0, CALLBACK_NULL) != MMSYSERR_NOERROR) {
        LOGI("Music: could not open the sound device");
        g_mixAlive = false;
        return;
    }
    std::vector<int16_t> pcm[kBufs];
    WAVEHDR hdr[kBufs] = {};
    for (int i = 0; i < kBufs; i++) {
        pcm[i].assign(kBlock * 2, 0);
        hdr[i].lpData = (LPSTR)pcm[i].data();
        hdr[i].dwBufferLength = kBlock * 4;
        waveOutPrepareHeader(out, &hdr[i], sizeof(WAVEHDR));
        waveOutWrite(out, &hdr[i], sizeof(WAVEHDR));
    }
    uint64_t emptySince = 0;
    while (g_mixRun) {
        for (int i = 0; i < kBufs; i++) {
            if (!(hdr[i].dwFlags & WHDR_DONE)) continue;
            MixBlock(pcm[i].data());
            waveOutWrite(out, &hdr[i], sizeof(WAVEHDR));
        }
        {
            std::lock_guard<std::mutex> lk(g_mu);
            if (!g_src.empty()) emptySince = 0;
            else if (!emptySince) emptySince = NowMs();
        }
        if (emptySince && NowMs() - emptySince > 3000) break;  // nothing to play for a while: the device is let go
        Sleep(4);
    }
    waveOutReset(out);
    for (int i = 0; i < kBufs; i++) waveOutUnprepareHeader(out, &hdr[i], sizeof(WAVEHDR));
    waveOutClose(out);
    g_mixAlive = false;
}

void EnsureMixer() {
    if (g_mixAlive) return;
    if (g_mixThread.joinable()) g_mixThread.join();
    g_mixRun = true;
    g_mixAlive = true;
    g_mixThread = std::thread(MixerMain);
}

void StopMixer() {
    g_mixRun = false;
    if (g_mixThread.joinable()) g_mixThread.join();
    g_mixAlive = false;
}

// ---- small things ----
float Dot(const CVector& a, const CVector& b) { return a.x * b.x + a.y * b.y + a.z * b.z; }
CVector Cross(const CVector& a, const CVector& b) {
    return CVector{a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x};
}

bool ValidUrl(const std::string& u) {
    if (u.size() < 10 || u.size() > kMaxUrl) return false;
    std::string head = ToLower(u.substr(0, 8));
    if (head.rfind("http://", 0) != 0 && head.rfind("https://", 0) != 0) return false;
    for (unsigned char c : u)
        if (c <= 32 || c == 127) return false;
    return true;
}

std::string HostOf(const std::string& u) {  // for the chat: the site, not the whole link
    size_t a = u.find("://");
    a = a == std::string::npos ? 0 : a + 3;
    size_t b = u.find_first_of("/:?#", a);
    return u.substr(a, b == std::string::npos ? std::string::npos : b - a);
}

class Music : public Module {
public:
    const char* Name() const override { return "Music"; }

    void OnInstallHooks() override {
        Net().SetHandler(proto::G_MUSIC, [](uint8_t from, Reader& r) { Instance().Handle(from, r); });
    }
    void OnPeerLeave(uint8_t id) override { Stop(id); }
    void OnSessionEnd() override { StopAll(); }
    void OnGameShutdown() override { StopAll(); }

    bool OnCommand(const std::string& cmd, const std::vector<std::string>& args) override {
        if (cmd != "music" && cmd != "musica") return false;
        auto say = [](const std::string& t) { ui::TheChat().AddSystem(t); };
        if (args.empty()) {
            say(TR("Музыка по ссылке: /music <ссылка на MP3>, /music stop, /music vol <0-100>, /music hear <on|off>",
                   "URL music: /music <link to an MP3>, /music stop, /music vol <0-100>, /music hear <on|off>"));
            return true;
        }
        std::string a = ToLower(args[0]);
        if (a == "stop" || a == "parar") {
            Stop(Net().MyId());
            if (Net().Online()) SendStop();
            say(TR("Музыка выключена.", "Music stopped."));
        } else if (a == "vol" || a == "volume") {
            if (args.size() < 2) {
                say(Format(TR("Громкость музыки: %d%%.", "Music volume: %d%%."), (int)std::lround(g_vol * 100)));
            } else {
                g_vol = std::clamp(atoi(args[1].c_str()), 0, 100) / 100.0f;
                say(Format(TR("Громкость музыки: %d%%.", "Music volume: %d%%."), (int)std::lround(g_vol * 100)));
            }
        } else if (a == "hear" || a == "ouvir") {
            std::string v = args.size() > 1 ? ToLower(args[1]) : "";
            m_hear = !(v == "off" || v == "nao" || v == "no" || v == "0");
            if (!m_hear) StopOthers();
            say(m_hear ? TR("Чужая музыка включена.", "Others' music is on.")
                       : TR("Чужая музыка выключена: ссылки партнёров не загружаются.",
                            "Others' music is off: partners' links are not loaded."));
        } else {
            Play(args[0]);
        }
        return true;
    }

    // the game thread, every frame: where each song is, how loud on each side
    void OnPostProcess() override {
        std::vector<std::shared_ptr<Source>> list;
        {
            std::lock_guard<std::mutex> lk(g_mu);
            list = g_src;
        }
        if (list.empty()) return;
        const CVector ear = cam::Source();
        CVector right = Cross(cam::Front(), cam::Up());
        float rl = std::sqrt(Dot(right, right));
        if (rl > 1e-4f) right = right * (1.0f / rl);
        CPlayerPed* me = FindPlayerPed(0);
        CVehicle* myCar = me ? me->VehicleIfIn() : nullptr;

        for (auto& s : list) {
            int st = s->state;
            if (st == kFailed) {
                ui::TheChat().AddError(Format(TR("Музыка не загрузилась (%s): %s", "The music did not load (%s): %s"),
                                              HostOf(s->url).c_str(), s->err.c_str()));
                LOGI("Music: %s failed: %s", s->url.c_str(), s->err.c_str());
            }
            if (st == kFailed || st == kEnded || st == kStopped) {
                Remove(s);
                continue;
            }
            CVector at;
            CVehicle* car = nullptr;
            if (!Anchor(s->owner, at, car)) {
                s->gL = s->gR = 0.0f;
                continue;
            }
            float gain, pan = 0.0f;
            if (car && car == myCar) {  // in the same car: all of it, from everywhere
                gain = 1.0f;
            } else {
                CVector d = at - ear;
                float dist = std::sqrt(Dot(d, d));
                float x = std::clamp((dist - kFullM) / (kFarM - kFullM), 0.0f, 1.0f);
                gain = (1.0f - x) * (1.0f - x);
                if (dist > 1.0f) pan = std::clamp(Dot(d * (1.0f / dist), right), -1.0f, 1.0f);
            }
            float th = (pan + 1.0f) * kPi / 4.0f, v = gain * g_vol * 1.41421356f;  // equal power, centre = full
            s->gL = std::cos(th) * v;
            s->gR = std::sin(th) * v;
            if (s->owner == Net().MyId() && Net().Online() && NowMs() - s->lastBeat >= kBeatMs) SendPlay(*s);
        }
    }

    static Music& Instance() {
        static Music m;
        return m;
    }

private:
    bool m_hear = true;
    uint32_t m_serial = (uint32_t)NowMs();

    // where a player's music comes from: its car's trunk, or the player itself on foot
    static bool Anchor(uint8_t owner, CVector& at, CVehicle*& car) {
        CPed* ped = nullptr;
        if (owner == Net().MyId()) {
            ped = FindPlayerPed(0);
        } else if (RemotePlayer* rp = Players::Instance().Get(owner)) {
            ped = rp->ped;
        }
        if (!ped) return false;
        car = ped->VehicleIfIn();
        if (car) {
            CMatrix* m = car->Matrix();
            if (m) {
                at = m->pos - m->forward * kTrunkM + m->up * 0.3f;
                return true;
            }
        }
        car = nullptr;
        at = ped->GetPosition();
        return true;
    }

    std::shared_ptr<Source> Find(uint8_t owner) {
        std::lock_guard<std::mutex> lk(g_mu);
        for (auto& s : g_src)
            if (s->owner == owner) return s;
        return nullptr;
    }
    void Remove(const std::shared_ptr<Source>& s) {
        s->cancel = true;
        std::lock_guard<std::mutex> lk(g_mu);
        g_src.erase(std::remove(g_src.begin(), g_src.end(), s), g_src.end());
    }
    void Stop(uint8_t owner) {
        if (auto s = Find(owner)) {
            s->state = kStopped;
            Remove(s);
        }
    }
    void StopOthers() {
        std::vector<std::shared_ptr<Source>> list;
        {
            std::lock_guard<std::mutex> lk(g_mu);
            list = g_src;
        }
        for (auto& s : list)
            if (s->owner != Net().MyId()) {
                s->state = kStopped;
                Remove(s);
            }
    }
    void StopAll() {
        std::vector<std::shared_ptr<Source>> list;
        {
            std::lock_guard<std::mutex> lk(g_mu);
            list = g_src;
        }
        for (auto& s : list) {
            s->state = kStopped;
            Remove(s);
        }
        StopMixer();
    }

    void Start(uint8_t owner, uint32_t serial, const std::string& url, uint64_t startMs) {
#ifdef MUSIC_HAVE_MP3
        auto s = std::make_shared<Source>();
        s->owner = owner;
        s->serial = serial;
        s->url = url;
        s->startMs = startMs;
        s->lastBeat = NowMs();
        {
            std::lock_guard<std::mutex> lk(g_mu);
            g_src.push_back(s);
        }
        EnsureMixer();
        std::thread([s] { LoadMain(s); }).detach();
#else
        (void)owner; (void)serial; (void)url; (void)startMs;
#endif
    }

    void Play(const std::string& url) {
#ifndef MUSIC_HAVE_MP3
        (void)url;
        ui::TheChat().AddError(TR("Эта сборка без minimp3: музыка по ссылке выключена.",
                                  "This build has no minimp3: URL music is off."));
#else
        if (!ValidUrl(url)) {
            ui::TheChat().AddError(TR("Нужна ссылка http:// или https:// (до 500 знаков).",
                                      "Give an http:// or https:// link (up to 500 characters)."));
            return;
        }
        uint8_t me = Net().MyId();
        Stop(me);
        ui::TheChat().AddSystem(Format(TR("Музыка: загружаю с %s ...", "Music: loading from %s ..."), HostOf(url).c_str()));
        uint32_t serial = ++m_serial;
        Start(me, serial, url, NowMs());
        if (Net().Online())
            if (auto s = Find(me)) SendPlay(*s);
#endif
    }

    void SendPlay(Source& s) {
        s.lastBeat = NowMs();
        Writer w(proto::G_MUSIC);
        w.U8(1);
        w.U32(s.serial);
        w.U32((uint32_t)std::min<uint64_t>(NowMs() - s.startMs, 0xFFFFFFFFu));
        w.Str(s.url, kMaxUrl);
        Net().Send(proto::CH_RELIABLE, w);
    }
    void SendStop() {
        Writer w(proto::G_MUSIC);
        w.U8(0);
        w.U32(0);
        Net().Send(proto::CH_RELIABLE, w);
    }

    void Handle(uint8_t from, Reader& r) {
        uint8_t op = r.U8();
        uint32_t serial = r.U32();
        if (!r.Ok() || from == Net().MyId()) return;
        if (op == 0) {
            if (Find(from)) {
                Stop(from);
                ui::TheChat().AddSystem(
                    Format(TR("%s выключает музыку.", "%s stops the music."), Net().PeerName(from).c_str()));
            }
            return;
        }
        uint32_t elapsed = r.U32();
        std::string url = r.Str(kMaxUrl);
        if (!r.Ok() || !m_hear || !ValidUrl(url)) return;
        auto s = Find(from);
        if (s && s->serial == serial && s->url == url) return;  // what it already plays: the repeat for latecomers
        Stop(from);
        ui::TheChat().AddSystem(
            Format(TR("%s включает музыку (%s).", "%s plays music (%s)."), Net().PeerName(from).c_str(), HostOf(url).c_str()));
        LOGI("Music: partner %d plays %s from %u ms", from, url.c_str(), elapsed);
        Start(from, serial, url, NowMs() - elapsed);
    }
};

struct Reg {
    Reg() { core::RegisterModule(&Music::Instance()); }
} g_reg;

}  // namespace
}  // namespace coop::music
