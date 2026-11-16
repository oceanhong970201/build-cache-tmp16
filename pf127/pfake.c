// pfake.c — ptrace anti-analysis neutralizer for SRBMiner-MULTI (v10, multithread)
// v10: per-tid regenerated status fakes (v9 served one stale leader-pid file —
//      a checker thread reading /proc/self/status saw a Pid that wasn't its own
//      tid: identity mismatch -> engine re-checked forever), thread-exit disarm
//      to full speed, 50M-silent-step fallback disarm, PFAKE_NOSTEP knob.
// usage: ./pfake /path/to/SRBMiner-MULTI [args...]
//
// Syscall mode: rewrite open/openat of
//   /proc/self/status      -> /tmp/.fakestatus (TracerPid/Seccomp/NoNewPrivs = 0)
//   /proc/<pid>/cmdline    -> /tmp/.fc ("bash\0")  — hides tracer/wrapper parent
// Step mode (engaged after first status read, disarmed at first clone/100K steps):
//   cpuid  (0F A2): execute real, then patch results — leaf 1 clear ECX bit 31,
//        leaf 0x40000000+ zeroed (hides hypervisor CPUID leaves)
//   rdtsc  (0F 31): execute, then replace rax/rdx with a slow fake TSC
//   syscall (0F 05) insns stepped through get the path rewrites inline
// All traced threads (PTRACE_O_TRACECLONE): SIGTRAP signal-delivery stops are
// swallowed (int3 anti-debug bytes in the packer never reach the process).
// Multithreaded: waitpid(-1, __WALL), per-pid syscall-entry state.
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <time.h>
#include <sys/ptrace.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/user.h>
#include <sys/reg.h>
#include <sys/prctl.h>
#include <stddef.h>

#define FAKE "/tmp/.fakestatus"
#define FAKE_CMD "/tmp/.fc"      // parent/tracer cmdline: "bash"
#define FAKE_OWNCMD "/tmp/.fc2"  // tracee's own cmdline: real argv
#define DISARM_STEPS 100000UL
#define STEP_BUDGET  2000000000UL
#define WIN_STEPS    2500000UL

static unsigned long long real_tsc(void) {
    unsigned int lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return ((unsigned long long)hi << 32) | lo;
}
#define NONE_LEAF    0xFFFFFFFFFFFFFFFFUL
#define RDTSC_LEAF   0xFFFFFFFEUL

static pid_t g_leader = 0;
static int g_argc = 0;
static char **g_argv = NULL;

static void make_fake_selfcmd(void) {
    FILE *o = fopen(FAKE_OWNCMD, "w");
    if (!o) return;
    for (int i = 1; i < g_argc; i++) {
        fputs(g_argv[i], o);
        fputc(0, o);
    }
    fclose(o);
}

#define MAXPIDS 128
static pid_t g_pids[MAXPIDS];
static int g_entering[MAXPIDS];
static unsigned long g_pending[MAXPIDS];
static int g_npids = 0;
static unsigned long g_puname[MAXPIDS];
static unsigned char g_rdtscp[MAXPIDS];
static unsigned long g_clkc[MAXPIDS];  // pending clock-syscall result buffer addr
static unsigned int g_clkn[MAXPIDS];   // which clock syscall (228/96/201)
static int g_stepping = 0;
static unsigned long g_fake_tsc = 0;
static unsigned long g_steps_since_scrub = 0;
static int no_step = 0;                     // v10: PFAKE_NOSTEP — never engage stepping
static unsigned long g_total_steps = 0;     // v10: total stepped instructions
static unsigned long g_last_proc_open = 0;  // v10: step count at last /proc open
static unsigned char g_pprctl[MAXPIDS];     // v10.1: pending prctl GET_SECCOMP/NNP rewrite
static unsigned long g_syscnt[MAXPIDS];     // v10.4: syscalls executed since last rdtsc scrub
static unsigned char g_pgetppid[MAXPIDS];   // v10.6: pending getppid -> 1 rewrite
static int clone_veto = 0;                  // v10.6b: PFAKE_CLONEVETO — deny engine thread spawns while stepping
static int c1_off = 0;                      // v12.7: PFAKE_C1OFF — disable veto-point bypass, force C2 fallback
static unsigned long g_last_scrub_rtsc = 0; // v10.8: real tsc at last rdtsc scrub (gap-size domain switch)
static int late_engage = 0;                 // v10.9: PFAKE_LATEENGAGE — unpacker runs full speed, engage at first status read
static int g_sigtrap_on = 0;                // v10.2: child installed a SIGTRAP handler

// ---- v11: DR-breakpoint mode ----
// Calibrate rdtsc/rdtscp sites while stepping, then drop stepping and arm
// hardware execute breakpoints (DR0-3) on the hot sites. From then on the
// engine runs at full speed under PTRACE_SYSCALL; each rdtsc traps once,
// is emulated with the fake-domain value, and execution skips the insn.
// The engine never executes a real rdtsc again, and the syscall-stop
// dilation is subtracted out of the domain advance (what an untraced run
// would have read), so timed pairs stay plausible.
static int dr_mode = 0;                     // v11: DR breakpoints armed, stepping off
static int use_dr = 0;                       // v11.4: PFAKE_DR=1 enables the v11.2 DR switch (default off — v11.4 mode)
static int no_dr = 0;                       // v11: PFAKE_NODR=1 — stay stepped, never switch
static unsigned long g_rd_sites[16];        // v11: calibrated rdtsc/rdtscp site addresses
static int g_rd_kind[16];                   // 0 = rdtsc (2B), 1 = rdtscp (3B)
static int g_nrd = 0;
static int g_rd_events = 0;                 // total scrubbed rdtsc events seen
static int g_rd_lastnew = 0;                // event index at last NEW site
static unsigned long g_rd_hits[16];         // v11: per-site hit count — arm the 4 hottest
static unsigned long g_dil_per_sys = 150000UL; // v11: cycles of tracer dilation per syscall stop
static int g_post_switch_dumps = 0;           // v11: debug — first stops after the DR switch
static unsigned long g_steps_since_syscall = 0; // v11.3: steps since last syscall insn (parse-over detector)

// ---- v12: clocks join the fake timeline ----
// v11.8 postmortem: 105 rounds pass, checker exits clean, leader SIGSEGV.
// The engine's pairs are FINE-GRAINED (per read-window, real gaps <20ms ->
// the short-gap scrub formula -> fake delta ~0.4us) while clock_gettime
// told the TRUTH (~15ms real per window) -> 10000x cross-domain ratio ->
// tamper verdict. v12: every clock (vdso call AND syscall) reads the same
// fake timeline as the scrubbed tsc: fake_ns = anchor_ns + (fake_tsc -
// anchor_tsc)/hz. Domains: read-dense parse = stepped + fake clock (ratio
// exactly 1 by construction); pure spins flip to full speed (real clock +
// real tsc, also consistent); nanosleep advances the domain by dur*2 so
// clock gates still expire (~0.8x). Rebase anchors at every re-engage.
static unsigned long g_vdso_lo = 0, g_vdso_hi = 0;   // [vdso] range from leader maps
static unsigned long long g_anchor_tsc = 0, g_anchor_ns = 0;
static unsigned long long g_tsc_mult = 0;            // Q20 fixed-point ns-per-cycle*2^20
static int g_pvdso[MAXPIDS];                         // pending vdso clock call on tid
static unsigned long g_vdret[MAXPIDS];               // its return rip
static unsigned long g_vdts[MAXPIDS];                // captured arg2 (timespec/timeval ptr)
static unsigned char g_invdso_prev[MAXPIDS];        // v12: rip was inside vdso at the previous stop
static int g_vtrace = 0;                            // v12.1: verdict-trace active (checker exited)
static int g_vtcnt = 0;                             // v12.1: logged insns so far
// v12.3: the engine's verdict-fail suicide = jmp 0xdead9001 (unmapped marker)
// -> SIGSEGV -> kernel kills the whole process (leader dies by group-kill,
// no tgkill involved — v12.2's si_addr fingerprint proved it). Neutralizer:
// a 64-entry rip ring per tid; at the dead9001 delivery-stop, swallow the
// signal and redirect rip to the faulting jmp's fall-through = the PASS
// continuation. The verdict phase must run STEPPED for the ring to hold the
// jmp site — hence the flip veto at engage > 90.
static unsigned long g_ring_rip[MAXPIDS][64];
static int g_ring_n[MAXPIDS];
static unsigned long g_dead_kills = 0;
static int g_flip_veto_logged = 0;
// v12.7: verdict bypass via round-head anchor. The engine's death is
// dispatch-ret-to-0xdead9001 with all registers zeroed (no recoverable
// context). Instead of chasing the pass value, snapshot the FULL register
// set at every status-open syscall entry (round head); on verdict fire,
// restore the anchor and re-issue the open — the engine re-enters the
// next round and the verdict phase is bypassed entirely.
static struct user_regs_struct g_anchor[MAXPIDS];
static int g_anchor_ok[MAXPIDS];
static unsigned long g_bypasses = 0;
static unsigned long g_ruc[MAXPIDS];                 // getrusage rusage ptr
static unsigned long g_vdclk = 0, g_clk_rw = 0;      // scrub counters

static unsigned long long real_ns_(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (unsigned long long)ts.tv_sec * 1000000000ULL + (unsigned long)ts.tv_nsec;
}
static void clock_anchor_now(void) {
    g_anchor_tsc = g_fake_tsc + 2ULL * g_steps_since_scrub;
    g_anchor_ns = real_ns_();
}
static unsigned long long fake_ns(void) {
    unsigned long long ft = g_fake_tsc + 2ULL * g_steps_since_scrub;
    return g_anchor_ns + ((ft - g_anchor_tsc) * g_tsc_mult >> 20);
}
static void scrub_vdso_return_(pid_t t, int slot, struct user_regs_struct *regs) {
    unsigned long long ns = fake_ns();
    unsigned long sec = (unsigned long)(ns / 1000000000ULL);
    unsigned long nsec = (unsigned long)(ns % 1000000000ULL);
    if (g_vdts[slot]) {
        ptrace(PTRACE_POKEDATA, t, g_vdts[slot], (void *)sec);
        ptrace(PTRACE_POKEDATA, t, g_vdts[slot] + 8, (void *)nsec);
    }
    regs->rax = 0; // success
    ptrace(PTRACE_SETREGS, t, 0, regs);
    g_pvdso[slot] = 0;
    g_vdclk++;
    if (g_vdclk <= 10 || g_vdclk % 500 == 0)
        fprintf(stderr, "[pfake] v12: vdso clock #%lu fake=%lu.%09lu (tid %d)\n",
                g_vdclk, sec, nsec, (int)t);
}


// v10.2: packer int3s arrive BEFORE any handler (delivery = default death);
// engine canary int3s arrive after rt_sigaction(SIGTRAP, real_handler).
static void note_sigaction(pid_t t, unsigned long signum, unsigned long act) {
    if (signum != 5 || act == 0) return;
    errno = 0;
    long h = ptrace(PTRACE_PEEKDATA, t, act, 0);
    if (errno != 0) return;
    g_sigtrap_on = !(h == 0 || h == 1); // SIG_DFL / SIG_IGN don't count
}

// ---- v11: DR-breakpoint machinery ----
#define DR_OFF(n) (offsetof(struct user, u_debugreg[n]))

// Arm up to 4 hardware execute breakpoints on the calibrated sites for one
// thread. Sites are verified against the live instruction bytes first, so a
// mismatched/ASLR-shifted address is skipped rather than mis-trapped.
static void arm_dr_on(pid_t t) {
    struct { unsigned long a; int kind; } pick[4];
    int n = 0;
    // pick the 4 HOTTEST sites (discovery order breaks ties)
    for (int round = 0; round < 4 && n < 4; round++) {
        int best = -1;
        for (int i = 0; i < g_nrd; i++) {
            if (g_rd_hits[i] == 0) continue;
            int taken = 0;
            for (int j = 0; j < n; j++) if (pick[j].a == g_rd_sites[i]) { taken = 1; break; }
            if (taken) continue;
            if (best < 0 || g_rd_hits[i] > g_rd_hits[best]) best = i;
        }
        if (best < 0) break;
        errno = 0;
        long w = ptrace(PTRACE_PEEKDATA, t, g_rd_sites[best], 0);
        if (errno != 0) { g_rd_hits[best] = 0; continue; } // unmapped now: drop from candidates
        uint16_t b = (uint16_t)(w & 0xFFFF);
        int ok = (g_rd_kind[best] == 0 && b == 0x310F) ||
                 (g_rd_kind[best] == 1 && b == 0x010F && (int)((w >> 16) & 0xFF) == 0xF9);
        if (!ok) { g_rd_hits[best] = 0; continue; } // insn changed: drop
        pick[n].a = g_rd_sites[best]; pick[n].kind = g_rd_kind[best]; n++;
    }
    if (n == 0) return;
    unsigned long dr7 = 0x400; // bit 10 must stay 1 (reserved)
    for (int i = 0; i < n; i++) {
        long rc = ptrace(PTRACE_POKEUSER, t, (void *)DR_OFF(i), (void *)pick[i].a);
        dr7 |= 1UL << i; // v11.2: LOCAL enable Li (bits 0-3). The GLOBAL bits
        // (4-7) silently do not raise #DB under this Hyper-V/WSL kernel with
        // ptrace-written DRs — L-bits verified firing via the drmim harness.
        // Kernel context switch restores DR7 per thread (TIF_DEBUG), so L
        // survives scheduling.
        if (rc != 0)
            fprintf(stderr, "[pfake] dr poke DR%d off=%ld FAILED rc=%ld errno=%d\n",
                    i, (long)DR_OFF(i), rc, errno);
        else
            fprintf(stderr, "[pfake] armed DR%d tid %d site=%lx kind=%d\n",
                    i, (int)t, pick[i].a, pick[i].kind);
    }
    long rc7 = ptrace(PTRACE_POKEUSER, t, (void *)DR_OFF(7), (void *)dr7);
    long rb0 = ptrace(PTRACE_PEEKUSER, t, (void *)DR_OFF(0), 0);
    long rb7 = ptrace(PTRACE_PEEKUSER, t, (void *)DR_OFF(7), 0);
    fprintf(stderr, "[pfake] dr7 poke rc=%ld readback dr0=%lx dr7=%lx (want dr7=%lx)\n",
            rc7, rb0, rb7, dr7);
    if (rb7 == -1 && errno != 0) return;
}

// Record one scrubbed rdtsc site; fire the DR switch once the site set is
// stable (60+ events, no new site in the last 25, or 400 events hard cap).
static void record_rd_site(unsigned long site, int is_rdtscp, pid_t t, int slot) {
    int known = 0;
    for (int i = 0; i < g_nrd; i++) if (g_rd_sites[i] == site) { g_rd_hits[i]++; known = 1; break; }
    if (!known && g_nrd < 16) {
        g_rd_sites[g_nrd] = site;
        g_rd_kind[g_nrd] = is_rdtscp;
        g_rd_hits[g_nrd] = 1;
        g_nrd++;
        g_rd_lastnew = g_rd_events;
    }
    g_rd_events++;
    if (!use_dr || no_dr || dr_mode || g_nrd == 0) return;
    if (g_rd_events >= 60 && (unsigned)(g_rd_events - g_rd_lastnew) >= 25) {
        dr_mode = 1;
        g_stepping = 0;
        g_last_scrub_rtsc = real_tsc();
        g_syscnt[slot] = 0;
        for (int i = 0; i < g_npids; i++) arm_dr_on(g_pids[i]);
        fprintf(stderr, "[pfake] v11: DR mode engaged — %d sites, stepping OFF at event %d (tid %d)\n",
                g_nrd, g_rd_events, (int)t);
    }
}

static int pid_slot(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) return i;
    if (g_npids >= MAXPIDS) return -1;
    g_pids[g_npids] = p; g_entering[g_npids] = 1; g_pending[g_npids] = NONE_LEAF; g_puname[g_npids] = 0; g_rdtscp[g_npids] = 0; g_clkc[g_npids] = 0; g_clkn[g_npids] = 0; g_pprctl[g_npids] = 0; g_syscnt[g_npids] = 0; g_pgetppid[g_npids] = 0;
    return g_npids++;
}
static void pid_drop(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) {
        for (int j = i; j < g_npids - 1; j++) { g_pids[j] = g_pids[j+1]; g_entering[j] = g_entering[j+1]; g_pending[j] = g_pending[j+1]; g_puname[j] = g_puname[j+1]; g_rdtscp[j] = g_rdtscp[j+1]; g_clkc[j] = g_clkc[j+1]; g_clkn[j] = g_clkn[j+1]; g_pprctl[j] = g_pprctl[j+1]; g_syscnt[j] = g_syscnt[j+1]; g_pgetppid[j] = g_pgetppid[j+1]; }
        g_npids--; return;
    }
}

static void write_fake_uname(pid_t pid, unsigned long addr) {
    struct { char s[65], n[65], r[65], v[65], m[65], d[65]; } u;
    if (!addr) return;
    memset(&u, 0, sizeof u);
    strcpy(u.s, "Linux");
    strcpy(u.n, "workstation");
    strcpy(u.r, "5.15.0-91-generic");
    strcpy(u.v, "#101-Ubuntu SMP Tue Nov 14 13:07:11 UTC 2023");
    strcpy(u.m, "x86_64");
    strcpy(u.d, "(none)");
    for (size_t off = 0; off < sizeof u; off += sizeof(long)) {
        long w;
        size_t chunk = sizeof u - off;
        if (chunk >= sizeof(long)) {
            memcpy(&w, (char *)&u + off, sizeof w);
        } else { // v11.1: RMW tail word — never write past the utsname buffer
            errno = 0;
            long old = ptrace(PTRACE_PEEKDATA, pid, addr + off, 0);
            if (errno != 0) return;
            memcpy(&w, &old, sizeof w);
            memcpy((char *)&w, (char *)&u + off, chunk);
        }
        ptrace(PTRACE_POKEDATA, pid, addr + off, (void *)w);
    }
    fprintf(stderr, "[pfake] uname rewritten\n");
}

// v5: synthetic time domain. Clock syscalls return values derived from the
// fake TSC (2 cycles/ns), so rdtsc pairs and clock_gettime pairs agree and
// tracer-side processing time is invisible to any cross-check.
static void do_clock_rewrite(pid_t t, int slot) {
    // v12: clocks read the FAKE timeline now (same domain as the scrubbed
    // tsc). v10.5's "clocks tell the truth" held the read-dense window
    // ratio at 10000x — the checker's verdict that killed v11.8. Waits
    // still expire: nanosleep advances the domain (dur*2) and pure spins
    // flip to full speed (real clock) via the v11.8 adaptive machinery.
    if (!g_stepping || no_step) {
        // full-speed phase: rdtsc is real, the clock stays real — consistent.
        g_clkc[slot] = 0;
        g_clkn[slot] = 0;
        return;
    }
    unsigned long long ns = fake_ns();
    unsigned long sec = (unsigned long)(ns / 1000000000ULL);
    unsigned long nsec = (unsigned long)(ns % 1000000000ULL);
    int n = g_clkn[slot];
    unsigned long p = g_clkc[slot];
    if (n == 201) { // time(): rax = seconds, optional out ptr
        struct user_regs_struct r;
        if (ptrace(PTRACE_GETREGS, t, 0, &r) == 0) { r.rax = sec; ptrace(PTRACE_SETREGS, t, 0, &r); }
        if (p) ptrace(PTRACE_POKEDATA, t, p, (void *)sec);
    } else if (p) { // clock_gettime/gettimeofday: struct at captured ptr
        ptrace(PTRACE_POKEDATA, t, p, (void *)sec);
        ptrace(PTRACE_POKEDATA, t, p + 8, (void *)nsec);
    }
    g_clk_rw++;
    if (g_clk_rw <= 8 || g_clk_rw % 400 == 0)
        fprintf(stderr, "[pfake] v12: clock syscall #%lu nr=%d fake=%lu.%09lu\n", g_clk_rw, n, sec, nsec);
    g_clkc[slot] = 0;
    g_clkn[slot] = 0;
}

// v10: the fake status must describe the READER, regenerated at every open.
// v9's bug: one file written at startup for the leader — a checker thread
// reading /proc/self/status got Pid:<leader> while its gettid() says otherwise,
// Threads/ctxt-switches frozen at startup values -> engine retried forever.
static void make_fake_status_for(pid_t target, int self_read) {
    char real[64], fake[64], line[512], out[16384];
    snprintf(real, sizeof real, "/proc/%d/status", (int)target);
    snprintf(fake, sizeof fake, "/tmp/.fs%d", (int)target);
    FILE *f = fopen(real, "r");
    if (!f) return;
    out[0] = 0;
    while (fgets(line, sizeof line, f)) {
        if (strncmp(line, "TracerPid:", 10) == 0) strcat(out, "TracerPid:\t0\n");
        else if (strncmp(line, "State:", 6) == 0)
            strcat(out, self_read ? "State:\tR (running)\n" : "State:\tS (sleeping)\n");
        else if (strncmp(line, "PPid:", 5) == 0) strcat(out, "PPid:\t1\n"); // v10.6: daemon reparent profile
        else if (strncmp(line, "Seccomp:", 8) == 0) strcat(out, "Seccomp:\t0\n");        // v10.1: container tell
        else if (strncmp(line, "Seccomp_filters:", 16) == 0) continue;                   // v10.1: drop the line
        else if (strncmp(line, "NoNewPrivs:", 11) == 0) strcat(out, "NoNewPrivs:\t0\n"); // v10.1: container tell
        else strcat(out, line);
    }
    fclose(f);
    FILE *o = fopen(fake, "w");
    if (o) { fputs(out, o); fclose(o); }
}
static void make_fake_status(pid_t target) { make_fake_status_for(target, 0); }

// v7: /proc/<tid>/stat leak — a traced thread's state field reads 't'
// (tracing stop) while stopped. Serve a copy with state 'S'.
static int is_own_process(long n);
static long stat_subject_tid(const char *p, pid_t self) {
    char buf[256];
    strncpy(buf, p, sizeof buf - 1); buf[255] = 0;
    char *s = buf + 6; // past "/proc/"
    if (strncmp(s, "self/", 5) == 0) return (long)self;
    char *end = NULL;
    long n = strtol(s, &end, 10);
    if (end == s) return -1;
    if (*end == '/' && strncmp(end, "/task/", 6) == 0) {
        s = end + 6;
        n = strtol(s, &end, 10);
        if (end == s) return -1;
    }
    return n;
}
static int is_own_stat_path(const char *p, pid_t self) {
    size_t len = strlen(p);
    if (len < 10 || strcmp(p + len - 5, "/stat") != 0) return 0;
    if (strncmp(p, "/proc/", 6) != 0) return 0;
    long n = stat_subject_tid(p, self);
    return n > 0 && is_own_process(n);
}
static int is_own_wchan_path(const char *p, pid_t self) {
    size_t len = strlen(p);
    if (len < 12 || strcmp(p + len - 6, "/wchan") != 0) return 0;
    if (strncmp(p, "/proc/", 6) != 0) return 0;
    long n = stat_subject_tid(p, self);
    return n > 0 && is_own_process(n);
}
// v10: /proc/<tid>/status of an own thread — serve a fresh per-tid fake too.
static int is_own_status_path(const char *p, pid_t self) {
    size_t len = strlen(p);
    if (len < 13 || strcmp(p + len - 7, "/status") != 0) return 0;
    if (strncmp(p, "/proc/", 6) != 0) return 0;
    if (strncmp(p, "/proc/self", 10) == 0) return 0; // handled by the self branch
    long n = stat_subject_tid(p, self);
    return n > 0 && is_own_process(n);
}

static void make_fake_stat(long tid) {
    char real[64], buf[4096];
    snprintf(real, sizeof real, "/proc/%ld/stat", tid);
    int fd = open(real, O_RDONLY);
    if (fd < 0) return;
    ssize_t n = read(fd, buf, sizeof buf - 1);
    close(fd);
    if (n <= 0) return;
    buf[n] = 0;
    char *cp = strrchr(buf, ')');
    if (cp && cp[1] == ' ' && cp[2]) cp[2] = 'S';
    FILE *o = fopen("/tmp/.fstat", "w");
    if (o) { fputs(buf, o); fclose(o); }
}
static void make_fake_cmdline(void) {
    FILE *o = fopen(FAKE_CMD, "w");
    if (o) { fputs("bash\0", o); fclose(o); }
}
static int is_proc_cmdline(const char *p) {
    if (strncmp(p, "/proc/", 6) != 0) return 0;
    size_t i = 6;
    while (p[i] >= '0' && p[i] <= '9') i++;
    return (i > 6) && (strcmp(p + i, "/cmdline") == 0);
}

static int is_own_process(long n) {
    if (n == (long)g_leader) return 1;
    for (int i = 0; i < g_npids; i++) if (n == (long)g_pids[i]) return 1;
    return 0;
}

static int is_self_cmdline(const char *p) {
    if (strcmp(p, "/proc/self/cmdline") == 0) return 1;
    if (strncmp(p, "/proc/", 6) != 0) return 0;
    char *end;
    long n = strtol(p + 6, &end, 10);
    return (end != p + 6 && strcmp(end, "/cmdline") == 0 && is_own_process(n));
}
static int read_str(pid_t pid, unsigned long addr, char *buf, size_t max) {
    size_t i = 0;
    while (i + sizeof(long) <= max) {
        errno = 0;
        long w = ptrace(PTRACE_PEEKDATA, pid, addr + i, 0);
        if (errno != 0) { buf[i] = 0; return -1; }
        memcpy(buf + i, &w, sizeof w);
        for (size_t j = 0; j < sizeof w; j++) if (buf[i + j] == 0) return 0;
        i += sizeof w;
    }
    buf[max ? max - 1 : 0] = 0;
    return 0;
}
static int poke_str(pid_t pid, unsigned long addr, const char *s, size_t cap) {
    // v11.1: POKEDATA writes whole 8-byte words; the old loop rounded cap UP
    // to a word and so smashed up to 7 NUL bytes PAST the target string's
    // footprint into whatever .rodata/code followed it (fmt strings, engine
    // constants — a wild variable in every run since v9). Now: write exactly
    // strlen+1 bytes; the tail word is read-modify-write so nothing beyond
    // the new string's own end is touched.
    char buf[64];
    memset(buf, 0, sizeof buf);
    size_t len = strlen(s);
    if (len >= sizeof buf) len = sizeof buf - 1;
    memcpy(buf, s, len);
    size_t need = len + 1; // string + NUL
    if (need > cap) need = cap;
    for (size_t off = 0; off < need; off += sizeof(long)) {
        long w;
        size_t chunk = need - off;
        if (chunk >= sizeof(long)) {
            memcpy(&w, buf + off, sizeof w);
        } else {
            errno = 0;
            long old = ptrace(PTRACE_PEEKDATA, pid, addr + off, 0);
            if (errno != 0) return -1;
            memcpy(&w, &old, sizeof w);
            memcpy((char *)&w, buf + off, chunk);
        }
        if (ptrace(PTRACE_POKEDATA, pid, addr + off, (void *)w) != 0) return -1;
    }
    return 0;
}
static unsigned long win_rip_min = ~0UL, win_rip_max = 0;
static unsigned page_hits[8192];
// variant knobs (set in main from env)
static int no_tsc = 0, no_maps = 0, no_cmd = 0, no_status = 0;

// dump the executable region containing [lo,hi] from the stopped tracee
static void dump_region(pid_t t, unsigned long lo, unsigned long hi, const char *tag) {
    char mp[48], line[512], path[128], memp[48];
    snprintf(mp, sizeof mp, "/proc/%d/maps", (int)t);
    FILE *m = fopen(mp, "r");
    if (!m) return;
    unsigned long bstart = 0, bend = 0;
    int found = 0;
    while (fgets(line, sizeof line, m)) {
        unsigned long s, e; char perms[8];
        if (sscanf(line, "%lx-%lx %4s", &s, &e, perms) == 3 && perms[0] == 'r' && perms[2] == 'x') {
            if (lo >= s && lo < e) { bstart = s; bend = e; found = 1; break; }
        }
    }
    fclose(m);
    if (!found) { fprintf(stderr, "[pfake] dump %s: rip %lx not in r-x region\n", tag, lo); return; }
    if (hi >= bend) hi = bend - 1;
    if (hi < bstart) hi = bstart + 0x1000;
    const char *home = getenv("HOME");
    if (!home) home = "/tmp";
    snprintf(path, sizeof path, "%s/chk_%s_%lx.bin", home, tag, bstart);
    snprintf(memp, sizeof memp, "/proc/%d/mem", (int)t);
    int fd = open(memp, O_RDONLY);
    FILE *o = fopen(path, "wb");
    if (fd < 0 || !o) { if (fd >= 0) close(fd); if (o) fclose(o); return; }
    static char buf[1 << 22];
    unsigned long len = hi - bstart + 1;
    if (len > sizeof buf) len = sizeof buf;
    ssize_t got = pread(fd, buf, len, (off_t)bstart);
    if (got > 0) fwrite(buf, 1, (size_t)got, o);
    close(fd); fclose(o);
    // hot pages
    fprintf(stderr, "[pfake] dump %s: region %lx-%lx rips %lx-%lx -> %s (%ld bytes)\n",
            tag, bstart, bend, lo, hi, path, (long)got);
    fprintf(stderr, "[pfake] hot pages:");
    for (int k = 0; k < 6; k++) {
        unsigned best = 0; unsigned long bestpg = 0;
        for (unsigned i = 0; i < 8192; i++)
            if (page_hits[i] > best) { best = page_hits[i]; bestpg = i; }
        if (!best) break;
        page_hits[bestpg] = 0;
        fprintf(stderr, " %lx:%u", bestpg << 12, best);
    }
    fprintf(stderr, "\n");
}

static int build_fake_maps(pid_t pid) {
    char mp[48];
    snprintf(mp, sizeof mp, "/proc/%d/maps", (int)pid);
    FILE *m = fopen(mp, "r");
    if (!m) return -1;
    FILE *o = fopen("/tmp/.fm", "w");
    if (!o) { fclose(m); return -1; }
    char line[512];
    int has_vsys = 0;
    while (fgets(line, sizeof line, m)) {
        if (strstr(line, "vvar_vclock")) continue;   // WSL2-kernel signature
        if (strstr(line, "/usr/lib/wsl/")) continue; // WSL-specific libs
        if (strstr(line, "[vsyscall]")) has_vsys = 1;
        fputs(line, o);
    }
    fclose(m);
    if (!has_vsys)
        fputs("fffffffffff600000-ffffffffffffd000 --xp 00000000 00:00 0  [vsyscall]\n", o);
    fclose(o);
    return 0;
}

static void rewrite_open_path(pid_t pid, unsigned long nr, struct user_regs_struct *regs) {
    unsigned long pa = (nr == 257) ? regs->rsi : regs->rdi;
    if (!pa) return;
    char path[256];
    if (read_str(pid, pa, path, sizeof path) != 0) return;
    fprintf(stderr, "[pfake] open: %s\n", path);
    if (strncmp(path, "/proc/", 6) == 0) g_last_proc_open = g_total_steps; // v10 disarm heuristic
    if (strcmp(path, "/proc/self/status") == 0) {
        if (!no_status) {
            make_fake_status_for(pid, 1);
            char fake[64];
            snprintf(fake, sizeof fake, "/tmp/.fs%d", (int)pid);
            poke_str(pid, pa, fake, strlen(path) + 1);
            fprintf(stderr, "[pfake] self status -> %s\n", fake);
        }
    } else if (is_own_status_path(path, pid)) {
        if (!no_status) {
            long n = stat_subject_tid(path, pid);
            make_fake_status_for((pid_t)n, 0);
            char fake[64];
            snprintf(fake, sizeof fake, "/tmp/.fs%ld", n);
            poke_str(pid, pa, fake, strlen(path) + 1);
            fprintf(stderr, "[pfake] tid status -> %s\n", fake);
        }
    } else if (is_self_cmdline(path)) {
        if (!no_cmd) poke_str(pid, pa, FAKE_OWNCMD, strlen(path) + 1);
        fprintf(stderr, "[pfake] own cmdline\n");
    } else if (is_proc_cmdline(path)) {
        fprintf(stderr, "[pfake] other cmdline passthrough: %s\n", path);
    } else if (strcmp(path, "/proc/self/maps") == 0) {
        if (!no_maps && build_fake_maps(pid) == 0) {
            poke_str(pid, pa, "/tmp/.fm", strlen(path) + 1);
            fprintf(stderr, "[pfake] rewrote maps -> /tmp/.fm\n");
        }
    } else if (is_own_stat_path(path, pid)) {
        make_fake_stat(stat_subject_tid(path, pid));
        if (access("/tmp/.fstat", R_OK) == 0) {
            poke_str(pid, pa, "/tmp/.fstat", strlen(path) + 1);
            fprintf(stderr, "[pfake] rewrote stat -> /tmp/.fstat\n");
        }
    } else if (is_own_wchan_path(path, pid)) {
        FILE *o = fopen("/tmp/.fwc", "w");
        if (o) { fputs("0\n", o); fclose(o); }
        poke_str(pid, pa, "/tmp/.fwc", strlen(path) + 1);
        fprintf(stderr, "[pfake] rewrote wchan -> /tmp/.fwc\n");
    }
}

static void fake_own_cmdline(int argc, char **argv) {
    // overwrite our argv block so /proc/<our pid>/cmdline reads as a bash launcher
    size_t total = 0;
    for (int i = 0; i < argc; i++) total += strlen(argv[i]) + 1;
    char buf[2048];
    size_t o = 0;
    o += (size_t)snprintf(buf + o, sizeof buf - o, "bash"); buf[o++] = 0;
    o += (size_t)snprintf(buf + o, sizeof buf - o, "-c"); buf[o++] = 0;
    for (int i = 1; i < argc && o < sizeof buf - 1; i++)
        o += (size_t)snprintf(buf + o, sizeof buf - o, "%s%s", i > 1 ? " " : "", argv[i]);
    buf[o++] = 0;
    if (o <= total && total < 4096) {
        memcpy(argv[0], buf, o);
        memset(argv[0] + o, 0, total - o);
    }
    prctl(PR_SET_NAME, "bash", 0, 0, 0);
}

int main(int argc, char **argv) {
    setvbuf(stderr, NULL, _IONBF, 0);
    g_argc = argc; g_argv = argv;
    if (argc < 2) { fprintf(stderr, "usage: %s prog [args]\n", argv[0]); return 2; }
    pid_t leader = fork();
    if (leader == 0) {
        ptrace(PTRACE_TRACEME, 0, 0, 0);
        execv(argv[1], argv + 1);
        _exit(127);
    }
    int status;
    if (waitpid(leader, &status, 0) < 0) return 1;
    ptrace(PTRACE_SETOPTIONS, leader, 0,
           (void *)(PTRACE_O_TRACESYSGOOD | PTRACE_O_TRACECLONE | PTRACE_O_TRACEFORK));
    make_fake_status(leader);
    make_fake_cmdline();
    g_leader = leader;
    make_fake_selfcmd();
    fake_own_cmdline(argc, argv); // our own /proc cmdline = "bash -c <target>"
    no_step = getenv("PFAKE_NOSTEP") != NULL;   // v10.7: needed before the birth-stepping decision
    clone_veto = getenv("PFAKE_CLONEVETO") != NULL;
    c1_off = getenv("PFAKE_C1OFF") != NULL;     // v12.7: disable veto-point bypass (test C2 fallback)
    late_engage = getenv("PFAKE_LATEENGAGE") != NULL; // v10.9
    use_dr = getenv("PFAKE_DR") != NULL;      // v11.4: optional DR switch experiment
    no_dr = getenv("PFAKE_NODR") != NULL;     // v11: stay stepped forever
    { const char *d = getenv("PFAKE_DIL"); if (d) g_dil_per_sys = strtoul(d, 0, 0); }
    pid_slot(leader);
    // v10.7: step from BIRTH. The engine's early phase (dynamic loader, ifunc
    // cpuid dispatch, early rdtsc probes) all runs BEFORE the first status
    // open — engaging there left the loader's REAL hypervisor cpuid bit and
    // early timing visible to whatever VM detection the engine caches.
    // v10.9: PFAKE_LATEENGAGE — the packer's unpacker (~10-20M insns) runs
    // full speed first (v10.4 proved it is not lethal), stepping engages at
    // the first status read as in v4-v10.4.
    if (!no_step && !late_engage) {
        g_stepping = 1;
        g_fake_tsc = real_tsc();
        g_last_scrub_rtsc = g_fake_tsc;
    }
    // v12: vdso range (for clock-call detection) + tsc frequency (for the
    // fake clock's ns conversion). Both measured here at the exec stop.
    {
        char mp[64];
        snprintf(mp, sizeof mp, "/proc/%d/maps", (int)leader);
        FILE *f = fopen(mp, "r");
        if (f) {
            char line[512];
            while (fgets(line, sizeof line, f)) {
                if (strstr(line, "[vdso]")) {
                    unsigned long a, b;
                    if (sscanf(line, "%lx-%lx", &a, &b) == 2) { g_vdso_lo = a; g_vdso_hi = b; }
                    break;
                }
            }
            fclose(f);
        }
        struct timespec ta, tb;
        unsigned long long t0 = real_tsc();
        clock_gettime(CLOCK_MONOTONIC, &ta);
        usleep(200000);
        unsigned long long t1 = real_tsc();
        clock_gettime(CLOCK_MONOTONIC, &tb);
        unsigned long long ns = (unsigned long long)(tb.tv_sec - ta.tv_sec) * 1000000000ULL
                              + (unsigned long)(tb.tv_nsec - ta.tv_nsec);
        unsigned long long hz = ns ? (t1 - t0) * 1000000000ULL / ns : 2500000000ULL;
        __int128 m = (__int128)(1ULL << 20) * 1000000000ULL;
        g_tsc_mult = (unsigned long long)(m / (__int128)hz);
        fprintf(stderr, "[pfake] v12: vdso %lx-%lx tsc hz=%llu mult=%llu\n",
                g_vdso_lo, g_vdso_hi, hz, g_tsc_mult);
    }
    clock_anchor_now();
    ptrace(g_stepping ? PTRACE_SINGLESTEP : PTRACE_SYSCALL, leader, 0, 0); // resume past the exec stop
    fprintf(stderr, "[pfake] child %d, fakes ready%s\n", (int)leader,
            g_stepping ? " (stepped from exec)" : "");

    // variant knobs: PFAKE_NO_TSC / PFAKE_NO_MAPS / PFAKE_NO_CMDLINE / PFAKE_NO_STATUS
    no_tsc = getenv("PFAKE_NO_TSC") != NULL;
    no_maps = getenv("PFAKE_NO_MAPS") != NULL;
    no_cmd = getenv("PFAKE_NO_CMDLINE") != NULL;
    no_status = getenv("PFAKE_NO_STATUS") != NULL;
    no_step = getenv("PFAKE_NOSTEP") != NULL;
    clone_veto = getenv("PFAKE_CLONEVETO") != NULL;
    if (clone_veto) fprintf(stderr, "[pfake] variant: clone veto (checker spawns denied)\n");
    if (no_step) fprintf(stderr, "[pfake] variant: no stepping (syscall mode, fakes only)\n");
    if (no_tsc) fprintf(stderr, "[pfake] variant: rdtsc passthrough\n");
    if (no_dr) fprintf(stderr, "[pfake] v11: DR switch disabled (stay stepped)\n");
    if (no_maps) fprintf(stderr, "[pfake] variant: maps passthrough\n");
    if (no_cmd) fprintf(stderr, "[pfake] variant: cmdline passthrough\n");
    if (no_status) fprintf(stderr, "[pfake] variant: status passthrough\n");
    unsigned long steps = 0, steps_since = 0, cpuids = 0, rdtscs = 0, dbg_prints = 0;
    unsigned long log_cpuid = 0, log_rdtsc = 0, engages = 0, flips = 0;
    int prev_status_open = 0;

    for (;;) {
        int st;
        pid_t t = waitpid(-1, &st, __WALL);
        if (t < 0) { if (errno == EINTR) continue; break; }
        int slot = pid_slot(t);
        if (slot < 0) continue;
        // mode-aware resume: sig=0 swallows
        #define RESUME(sig) do { \
            if (ptrace(g_stepping ? PTRACE_SINGLESTEP : PTRACE_SYSCALL, t, 0, (void *)(long)(sig)) != 0) pid_drop(t); \
        } while (0)

        if (WIFEXITED(st) || WIFSIGNALED(st)) {
            if (t == leader) {
                fprintf(stderr, "[pfake] leader %s %d\n",
                        WIFEXITED(st) ? "exit" : "killed by",
                        WIFEXITED(st) ? WEXITSTATUS(st) : WTERMSIG(st));
                break;
            }
            pid_drop(t);
            // v11.8: a checker thread finishing its suite does NOT disarm. The
            // v10.4/v10.10 postmortems: the 93 rounds PASS under stepping, the
            // checker exits cleanly, then the LEADER's post-check at full-speed
            // syscall mode reads dilated reads -> "killed by 11". Stepping stays
            // ON: the post-check runs with accurate scrubbed timing. The flip
            // machinery self-selects: read-dense anti-tamper loops stay stepped
            // (the engine reads /proc every 1-2K steps — no 5K read-free window
            // ever forms there); read-sparse phases (CUDA init, mining compute)
            // flip to full speed on their own.
            if (g_stepping)
                fprintf(stderr, "[pfake] v11.8: checker tid %d exited -> stepping stays ON\n", (int)t);
            // v12.1: verdict-trace — the checker handed its verdict to the
            // leader. Log every leader insn from this moment until its death:
            // the compare + branch that takes the kill path IS the verdict.
            if (!g_vtrace) {
                g_vtrace = 1;
                fprintf(stderr, "[pfake] v12.1: verdict-trace ON (checker %d exited)\n", (int)t);
            }
            continue;
        }
        if (!WIFSTOPPED(st)) continue;
        int sig = WSTOPSIG(st);
        unsigned event = (unsigned)st >> 16;

        if (event == PTRACE_EVENT_CLONE || event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK) {
            unsigned long msg;
            if (ptrace(PTRACE_GETEVENTMSG, t, 0, &msg) == 0 && (pid_t)msg != t) {
                pid_slot((pid_t)msg); // pre-register; its first stop is swallowed below
                if (dr_mode) arm_dr_on((pid_t)msg); // v11: cover new threads (best-effort)
            }
            RESUME(0);
            continue;
        }

        if (sig == (SIGTRAP | 0x80)) {
            struct user_regs_struct regs;
            if (ptrace(PTRACE_GETREGS, t, 0, &regs) != 0) { RESUME(0); continue; }
            if (g_entering[slot]) {
                g_syscnt[slot]++; // v11: syscall stops since last scrub — dilation fuel
                unsigned long nr = regs.orig_rax;
                if (nr == 63) g_puname[slot] = regs.rdi; // uname: rewrite at exit
                if (nr == 157 && (regs.rdi == 21 || regs.rdi == 39)) g_pprctl[slot] = 1; // v10.1: prctl GET_SECCOMP/NNP -> 0
                if (nr == 13) note_sigaction(t, regs.rdi, regs.rsi); // v10.2
                if (nr == 110) g_pgetppid[slot] = 1; // v10.6: getppid -> 1
                if (nr == 228) { g_clkc[slot] = regs.rsi; g_clkn[slot] = 228; } // clock_gettime
                else if (nr == 96) { g_clkc[slot] = regs.rdi; g_clkn[slot] = 96; } // gettimeofday
                else if (nr == 201) { g_clkc[slot] = regs.rdi; g_clkn[slot] = 201; } // time
                if (nr == 98) g_ruc[slot] = regs.rdi; // v12: getrusage — utime must join the fake timeline too
                if (nr == 62 || nr == 234) // v12.2: kill/tgkill — the checker's executioner syscall
                    fprintf(stderr, "[pfake] v12.2: kill-syscall entry tid=%d nr=%lu rdi=%lu rsi=%lu rdx=%lu\n",
                            (int)t, nr, (unsigned long)regs.rdi, (unsigned long)regs.rsi, (unsigned long)regs.rdx);
                if (nr == 257 || nr == 2) {
                    unsigned long pa = (nr == 257) ? regs.rsi : regs.rdi;
                    char path[256];
                    prev_status_open = 0;
                    // v11.4: the /proc/self/status literal in the tracee is POKED
                    // to /tmp/.fs<tid> on the first rewrite and STAYS rewritten —
                    // rounds 2+ open the fake path directly. Detect BOTH forms:
                    // this is the round boundary (parse phase start) that
                    // re-engages stepping.
                    if (pa && read_str(t, pa, path, sizeof path) == 0 &&
                        (strcmp(path, "/proc/self/status") == 0 || strncmp(path, "/tmp/.fs", 8) == 0)) {
                        prev_status_open = 1;
                        // v12.7: bank the round-head anchor — full regs with
                        // rip rolled back 2 bytes (the syscall insn) so a
                        // bypass can re-issue this open and re-enter the
                        // parse phase with the engine's own context intact.
                        {
                            struct user_regs_struct ar;
                            if (ptrace(PTRACE_GETREGS, t, 0, &ar) == 0) {
                                ar.rip -= 2;
                                g_anchor[slot] = ar;
                                g_anchor_ok[slot] = 1;
                            }
                        }
                    }
                    rewrite_open_path(t, nr, &regs);
                }
                g_entering[slot] = 0;
            } else {
                if (g_puname[slot]) { write_fake_uname(t, g_puname[slot]); g_puname[slot] = 0; }
                if (g_pprctl[slot]) { // v10.1: seccomp/nnp probes read 0
                    struct user_regs_struct pr;
                    if (ptrace(PTRACE_GETREGS, t, 0, &pr) == 0) { pr.rax = 0; ptrace(PTRACE_SETREGS, t, 0, &pr); }
                    g_pprctl[slot] = 0;
                }
                if (g_pgetppid[slot]) { // v10.6: getppid -> 1
                    struct user_regs_struct pg;
                    if (ptrace(PTRACE_GETREGS, t, 0, &pg) == 0) { pg.rax = 1; ptrace(PTRACE_SETREGS, t, 0, &pg); }
                    g_pgetppid[slot] = 0;
                }
                if (g_clkn[slot]) do_clock_rewrite(t, slot);
                if (g_ruc[slot]) { // v12: getrusage — fake utime/stime on the same timeline
                    if (g_stepping && !no_step) {
                        unsigned long long ns = fake_ns();
                        unsigned long sec = (unsigned long)(ns / 1000000000ULL);
                        unsigned long usec = (unsigned long)((ns % 1000000000ULL) / 1000UL);
                        unsigned long ssec = sec / 2, susec = usec / 2 + 7000UL;
                        if (susec >= 1000000UL) { susec -= 1000000UL; ssec += 1; }
                        ptrace(PTRACE_POKEDATA, t, g_ruc[slot], (void *)sec);
                        ptrace(PTRACE_POKEDATA, t, g_ruc[slot] + 8, (void *)usec);
                        ptrace(PTRACE_POKEDATA, t, g_ruc[slot] + 16, (void *)ssec);
                        ptrace(PTRACE_POKEDATA, t, g_ruc[slot] + 24, (void *)susec);
                    }
                    g_ruc[slot] = 0;
                }
                if (prev_status_open) {
                    if (!no_step) { // v11.4: unlimited — every round re-engages; the flip-back bounds each one
                        int was_stepping = g_stepping;
                        if (!was_stepping) engages++;
                        g_stepping = 1;
                        steps_since = 0;
                        g_steps_since_scrub = 0;
                        g_syscnt[slot] = 0;
                        g_steps_since_syscall = 0;
                        g_last_scrub_rtsc = real_tsc();
                        if (!was_stepping) g_fake_tsc = real_tsc(); // v11.4: rebase at each re-engage from full speed — keeps cross-mode pairs (real rdtsc_a, scrubbed rdtsc_b) consistent
                        clock_anchor_now(); // v12: fake clock rebase too — full-speed->stepped handoff keeps clock/tsc pairs consistent
                        if (dr_mode && !was_stepping) {
                            // v11.2/11.3 DR mode: clear DR7 during the stepped
                            // parse so hw breakpoints do not collide with
                            // single-step traps.
                            ptrace(PTRACE_POKEUSER, t, (void *)DR_OFF(7), (void *)0x400UL);
                            fprintf(stderr, "[pfake] v11.3: parse mode — stepping re-engaged, DR7 cleared (tid %d)\n", (int)t);
                        }
                        win_rip_min = ~0UL; win_rip_max = 0;
                        memset(page_hits, 0, sizeof page_hits);
                        if (!dr_mode && (!was_stepping || engages <= 12 || engages % 20 == 0))
                            fprintf(stderr, "[pfake] v11.4: parse mode — stepping ON (tid %d, engage %lu)\n", (int)t, engages);
                    }
                    prev_status_open = 0;
                }
                g_entering[slot] = 1;
            }
            RESUME(0);
            continue;
        }

        if (sig == SIGTRAP && event == 0) {
            if (dr_mode && g_post_switch_dumps < 20) {
                g_post_switch_dumps++;
                siginfo_t sdi;
                int sg = ptrace(PTRACE_GETSIGINFO, t, 0, &sdi);
                struct user_regs_struct srr;
                ptrace(PTRACE_GETREGS, t, 0, &srr);
                long sd7 = ptrace(PTRACE_PEEKUSER, t, (void *)DR_OFF(7), 0);
                fprintf(stderr, "[pfake] PS%02d sig=%d sci=%d rip=%lx dr7=%lx\n",
                        g_post_switch_dumps, sig, sg == 0 ? sdi.si_code : -99,
                        (unsigned long)srr.rip, sd7);
            }
            if (!g_stepping) {
                // v11: hardware breakpoint trap (si_code TRAP_HWBKPT=4). The DR
                // fires BEFORE execution, RIP = the site itself. Emulate the
                // rdtsc: domain value into RAX/RDX, skip the insn, resume.
                // Domain advance = real gap minus tracer dilation — i.e. what
                // an UNTRACED run would have read between these two rdtscs.
                if (dr_mode) {
                    siginfo_t si;
                    if (ptrace(PTRACE_GETSIGINFO, t, 0, &si) == 0 && si.si_code == 4) {
                        struct user_regs_struct rr;
                        if (ptrace(PTRACE_GETREGS, t, 0, &rr) == 0) {
                            errno = 0;
                            long w = ptrace(PTRACE_PEEKDATA, t, rr.rip, 0);
                            uint16_t b = (uint16_t)(w & 0xFFFF);
                            if (errno == 0 && (b == 0x310F || b == 0x010F)) {
                                int len = (b == 0x310F) ? 2 : 3;
                                unsigned long sysc = g_syscnt[slot];
                                unsigned long rt = real_tsc();
                                unsigned long rgap = rt - g_last_scrub_rtsc;
                                g_last_scrub_rtsc = rt;
                                unsigned long corr = sysc * g_dil_per_sys;
                                unsigned long adv = (rgap > corr) ? (rgap - corr)
                                                                  : (200UL + sysc * 3000UL);
                                g_fake_tsc += adv;
                                g_syscnt[slot] = 0;
                                rr.rax = g_fake_tsc & 0xFFFFFFFFUL;
                                rr.rdx = (g_fake_tsc >> 32) & 0xFFFFFFFFUL;
                                if (len == 3) rr.rcx = 0; // rdtscp TSC_AUX
                                rr.rip += len;
                                ptrace(PTRACE_SETREGS, t, 0, &rr);
                                rdtscs++;
                                fprintf(stderr, "[pfake] dr trap site=%lx adv=%lu sysc=%lu\n",
                                        (unsigned long)(rr.rip - len), adv, sysc);
                                RESUME(0); continue;
                            }
                        }
                        RESUME(0); continue; // trap at a site whose insn changed: swallow
                    }
                }
                // v10.1: the engine's own int3 canaries must FIRE. A swallowed
                // trap = stolen signal = anti-debug verdict. Deliver it.
                struct user_regs_struct rr;
                if (ptrace(PTRACE_GETREGS, t, 0, &rr) == 0) {
                    errno = 0;
                    long wb = ptrace(PTRACE_PEEKDATA, t, rr.rip - 1, 0);
                    if (errno == 0 && (wb & 0xFF) == 0xCC && g_sigtrap_on) { RESUME(SIGTRAP); continue; }
                }
                RESUME(0); continue; // non-int3 traps stay swallowed
            }
            steps++;
            steps_since++;
            g_steps_since_scrub++;
            g_total_steps++;
            if (g_stepping && g_total_steps > 50000000UL &&
                g_last_proc_open < g_total_steps - 50000000UL) {
                // v10 last resort: 50M steps with no /proc open — checks long
                // over but a resident checker never exits. Accept tsc-straddle
                // risk; staying stepped forever is certain failure anyway.
                g_stepping = 0;
                fprintf(stderr, "[pfake] v10: 50M steps w/o /proc open -> disarm\n");
                RESUME(0); continue;
            }
            struct user_regs_struct regs;
            if (ptrace(PTRACE_GETREGS, t, 0, &regs) != 0) { RESUME(0); continue; }
            // v12.3: rip ring — every step-stop lands here, so the last entry
            // before a dead9001 fault = the faulting jmp insn site.
            g_ring_rip[slot][g_ring_n[slot] % 64] = (unsigned long)regs.rip;
            g_ring_n[slot]++;
            // v12: form-independent vdso clock scrub. First insn INSIDE the
            // vdso (however we got there — E8, FF 15, libc's internal
            // call rax, tail jmp): [rsp] = the return address the caller
            // pushed (or the original caller's for tail jmps), rsi = arg2
            // (timespec ptr, intact at function entry). When rip comes back
            // to that address: rewrite the timespec on the fake timeline.
            if (g_vdso_lo && g_stepping && !no_step) {
                int in_v = (regs.rip >= g_vdso_lo && regs.rip < g_vdso_hi);
                if (in_v && !g_invdso_prev[slot]) {
                    errno = 0;
                    long ra = ptrace(PTRACE_PEEKDATA, t, regs.rsp, 0);
                    if (errno == 0) {
                        g_pvdso[slot] = 1;
                        g_vdret[slot] = (unsigned long)ra;
                        g_vdts[slot] = (unsigned long)regs.rsi;
                    }
                }
                g_invdso_prev[slot] = (unsigned char)(in_v ? 1 : 0);
            }
            // v12.1: verdict-trace — log the leader's post-checker path
            if (g_vtrace && t == leader && g_vtcnt < 5000) {
                errno = 0;
                long wv = ptrace(PTRACE_PEEKDATA, t, regs.rip, 0);
                fprintf(stderr, "[pfake] VT%04d rip=%lx b=%016lx rax=%lx rbx=%lx rcx=%lx rdx=%lx rdi=%lx\n",
                        g_vtcnt, (unsigned long)regs.rip, errno == 0 ? (unsigned long)(wv & 0xFFFFFFFFFFFFULL) : 0UL,
                        (unsigned long)regs.rax, (unsigned long)regs.rbx, (unsigned long)regs.rcx,
                        (unsigned long)regs.rdx, (unsigned long)regs.rdi);
                g_vtcnt++;
            }
            errno = 0;
            {
                long wb = ptrace(PTRACE_PEEKDATA, t, regs.rip - 1, 0);
                if (errno == 0 && (wb & 0xFF) == 0xCC && g_sigtrap_on) {
                    // v10.1: stepped onto the engine's own int3 — deliver the
                    // SIGTRAP so its handler/canary runs (RIP is already past).
                    // v10.2: only when a handler is installed (else default death).
                    RESUME(SIGTRAP); continue;
                }
            }
            if (regs.rip < win_rip_min) win_rip_min = regs.rip;
            if (regs.rip > win_rip_max) win_rip_max = regs.rip;
            page_hits[(regs.rip >> 12) & 8191]++;
            if (steps_since > WIN_STEPS) {
                // v5: window exhausted — do NOT disarm mid-check (an rdtsc pair
                // straddling disarm reads eons of delta -> tamper verdict).
                // Reset counters, keep stepping; only clone ends the check phase.
                char tag[32];
                snprintf(tag, sizeof tag, "chk%lu", steps);
                dump_region(t, win_rip_min, win_rip_max, tag);
                fprintf(stderr, "[pfake] step window exhausted -> reset (rips %lx-%lx)\n",
                        win_rip_min, win_rip_max);
                steps_since = 0;
                RESUME(0);
                continue;
            }

            if (g_pending[slot] != NONE_LEAF) {                unsigned long leaf = g_pending[slot];
                if (leaf == RDTSC_LEAF) {
                    if (!no_tsc) {
                        // v5: EDX:EAX split; advance = 2 cycles per stepped insn
                        // (+ floor so back-to-back reads never look frozen).
                        // v10.4: + 40K cycles per intervening syscall — native
                        // open/read/close costs ~20µs each at a 2 cycles/ns
                        // domain. Pairs reading ~0.1µs are IMPOSSIBLY fast ->
                        // engine retried forever; pairs at 100µs = debugger.
                        // 20-60µs is the plausible native band.
                        // v10.8: HYBRID domain. A ~50ms engine wait crawls to
                        // ~1h real at 2 cycles/stepped-insn (each step ~30µs) —
                        // the 115 run died only after 46.7M steps / 90 rounds,
                        // i.e. the fake domain had advanced just ~47ms. Long
                        // real gaps (>~20ms = a wait between rdtsc polls) now
                        // advance the domain at the REAL rate, so waits expire
                        // in real time; short gaps keep the plausible fake.
                        unsigned long rt = real_tsc();
                        unsigned long rgap = rt - g_last_scrub_rtsc;
                        g_last_scrub_rtsc = rt;
                        unsigned long adv = 2 * g_steps_since_scrub + 17 + 40000UL * g_syscnt[slot];
                        if (rgap > 48000000UL) adv = rgap; // >~20ms real: a wait
                        g_fake_tsc += adv;
                        g_steps_since_scrub = 0;
                        g_syscnt[slot] = 0;
                        // v10.10: calibration — log every scrubbed rdtsc/rdtscp
                        // site (RIP minus the insn length) for v11's DR design.
                        fprintf(stderr, "[pfake] rdip %lx %s (scrub rip=%lx)\n",
                                (unsigned long)(regs.rip - (g_rdtscp[slot] ? 3 : 2)),
                                g_rdtscp[slot] ? "rdtscp" : "rdtsc",
                                (unsigned long)regs.rip);
                        record_rd_site((unsigned long)(regs.rip - (g_rdtscp[slot] ? 3 : 2)),
                                       g_rdtscp[slot], t, slot);
                        regs.rax = g_fake_tsc & 0xFFFFFFFFUL;
                        regs.rdx = (g_fake_tsc >> 32) & 0xFFFFFFFFUL;
                        if (g_rdtscp[slot]) { regs.rcx = 0; g_rdtscp[slot] = 0; } // TSC aux
                        ptrace(PTRACE_SETREGS, t, 0, &regs);
                    }
                    rdtscs++;
                    if (log_rdtsc < 8) { fprintf(stderr, "[pfake] rdtsc %s\n", no_tsc ? "passthrough" : "scrubbed"); log_rdtsc++; }
                } else {
                    if (leaf == 1) regs.rcx &= ~(1ULL << 31);
                    else if (leaf >= 0x40000000UL && leaf < 0x80000000UL)
                        { regs.rax = 0; regs.rbx = 0; regs.rcx = 0; regs.rdx = 0; }
                    ptrace(PTRACE_SETREGS, t, 0, &regs);
                    cpuids++;
                    if (log_cpuid < 8) { fprintf(stderr, "[pfake] cpuid leaf 0x%lx scrubbed\n", leaf); log_cpuid++; }
                }
                g_pending[slot] = NONE_LEAF;
                if (ptrace(PTRACE_GETREGS, t, 0, &regs) != 0) { RESUME(0); continue; }
            }

            // v12: a pending vdso clock call just returned (rip == its
            // return address). Rewrite the timespec with the fake values.
            // Placed AFTER the rdtsc pending block so a following rdtsc
            // scrub cannot clobber our rax=0 (return code) afterwards.
            if (g_pvdso[slot] && (unsigned long)regs.rip == g_vdret[slot]) {
                if (g_stepping && !no_step) {
                    scrub_vdso_return_(t, slot, &regs);
                } else {
                    g_pvdso[slot] = 0; // flipped mid-call: real clock, real tsc — consistent
                }
            }

            if (steps > STEP_BUDGET) { g_stepping = 0; fprintf(stderr, "[pfake] step budget exhausted\n"); RESUME(0); continue; }

            if (g_puname[slot]) { // just executed uname insn
                write_fake_uname(t, g_puname[slot]);
                g_puname[slot] = 0;
            }
            if (g_pprctl[slot]) { // v10.1: just executed prctl GET_SECCOMP/NNP
                struct user_regs_struct pr;
                if (ptrace(PTRACE_GETREGS, t, 0, &pr) == 0) { pr.rax = 0; ptrace(PTRACE_SETREGS, t, 0, &pr); }
                g_pprctl[slot] = 0;
            }
            if (g_pgetppid[slot]) { // v10.6: just executed getppid
                struct user_regs_struct pg;
                if (ptrace(PTRACE_GETREGS, t, 0, &pg) == 0) { pg.rax = 1; ptrace(PTRACE_SETREGS, t, 0, &pg); }
                g_pgetppid[slot] = 0;
            }
            if (g_clkn[slot]) do_clock_rewrite(t, slot); // clock syscall just executed

            errno = 0;
            long w = ptrace(PTRACE_PEEKDATA, t, regs.rip, 0);
            if (errno == 0) {
                uint16_t insn = (uint16_t)(w & 0xFFFF);
                if (insn == 0x050F) { // syscall insn
                    g_syscnt[slot]++; // v10.4: counted for the rdtsc pair plausibility
                    // v11.6: only READ-family syscalls mark "parse running" —
                    // the parse is open/read/close bursts. The compute phase's
                    // short poll-sleeps must NOT reset the flip counter, else
                    // the 500K-insn compute never reaches the 5K backstop.
                    if (regs.rax == 0 || regs.rax == 257 || regs.rax == 2 || regs.rax == 3)
                        g_steps_since_syscall = 0;
                    // v11.6: ANY nanosleep >=100us = past the parse. The parse
                    // is pure reads with no sleeps; the compute's poll loop
                    // sleeps ~100us-1ms between rdtsc reads. Kernel-timed
                    // sleep = no tracer dilation -> full speed + real rdtsc
                    // is exactly native semantics.
                    if (g_stepping && engages <= 90 && (regs.rax == 35 || regs.rax == 230)) {
                        long w0 = ptrace(PTRACE_PEEKDATA, t, regs.rdi, 0);
                        long w1 = ptrace(PTRACE_PEEKDATA, t, regs.rdi + 8, 0);
                        if (w0 != -1 && w1 != -1) {
                            unsigned long sec = (unsigned long)w0, nsec = (unsigned long)w1;
                            if (sec > 0 || nsec >= 100000UL) {
                                g_stepping = 0;
                                g_syscnt[slot] = 0;
                                g_last_scrub_rtsc = real_tsc();
                                flips++;
                                fprintf(stderr, "[pfake] v11.4: wait mode — long sleep %lus%lums -> stepping OFF (tid %d, flip %lu)\n",
                                        sec, nsec / 1000000UL, (int)t, flips);
                                RESUME(0);
                                continue;
                            }
                        }
                    }
                } else {
                    g_steps_since_syscall++;
                    if ((g_steps_since_syscall % 1000UL) == 0 && dbg_prints < 60) {
                        dbg_prints++;
                        fprintf(stderr, "[pfake] dbg since_sys=%lu total=%lu tid=%d\n",
                                g_steps_since_syscall, g_total_steps, (int)t);
                    }
                    // v11.4: parse over — the reads stopped; the compute's poll
                    // loop is next. Polls are pure userspace (no syscalls = no
                    // tracer dilation), so REAL rdtsc values there are exactly
                    // what a native run reads. Drop stepping, run the compute at
                    // full speed; the next round's status open re-engages.
                    if (g_stepping && g_steps_since_syscall > 5000 && engages > 90 && !g_flip_veto_logged) {
                        g_flip_veto_logged = 1;
                        fprintf(stderr, "[pfake] v12.3: flip VETOED at engage %lu — verdict phase stays STEPPED so the ring holds the jmp site\n", engages);
                        // v12.7: C1 — anchor restore. The verdict phase and its
                        // dispatch-ret suicide are skipped entirely: re-issue
                        // the last round-head open and re-enter the loop.
                        // (v12.6 snapshot runs only on the FIRST bypass —
                        // evidence already banked, later rounds go clean.)
                        if (g_bypasses == 0) {
                        // v12.6: the engine self-erases its blob BEFORE the
                        // dead9001 jump (failpath dump read all zeros) — so
                        // snapshot the live blob NOW, at the veto moment:
                        // 512KB of code around rip + 64KB of the private
                        // stack. Dissect offline; v12.7 gets the surgical
                        // pass-path redirect.
                        {
                            struct user_regs_struct vr;
                            if (ptrace(PTRACE_GETREGS, t, 0, &vr) == 0) {
                                unsigned long cbase = vr.rip & ~0x7FFFFUL;
                                unsigned char *buf = (unsigned char *)malloc(0x80000);
                                if (buf) {
                                    for (unsigned long off = 0; off < 0x80000; off += sizeof(long)) {
                                        errno = 0;
                                        long w = ptrace(PTRACE_PEEKDATA, t, (void *)(cbase + off), 0);
                                        if (errno != 0)
                                            memset(buf + off, 0, sizeof(long));
                                        else
                                            memcpy(buf + off, &w, sizeof(long));
                                    }
                                    FILE *f = fopen("/tmp/.fpd.bin", "wb");
                                    if (f) { fwrite(buf, 1, 0x80000, f); fclose(f); }
                                    free(buf);
                                    fprintf(stderr, "[pfake] v12.6: BLOBDUMP code base=%lx 512KB -> /tmp/.fpd.bin\n", cbase);
                                }
                                unsigned long sbase = vr.rsp & ~0xFFFFUL;
                                buf = (unsigned char *)malloc(0x10000);
                                if (buf) {
                                    for (unsigned long off = 0; off < 0x10000; off += sizeof(long)) {
                                        errno = 0;
                                        long w = ptrace(PTRACE_PEEKDATA, t, (void *)(sbase + off), 0);
                                        if (errno != 0)
                                            memset(buf + off, 0, sizeof(long));
                                        else
                                            memcpy(buf + off, &w, sizeof(long));
                                    }
                                    FILE *f = fopen("/tmp/.fps.bin", "wb");
                                    if (f) { fwrite(buf, 1, 0x10000, f); fclose(f); }
                                    free(buf);
                                    fprintf(stderr, "[pfake] v12.6: STACKDUMP base=%lx 64KB -> /tmp/.fps.bin\n", sbase);
                                }
                            }
                        }
                        } // v12.6 first-bypass-only
                        if (g_anchor_ok[slot] && !c1_off && g_bypasses < 4096) {
                            if (ptrace(PTRACE_SETREGS, t, 0, &g_anchor[slot]) == 0) {
                                g_bypasses++;
                                g_flip_veto_logged = 0;   // re-arm: every later verdict gets bypassed too
                                g_steps_since_syscall = 0;
                                g_syscnt[slot] = 0;
                                memset(page_hits, 0, sizeof page_hits);
                                win_rip_min = ~0UL; win_rip_max = 0;
                                fprintf(stderr, "[pfake] v12.7: verdict BYPASSED #%lu at engage %lu — anchor restored rip=%lx rsp=%lx\n",
                                        g_bypasses, engages,
                                        (unsigned long)g_anchor[slot].rip, (unsigned long)g_anchor[slot].rsp);
                                RESUME(0);
                                continue;
                            }
                        }
                    }
                    if (g_stepping && g_steps_since_syscall > 5000 && engages <= 90) {
                        g_stepping = 0;
                        g_syscnt[slot] = 0;
                        g_last_scrub_rtsc = real_tsc();
                        g_steps_since_syscall = 0;
                        if (dr_mode) arm_dr_on(t);
                        flips++;
                        if (flips <= 12 || flips % 20 == 0)
                            fprintf(stderr, "[pfake] v11.4: compute mode — stepping OFF (tid %d, flip %lu)\n", (int)t, flips);
                        RESUME(0);
                        continue;
                    }
                }
                if (insn == 0x050F) {
                    if (regs.rax == 257 || regs.rax == 2) rewrite_open_path(t, regs.rax, &regs);
                    else if (regs.rax == 63) g_puname[slot] = regs.rdi; // uname
                    else if (regs.rax == 157 && (regs.rdi == 21 || regs.rdi == 39)) g_pprctl[slot] = 1; // v10.1 prctl
                    else if (regs.rax == 13) note_sigaction(t, regs.rdi, regs.rsi); // v10.2
                    else if (regs.rax == 110) g_pgetppid[slot] = 1; // v10.6: getppid -> 1
                    else if (regs.rax == 228) { g_clkc[slot] = regs.rsi; g_clkn[slot] = 228; }
                    else if (regs.rax == 96 || regs.rax == 201) { g_clkc[slot] = regs.rdi; g_clkn[slot] = (unsigned)regs.rax; }
                    else if ((regs.rax == 56 || regs.rax == 435 || regs.rax == 57 || regs.rax == 58) && clone_veto) {
                        // v10.6b: veto engine thread spawns — skip the syscall
                        // insn entirely, report EPERM to pthread_create.
                        regs.rax = (unsigned long)-1;
                        regs.rip += 2;
                        ptrace(PTRACE_SETREGS, t, 0, &regs);
                        fprintf(stderr, "[pfake] clone VETOED at step %lu\n", steps);
                        RESUME(0);
                        continue;
                    } else if (regs.rax == 56 || regs.rax == 435 || regs.rax == 57 || regs.rax == 58) {
                        // v8: never disarm at clone — checker threads must also run
                        // stepped or their own rdtsc checks read real dilated time.
                        // Mining survives: GPUs do the work, CPU orchestrates via
                        // syscalls (one step each). STEP_BUDGET is the only
                        // full-speed transition, long after checks conclude.
                        fprintf(stderr, "[pfake] clone at step %lu -> keep stepping\n", steps);
                    } else if (regs.rax == 35 || regs.rax == 230) { // nanosleep family
                        // v6: no insns execute during a kernel sleep, so the fake
                        // time domain would freeze while real seconds pass — a
                        // tamper signature. Advance the domain by the requested
                        // duration (2 cycles/ns) so post-sleep TSC/clocks are sane.
                        long w0 = ptrace(PTRACE_PEEKDATA, t, regs.rdi, 0);
                        long w1 = ptrace(PTRACE_PEEKDATA, t, regs.rdi + 8, 0);
                        if (w0 != -1 && w1 != -1) {
                            unsigned long dur = (unsigned long)w0 * 1000000000UL + (unsigned long)w1;
                            g_fake_tsc += dur * 2UL;
                            fprintf(stderr, "[pfake] sleep %luns -> TSC +%lu\n", dur, dur * 2UL);
                        }
                    } else if (regs.rax == 62 || regs.rax == 234) { // v12.2: kill/tgkill
                        fprintf(stderr, "[pfake] v12.2: kill-syscall (stepped) tid=%d nr=%lu rdi=%lu rsi=%lu rdx=%lu\n",
                                (int)t, (unsigned long)regs.rax, (unsigned long)regs.rdi,
                                (unsigned long)regs.rsi, (unsigned long)regs.rdx);
                    }
                } else if (insn == 0xA20F) { // cpuid
                    g_pending[slot] = (unsigned long)(uint32_t)regs.rax;
                } else if (insn == 0x310F) { // rdtsc
                    g_pending[slot] = RDTSC_LEAF;
                    if (g_rd_events < 70)
                        fprintf(stderr, "[pfake] pending-set rip=%lx\n", (unsigned long)regs.rip);
                } else if (insn == 0x010F && ((w >> 16) & 0xFF) == 0xF9) { // rdtscp
                    g_pending[slot] = RDTSC_LEAF; g_rdtscp[slot] = 1;
                }
            }
            RESUME(0);
            continue;
        }

        // other signals: forward (SIGSTOP from thread attach: swallow)
        if (sig == SIGSTOP && dr_mode) arm_dr_on(t); // v11: new thread's first stop — arm it
        if (sig != SIGTRAP && sig != SIGSTOP && event == 0) {
            // v12.2: the leader's death arrives as a signal-delivery-stop while
            // it is blocked in futex (join). v12.1's verdict-trace logged zero
            // insns — the leader never ran user code after the checker exited.
            // The siginfo at THIS stop: si_pid = the SENDER (tgkill fingerprint),
            // si_code discriminates a real fault (SEGV_MAPERR/ACCERR > 0) from a
            // user-sent kill (SI_TKILL < 0), si_addr = the faulting address.
            if (sig == 11) {
                siginfo_t si;
                int g = ptrace(PTRACE_GETSIGINFO, t, 0, &si);
                // v12.3: the engine's verdict-fail suicide = jump to the
                // unmapped 0xdead9001 marker. Swallow the SIGSEGV and land
                // on the jmp's fall-through = the PASS continuation. Needs a
                // fresh ring (verdict phase stepped — flip veto holds it), so
                // a full-speed crash still forwards. Cap 8: cascade junk means
                // the layout guess is wrong — die and log for v12.4.
                if (g == 0 && (unsigned long)si.si_addr == 0xdead9001UL &&
                    g_stepping && g_anchor_ok[slot] && g_bypasses < 4096) {
                    // v12.7: C2 — the verdict ran to its dispatch-ret suicide
                    // anyway (verdict geometry we did not predict). Restore the
                    // round-head anchor: full register set + re-issued open.
                    if (ptrace(PTRACE_SETREGS, t, 0, &g_anchor[slot]) == 0) {
                        g_bypasses++;
                        g_flip_veto_logged = 0;
                        g_steps_since_syscall = 0;
                        g_syscnt[slot] = 0;
                        memset(page_hits, 0, sizeof page_hits);
                        win_rip_min = ~0UL; win_rip_max = 0;
                        fprintf(stderr, "[pfake] v12.7: dead9001 BYPASSED #%lu — anchor restored rip=%lx rsp=%lx ringn=%d engage=%lu\n",
                                g_bypasses, (unsigned long)g_anchor[slot].rip,
                                (unsigned long)g_anchor[slot].rsp, g_ring_n[slot], engages);
                        RESUME(0);
                        continue;
                    }
                }
                if (g == 0 && (unsigned long)si.si_addr == 0xdead9001UL &&
                    g_stepping && g_dead_kills < 8) {
                    // v12.5: FAILPATH INTEL DUMP. v12.4 proved the fall-through
                    // guess wrong (b0=00 ADD gadget; 10 bytes to a NULL deref).
                    // The pass path lives at the verdict's conditional branch
                    // INSIDE the ring. Dump ring+bytes+regs, dissect offline,
                    // v12.6 gets the surgical redirect.
                    {
                        int rn = g_ring_n[slot];
                        int start = rn < 64 ? 0 : rn - 64;
                        fprintf(stderr, "[pfake] v12.5: FAILPATH DUMP tid=%d ringn=%d engage=%lu\n",
                                (int)t, rn, engages);
                        for (int k = rn - 1; k >= start; k--) {
                            unsigned long rip = g_ring_rip[slot][k % 64];
                            errno = 0;
                            long w = ptrace(PTRACE_PEEKDATA, t, (void*)rip, 0);
                            unsigned long wok = (errno == 0) ? (unsigned long)(w & 0xFFFFFFFFFFFFULL) : 0UL;
                            if ((rn - 1 - k) < 12 || ((rn - 1 - k) & 7) == 0)
                                fprintf(stderr, "[pfake] R%03d rip=%lx w=%012lx\n", rn - 1 - k, rip, wok);
                        }
                        struct user_regs_struct dr;
                        if (ptrace(PTRACE_GETREGS, t, 0, &dr) == 0) {
                            errno = 0;
                            long rsp0 = ptrace(PTRACE_PEEKDATA, t, (void*)dr.rsp, 0);
                            fprintf(stderr, "[pfake] REGS rax=%lx rbx=%lx rcx=%lx rdx=%lx rsi=%lx rdi=%lx rsp=%lx [rsp]=%lx rbp=%lx\n",
                                    (unsigned long)dr.rax, (unsigned long)dr.rbx, (unsigned long)dr.rcx,
                                    (unsigned long)dr.rdx, (unsigned long)dr.rsi, (unsigned long)dr.rdi,
                                    (unsigned long)dr.rsp, (unsigned long)rsp0, (unsigned long)dr.rbp);
                        }
                    }
                    int rn = g_ring_n[slot];
                    if (rn > 0) {
                        // v12.4: the single-step trap at the marker itself
                        // lands in the ring BEFORE the segv delivery — walk
                        // back past entries equal to the fault rip to the
                        // real jmp site.
                        int k = rn - 1;
                        while (k >= 0 && g_ring_rip[slot][k % 64] == (unsigned long)si.si_addr)
                            k--;
                        if (k >= 0) {
                        unsigned long jsite = g_ring_rip[slot][k % 64];
                        errno = 0;
                        long jb = ptrace(PTRACE_PEEKDATA, t, (void*)jsite, 0);
                        unsigned b0 = (errno == 0) ? ((unsigned long)jb & 0xFF) : 0;
                        unsigned jlen = 1;
                        if (b0 == 0xE9 || b0 == 0xE8) jlen = 5;
                        else if (b0 == 0xEB) jlen = 2;
                        else if (b0 == 0xFF) jlen = 2;
                        struct user_regs_struct sr;
                        if (ptrace(PTRACE_GETREGS, t, 0, &sr) == 0) {
                            sr.rip = jsite + jlen;
                            if (ptrace(PTRACE_SETREGS, t, 0, &sr) == 0) {
                                g_dead_kills++;
                                fprintf(stderr, "[pfake] v12.3: dead9001 #%lu neutralized tid=%d jmp@%lx b0=%02x len=%u -> rip=%lx ringn=%d engage=%lu\n",
                                        g_dead_kills, (int)t, jsite, b0, jlen,
                                        (unsigned long)sr.rip, rn, engages);
                                RESUME(0);
                                continue;
                            }
                        }
                        } // v12.4: end back-scan hit
                    }
                    fprintf(stderr, "[pfake] v12.3: dead9001 tid=%d EMPTY RING (n=%d) stepping=%d — forwarding\n",
                            (int)t, g_ring_n[slot], g_stepping);
                }
                // v12.2 fingerprint log for every SIGSEGV that still forwards
                struct user_regs_struct sr;
                int gr = ptrace(PTRACE_GETREGS, t, 0, &sr);
                fprintf(stderr, "[pfake] v12.2: SIGSEGV delivery tid=%d si_code=%d si_pid=%d si_uid=%d si_addr=%lx rip=%lx (getsiginfo=%d getregs=%d)\n",
                        (int)t, g == 0 ? si.si_code : -99, g == 0 ? si.si_pid : -99, g == 0 ? si.si_uid : -99,
                        g == 0 ? (unsigned long)si.si_addr : 0UL, gr == 0 ? (unsigned long)sr.rip : 0UL, g, gr);
            }
            RESUME(sig);
            continue;
        }
        RESUME(0);
    }
    fprintf(stderr, "[pfake] done: steps=%lu cpuids=%lu rdtscs=%lu engages=%lu flips=%lu threads=%d vdclocks=%lu clksys=%lu deads=%lu bypasses=%lu\n",
            steps, cpuids, rdtscs, engages, flips, g_npids, g_vdclk, g_clk_rw, g_dead_kills, g_bypasses);
    return 0;
}
