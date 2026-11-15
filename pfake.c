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
static int g_sigtrap_on = 0;                // v10.2: child installed a SIGTRAP handler

// v10.2: packer int3s arrive BEFORE any handler (delivery = default death);
// engine canary int3s arrive after rt_sigaction(SIGTRAP, real_handler).
static void note_sigaction(pid_t t, unsigned long signum, unsigned long act) {
    if (signum != 5 || act == 0) return;
    errno = 0;
    long h = ptrace(PTRACE_PEEKDATA, t, act, 0);
    if (errno != 0) return;
    g_sigtrap_on = !(h == 0 || h == 1); // SIG_DFL / SIG_IGN don't count
}

static int pid_slot(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) return i;
    if (g_npids >= MAXPIDS) return -1;
    g_pids[g_npids] = p; g_entering[g_npids] = 1; g_pending[g_npids] = NONE_LEAF; g_puname[g_npids] = 0; g_rdtscp[g_npids] = 0; g_clkc[g_npids] = 0; g_clkn[g_npids] = 0; g_pprctl[g_npids] = 0;
    return g_npids++;
}
static void pid_drop(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) {
        for (int j = i; j < g_npids - 1; j++) { g_pids[j] = g_pids[j+1]; g_entering[j] = g_entering[j+1]; g_pending[j] = g_pending[j+1]; g_puname[j] = g_puname[j+1]; g_rdtscp[j] = g_rdtscp[j+1]; g_clkc[j] = g_clkc[j+1]; g_clkn[j] = g_clkn[j+1]; g_pprctl[j] = g_pprctl[j+1]; }
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
        memcpy(&w, (char *)&u + off, sizeof w);
        ptrace(PTRACE_POKEDATA, pid, addr + off, (void *)w);
    }
    fprintf(stderr, "[pfake] uname rewritten\n");
}

// v5: synthetic time domain. Clock syscalls return values derived from the
// fake TSC (2 cycles/ns), so rdtsc pairs and clock_gettime pairs agree and
// tracer-side processing time is invisible to any cross-check.
static void do_clock_rewrite(pid_t t, int slot) {
    // v10.3: in syscall (non-stepped) mode the kernel's own values are
    // truthful and consistent with real rdtsc — rewriting them with
    // real_tsc/2 corrupts CLOCK_REALTIME (1970 dates) and CPUTIME clocks.
    if (!g_stepping) { g_clkc[slot] = 0; g_clkn[slot] = 0; return; }
    unsigned long base = g_fake_tsc;
    unsigned long ns = base / 2UL;
    unsigned long sec = ns / 1000000000UL;
    unsigned long sub = ns % 1000000000UL;
    unsigned long addr = g_clkc[slot];
    unsigned int nr = g_clkn[slot];
    g_clkc[slot] = 0; g_clkn[slot] = 0;
    if (nr == 201) { // time(t): rax = seconds
        struct user_regs_struct r;
        if (ptrace(PTRACE_GETREGS, t, 0, &r) == 0) {
            r.rax = sec;
            ptrace(PTRACE_SETREGS, t, 0, &r);
        }
        if (addr) ptrace(PTRACE_POKEDATA, t, addr, (void *)(long)sec);
    } else if (addr) {
        long w1 = (nr == 228) ? (long)sub  // clock_gettime {sec, nsec}
                              : (long)((ns / 1000UL) % 1000000UL); // gettimeofday {sec, usec}
        ptrace(PTRACE_POKEDATA, t, addr, (void *)(long)sec);
        ptrace(PTRACE_POKEDATA, t, addr + 8, (void *)w1);
    }
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
    char buf[64];
    memset(buf, 0, sizeof buf);
    strncpy(buf, s, sizeof buf - 1);
    for (size_t off = 0; off < cap; off += sizeof(long)) {
        long w;
        memcpy(&w, buf + off, sizeof w);
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
    pid_slot(leader);
    ptrace(PTRACE_SYSCALL, leader, 0, 0); // resume past the exec stop
    fprintf(stderr, "[pfake] child %d, fakes ready\n", (int)leader);

    int reengage_budget = 512;
    // variant knobs: PFAKE_NO_TSC / PFAKE_NO_MAPS / PFAKE_NO_CMDLINE / PFAKE_NO_STATUS
    no_tsc = getenv("PFAKE_NO_TSC") != NULL;
    no_maps = getenv("PFAKE_NO_MAPS") != NULL;
    no_cmd = getenv("PFAKE_NO_CMDLINE") != NULL;
    no_status = getenv("PFAKE_NO_STATUS") != NULL;
    no_step = getenv("PFAKE_NOSTEP") != NULL;
    if (no_step) fprintf(stderr, "[pfake] variant: no stepping (syscall mode, fakes only)\n");
    if (no_tsc) fprintf(stderr, "[pfake] variant: rdtsc passthrough\n");
    if (no_maps) fprintf(stderr, "[pfake] variant: maps passthrough\n");
    if (no_cmd) fprintf(stderr, "[pfake] variant: cmdline passthrough\n");
    if (no_status) fprintf(stderr, "[pfake] variant: status passthrough\n");
    unsigned long steps = 0, steps_since = 0, cpuids = 0, rdtscs = 0;
    unsigned long log_cpuid = 0, log_rdtsc = 0;
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
            // v10: a checker thread finishing its suite = checks concluded ->
            // syscall mode for full speed; /proc rewrites stay live there.
            if (g_stepping) {
                g_stepping = 0;
                fprintf(stderr, "[pfake] v10: tid %d exited -> disarm to full speed\n", (int)t);
            }
            continue;
        }
        if (!WIFSTOPPED(st)) continue;
        int sig = WSTOPSIG(st);
        unsigned event = (unsigned)st >> 16;

        if (event == PTRACE_EVENT_CLONE || event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK) {
            unsigned long msg;
            if (ptrace(PTRACE_GETEVENTMSG, t, 0, &msg) == 0 && (pid_t)msg != t)
                pid_slot((pid_t)msg); // pre-register; its first stop is swallowed below
            RESUME(0);
            continue;
        }

        if (sig == (SIGTRAP | 0x80)) {
            struct user_regs_struct regs;
            if (ptrace(PTRACE_GETREGS, t, 0, &regs) != 0) { RESUME(0); continue; }
            if (g_entering[slot]) {
                unsigned long nr = regs.orig_rax;
                if (nr == 63) g_puname[slot] = regs.rdi; // uname: rewrite at exit
                if (nr == 157 && (regs.rdi == 21 || regs.rdi == 39)) g_pprctl[slot] = 1; // v10.1: prctl GET_SECCOMP/NNP -> 0
                if (nr == 13) note_sigaction(t, regs.rdi, regs.rsi); // v10.2
                if (nr == 228) { g_clkc[slot] = regs.rsi; g_clkn[slot] = 228; } // clock_gettime
                else if (nr == 96) { g_clkc[slot] = regs.rdi; g_clkn[slot] = 96; } // gettimeofday
                else if (nr == 201) { g_clkc[slot] = regs.rdi; g_clkn[slot] = 201; } // time
                if (nr == 257 || nr == 2) {
                    unsigned long pa = (nr == 257) ? regs.rsi : regs.rdi;
                    char path[256];
                    prev_status_open = 0;
                    if (pa && read_str(t, pa, path, sizeof path) == 0 && strcmp(path, "/proc/self/status") == 0)
                        prev_status_open = 1;
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
                if (g_clkn[slot]) do_clock_rewrite(t, slot);
                if (prev_status_open) {
                    if (reengage_budget > 0 && !no_step) {
                        reengage_budget--;
                        int was_stepping = g_stepping;
                        g_stepping = 1;
                        steps_since = 0;
                        g_steps_since_scrub = 0;
                        if (!was_stepping) g_fake_tsc = real_tsc(); // base only on first engage — never rebase mid-flight
                        win_rip_min = ~0UL; win_rip_max = 0;
                        memset(page_hits, 0, sizeof page_hits);
                        fprintf(stderr, "[pfake] step mode engaged (tid %d, window %d)\n", (int)t, 48 - reengage_budget);
                    }
                    prev_status_open = 0;
                }
                g_entering[slot] = 1;
            }
            RESUME(0);
            continue;
        }

        if (sig == SIGTRAP && event == 0) {
            if (!g_stepping) {
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
                        // The fake TSC is the master clock: clock syscalls derive
                        // from it, so rdtsc and clock_gettime always agree.
                        g_fake_tsc += 2 * g_steps_since_scrub + 17;
                        g_steps_since_scrub = 0;
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
            if (g_clkn[slot]) do_clock_rewrite(t, slot); // clock syscall just executed

            errno = 0;
            long w = ptrace(PTRACE_PEEKDATA, t, regs.rip, 0);
            if (errno == 0) {
                uint16_t insn = (uint16_t)(w & 0xFFFF);
                if (insn == 0x050F) { // syscall insn
                    if (regs.rax == 257 || regs.rax == 2) rewrite_open_path(t, regs.rax, &regs);
                    else if (regs.rax == 63) g_puname[slot] = regs.rdi; // uname
                    else if (regs.rax == 157 && (regs.rdi == 21 || regs.rdi == 39)) g_pprctl[slot] = 1; // v10.1 prctl
                    else if (regs.rax == 13) note_sigaction(t, regs.rdi, regs.rsi); // v10.2
                    else if (regs.rax == 228) { g_clkc[slot] = regs.rsi; g_clkn[slot] = 228; }
                    else if (regs.rax == 96 || regs.rax == 201) { g_clkc[slot] = regs.rdi; g_clkn[slot] = (unsigned)regs.rax; }
                    else if (regs.rax == 56 || regs.rax == 435 || regs.rax == 57 || regs.rax == 58) {
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
                    }
                } else if (insn == 0xA20F) { // cpuid
                    g_pending[slot] = (unsigned long)(uint32_t)regs.rax;
                } else if (insn == 0x310F) { // rdtsc
                    g_pending[slot] = RDTSC_LEAF;
                } else if (insn == 0x010F && ((w >> 16) & 0xFF) == 0xF9) { // rdtscp
                    g_pending[slot] = RDTSC_LEAF; g_rdtscp[slot] = 1;
                }
            }
            RESUME(0);
            continue;
        }

        // other signals: forward (SIGSTOP from thread attach: swallow)
        if (sig != SIGTRAP && sig != SIGSTOP && event == 0) RESUME(sig);
        else RESUME(0);
    }
    fprintf(stderr, "[pfake] done: steps=%lu cpuids=%lu rdtscs=%lu threads=%d\n",
            steps, cpuids, rdtscs, g_npids);
    return 0;
}
