// pfake.c — ptrace anti-analysis neutralizer for SRBMiner-MULTI (v3, multithread)
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
#define STEP_BUDGET  3000000UL
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

static int pid_slot(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) return i;
    if (g_npids >= MAXPIDS) return -1;
    g_pids[g_npids] = p; g_entering[g_npids] = 1; g_pending[g_npids] = NONE_LEAF; g_puname[g_npids] = 0;
    return g_npids++;
}
static void pid_drop(pid_t p) {
    for (int i = 0; i < g_npids; i++) if (g_pids[i] == p) {
        for (int j = i; j < g_npids - 1; j++) { g_pids[j] = g_pids[j+1]; g_entering[j] = g_entering[j+1]; g_pending[j] = g_pending[j+1]; g_puname[j] = g_puname[j+1]; }
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

static void make_fake_status(pid_t target) {
    char real[64], line[512], out[16384];
    snprintf(real, sizeof real, "/proc/%d/status", (int)target);
    FILE *f = fopen(real, "r");
    if (!f) return;
    out[0] = 0;
    while (fgets(line, sizeof line, f)) {
        if (strncmp(line, "TracerPid:", 10) == 0) strcat(out, "TracerPid:\t0\n");
        else if (strncmp(line, "Seccomp:", 8) == 0) strcat(out, "Seccomp:\t0\n");
        else if (strncmp(line, "Seccomp_filters:", 16) == 0) strcat(out, "Seccomp_filters:\t0\n");
        else if (strncmp(line, "NoNewPrivs:", 11) == 0) strcat(out, "NoNewPrivs:\t0\n");
        else strcat(out, line);
    }
    fclose(f);
    FILE *o = fopen(FAKE, "w");
    if (o) { fputs(out, o); fclose(o); }
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
    if (strcmp(path, "/proc/self/status") == 0) {
        poke_str(pid, pa, FAKE, 18);
    } else if (is_self_cmdline(path)) {
        poke_str(pid, pa, FAKE_OWNCMD, strlen(path) + 1);
        fprintf(stderr, "[pfake] rewrote own cmdline -> %s\n", FAKE_OWNCMD);
    } else if (is_proc_cmdline(path)) {
        // parent / other pid cmdline: our own argv is already faked in memory — pass through
        fprintf(stderr, "[pfake] other cmdline passthrough: %s\n", path);
    } else if (strcmp(path, "/proc/self/maps") == 0) {
        if (build_fake_maps(pid) == 0) {
            poke_str(pid, pa, "/tmp/.fm", strlen(path) + 1);
            fprintf(stderr, "[pfake] rewrote maps -> /tmp/.fm\n");
        }
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

    int stepping = 0;
    int reengage_budget = 48;
    unsigned long steps = 0, steps_since = 0, cpuids = 0, rdtscs = 0, fake_tsc = 0x100000UL;
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
            if (ptrace(stepping ? PTRACE_SINGLESTEP : PTRACE_SYSCALL, t, 0, (void *)(long)(sig)) != 0) pid_drop(t); \
        } while (0)

        if (WIFEXITED(st) || WIFSIGNALED(st)) {
            if (t == leader) {
                fprintf(stderr, "[pfake] leader %s %d\n",
                        WIFEXITED(st) ? "exit" : "killed by",
                        WIFEXITED(st) ? WEXITSTATUS(st) : WTERMSIG(st));
                break;
            }
            pid_drop(t);
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
                if (prev_status_open) {
                    if (reengage_budget > 0) {
                        reengage_budget--;
                        stepping = 1;
                        steps_since = 0;
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
            if (!stepping) { RESUME(0); continue; } // int3 in syscall mode: swallow
            steps++;
            steps_since++;
            struct user_regs_struct regs;
            if (ptrace(PTRACE_GETREGS, t, 0, &regs) != 0) { RESUME(0); continue; }
            if (regs.rip < win_rip_min) win_rip_min = regs.rip;
            if (regs.rip > win_rip_max) win_rip_max = regs.rip;
            page_hits[(regs.rip >> 12) & 8191]++;
            if (steps_since > 400000) {
                stepping = 0;
                char tag[32];
                snprintf(tag, sizeof tag, "chk%lu", steps);
                dump_region(t, win_rip_min, win_rip_max, tag);
                fprintf(stderr, "[pfake] step window exhausted -> disarm (rips %lx-%lx)\n",
                        win_rip_min, win_rip_max);
                RESUME(0);
                continue;
            }

            if (g_pending[slot] != NONE_LEAF) {                unsigned long leaf = g_pending[slot];
                if (leaf == RDTSC_LEAF) {
                    struct timespec ts;
                    clock_gettime(CLOCK_MONOTONIC, &ts);
                    // fake 2GHz TSC tracking real wall time (freq-consistent)
                    fake_tsc = (unsigned long)ts.tv_sec * 2000000000UL + (unsigned long)ts.tv_nsec * 2UL;
                    regs.rax = fake_tsc; regs.rdx = 0;
                    ptrace(PTRACE_SETREGS, t, 0, &regs);
                    rdtscs++;
                    if (log_rdtsc < 8) { fprintf(stderr, "[pfake] rdtsc scrubbed\n"); log_rdtsc++; }
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

            if (steps > STEP_BUDGET) { stepping = 0; fprintf(stderr, "[pfake] step budget exhausted\n"); RESUME(0); continue; }

            if (g_puname[slot]) { // just executed uname insn
                write_fake_uname(t, g_puname[slot]);
                g_puname[slot] = 0;
            }

            errno = 0;
            long w = ptrace(PTRACE_PEEKDATA, t, regs.rip, 0);
            if (errno == 0) {
                uint16_t insn = (uint16_t)(w & 0xFFFF);
                if (insn == 0x050F) { // syscall insn
                    if (regs.rax == 257 || regs.rax == 2) rewrite_open_path(t, regs.rax, &regs);
                    else if (regs.rax == 63) g_puname[slot] = regs.rdi; // uname
                    else if (regs.rax == 56 || regs.rax == 435) { // clone/clone3
                        stepping = 0;
                        fprintf(stderr, "[pfake] clone at step %lu -> disarm (full speed)\n", steps);
                    } else if (regs.rax == 35 || regs.rax == 230) { // nanosleep family: check window over
                        stepping = 0;
                        steps_since = 0;
                    }
                } else if (insn == 0xA20F) { // cpuid
                    g_pending[slot] = (unsigned long)(uint32_t)regs.rax;
                } else if (insn == 0x310F) { // rdtsc
                    g_pending[slot] = RDTSC_LEAF;
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
