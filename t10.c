// t10 v6 — correct geometry: compute-phase smash of persistent slots is
// followed by a next-round refresh BEFORE the verdict. The v12.7 veto fires
// at the flip point (compute tail, after smash, before refresh) and its
// regs-only anchor restore re-enters the loop on SMASHED slots -> wild rip
// 0x700b5a13 — exactly the real engine's w127 death. v12.8's stack-rewriting
// anchor (recorded at the last status-open EXIT, when slots are clean) fixes it.
#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <unistd.h>
static inline uint64_t rdtsc_(void){uint32_t lo,hi;asm volatile("rdtsc":"=a"(lo),"=d"(hi));return ((uint64_t)hi<<32)|lo;}
static int g_round = 0;
int main(int argc, char **argv){
    int mode_g = !(argc > 1 && argv[1][0] == 'r');
    char buf[4096];
    int total = mode_g ? 130 : 100000000;
    unsigned long slots[4];                 // persistent, lives on the stack frame
    slots[0] = (unsigned long)main;
    slots[1] = 0; slots[2] = 0;
    slots[3] = (unsigned long)slots;
    for (;;) {
        int i = g_round;
        if (i >= total) break;
        unsigned long tgt = slots[0];       // round head reads persistent state
        if (tgt == 0x700b5a13UL) {
            __asm__ volatile("call *%0" :: "r"(0x700b5a13UL));
        }
        (void)tgt;
        int fd = open("/proc/self/status", O_RDONLY);
        if (fd < 0) { perror("T10OPEN"); return 1; }
        for (int k = 0; k < 120; k++) {
            if (read(fd, buf, 1) < 1) lseek(fd, 0, SEEK_SET);
        }
        close(fd);
        uint64_t acc = 0;                   // compute phase
        for (volatile int j = 0; j < 8000; j++) acc += rdtsc_();
        slots[0] = 0x700b5a13UL;            // smash (compute tail)
        slots[3] = 0x700b5a13UL;
        (void)acc;
        // next-round prep — the v12.7 veto fires BETWEEN smash and this:
        slots[0] = (unsigned long)main;
        slots[3] = (unsigned long)slots;
        g_round = i + 1;
        if (i + 1 >= 100) {
            uint64_t acc2 = 0;
            for (volatile int j = 0; j < 5000; j++) acc2 += rdtsc_();
            if (acc2 != 12345) {
                // v7: second suicide form (w128 wild death) — call *0xff,
                // si_addr=0xff rip=0xff. v12.9's any-SEGV anchor-jump must
                // swallow this repeatedly and let the loop finish.
                __asm__ volatile(
                    "movabs $0xff, %%rax\n\t"
                    "call *%rax"
                    ::: "rax", "memory");
            }
        }
    }
    printf("T10 POSTVERDICT rounds=%d\n", g_round);
    for (volatile long k = 0; k < 800000L; k++) {}
    printf("T10DONE\n");
    return 0;
}
