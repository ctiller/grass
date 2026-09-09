/* One disposable process per case. VEH captures context before stack unwinding.
   Protocol v1 uses the host stack; --stack adds bounded scratch-stack capture.
   See README.md for the protocol, sources, and observation boundaries. */
#define WIN32_LEAN_AND_MEAN
#define _WIN32_WINNT 0x0602
#include <windows.h>
#include <intrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned char *code;
static size_t length;
static DWORD64 input[16], entry_rsp;
static DWORD flags;
static int started;
static int stack_mode;
static size_t terminal_offset;
static unsigned char *scratch;
static unsigned char scratch_before[65536];
static unsigned char scratch_after[65536];
static DWORD64 *stack_slots; /* target exit RSP in its own RW page */
static DWORD64 *restore_slot; /* original host RSP in a separate read-only page */
static DWORD64 original_host_rsp;
static ULONG_PTR host_low, host_high;
static size_t page_size;

static int separated(uintptr_t a, size_t an, uintptr_t b, size_t bn) {
    return an && bn && a <= UINTPTR_MAX-an && b <= UINTPTR_MAX-bn &&
        (a+an <= b || b+bn <= a);
}

static void print_bytes(const unsigned char *bytes, size_t size) {
    for (size_t i = 0; i < size; ++i) printf("%02x", bytes[i]);
}

static void registers(CONTEXT *c, DWORD64 *r, int set) {
#define REG(i, name) if (set) c->name = r[i]; else r[i] = c->name
    REG(0,Rax); REG(1,Rcx); REG(2,Rdx); REG(3,Rbx);
    /* RSP is captured but never initialized from arbitrary corpus data. */
    if (!set) r[4] = c->Rsp;
    REG(5,Rbp); REG(6,Rsi); REG(7,Rdi); REG(8,R8); REG(9,R9);
    REG(10,R10); REG(11,R11); REG(12,R12); REG(13,R13);
    REG(14,R14); REG(15,R15);
#undef REG
}

static LONG CALLBACK capture(EXCEPTION_POINTERS *p) {
    CONTEXT *c = p->ContextRecord;
    EXCEPTION_RECORD *e = p->ExceptionRecord;
    uintptr_t at = (uintptr_t)e->ExceptionAddress;
    if (!started && e->ExceptionCode == EXCEPTION_BREAKPOINT && at == (uintptr_t)code) {
        started = 1;
        if (stack_mode) {
            if (c->Rsp < host_low || c->Rsp >= host_high) ExitProcess(5);
            original_host_rsp = c->Rsp;
            *restore_slot = original_host_rsp;
            DWORD previous;
            if (!VirtualProtect(restore_slot,page_size,PAGE_READONLY,&previous)) ExitProcess(3);
            c->Rsp = (DWORD64)(scratch + sizeof(scratch_before) - 120);
        }
        entry_rsp = c->Rsp;
        registers(c, input, 1);
        /* Change arithmetic flags only; preserve OS-controlled bits. */
        c->EFlags = (c->EFlags & ~0x8D5u) | (flags & 0x8D5u);
        c->Rip = (DWORD64)(code + 1);
        return EXCEPTION_CONTINUE_EXECUTION;
    }
    if (!started) return EXCEPTION_CONTINUE_SEARCH;
    if (at < (uintptr_t)(code + 1) || at > (uintptr_t)(code + 1 + terminal_offset))
        ExitProcess(6); /* no other handler may resume a failed probe */
    DWORD64 actual[16];
    registers(c, actual, 0);
    int completed = e->ExceptionCode == EXCEPTION_BREAKPOINT && at == (uintptr_t)(code + 1 + terminal_offset);
    if (stack_mode && completed) {
        /* Terminal INT3 ran on the original host stack, not the observed memory. */
        if (c->Rsp != original_host_rsp || *restore_slot != original_host_rsp) ExitProcess(5);
        actual[4] = stack_slots[0];
        memcpy(scratch_after, scratch, sizeof(scratch_after));
    }
    printf("{\"status\":\"%s\",\"exception\":%lu,\"pc_offset\":%llu,\"rip_offset\":%llu,\"entry_rsp\":%llu,\"flags\":%lu,\"registers\":[",
        completed ? "completed" : (at >= (uintptr_t)(code + 1 + length) ? "harness-error" : "fault"), e->ExceptionCode,
        (unsigned long long)(at - (uintptr_t)(code + 1)),
        (unsigned long long)(c->Rip - (DWORD64)(code + 1)), entry_rsp, c->EFlags);
    for (int i = 0; i < 16; ++i) printf("%s%llu", i ? "," : "", actual[i]);
    printf("]");
    if (stack_mode) {
        printf(",\"stack\":");
        if (!completed) printf("null"); /* fault delivery may have modified scratch */
        else {
            printf("{\"base\":%llu,\"size\":%zu,\"entry_offset\":%zu,\"host_low\":%llu,\"host_high\":%llu,\"host_rsp\":%llu,\"code_base\":%llu,\"page_size\":%zu,\"suffix\":\"",
                (unsigned long long)(uintptr_t)scratch, sizeof(scratch_before), sizeof(scratch_before)-120,
                (unsigned long long)host_low, (unsigned long long)host_high, original_host_rsp,
                (unsigned long long)(uintptr_t)code, page_size);
            print_bytes(code+1+length,14);
            printf("\",\"before\":\"");
            print_bytes(scratch_before, sizeof(scratch_before));
            printf("\",\"after\":\""); print_bytes(scratch_after, sizeof(scratch_after));
            printf("\"}");
        }
    }
    printf("}\n");
    fflush(stdout);
    ExitProcess(0);
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--host")) {
        int r[4]; char vendor[13];
        __cpuid(r, 0); memcpy(vendor,r+1,4); memcpy(vendor+4,r+3,4); memcpy(vendor+8,r+2,4); vendor[12]=0;
        __cpuid(r, 1);
        printf("{\"vendor\":\"%s\",\"cpuid_1_eax\":%u,\"hypervisor_present\":%s}",
            vendor, (unsigned)r[0], ((unsigned)r[2] >> 31) ? "true" : "false");
        return 0;
    }
    stack_mode = argc == 20 && !strcmp(argv[19], "--stack");
    if (argc != 19 && !stack_mode) return 2;
    length = strlen(argv[1]) / 2;
    if (!length || length > (stack_mode ? 255u : 15u) || strlen(argv[1]) != length * 2) return 2;
    SYSTEM_INFO system; GetSystemInfo(&system);
    size_t page = system.dwPageSize;
    page_size = page;
    if (page < 1024 || page > sizeof(scratch_before) || sizeof(scratch_before)%page) return 3;
    code = VirtualAlloc(NULL, 3*page, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!code) return 3;
    code[0] = 0xCC;
    for (size_t i = 0; i < length; ++i) {
        char pair[3] = {argv[1][2*i], argv[1][2*i+1], 0}, *end;
        unsigned long b = strtoul(pair, &end, 16);
        if (*end) return 2;
        code[i+1] = (unsigned char)b;
    }
    terminal_offset = length;
    if (stack_mode) {
        unsigned char *reservation = VirtualAlloc(NULL, sizeof(scratch_before)+2*page,
            MEM_RESERVE, PAGE_NOACCESS);
        if (!reservation) return 3;
        scratch = VirtualAlloc(reservation+page, sizeof(scratch_before), MEM_COMMIT, PAGE_READWRITE);
        if (!scratch) return 3;
        GetCurrentThreadStackLimits(&host_low, &host_high);
        if (host_high <= host_low ||
            !separated((uintptr_t)code,3*page,(uintptr_t)reservation,sizeof(scratch_before)+2*page) ||
            !separated((uintptr_t)code,3*page,host_low,host_high-host_low) ||
            !separated((uintptr_t)reservation,sizeof(scratch_before)+2*page,host_low,host_high-host_low)) return 3;
        for (size_t i=0; i<sizeof(scratch_before); ++i) scratch[i] = (unsigned char)(i*37+0xA5);
        memcpy(scratch_before, scratch, sizeof(scratch_before));
        stack_slots = (DWORD64 *)(code+page);
        restore_slot = (DWORD64 *)(code+2*page);
        /* MOV [RIP+disp32],RSP; MOV RSP,[RIP+disp32]. Neither touches flags. */
        unsigned char *suffix = code+1+length;
        const unsigned char save[] = {0x48,0x89,0x25}, restore[] = {0x48,0x8B,0x25};
        int32_t displacement = (int32_t)((unsigned char *)&stack_slots[0] - (suffix+7));
        memcpy(suffix,save,3); memcpy(suffix+3,&displacement,4);
        displacement = (int32_t)((unsigned char *)restore_slot - (suffix+14));
        memcpy(suffix+7,restore,3); memcpy(suffix+10,&displacement,4);
        terminal_offset += 14;
    }
    code[terminal_offset+1] = 0xCC;
    for (int i = 0; i < 16; ++i) {
        char *end; input[i] = _strtoui64(argv[i+2], &end, 16); if (*end) return 2;
    }
    flags = strtoul(argv[18], NULL, 16);
    DWORD old;
    if (!VirtualProtect(code,page,PAGE_EXECUTE_READ,&old) ||
        !FlushInstructionCache(GetCurrentProcess(),code,page) ||
        !AddVectoredExceptionHandler(1,capture)) return 3;
    SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);
    ((void (*)(void))code)();
    return 4; /* No case may return through the C call frame. */
}
