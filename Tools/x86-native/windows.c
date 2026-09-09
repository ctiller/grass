/* One disposable process per case. VEH captures context before stack unwinding.
   Only register-only, non-RSP cases are supported by protocol v1.
   See README.md for the protocol, sources, and observation boundaries. */
#define WIN32_LEAN_AND_MEAN
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
        entry_rsp = c->Rsp;
        registers(c, input, 1);
        /* Change arithmetic flags only; preserve OS-controlled bits. */
        c->EFlags = (c->EFlags & ~0x8D5u) | (flags & 0x8D5u);
        c->Rip = (DWORD64)(code + 1);
        return EXCEPTION_CONTINUE_EXECUTION;
    }
    if (!started || at < (uintptr_t)(code + 1) || at > (uintptr_t)(code + 1 + length))
        return EXCEPTION_CONTINUE_SEARCH;
    DWORD64 actual[16];
    registers(c, actual, 0);
    int completed = e->ExceptionCode == EXCEPTION_BREAKPOINT && at == (uintptr_t)(code + 1 + length);
    printf("{\"status\":\"%s\",\"exception\":%lu,\"pc_offset\":%llu,\"rip_offset\":%llu,\"entry_rsp\":%llu,\"flags\":%lu,\"registers\":[",
        completed ? "completed" : "fault", e->ExceptionCode,
        (unsigned long long)(at - (uintptr_t)(code + 1)),
        (unsigned long long)(c->Rip - (DWORD64)(code + 1)), entry_rsp, c->EFlags);
    for (int i = 0; i < 16; ++i) printf("%s%llu", i ? "," : "", actual[i]);
    printf("]}\n");
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
    if (argc != 19) return 2;
    length = strlen(argv[1]) / 2;
    if (!length || length > 15 || strlen(argv[1]) != length * 2) return 2;
    code = VirtualAlloc(NULL, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    if (!code) return 3;
    code[0] = 0xCC;
    for (size_t i = 0; i < length; ++i) {
        char pair[3] = {argv[1][2*i], argv[1][2*i+1], 0}, *end;
        unsigned long b = strtoul(pair, &end, 16);
        if (*end) return 2;
        code[i+1] = (unsigned char)b;
    }
    code[length+1] = 0xCC;
    for (int i = 0; i < 16; ++i) {
        char *end; input[i] = _strtoui64(argv[i+2], &end, 16); if (*end) return 2;
    }
    flags = strtoul(argv[18], NULL, 16);
    DWORD old;
    if (!VirtualProtect(code,4096,PAGE_EXECUTE_READ,&old) ||
        !FlushInstructionCache(GetCurrentProcess(),code,4096) ||
        !AddVectoredExceptionHandler(1,capture)) return 3;
    SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX);
    ((void (*)(void))code)();
    return 4; /* No case may return through the C call frame. */
}
