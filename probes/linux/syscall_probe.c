/* External Linux syscall probes, not Grass emission or proof authority.
 * The direct paths issue the architecture syscall instruction themselves.
 * The libc paths deliberately call libc's syscall(2) wrapper for comparison. */
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

_Static_assert(sizeof(long) == 8 && sizeof(void *) == 8,
               "This probe requires the Linux LP64 syscall ABI.");

#if defined(__x86_64__)
static long direct_syscall3(long number, long a1, long a2, long a3) {
    long result;
    __asm__ volatile ("syscall" : "=a"(result) : "a"(number), "D"(a1),
                      "S"(a2), "d"(a3) : "rcx", "r11", "memory");
    return result;
}
static void direct_exit_group(int status) {
    __asm__ volatile ("syscall" : : "a"((long)SYS_exit_group), "D"((long)status)
                      : "rcx", "r11", "memory");
    __builtin_unreachable();
}
#elif defined(__aarch64__)
static long direct_syscall3(long number, long a1, long a2, long a3) {
    register long x8 __asm__("x8") = number;
    register long x0 __asm__("x0") = a1;
    register long x1 __asm__("x1") = a2;
    register long x2 __asm__("x2") = a3;
    __asm__ volatile ("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}
static void direct_exit_group(int status) {
    register long x8 __asm__("x8") = SYS_exit_group;
    register long x0 __asm__("x0") = status;
    __asm__ volatile ("svc 0" : : "r"(x8), "r"(x0) : "memory");
    __builtin_unreachable();
}
#else
#error "This probe supports only Linux x86-64 and AArch64."
#endif

static long invoke(const char *route, long number, long a1, long a2, long a3, int *error) {
    if (!strcmp(route, "direct_raw_assembly")) {
        long result = direct_syscall3(number, a1, a2, a3);
        *error = result < 0 ? (int)-result : 0;
        return result;
    }
    errno = 0;
    long result = syscall(number, a1, a2, a3);
    *error = result == -1 ? errno : 0;
    return result;
}

static int emit_record(int fd, const char *name, const char *route, const char *operation,
                       size_t requested, long result, int raw_error, long emitted) {
    return dprintf(fd, "{\"case\":\"%s\",\"route\":\"%s\",\"operation\":\"%s\","
                   "\"requested\":%zu,\"result\":%ld,\"raw_error\":%d,\"emitted\":%ld}\n",
                   name, route, operation, requested, result, raw_error, emitted) < 0 ? 1 : 0;
}

int main(int argc, char **argv) {
    const char *name, *route;
    int record_fd, error;
    long result, emitted = 0;
    unsigned char buffer[64];
    static const unsigned char payload[] = "grass-linux-syscall";
    size_t requested;
    if (argc != 3) return 64;
    name = argv[1]; record_fd = atoi(argv[2]);
    route = !strncmp(name, "raw_", 4) ? "direct_raw_assembly" :
            !strncmp(name, "libc_", 5) ? "libc_syscall_wrapper" : NULL;
    if (!route) return 64;
    if (!strcmp(name, "raw_missing_record_control")) return 0;
    if (!strcmp(name, "raw_exit_group") || !strcmp(name, "libc_exit_group")) {
        if (!strcmp(name, "raw_exit_group")) direct_exit_group(37);
        syscall(SYS_exit_group, 37); return 65;
    }
    if (!strcmp(name, "raw_number_high32")) {
        /* Linux x86-64 consumes EAX and Linux AArch64 consumes W8 as the number. */
        requested = (size_t)((unsigned long)SYS_getpid | (1UL << 32));
        result = direct_syscall3((long)requested, 0, 0, 0);
        error = result < 0 ? (int)-result : 0;
        return emit_record(record_fd, name, route, "number_width", requested, result, error, 0);
    }
    if (!strcmp(name, "raw_write") || !strcmp(name, "libc_write") ||
        !strcmp(name, "raw_write_badfd") || !strcmp(name, "libc_write_badfd")) {
        int fd = strstr(name, "badfd") ? -1 : STDOUT_FILENO;
        requested = sizeof(payload) - 1;
        result = invoke(route, SYS_write, fd, (long)payload, (long)requested, &error);
        return emit_record(record_fd, name, route, "write", requested, result, error, result > 0 ? result : 0);
    }
    if (!strcmp(name, "raw_read") || !strcmp(name, "libc_read")) {
        requested = sizeof(buffer);
        result = invoke(route, SYS_read, STDIN_FILENO, (long)buffer, (long)requested, &error);
        if (result > 0) emitted = direct_syscall3(SYS_write, STDOUT_FILENO, (long)buffer, result);
        return emit_record(record_fd, name, route, "read", requested, result, error, emitted);
    }
    return 64;
}
