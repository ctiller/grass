/* External model probes, not Grass emission or proof authority.
 * Source: Microsoft WriteFile (Parameters, Synchronization, Pipes), 2026-09-09.
 * Each invocation is isolated by the runner's process timeout. */
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdio.h>
#include <string.h>

static unsigned char input[65536], received[65536];

int main(int argc, char **argv) {
    HANDLE reader = INVALID_HANDLE_VALUE, writer = INVALID_HANDLE_VALUE;
    DWORD requested = 15, count = 0xA5A5A5A5, got = 0, error, available = 0;
    BOOL result, read_ok = TRUE;
    unsigned i;
    char pipe_name[128];
    if (argc != 2) return 2;
    for (i = 0; i < sizeof(input); ++i) input[i] = (unsigned char)(i * 37 + 11);
    if (!strcmp(argv[1], "partial")) {
        sprintf_s(pipe_name, sizeof(pipe_name), "\\\\.\\pipe\\grass-writefile-%lu", GetCurrentProcessId());
        writer = CreateNamedPipeA(pipe_name, PIPE_ACCESS_OUTBOUND,
            PIPE_TYPE_BYTE | PIPE_READMODE_BYTE | PIPE_NOWAIT, 1, 4096, 4096, 0, NULL);
        if (writer == INVALID_HANDLE_VALUE) return 3;
        reader = CreateFileA(pipe_name, GENERIC_READ, 0, NULL, OPEN_EXISTING, 0, NULL);
        if (reader == INVALID_HANDLE_VALUE) { CloseHandle(writer); return 4; }
        requested = sizeof(input);
    } else if (strcmp(argv[1], "invalid")) {
        if (!CreatePipe(&reader, &writer, NULL, 4096)) return 5;
        if (!strcmp(argv[1], "zero")) requested = 0;
        else if (!strcmp(argv[1], "broken")) { CloseHandle(reader); reader = INVALID_HANDLE_VALUE; }
        else if (strcmp(argv[1], "success")) return 2;
    }
    SetLastError(0xDEADBEEF);
    result = WriteFile(writer, input, requested, &count, NULL);
    error = GetLastError(); /* only interpreted on failure */
    if (reader != INVALID_HANDLE_VALUE) {
        read_ok = PeekNamedPipe(reader, NULL, 0, NULL, &available, NULL);
        if (read_ok && available) {
            DWORD to_read = available < sizeof(received) ? available : sizeof(received);
            read_ok = ReadFile(reader, received, to_read, &got, NULL);
        }
    }
    printf("{\"case\":\"%s\",\"requested\":%lu,\"bool\":%d,\"count\":%lu,"
           "\"last_error\":%lu,\"observed\":%lu,\"read_ok\":%s,\"prefix_matches\":%s}\n",
           argv[1], requested, result, count, error, got, read_ok ? "true" : "false",
           got <= sizeof(input) && !memcmp(input, received, got) ? "true" : "false");
    if (reader != INVALID_HANDLE_VALUE) CloseHandle(reader);
    if (writer != INVALID_HANDLE_VALUE) CloseHandle(writer);
    return 0;
}
