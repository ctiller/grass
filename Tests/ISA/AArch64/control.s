// Independent assembler input for the fixed words in Control.lean.
// clang --target=aarch64-linux-gnu -c control.s -o control.o
.text
cbz x0, .+8
cbz w1, .-4
cbz xzr, .-4
svc #0
svc #65535
hvc #0
smc #0
brk #0
