/* Callable contract: p points to a live writable object of exactly 8 bytes.
   `volatile` makes both stores observable to the optimizer, so this corpus
   deliberately retains two source-level write attempts for disassembly.
   This is a compiler-artifact diagnostic, not a safety or execution claim. */
void probe(volatile unsigned int *p) {
    p[0] = 11u;
    p[1] = 42u;
}
