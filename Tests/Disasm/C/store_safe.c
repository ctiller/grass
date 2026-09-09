/* Callable contract: p points to a live writable object of exactly 8 bytes.
   This fixture's claim concerns the attempted store, not standalone startup. */
void probe(unsigned int *p) {
    p[1] = 42;
}
