/* The same live writable 8-byte caller contract as sequence_safe.c.
   `volatile` preserves both attempted stores for compiler inspection; the
   second begins at p[2], outside the declared eight-byte object. This source
   does not certify a native execution or a formal violation. */
void probe(volatile unsigned int *p) {
    p[0] = 11u;
    p[2] = 42u;
}
