/* The same live 8-byte caller contract as store_safe.c.
   The attempted four-byte store begins at the object's one-past address. */
void probe(unsigned int *p) {
    p[2] = 42;
}
