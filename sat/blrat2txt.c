// binary LRAT (CaDiCaL --lrat, --binary=true) -> text LRAT for lrat-check.
// Line forms: 'a' <id:varint-zigzag> <lit:varint-zigzag>... 0 <hint:varint>... 0
//             'd' <id:varint-zigzag> <lit:varint-zigzag>... 0
// All fields are zigzag-encoded varints (ids/hints positive, so 2*x).
#include <stdio.h>
#include <stdlib.h>

static unsigned long long rdvar(FILE *f) {
    unsigned long long v = 0; int sh = 0, c;
    do {
        c = fgetc(f);
        if (c == EOF) { fprintf(stderr, "EOF mid-varint\n"); exit(2); }
        v |= (unsigned long long)(c & 0x7f) << sh; sh += 7;
    } while (c & 0x80);
    return v;
}
static long zz(unsigned long long u) { return (u & 1) ? -(long)((u - 1) >> 1) : (long)(u >> 1); }

int main(int argc, char **argv) {
    FILE *in = argc > 1 ? fopen(argv[1], "rb") : stdin;
    FILE *out = argc > 2 ? fopen(argv[2], "w") : stdout;
    if (!in || !out) return 2;
    int c;
    while ((c = fgetc(in)) != EOF) {
        if (c == 'c' || c == 'p' || c == '\n' || c == ' ' || c == '\t' || c == '\r') {
            while (c != '\n' && c != EOF) c = fgetc(in);   // skip comment/header line
            continue;
        }
        if (c != 'a' && c != 'd') { fprintf(stderr, "bad marker 0x%02x\n", c); return 2; }
        long id = zz(rdvar(in));
        if (c == 'd') {
            // binary 'd' record: id + lits + 0  ->  text: "id d 0"
            for (;;) { long l = zz(rdvar(in)); if (!l) break; }
            fprintf(out, "%ld d 0\n", id);
        } else {
            fprintf(out, "%ld", id);
            for (;;) { long l = zz(rdvar(in)); if (!l) break; fprintf(out, " %ld", l); }
            fprintf(out, " 0");
            for (;;) { long h = zz(rdvar(in)); if (!h) break; fprintf(out, " %ld", h); }
            fprintf(out, " 0\n");
        }
    }
    return 0;
}
