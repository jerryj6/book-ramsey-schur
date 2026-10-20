// binary LRAT (CaDiCaL --lrat, --binary=true) -> text LRAT for lrat-check.
// Line forms: 'a' <id:varint-zigzag> <lit:varint-zigzag>... 0 <hint:varint>... 0
//             'd' <deleted-clause-id:varint-zigzag>... 0
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

static long last_add = 0;   /* id of the most recent 'a' record (for 'd' line index) */

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
        if (c == 'd') {
            /* binary 'd' record: 'd' <deleted-id>... 0. Text LRAT form:
               "<index> d <ids>... 0" — the leading index is ignored by
               lrat-check for deletions; CaDiCaL prints latest_id there. */
            fprintf(out, "%ld d", last_add);
            for (;;) { long l = zz(rdvar(in)); if (!l) break; fprintf(out, " %ld", l); }
            fprintf(out, " 0\n");
        } else {
            long id = zz(rdvar(in));
            last_add = id;
            fprintf(out, "%ld", id);
            for (;;) { long l = zz(rdvar(in)); if (!l) break; fprintf(out, " %ld", l); }
            fprintf(out, " 0");
            for (;;) { long h = zz(rdvar(in)); if (!h) break; fprintf(out, " %ld", h); }
            fprintf(out, " 0\n");
        }
    }
    return 0;
}
