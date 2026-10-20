/* gen_bookrow.c — clean-room CNF generator for book Ramsey numbers.
 *
 * Encodes: 2-colouring edges of K_N, no red B_m, no blue B_n,
 * with optional row-fixing (vertex 0 red-degree = d) and global
 * degree bounds lo <= redDeg(v) <= hi, plus optional cube units.
 *
 * Semantics (standard book-Ramsey SAT encoding):
 *   Edge var E(i,j), i<j, true = red, false = blue.
 *   For each edge (u,v): aux c_w <-> E(u,w)&E(v,w)  (common RED neighbor)
 *                        aux d_w <-> !E(u,w)&!E(v,w) (common BLUE neighbor)
 *   Red B_m-free:  E(u,v)  -> sum_w c_w <= m-1
 *   Blue B_n-free: !E(u,v) -> sum_w d_w <= n-1
 *   Row fixing (d>=0): E(0,k)=1 for k<=d, 0 for k>d.
 *   Bounds: forall v, lo <= redDeg(v) <= hi  (Sinz sequential counters).
 *
 * Usage: gen_bookrow N m n d lo hi [cubefile]
 *   d<0 disables row fixing; lo<=0 disables lower bound; hi>=N-1 disables upper.
 *   cubefile: whitespace-separated signed ints, one optional extra literal set
 *   appended as unit clauses (for cube-and-conquer leaves).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int N, M, Nb, D, LO, HI;
static int edge_max;          /* C(N,2) */
static int aux_next;          /* next free variable id */
static long emitted;

static int E(int u, int v){ /* var id of edge (u,v), u!=v, symmetric */
    int a = u < v ? u : v, b = u < v ? v : u;
    return a * (2*N - a - 1) / 2 + (b - a);   /* 1..edge_max */
}

static void emit0(void){ printf("0\n"); emitted++; }
static void emit1(int a){ printf("%d 0\n", a); emitted++; }
static void emit2(int a,int b){ printf("%d %d 0\n", a,b); emitted++; }
static void emit3(int a,int b,int c){ printf("%d %d %d 0\n", a,b,c); emitted++; }
static void emit4(int a,int b,int c,int d){ printf("%d %d %d %d 0\n",a,b,c,d); emitted++; }

/* Sinz at-most-K over lits xs[0..len-1]; aux vars drawn from aux_next.
 * If K<=0 emits -x_i units; if K>=len emits nothing. */
static void atmost(int *xs, int len, int K){
    if (K >= len) return;
    if (K <= 0){ for (int i=0;i<len;i++) emit1(-xs[i]); return; }
    int base = aux_next; aux_next += (len-1) * K;   /* s[t][j], t=0..len-2, j=0..K-1 */
    /* first input */
    emit2(-xs[0], base);
    for (int j=1;j<K;j++) emit1(-(base+j));
    /* middle inputs t=1..len-2 */
    for (int t=1;t<len-1;t++){
        int prev = base + (t-1)*K, cur = base + t*K;
        emit2(-xs[t], cur);
        emit2(-(prev), cur);
        for (int j=1;j<K;j++){
            emit2(-(prev+j), cur+j);
            emit3(-xs[t], -(prev+j-1), cur+j);
        }
        emit2(-xs[t], -(prev+K-1));
    }
    /* last input */
    emit2(-xs[len-1], -(base + (len-2)*K + K-1));
}

int main(int argc, char **argv){
    if (argc < 7){ fprintf(stderr,"usage: %s N m n d lo hi [cubefile]\n",argv[0]); return 2; }
    N=atoi(argv[1]); M=atoi(argv[2]); Nb=atoi(argv[3]);
    D=atoi(argv[4]); LO=atoi(argv[5]); HI=atoi(argv[6]);
    const char *cubefile = argc>7 ? argv[7] : NULL;
    edge_max = N*(N-1)/2;
    aux_next = edge_max + 1;

    /* Variable layout (canonical — archived CNFs/cubes/certs use it):
         1..edge_max        edge vars E(u,v)
         edge_max+1 ..      reserved N*N block (unused by the encoder, but part
                            of the emitted numbering — do not remove)
         then red_base / blu_base blocks of edge_max*N each (per-edge
                            common-neighbour aux vars)
         then per-edge guarded Sinz counters, degree counters, block-lex vars.
       gen_deg_cubes.py:layout() must mirror this exactly. */
    aux_next += N * N;
    int red_base = aux_next; aux_next += edge_max * N;
    int blu_base = aux_next; aux_next += edge_max * N;
    int deg_aux_start = aux_next;      /* degree counters allocated dynamically */
    /* Worst-case aux for degree counters: N vertices * (N-2)*(N-1) */
    int total_vars = aux_next - 1 + N * (N-1) * (N-1);

    /* We can't know clause count before writing; emit to stdout would need
       header first. Buffer: just print header with computed counts. We instead
       compute counts by a dry run? Simpler: write to a temp stream via two-pass.
       Here: print header placeholder, then clauses, then fixup is not possible
       on stdout. So we do pass 1 counting into memory? Easiest: emit clauses to
       a tmpfile, then print header + copy. */
    char tmp[] = "/tmp/genbrXXXXXX";
    int fd = mkstemp(tmp);
    FILE *mem = fdopen(fd, "w+");   /* reread after rewind() to copy to stdout */
    FILE *out = stdout;
    stdout = mem;   /* hack: emit* write to mem */

    /* --- book-free clauses --- */
    for (int u=0;u<N;u++) for (int v=u+1;v<N;v++){
        int e = E(u,v);
        int eidx = e-1;
        int *xs = malloc(sizeof(int)*N);
        int *ys = malloc(sizeof(int)*N);
        int nx=0, ny=0;
        for (int w=0;w<N;w++) if (w!=u && w!=v){
            int cr = red_base + eidx*N + w;
            int cb = blu_base + eidx*N + w;
            /* cr <-> E(u,w) & E(v,w) */
            emit2(-cr, E(u,w)); emit2(-cr, E(v,w)); emit3(cr, -E(u,w), -E(v,w));
            /* cb <-> !E(u,w) & !E(v,w) */
            emit2(-cb, -E(u,w)); emit2(-cb, -E(v,w)); emit3(cb, E(u,w), E(v,w));
            xs[nx++]=cr; ys[ny++]=cb;
        }
        /* E(u,v) -> atmost(xs, m-1): encode as atmost(xs + [E], m-1+1)? No:
           E -> C means atmost over xs guarded by E. Guard each clause with -E.
           Implement guarded Sinz manually below instead. */
        /* red side: if E(u,v) then at most M-1 of xs */
        {
            int K = M-1, len = nx;
            if (K < len){
                if (K<=0){ for (int i=0;i<len;i++) emit2(-e, -xs[i]); }
                else {
                    int base = aux_next; aux_next += (len-1)*K;
                    emit3(-e, -xs[0], base);
                    for (int j=1;j<K;j++) emit2(-e, -(base+j));
                    for (int t=1;t<len-1;t++){
                        int prev=base+(t-1)*K, cur=base+t*K;
                        emit3(-e, -xs[t], cur);
                        emit3(-e, -(prev), cur);
                        for (int j=1;j<K;j++){
                            emit3(-e, -(prev+j), cur+j);
                            emit4(-e, -xs[t], -(prev+j-1), cur+j);
                        }
                        emit3(-e, -xs[t], -(prev+K-1));
                    }
                    emit3(-e, -xs[len-1], -(base+(len-2)*K+K-1));
                }
            }
        }
        /* blue side: if !E(u,v) then at most Nb-1 of ys */
        {
            int K = Nb-1, len = ny;
            if (K < len){
                if (K<=0){ for (int i=0;i<len;i++) emit2(e, -ys[i]); }
                else {
                    int base = aux_next; aux_next += (len-1)*K;
                    emit3(e, -ys[0], base);
                    for (int j=1;j<K;j++) emit2(e, -(base+j));
                    for (int t=1;t<len-1;t++){
                        int prev=base+(t-1)*K, cur=base+t*K;
                        emit3(e, -ys[t], cur);
                        emit3(e, -(prev), cur);
                        for (int j=1;j<K;j++){
                            emit3(e, -(prev+j), cur+j);
                            emit4(e, -ys[t], -(prev+j-1), cur+j);
                        }
                        emit3(e, -ys[t], -(prev+K-1));
                    }
                    emit3(e, -ys[len-1], -(base+(len-2)*K+K-1));
                }
            }
        }
        free(xs); free(ys);
    }

    /* --- row fixing: vertex 0 red-degree = D --- */
    if (D >= 0){
        for (int k=1;k<N;k++) emit1(k<=D ? E(0,k) : -E(0,k));
    }

    /* --- global degree bounds lo<=deg(v)<=hi --- */
    if (LO>0 || HI < N-1){
        int *lits = malloc(sizeof(int)*N);
        int *nlits = malloc(sizeof(int)*N);
        for (int v=0;v<N;v++){
            int c=0;
            for (int w=0;w<N;w++) if (w!=v){ lits[c]=E(v,w); nlits[c]=-E(v,w); c++; }
            if (HI < N-1) atmost(lits, c, HI);
            if (LO>0) atmost(nlits, c, (N-1)-LO);   /* at most N-1-LO blue edges */
        }
        free(lits); free(nlits);
    }

    /* --- block-lex symmetry breaking (RowCNF.lean rowBlockLexClauses) ---
       For consecutive vertices i,i+1 both in the same interchangeability
       block (i in 1..N-2, i != D when D>=0): enforce row_i >=lex row_{i+1}
       where each row is the red-edge profile over V\{i,i+1} in natural order.
       leader: [a -b] (t=0) or [-prev a -b]; equality defines lex(i,t) <->
       prev && (a<->b). Matches the shipped spec clause-for-clause. */
    {
        for (int i=1;i<N-1;i++){
            if (D>=0 && i==D) continue;
            /* k sequence: vertices excluding i and i+1, in natural order */
            int prev = 0;
            int pos = 0;
            for (int k=0;k<N;k++){
                if (k==i || k==i+1) continue;
                int a = E(i,k), b = E(i+1,k);
                int q = 0;
                if (pos < N-3){ /* t < N-3 -> equality defines q = lex(i,t) */
                    q = aux_next++;
                }
                /* leader */
                if (pos == 0) emit2(a, -b);
                else emit3(-prev, a, -b);
                /* equality */
                if (q){
                    if (pos == 0){ emit3(-a,-b,q); emit3(a,b,q); }
                    else { emit4(-prev,-a,-b,q); emit4(-prev,a,b,q); }
                }
                prev = q;
                pos++;
            }
        }
    }

    /* --- cube units --- */
    if (cubefile){
        FILE *cf = fopen(cubefile,"r");
        if (!cf){ fprintf(stderr,"cannot open %s\n",cubefile); return 2; }
        int lit;
        while (fscanf(cf,"%d",&lit)==1) emit1(lit);
        fclose(cf);
    }

    fflush(mem);
    long clauses = emitted;
    int vars = aux_next - 1;
    fprintf(out, "c gen_bookrow N=%d m=%d n=%d d=%d lo=%d hi=%d\n", N,M,Nb,D,LO,HI);
    fprintf(out, "p cnf %d %ld\n", vars, clauses);
    rewind(mem);
    char buf[65536]; size_t r;
    while ((r=fread(buf,1,sizeof buf,mem))>0) fwrite(buf,1,r,out);
    fclose(mem); remove(tmp);
    return 0;
}
