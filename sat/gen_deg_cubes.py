#!/usr/bin/env python3
# gen_deg_cubes.py — emit degree-count cube files for gen_bookrow layout.
# Layout recomputation (must mirror gen_bookrow.c exactly — archived
# CNFs/cubes/certs all use the C layout, including the reserved N*N block):
#   edges 1..edge_max
#   reserved block of N*N vars (emitted by gen_bookrow.c, unused)
#   red_base = edge_max+1+N*N      (size edge_max*N)
#   blu_base = red_base+edge_max*N (size edge_max*N)
#   per-edge guarded Sinz (u<v in order): red (len-1)*(M-1) then blue (len-1)*(Nb-1)
#   degree bounds: per vertex v: hi-branch (len=N-1 regs... len-1 rows? see below)
#     atmost over c=N-1 lits, K=HI  -> (c-1)*K vars  [if HI < N-1]
#     lo-branch atmost over negated, K=(N-1)-LO     -> (c-1)*K vars  [if LO>0]
#   hi-branch row t (t=0..len-2), j=0..K-1 : var = base + t*K + j
#   s_t[j] = ">= j+1 of first t+1 inputs"; inputs = E(v,w) for w=0..N-1, w!=v.
import sys, itertools, os

def layout(N, m, n, d, lo, hi):
    em = N*(N-1)//2
    aux = em + 1
    aux += N*N  # reserved block, mirroring gen_bookrow.c (part of the canonical layout)
    red_base = aux; aux += em*N
    blu_base = aux; aux += em*N
    # per-edge counters
    for u in range(N):
        for v in range(u+1, N):
            len_ = N-2
            Kr, Kb = m-1, n-1
            if 0 < Kr < len_: aux += (len_-1)*Kr
            if 0 < Kb < len_: aux += (len_-1)*Kb
    deg_start = aux
    vbase = {}
    for v in range(N):
        c = N-1
        if hi < N-1:
            vbase[(v,'hi')] = aux; aux += (c-1)*hi
        if lo > 0:
            vbase[(v,'lo')] = aux; aux += (c-1)*((N-1)-lo)
    return deg_start, vbase

def E(u,v,N):
    a,b=min(u,v),max(u,v); return a*(2*N-a-1)//2+(b-a)

def s19(v, j, N, m, n, lo, hi, vbase):
    # register "first t+1 inputs count >= j+1" on row t=len-2 for hi-branch
    c = N-1; K = hi; t = c-2   # last register row covers inputs 0..c-2 = first c-1 inputs
    return vbase[(v,'hi')] + t*K + j

def count_cube(v, cnt, N, m, n, lo, hi, vbase):
    # lits forcing "reds among first N-2 inputs of v's row == cnt"
    # rows cover inputs 0..N-3 (N-2 inputs); last input index N-2 = edge to w=N-1? no:
    # inputs exclude w==v; count over first N-2 inputs, remaining input is last.
    # s19[j] true iff >= j+1 of first N-2 inputs red (for hi-branch, j=0..hi-1)
    K = hi
    lits = []
    if cnt > 0: lits.append( s19(v, cnt-1, N,m,n,lo,hi,vbase))
    if cnt < K: lits.append(-s19(v, cnt, N,m,n,lo,hi,vbase))
    return lits

def main():
    outdir, N, m, n, d, lo, hi, verts = sys.argv[1], *map(int, sys.argv[2:8]), list(map(int, sys.argv[8].split(',')))
    _, vbase = layout(N,m,n,d,lo,hi)
    os.makedirs(outdir, exist_ok=True)
    # per vertex: count20 range = lo-1 .. hi (deg=count20 + lastinput in {0,1})
    opts = []
    for v in verts:
        opts.append([(v,c) for c in range(lo-1, hi+1)])
    leaves = list(itertools.product(*opts))
    for i, combo in enumerate(leaves):
        lits=[]
        for (v,c) in combo:
            lits += count_cube(v, c, N,m,n,lo,hi,vbase)
        open(f'{outdir}/leaf_{i:04d}.cube','w').write(' '.join(map(str,lits))+'\n')
    print(f"{len(leaves)} leaves -> {outdir}")

if __name__ == '__main__':
    main()
