#!/usr/bin/env python3
# gen_degfixN.py — depth-N: inside any degfix case cube, pin the next
# unpinned vertex's count. Usage: gen_degfixN.py <case> [<case>...]
# Writes cases to cases_degfixN.txt (appended).
import os, sys
sys.path.insert(0, '.')
from gen_deg_cubes import layout, E, count_cube

N, m, n, d, lo, hi = 22, 4, 7, 10, 7, 10
_, vbase = layout(N, m, n, d, lo, hi)
EM = N * (N - 1) // 2
RANGES = {}
for v in range(N):
    b = vbase.get((v, 'hi'))
    if b is not None: RANGES[v] = range(b, b + (N - 2) * hi)

def row_inputs(v):
    return [w for w in range(N) if w != v][:-1]

def pinned_vertices(base):
    used = set(abs(l) for l in base if abs(l) > EM)
    out = set()
    for v, rng in RANGES.items():
        if used & set(rng): out.add(v)
    return out

def main():
    out = open('cases_degfixN.txt', 'a')
    for case in sys.argv[1:]:
        cf = f'cubes/orig_degfix/{case}.cube'
        base = [int(x) for x in open(cf).read().split()]
        pinned = {abs(l): (1 if l > 0 else 0) for l in base if abs(l) <= EM}
        used_vs = pinned_vertices(base)
        best_v = best_score = best_pinR = best_free = None
        for v in range(N):
            if v in used_vs: continue
            ins = [E(v, w, N) for w in row_inputs(v)]
            pinR = sum(1 for e in ins if e in pinned and pinned[e] == 1)
            pinB = sum(1 for e in ins if e in pinned and pinned[e] == 0)
            free = len(ins) - pinR - pinB
            score = pinR + pinB
            if best_v is None or score > best_score or (score == best_score and free < best_free):
                best_v, best_score, best_pinR, best_free = v, score, pinR, free
        lo_c = max(lo - 1, best_pinR)
        hi_c = min(hi, best_pinR + best_free)
        i = 0
        for cnt in range(lo_c, hi_c + 1):
            lits = list(base) + count_cube(best_v, cnt, N, m, n, lo, hi, vbase)
            name = f'{case}x{best_v}_{cnt:02d}'
            path = f'cubes/orig_degfix/{name}.cube'
            open(path, 'w').write(' '.join(map(str, lits)) + '\n')
            out.write(f'degfix_{name} {N} {m} {n} {d} {lo} {hi} {path}\n')
            i += 1
        print(f'{case}: next v={best_v} pinR={best_pinR} free={best_free} -> {i}')
    out.close()

main()
