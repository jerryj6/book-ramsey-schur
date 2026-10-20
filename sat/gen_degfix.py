#!/usr/bin/env python3
# gen_degfix.py — close timed-out orig_replay leaves by degree-count pins.
# For each leaf: pick vertex v with most pinned inputs among first N-2 inputs;
# emit one child per feasible count value covering v's possible degrees.
import os, sys
sys.path.insert(0, '.')
from gen_deg_cubes import layout, E, count_cube

N, m, n, d, lo, hi = 22, 4, 7, 10, 7, 10
_, vbase = layout(N, m, n, d, lo, hi)
LAST = N - 1  # last input index of each row (w=N-1, or w=N-2 if v=N-1)

def edge_id(u, v): return E(u, v, N)

def decode(e):
    for u in range(N - 1):
        b = u * (2 * N - u - 1) // 2
        if b < e <= b + (N - 1 - u):
            return u, u + (e - b)
    return None

def row_inputs(v):
    # first N-2 inputs of v's Sinz row = all w != v except the last one
    ws = [w for w in range(N) if w != v]
    return ws[:-1]

def main():
    timed_out = sys.argv[1:] or ['0037','0040','0129','0166','0200','0214','0271']
    os.makedirs('cubes/orig_degfix', exist_ok=True)
    out = open('cases_degfix.txt', 'w')
    total = 0
    for lf in timed_out:
        cf = f'cubes/orig_replay/leaf_{lf}.cube'
        base = [int(x) for x in open(cf).read().split()]
        pinned = {abs(l): (1 if l > 0 else 0) for l in base if abs(l) <= N*(N-1)//2}
        # score each vertex by pinned inputs in its first N-2 inputs
        best_v = best_score = best_pinR = best_free = None
        for v in range(N):
            ins = [edge_id(v, w) for w in row_inputs(v)]
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
            name = f'd{lf}_{cnt:02d}'
            path = f'cubes/orig_degfix/{name}.cube'
            open(path, 'w').write(' '.join(map(str, lits)) + '\n')
            out.write(f'degfix_{name} {N} {m} {n} {d} {lo} {hi} {path}\n')
            i += 1
        print(f'leaf {lf}: v={best_v} pinR={best_pinR} free={best_free} cnt=[{lo_c}..{hi_c}] -> {i} children')
        total += i
    out.close()
    print('total children:', total)

main()
