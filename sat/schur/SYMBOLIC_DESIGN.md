**Design (write gen_sym.c with args: s t B J [mode])**
- **Expressions.** E is the set of pairs e=(a,b) standing for e(u) = a·u + b, with 0 ≤ a ≤ M and −B ≤ b ≤ B. Keep e only if:
  - a=0 ⇒ b ≥ 1;
  - a=M ⇒ b ≤ −1 (in mode=control use b ≤ −2 instead, i.e. top value M·u−2).
  - With u0 = max(B+1, J+1, s, t, 4), every kept e satisfies 1 ≤ e(u) ≤ M·u−1 for all u ≥ u0. Assert this in code for a = 0..M.
- **Variables.** col[e][i] for i in 1..3, with exactly-one per e.
- **Colour 1 (parameter s) and colour 2 (parameter t).** Same reachability as gen_schur, over E with coefficient-wise addition:
  - R_i[1][e] ← col[e][i];
  - R_i[j][e+f] ← R_i[j−1][e] ∧ col[f][i] whenever e+f ∈ E, for j = 2..k_i−1;
  - forbid R_i[k_i−1][e] ∧ col[e][i].
- **Colour 3 (u−1 summands), "c-padding" encoding.** For each constant c with (0,c) ∈ E and c ≤ M, so that (c,−c) ∈ E:
  - P_c[0][(c,−c)] ← col[(0,c)][3]. The value is (u−1)·c: u−1 copies of c.
  - For j = 1..J: P_c[j][x − (0,c) + y] ← P_c[j−1][x] ∧ col[y][3] for y ∈ E, whenever the result is in E. This replaces one copy of c by y; u ≥ J+1 guarantees enough copies.
  - Forbid P_c[j][x] ∧ col[x][3] for every j = 0..J and every x.
- **Soundness.** For any fixed U ≥ u0 and any 3-colouring χ of [1, M·U−1], setting col[e] = χ(e(U)) and R/P to the true representability satisfies every clause unless χ has a monochromatic solution. Coinciding expressions don't matter. So UNSAT ⇒ S(3;s,t,U) ≤ M·U−1 for all U ≥ u0.
- **Outputs.** Write a map file listing every variable's meaning (var id → kind, i/c/j, (a,b)). We'll need it for Lean later.

**Runs (kissat; cap 30 min each to start)**
1. (s,t) = (4,4), M=11: B ∈ {6,10,15,20,30}, J ∈ {1,2,3}. Report vars/clauses, the result and the time.
2. mode=control for the smallest UNSAT (B,J). It must be SAT, since a valid colouring exists for every u. Decode the model into the colour of each (a,b) and sanity-check it.
3. If (4,4) gives UNSAT, repeat for (4,5) M=14, (5,5) M=19, (4,6) M=17, (5,6) M=24, (6,6) M=29, increasing B if needed.
4. For each (s,t) that goes UNSAT, close the finite range with the existing gen_schur: N = M·u−1 must be UNSAT and N = M·u−2 must be SAT (checked by check_schur) for every u from t up to u0−1. Note u ≥ t is required, since s ≤ t ≤ u.

If (4,4) is SAT for every (B,J), report the model's structure: which (a,b) get which colour, and for small B, which constraint types look missing. Don't invent a new encoding; I'll redesign.

Report a table and paths.
