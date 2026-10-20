# Book Ramsey numbers and Schur numbers — computer-assisted proofs

This repository contains computer-assisted proofs of three results, each shipped with

* a paper describing the argument (`paper/`, LaTeX sources included),
* an end-to-end Lean 4 formalization (`lean/`),
* the SAT encoders, cube generators and checkers used for the computational leaves
  (`sat/`), with the certificates (CNF / LRAT, ≈ 50 GB) archived on Zenodo:
  [10.5281/zenodo.23510386](https://doi.org/10.5281/zenodo.23510386) and
  [10.5281/zenodo.23513200](https://doi.org/10.5281/zenodo.23513200)
  (see [Certificates](#certificates)),
* a complete per-leaf coverage manifest and verification record (`docs/`).

The results are computer-assisted and have not been externally peer-reviewed; see
[Status and caveats](#status-and-caveats).

## Results

### R(B₄,B₉) = 27

Every red/blue colouring of K₂₇ contains a red book B₄ (4 triangles sharing a
common edge) or a blue book B₉. This settles the previously open `{27, 28}` cell
of the book Ramsey table. In Lean (`lean/b49/R49Final.lean`):

```lean
theorem R_B4_B9_eq : LowerBound 26 4 9 ∧ UpperBound 27 4 9
```

`UpperBound N m n` states that every symmetric colouring of `K_N` has a red edge
with ≥ m red common neighbours or a blue edge with ≥ n blue common neighbours;
`LowerBound N m n` is an explicit counterexample colouring of `K_N`
(`lean/b49/Statement.lean`).

### R(B₄,B₇) = 22

Every red/blue colouring of K₂₂ contains a red B₄ or a blue B₇, and there is a
colouring of K₂₁ avoiding both. In Lean (`lean/r47/R47Final.lean`):

```lean
theorem R_B4_B7_eq : LowerBound 21 4 7 ∧ UpperBound 22 4 7
```

### Ahmed–Schaal Conjecture 2

For generalized Schur numbers `S(3;s,t,u)` — the least N such that every
3-colouring of `[1,N]` has a colour-0 solution of `x₁+…+x_{s−1} = x_s`, a
colour-1 solution for `t`, or a colour-2 solution for `u` (repetition allowed) —
the conjectured closed form `S(3;s,t,u) = s·t·u − t·u − u − 1` is proved for

    (s,t) ∈ {(4,4), (4,5), (4,6), (5,5)}   and all u ≥ t.

In Lean (`lean/schur/SchurFinal.lean`), e.g.

```lean
theorem conj_4_4 : ConjFamily 4 4
```

## Proof overview

### Book Ramsey upper bounds

1. **Reduction.** A good colouring of `K_N` (no red B_m, no blue B_n) is encoded
   as a SAT instance on the `C(N,2)` edge variables: book clauses forbid any
   edge having ≥ m (resp. ≥ n) same-colour common neighbours
   (`sat/gen_bookrow.c`).
2. **Degree stratification.** In any B₄-free red graph the red-degree of every
   vertex is bounded by a triangle-free graph on that many vertices. The search
   space is partitioned by per-vertex degree bounds (`Peeling.lean`), and each
   stratum is split into cubes (partial assignments) that are refuted
   independently.
3. **Coverage tree.** Hard leaves are split recursively by degree-pin
   (fixing one vertex's exact degree) and edge-OR descent, producing a coverage
   tree whose 812 leaves are each individually UNSAT
   (`docs/COVERAGE.csv` — one row per leaf: family, verdict, LRAT bytes, sha256).
4. **Certificates.** Every leaf carries a CaDiCaL **binary** LRAT certificate
   (`.lrat.gz`), independently checkable by `lrat-check` after conversion
   (`sat/blrat2txt.c`, `scripts/verify_cert.sh`).

### Lower bounds

* `R(B₄,B₉) > 26`: the unique srg(26,10,3,4) used as the red graph — red-degrees
  are 10, every red edge has exactly 3 red common neighbours, and every blue
  edge exactly 8; checked by `native_decide` in `lean/b49/B49Witness.lean`.
* `R(B₄,B₇) > 21`: an explicit colouring of `K₂₁`, `LowerBound 21 4 7` in
  `lean/r47/R47Final.lean`.

### Schur (symbolic encoding)

For each (s,t) pair the statement splits into a finite range of u (one ordinary
CNF per u) and a *symbolic* range u ≥ threshold, where a single CNF — built over
interval-structured colour variables — proves every u simultaneously
(`lean/schur/SymCNF.lean`, `SymValid.lean`, `SymSound.lean`). Lower-bound
colourings are given in `lean/schur/Construction.lean`.

## Trust base

`#print axioms` invocations are included in `R49Final.lean`, `R47Final.lean` and
`schur/Axioms.lean`; recorded output is in `docs/R47_AXIOMS.txt`,
`docs/SCHUR_AXIOMS.txt`, and `docs/B49_lean_final.log`. Semantic arguments
(definitions, reductions, encoding soundness, witness validity) are
kernel-checked; `native_decide` is used for closed Boolean computations — the
srg witness check, the 312 embedded d10 coverage cubes in `Step_d10.lean`,
coverage checks, **and the `LRAT.check` certificate verifications inside the
Step_* modules** — so the trust base includes the Lean compiler/runtime for
those native evaluations. There is no `sorry` in the import closure.

The SAT solvers are not trusted: each leaf's claim is its LRAT certificate, and
a wrong certificate makes `lrat-check` fail.

## Certificates

The ≈ 50 GB certificate archive (CNF + gzipped binary LRAT + solver log per
leaf, plus `COVERAGE.csv`) is archived on Zenodo across two records — Zenodo
caps each record at 50 GB:

* **[10.5281/zenodo.23510386](https://doi.org/10.5281/zenodo.23510386)** — main
  record: all Ramsey certificates (88 files).
* **[10.5281/zenodo.23513200](https://doi.org/10.5281/zenodo.23513200)** — the
  Ahmed–Schaal certificates (`sa_certs/{cnf,lrat,log}`).

Each logical archive is split into 600 MB `partNNpart` pieces on the record.
Reassemble and unpack with:

```sh
cat v3_b49.tar.part* > v3_b49.tar && tar -xf v3_b49.tar
```

| Archive | Contents |
|---|---|
| `v3_b49.tar` | all 53 B₄₉ leaves (R(B₄,B₉)=27, complete) |
| `v3_d8.tar`, `v3_d9.tar` | R₄₇ d8/d9 families |
| `v3_r47_rest.tar` | r47 monolithics, d6/d7/d10–d13, controls |
| `v3_replay0–9.tar` | the origT/f0129/f0040 replay families (~37 GB) |
| `v3_corner.lrat.gz` | the corner leaf's 2.9 GB certificate (the 6.7 GB proof, gzipped) |
| `v3_sa_certs.tar` | Ahmed–Schaal certificates — on the part-2 record |
| `v3_docs.tar`, `COVERAGE.csv` | status/handoff docs + the leaf manifest |

Unpack each archive to get `r47/…`, `b49/…` or `sa_certs/…` trees of
`<leaf>.{cnf,cube,res,log,lrat.gz}`.

**Verify any leaf** (binary → text LRAT, then `lrat-check`):

```sh
zcat leaf.lrat.gz | ./sat/blrat2txt > leaf.txt
lrat-check leaf.cnf leaf.txt        # or: scripts/verify_cert.sh leaf.cnf leaf.lrat.gz
```

`blrat2txt` decodes CaDiCaL's binary proof format (`a`/`d` records of zigzag
varints, `map(u): even → u/2, odd → −((u−1)/2)`). lrat-check needs the text form.

Verification already run (`docs/verify_report.txt`):

* the hardest leaf of the campaign — the all-degree-10 corner of leaf
  `origT_0129` in R(B₄,B₇), a 6.7 GB proof — **VERIFIED**
  (40,966,628 clauses checked),
* a random 40-certificate sample across every family: **40/40 VERIFIED**,
* every one of the 812 leaves additionally carries a solver verdict (809 UNSAT,
  2 SAT, 1 TIMEOUT) and a sha256 in `docs/COVERAGE.csv`; all 27 monolithic B49
  leaves were additionally `lrat-check`ed (`docs/B49_independent_check.csv`),
  as were all 94 Schur certificates (`sat/schur/LRAT_MANIFEST.csv`).

## Repository map

```
README.md            this file
LICENSE              MIT
CITATION.cff
paper/               R_B4_B7.tex/.pdf, R_B4_B9.tex/.pdf, Schur_AhmedSchaal.tex/.pdf (amsart)
lean/
  lean-toolchain     leanprover/lean4:v4.35.0; lakefile.lean is a rebuild
                     scaffold — the tree is a partial snapshot, see
                     docs/LEAN_STATUS.md for the missing modules
  b49/               R(B₄,B₉)=27: Statement, RowCNF, RowBridge, Peeling,
                     B49Witness (srg(26,10,3,4) lower bound), Step_d09_*, R49Final
  r47/               R(B₄,B₇)=22: Statement, Peeling, Step_routeA_d9, Step_d10
                     (312 embedded coverage cubes), Step_d10_Coverage, R47Final
  schur/             SchurStatement, SymCNF/SymValid/SymSound (symbolic encoding),
                     Construction (lower bounds), SchurFinal, Axioms
sat/                 gen_bookrow.c (CNF encoder), gen_deg*.py (degree cubes),
                     refine_splits.py, assemble_certs.py, run_case.sh,
                     batch_verify.sh, blrat2txt.c (binary→text LRAT)
sat/schur/           Schur-side generators/checkers (gen_schur.c, gen_sym.c,
                     check_schur.c, gen_sym2.py), SYMBOLIC_DESIGN.md,
                     LRAT_MANIFEST.csv (94 PASS)
scripts/verify_cert.sh
docs/                CERT_STATUS.md, LEAN_STATUS.md, HANDOFF.md (archive layout),
                     COVERAGE.csv (812 leaves, B4×B7/B4×B9 families only),
                     verify_report.txt, B49_independent_check.csv,
                     R47_AXIOMS.txt, SCHUR_AXIOMS.txt, B49_lean_final.log,
                     R47_REGEN_STATUS.md, R47_*_manifest.json
```

## Status and caveats

* **Computer-assisted.** The upper bounds have no human-readable proof; they rest
  on 812 leaves, with certificates up to ~6.7 GB of LRAT.
* **`native_decide`.** The Lean development trusts the Lean compiler/runtime for
  the closed Boolean evaluations listed above, including the `LRAT.check` runs
  inside the certificate modules.
* **Not externally peer-reviewed.** Scrutiny is welcome, especially of the CNF
  encodings (`sat/gen_bookrow.c`), the coverage-tree completeness argument
  (`docs/CERT_STATUS.md`), and the symbolic Schur encoding
  (`lean/schur/SymSound.lean`).
* **Partial Lean snapshot.** The released `lean/` tree does not build: several
  modules (encoding layer, most Step_* certificate modules, Schur cert
  modules) were lost with the build VM — `docs/LEAN_STATUS.md` lists them and
  explains what can be reconstructed from the certificate archive. The final
  theorems currently stand on the external `lrat-check` verification.
* **Certificate archive.** The ≈50 GB archive is published on Zenodo
  ([10.5281/zenodo.23510386](https://doi.org/10.5281/zenodo.23510386),
  [10.5281/zenodo.23513200](https://doi.org/10.5281/zenodo.23513200));
  `docs/HANDOFF.md` describes the layout.
* **Certificate provenance.** The released certificates were produced by a
  clean-room re-encoding of the campaign's cube partitions, validated against
  known small Ramsey values; SAT controls (e.g. `R(B₄,B₇)>16` satisfiable) are
  included in the archive.

## Citation

```bibtex
@misc{yong2026bookramseyschur,
  author       = {Jerry Yong},
  title        = {Computer-assisted proofs: $R(B_4,B_7)=22$, $R(B_4,B_9)=27$,
                  and Ahmed--Schaal Conjecture 2},
  year         = {2026},
  howpublished = {\url{https://github.com/jerryj6/book-ramsey-schur}},
  note         = {Computer-assisted; Lean 4 formalizations; SAT certificates:
                  \url{https://doi.org/10.5281/zenodo.23510386},
                  \url{https://doi.org/10.5281/zenodo.23513200}}
}
```

See also `CITATION.cff`.

## License

Code (Lean sources, C/Python generators, scripts) is released under the MIT
License (`LICENSE`). The papers (`paper/`) are released under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
