# Book Ramsey numbers and Schur numbers — computer-assisted proofs

Computer-assisted proofs of three results, each with a paper, an end-to-end
Lean 4 formalization, and independently verifiable SAT certificates:

* **R(B₄,B₇) = 22** — every red/blue colouring of K₂₂ contains a red book
  B₄ (4 triangles sharing an edge) or a blue book B₇ (`paper/R_B4_B7.pdf`,
  `lean/r47/`).
* **R(B₄,B₉) = 27** — settling the previously open {27,28} cell of the book
  Ramsey table (`paper/R_B4_B9.pdf`, `lean/b49/`).
* **Ahmed–Schaal Conjecture 2** — S(3;s,t,u) for (s,t) ∈ {(4,4),(4,5),(4,6),(5,5)}
  and all u ≥ t, via a *symbolic* SAT encoding whose single CNF covers all u
  (`paper/Schur_AhmedSchaal.pdf`, `lean/schur/`).

Lower bounds are witnessed constructions (e.g. `lean/b49/B49Witness.lean`);
upper bounds are UNSAT verdicts on degree-stratified cube partitions whose
LRAT certificates are independently checkable — see below.

## Status and caveats

Computer-assisted results, not externally peer-reviewed. The certificate
payloads are large (≈44 GB total) and are distributed out-of-band (archive
links in `docs/HANDOFF.md`); this repository carries the papers, the Lean
formalizations, the generators, the converters, and the full coverage
manifest `docs/COVERAGE.csv` (813 leaves, verdict + sha256 per leaf).

## Verifying a certificate

Every `.lrat.gz` payload is **binary** LRAT (CaDiCaL `--lrat`, `--binary=true`
default). drat-trim's `lrat-check` reads text LRAT, so verification goes
through the bundled converter `sat/blrat2txt.c`:

```bash
git clone https://github.com/arminbiere/drat-trim && (cd drat-trim && make -j)
./scripts/verify_cert.sh leaf.cnf leaf.lrat.gz
# which does: zcat leaf.lrat.gz | ./sat/blrat2txt > fifo && lrat-check leaf.cnf fifo
```

The converter decodes CaDiCaL's binary proof format:
`a <id> <lits>… 0 <hints>… 0` / `d <id> <lits>… 0` records, each field a
zigzag varint with `map(u): even → u/2, odd → −((u−1)/2)`, and emits text LRAT
(`id d 0` for deletions).

Verification already run (see `docs/verify_report.txt` and
`docs/CERT_STATUS.md`):

* the hardest leaf of the campaign — the all-degree-10 corner of leaf
  `origT_0129` in the R(B₄,B₇) certificate, a 6.7 GB proof — **VERIFIED**
  (40,966,628 clauses, ~5 min of lrat-check),
* a random 40-certificate sample across every family: **40/40 VERIFIED**,
* every leaf additionally carries a solver UNSAT verdict and sha256 manifest.

## Layout

    paper/   the three result papers (PDF)
    lean/    Lean 4 formalizations: b49 (R(B4,B9)), r47 (R(B4,B7)), schur
    sat/     CNF encoders, cube/descent generators, binary-LRAT converter
    docs/    CERT_STATUS.md, HANDOFF.md, COVERAGE.csv, verify_report.txt
    scripts/ verify_cert.sh

## License

MIT (see LICENSE).
