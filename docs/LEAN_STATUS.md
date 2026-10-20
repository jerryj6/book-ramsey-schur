# Lean source status — partial snapshot

The `lean/` tree is a **partial source snapshot**, not a buildable project.
Several modules referenced by the shipped files were lost with the build VM
before release and have not been reconstructed. `lean-toolchain` and
`lakefile.lean` are scaffolds restored for reconstruction work (toolchain
`leanprover/lean4:v4.35.0`, matching the same-era `jerryj6/erdos-616-t21`
release); they do not make the tree build.

## Missing modules (referenced but not shipped)

| Area | Missing |
|---|---|
| core encoding | `BookRamsey.PureCNF` (edge/triangle vars, `passign`, counter bases), `BookRamsey.PureBridge` (encoding soundness), `BookRamsey.Relabel`, `BookRamsey.LexExists` (block-lex witness), `BookRamsey.Inflate` (pure gzip/base64 decoder), `BookRamsey.LMPVWitness` (K21 lower bound) |
| R(B4,B7) steps | `BookRamsey.R47.Step_d0..d9`, `Step_d11..d21`, `Step_routeA_d7`, `Step_routeA_d8`, `Step_d10_Cubes`, `Step_routeA_d9_Cubes`, `Step_routeA_d9_Coverage` |
| R(B4,B9) steps | `BookRamsey.R49.Step_d00..d26` (only `Step_d09_lo9_hi9.head.lean` survives as a template) |
| Schur | `Schur.DirCerts`, `Schur.SymCert44/45/46/55`, `Schur.SymValidCases` |

## What survives and where the evidence lives

- The 25 shipped modules are the semantic layer: statements, encodings
  (`RowCNF`, `SymCNF`), witnesses (`B49Witness`, `LMPVWitness` — the latter
  missing), bridges, peelings, finals. The Step pattern is fully visible in
  `lean/b49/Step_d09_lo9_hi9.head.lean`: `include_str` a base64-gzipped LRAT
  payload, `LRAT.check` under `native_decide`, then `row_excl_of_check`.
- The certificate payloads the Step modules embed are the same `.lrat.gz`
  files in the Zenodo certificate archive (see README → Certificates).
  `sat/batch_verify.sh` + `sat/blrat2txt` are the check path.
- Independent check tables: `docs/B49_independent_check.csv` (27/27 PASS,
  lrat-check on monolithic B49 leaves), `sat/schur/LRAT_MANIFEST.csv`
  (94/94 PASS, Schur finite certificates), `sat/schur/SYMMETRIC_MANIFEST.csv`
  (all 23 archived symbolic payloads audited: 16 proofs PASS — covering the
  complete theorem chain (4,4) B20J2 / (4,5) B30J1 / (4,6) B30J2 / (5,5) B30J3;
  5 parameter-sweep rows are 0-byte placeholders whose formulas are SAT;
  the two (5,5) J1/J2 payloads end before the empty clause — marked FAIL),
  `docs/verify_report.txt` (40/40 PASS
  sample across all families plus the 6.7 GB corner certificate).
- `#print axioms` output: `docs/R47_AXIOMS.txt`, `docs/SCHUR_AXIOMS.txt`,
  `docs/B49_lean_final.log` (last build log) — the theorems' trust base is
  `propext`, `Classical.choice`, `Quot.sound`, and `native_decide` axioms.

## Rebuilding

Two routes, in increasing effort:

1. **Verify the mathematical content without Lean** — every leaf's CNF + LRAT
   in the archive checks with the shipped converter + stock `lrat-check`; the
   coverage argument is `docs/COVERAGE.csv` + `docs/CERT_STATUS.md`.
2. **Restore the missing modules** — `PureCNF`/`PureBridge` are the encoding
   and its soundness proof; the Step_* modules are mechanically regenerable
   from the archived `.lrat.gz` payloads given the head template. Until they
   are restored, `R49Final`/`R47Final`/`SchurFinal` cannot be rebuilt and the
   final theorems stand on the external certificate checks above.
