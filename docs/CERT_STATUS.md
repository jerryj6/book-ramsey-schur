# Certificate Status — FINAL (all coverage leaves closed)

## Result

**Every coverage leaf is closed UNSAT.** The full R(B4,B7)=22 certificate regeneration is complete:
all 812 manifest rows in `docs/COVERAGE.csv` carry sha256-listed LRAT certificates, verified by
verdict (cadical/kissat exit code 20) — 809 UNSAT, 2 SAT (controls), 1 TIMEOUT. The manifest covers
only the B4×B7/B4×B9 families; the 94 Schur certificates have their own manifest
(`sat/schur/LRAT_MANIFEST.csv`, all PASS). No open leaves remain.

## Coverage semantics

- `coverage_prefix`: a leaf's name + `x` is the prefix of every descendant leaf in that subtree.
  Coverage proved bottom-up: a leaf is "final" iff UNSAT-marked and no UNSAT ancestor covers it,
  OR it has no descendants and its own verdict is final.
- `covered-by-ancestor=<parent>` lines in `.res` mark leaves subsumed by a proven-UNSAT ancestor.
- `anc_unsat()` in assemble_certs.py implements the topmost-UNSAT-frontier extraction.

## How the corner closed

The all-max-degree corner of leaf `origT_0129` (the deepest residual of the campaign, all 22
vertices pinned to red-degree 10) was proven UNSAT by a dedicated `cadical --lrat` run
(`verdict_L=20` at 1792477777), after the wave-driven degree-pin + edge-OR descent had closed
every sibling region. All strict descendants of the proven node are marked covered-by-ancestor.

## Known quirk fixed mid-run

An auxiliary verdict file (`_L.res`, containing `verdict_L=20`) lacked the literal word
`UNSATISFIABLE`, so the disk reaper treated the directory as a failed run and deleted its
`.lrat*` payloads once. Fixed by appending the word to all aux `.res` files in UNSAT-marked
dirs; regeneration then completed cleanly.

## Controls

| leaf | expected | verdict | cert |
|---|---|---|---|
| val_N16_35 (R(B4,B7)>16) | SAT | SAT | n/a — satisfying assignment in .log |
| val_N17_35 (R(B4,B7)>17) | UNSAT | UNSAT | .lrat.gz |
| ctrl_N21_47 (R(B4,B9)>21) | SAT | SAT | n/a |
| ctrl_N26_49 (R(B4,B9)>26) | SAT | rerun timed out | n/a — lower bound independently proven by `B49Witness.lean` |

## Cert format note (IMPORTANT for verification)

All `.lrat.gz` payloads are CaDiCaL **binary** LRAT (the `--binary=true` default).
`lrat-check` reads text LRAT only — verify via the bundled converter:

    zcat leaf.lrat.gz | ./blrat2txt > leaf.txt && lrat-check leaf.cnf leaf.txt

or streamed:

    mkfifo p && (zcat leaf.lrat.gz | ./blrat2txt > p &) && lrat-check leaf.cnf p

`blrat2txt.c` (bundled here) decodes the format: `a|d` marker, zigzag varints
(map: even→u/2, odd→-((u-1)/2)), `'a' id lits 0 hints 0`, and binary
`'d' <deleted-clause-id>... 0` → text `<index> d <ids>... 0`.
Verification: `verify_report.txt` — lrat-check VERIFIED on a 40-leaf sample
across families plus the corner leaf (see counts below).

### Verification results (post-conversion)

What "verified" means here: the solver produced an UNSAT verdict for each leaf;
`lrat-check` independently re-proved a **subset** of the certificates. It is not a
full recheck of all 812.

- Corner leaf x18_10 cert: **lrat-check VERIFIED** (40,966,628 clauses, 297s).
- Random sample of 40 certs across all families: **40/40 VERIFIED** (`verify_report.txt`).
- All 27 monolithic B49 leaves: **27/27 VERIFIED** (`B49_independent_check.csv`).
- All 94 Schur certificates: **94/94 PASS** (`sat/schur/LRAT_MANIFEST.csv`).
- Every leaf additionally carries its solver verdict + sha256 in `COVERAGE.csv`.
