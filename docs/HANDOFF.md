# HANDOFF — regeneration complete

State: ALL coverage leaves closed UNSAT (frontier exhausted; `open=0`).

The ~50 GB certificate archive lives on Zenodo:
`10.5281/zenodo.23510386` (main: all Ramsey certs, 88 files) and
`10.5281/zenodo.23516415` (part 2: Ahmed–Schaal certs). Each archive is split
into 600 MB `partNNpart` pieces — `cat name.tar.part* > name.tar && tar -xf name.tar`.

This bundle's `cert_pack/` tree mirrors `runs/` layout. Each leaf directory contains:

- `<leaf>.cnf` — DIMACS CNF (symmetry-broken Ramsey instance)
- `<leaf>.cube` — cube file (assumptions) when the leaf is a cube-split node
- `<leaf>.res` — solver verdict line(s); UNSAT leaves say `UNSATISFIABLE` or `verdict=UNSATISFIABLE`
- `<leaf>.log` — solver log
- `<leaf>.lrat.gz` — LRAT certificate (only on UNSAT leaves; controls carry none)

`COVERAGE.csv` rows: `leaf,family,verdict,cert_present,sha256`. `missing/nonfinal` rows at
assembly time were only `ctrl_N26_49` (SAT control, no cert expected; lower bound lives in Lean).

Families: b49 (B₄₉ degree cases), r47 (R₄₇ monolithic + split subtrees), origT (310 monolithic
d10 leaves + 0129/0040 subtree frontiers), f0129 (285 topmost UNSAT leaves of the leaf-0129
descent), f0040 (5 leaves), controls.

Regeneration recipe for a fresh VM is unchanged: `run_case.sh <case>` (cadical `--lrat`,
gzip on success), `gen_degfixN.py` for degree-pin descent, `assemble_certs.py` for the pack.
The reaper footgun — aux `.res` files must contain the word `UNSATISFIABLE` in solved dirs —
is documented in CERT_STATUS.md.
