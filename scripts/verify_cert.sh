#!/usr/bin/env bash
# verify_cert.sh <leaf.cnf> <leaf.lrat.gz>
# Verifies a CaDiCaL binary-LRAT certificate with drat-trim's lrat-check,
# via the bundled binary->text converter (sat/blrat2txt).
set -euo pipefail
CNF="$1"; LRAT_GZ="$2"
DIR="$(cd "$(dirname "$0")/.." && pwd)"
CONV="$DIR/sat/blrat2txt"
[ -x "$CONV" ] || gcc -O2 -o "$CONV" "$DIR/sat/blrat2txt.c"
FIFO="$(mktemp -u)"
mkfifo "$FIFO"
trap 'rm -f "$FIFO"' EXIT
( zcat "$LRAT_GZ" | "$CONV" > "$FIFO" ) &
lrat-check "$CNF" "$FIFO"
