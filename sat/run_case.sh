#!/bin/bash
# run_case.sh NAME N m n d lo hi [cubefile]
# Generates CNF, solves with cadical --lrat, records verdict.
set -u
cd ~/math_hunt
name=$1; N=$2; m=$3; n=$4; d=$5; lo=$6; hi=$7; cube=${8:-}
out=runs/$name
mkdir -p "$out"
[ -s "$out/$name.res" ] && exit 0
cnf=$out/$name.cnf; lrat=$out/$name.lrat; resf=$out/$name.res; log=$out/$name.log
./gen_bookrow "$N" "$m" "$n" "$d" "$lo" "$hi" ${cube:+$cube} > "$cnf" 2>"$log"
start=$(date +%s.%N)
timeout 3600 tools/cadical/build/cadical --lrat "$cnf" "$lrat" >> "$log" 2>&1
rc=$?
end=$(date +%s.%N)
verdict=$(grep -m1 "^s " "$log" | awk '{print $2}')
echo "$name N=$N m=$m n=$n d=$d lo=$lo hi=$hi cube=${cube:-none} verdict=${verdict:-TIMEOUT_rc$rc} secs=$(echo "$end-$start"|bc)" | tee "$resf"
[ "$verdict" = "UNSATISFIABLE" ] && gzip -9 -f "$lrat" 2>/dev/null
exit 0
