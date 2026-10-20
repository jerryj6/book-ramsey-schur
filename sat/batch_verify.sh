mkfifo /tmp/pv 2>/dev/null
: > verify_report.txt
for g in $(find cert_pack -name '*.lrat.gz' | sort -R | head -40); do
  cnf="${g%.lrat.gz}.cnf"
  ( zcat "$g" | ./blrat2txt > /tmp/pv ) &
  res=$(timeout 300 tools/drat-trim/lrat-check "$cnf" /tmp/pv 2>/dev/null | grep -E 'VERIFIED' | head -1)
  wait
  echo "$res ${g#cert_pack/}" >> verify_report.txt
done
