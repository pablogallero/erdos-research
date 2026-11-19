#!/bin/sh
# Validate the C/GMP port (odd_weird_family.c) against the Python reference (odd_weird_family.py).
# MANDATORY after any change to either file, before using the C binary on the omega = 6 checkpoint.
#
# Usage: sh scripts/validate-owf.sh            (about 1-2 min: K = 4 and K = 5, all C paths, cross-resume)
#
# Checks, for K = 4 and K = 5, all in a fresh temporary directory (the real checkpoint is never touched):
#   1. Python and C print the same result (True/False), the same counters (n, fam, qchk, star, skip)
#      and the same failure list; the C run is repeated with PSLOW=1 (mpz only) and PSLOW=2 (256-bit).
#   2. The checkpoints written by Python and by C are byte-identical.
#   3. Cross-resume (K = 5 only): a Python run cut by `timeout` is finished by C, and a C run cut by
#      `timeout` is finished by Python; both end True with the same key set as a full run.
# Exits non-zero at the first mismatch.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
gcc -O2 -Wall -o "$TMP/owf" "$HERE/odd_weird_family.c" -lgmp

# Result line without the trailing time (Python) / nfail field (C), plus the failure lines.
norm() { sed -e "s/, 'nfail': [0-9]*//" -e 's/} [0-9.]*$/}/' -e '/^progress /d' "$1"; }

fail() { echo "FAIL: $*"; exit 1; }

for K in 4 5; do
  ( cd "$TMP" && python3 -I "$HERE/odd_weird_family.py" $K "$TMP/py$K.ck" > "$TMP/py$K.out" 2>/dev/null )
  norm "$TMP/py$K.out" > "$TMP/py$K.n"
  echo "K=$K python: $(head -1 "$TMP/py$K.n")"
  for MODE in auto 1 2; do
    rm -f "$TMP/c$K.ck"
    if [ $MODE = auto ]; then "$TMP/owf" $K "$TMP/c$K.ck" > "$TMP/c$K.out" 2>/dev/null
    else PSLOW=$MODE "$TMP/owf" $K "$TMP/c$K.ck" > "$TMP/c$K.out" 2>/dev/null; fi
    norm "$TMP/c$K.out" > "$TMP/c$K.n"
    cmp -s "$TMP/py$K.n" "$TMP/c$K.n" || { diff "$TMP/py$K.n" "$TMP/c$K.n"; fail "K=$K PSLOW=$MODE counters differ"; }
    cmp -s "$TMP/py$K.ck" "$TMP/c$K.ck" || fail "K=$K PSLOW=$MODE checkpoint differs"
    echo "K=$K C (PSLOW=$MODE): same counters, same failures, byte-identical checkpoint ($(wc -l < "$TMP/c$K.ck") lines)"
  done
done

sort -u "$TMP/py5.ck" > "$TMP/full5.keys"
# Python cut, C finishes.
( cd "$TMP" && timeout 10 python3 -I "$HERE/odd_weird_family.py" 5 "$TMP/x1.ck" > /dev/null 2>&1 ) || true
N1=$(wc -l < "$TMP/x1.ck")
"$TMP/owf" 5 "$TMP/x1.ck" 2>/dev/null | grep -q '^5 True' || fail "Python->C resume did not end True"
sort -u "$TMP/x1.ck" | cmp -s - "$TMP/full5.keys" || fail "Python->C resume: key set differs"
echo "cross-resume Python->C: cut at $N1 lines, C finished True, same key set"
# C cut, Python finishes.
timeout 1 "$TMP/owf" 5 "$TMP/x2.ck" > /dev/null 2>&1 || true
N2=$(wc -l < "$TMP/x2.ck")
( cd "$TMP" && python3 -I "$HERE/odd_weird_family.py" 5 "$TMP/x2.ck" 2>/dev/null ) | grep -q '^5 True' || fail "C->Python resume did not end True"
sort -u "$TMP/x2.ck" | cmp -s - "$TMP/full5.keys" || fail "C->Python resume: key set differs"
echo "cross-resume C->Python: cut at $N2 lines, Python finished True, same key set"
echo "ALL OK"
