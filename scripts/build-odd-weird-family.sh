#!/bin/sh
# Build the C/GMP port of odd_weird_family.py. Usage: sh scripts/build-odd-weird-family.sh [OUT]
# The binary is not committed (default output /tmp/owf).
# This only builds and smoke-tests (K = 4); the comparison with Python is scripts/validate-owf.sh (mandatory).
set -e
OUT=${1:-/tmp/owf}
gcc -O2 -Wall -o "$OUT" "$(dirname "$0")/odd_weird_family.c" -lgmp
"$OUT" 4
