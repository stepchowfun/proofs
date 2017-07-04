#!/usr/bin/env bash
set -eu -o pipefail

# This script checks that lines in the given file(s) are at most 80 bytes,
# including newline characters. It prints violations to standard output.

# Usage:
#   ./check-line-lengths.sh file1 file2 ...

LINE_LENGTH_VIOLATIONS="$( \
  awk '{ if (length > 79) { print length, FILENAME, "@", FNR }}' "$@" \
)"

if ! test -z "$LINE_LENGTH_VIOLATIONS"; then
  echo "$LINE_LENGTH_VIOLATIONS"
  exit 1
fi
