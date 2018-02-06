#!/usr/bin/env bash
set -eu -o pipefail

# This script applies basic general linting to a source file.
#
# Usage:
#   ./genera-lint.sh file

# Check that lines in the given file(s) are at most 80 bytes, including
# line breaks.

LINE_LENGTH_VIOLATIONS="$( \
  awk '{ if (length > 79) { print length, FILENAME, "@", FNR }}' "$1" \
)"

if ! test -z "$LINE_LENGTH_VIOLATIONS"; then
  echo "Error: $1 has lines which are longer than 80 bytes (including line"
  echo "       breaks)."
  echo "$LINE_LENGTH_VIOLATIONS"
  exit 1
fi

# Check for trailing whitespace.

if grep -E -n '[[:space:]]$$' "$1"; then
  echo "Error: $1 has trailing whitespace."
  exit 1
fi

# Check that there is a blank line at the end of the file.

if test "$(cat "$1" | wc -c)" -ne 0; then
  if test "$(tail -c 1 "$1" | wc -l)" -ne 1; then
    echo "Error: $1 is not terminated with a blank line."
    exit 1
  fi

  if test "$(tail -c 2 "$1" | wc -l)" -ne 1; then
    echo "Error: $1 is terminated with multiple blank lines."
    exit 1
  fi
fi

# Check that there are no tabs, with more permissive behavior if the file is
# called `Makefile`.

if test "$(basename "$1")" = Makefile; then
  if grep -E -n $'.\t' "$1"; then
    echo "Error: $1 has a tab in a non-required position."
    exit 1
  fi
else
  if grep -E -n $'\t' "$1"; then
    echo "Error: $1 has a tab."
    exit 1
  fi
fi
