#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${COMPARATOR:?Set COMPARATOR}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT}"
export COMPARATOR_LANDRUN="${FAKE_LANDRUN:-landrun}"
tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/hlawka-negative-XXXXXX")
cp ExistenceChallenge.lean "$tmpdir/ExistenceChallenge.lean"
trap 'cp "$tmpdir/ExistenceChallenge.lean" ExistenceChallenge.lean; rm -rf "$tmpdir"' EXIT
sed 's/0 < m ∧ m ≤ M ∧/0 < m ∧ M < m ∧/' ExistenceChallenge.lean > "$tmpdir/mutated.lean"
cp "$tmpdir/mutated.lean" ExistenceChallenge.lean
lake env lean ExistenceChallenge.lean >/dev/null
output=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" comparator-existence.json 2>&1 || true)
if [ -z "$output" ]; then
  echo "FAIL: comparator produced no output (may not have run)"
  exit 1
fi
if echo "$output" | grep -qi "Your solution is okay"; then
  echo "FAIL: comparator accepted strengthened inconsistent boundary"
  exit 1
fi
if ! echo "$output" | grep -qiE "(mismatch|error|fail|reject|differ)"; then
  echo "WARN: comparator output does not contain an expected rejection keyword"
  echo "Output was: $output"
  exit 1
fi
echo "PASS: comparator rejected strengthened boundary"
