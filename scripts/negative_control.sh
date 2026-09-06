#!/bin/bash
# Negative control: confirm the comparator rejects a mutated theorem statement.
#
# Mutates the Challenge by strengthening m ≤ M to M < m, making the
# boundary inconsistent. The Solution still proves the original (unmutated)
# bound, so the mutated Challenge and the Solution should no longer match.
# Requires a passing baseline first.
set -euo pipefail
cd "$(dirname "$0")/.."

: "${COMPARATOR:?Set COMPARATOR to the comparator binary path}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to a v4.33.0-compatible lean4export binary}"

if [[ -n "${FAKE_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$FAKE_LANDRUN"
fi

CONFIG="comparator-existence.json"
CHALLENGE="ExistenceChallenge.lean"
THEOREM="PalomarHlawkaSchatten.dimension_independent_hlawka_constant_for_schatten_norms"

echo "=== Negative control ==="

# Step 1: Verify baseline passes
echo "[1/3] Verifying baseline ..."
BASELINE=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
if ! echo "$BASELINE" | grep -qi "Your solution is okay"; then
  echo "FAIL: baseline comparator run does not pass — negative control is unreliable"
  echo "$BASELINE" | tail -5
  exit 1
fi
echo "  Baseline passes"

# Step 2: Build a mutated Challenge
echo "[2/3] Building mutated Challenge ..."
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/hlawka-neg-ctrl-XXXXXX")

cp "$CHALLENGE" "$WORKDIR/Challenge.lean.orig"
trap 'cp "$WORKDIR/Challenge.lean.orig" "$CHALLENGE"; rm -rf "$WORKDIR"' EXIT

sed 's/0 < m ∧ m ≤ M ∧/0 < m ∧ M < m ∧/' "$CHALLENGE" > "$WORKDIR/Challenge.lean"
cp "$WORKDIR/Challenge.lean" "$CHALLENGE"

echo "  Mutated: strengthened m ≤ M to M < m"
if ! lake build ExistenceChallenge 2>&1 | tail -3; then
  echo "  (mutated build failed — trap restores $CHALLENGE)"
  exit 1
fi

# Step 3: Run comparator on mutated Challenge
echo "[3/3] Running comparator on mutated Challenge ..."
OUTPUT=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
echo "$OUTPUT" | tail -5

echo "  Restoring original and rebuilding ..."

if echo "$OUTPUT" | grep -q "^FAIL $THEOREM"; then
  echo "PASS: comparator correctly rejected the mutated Challenge (statement mismatch)"
  exit 0
else
  echo "FAIL: comparator did not reject $THEOREM as expected"
  exit 1
fi
