#!/usr/bin/env bash
# Require a passing baseline, then reject a specific strengthened statement.
# The original source and its compiled artifact are restored on every exit.
set -euo pipefail
cd "$(dirname "$0")/.."

if (( $# > 1 )); then
  echo "Usage: $0 [comparator-config.json]" >&2
  exit 2
fi

: "${COMPARATOR:?Set COMPARATOR to the comparator binary path}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to a lean4export built for the toolchain in lean-toolchain.}"

PALOMAR_CONFIG="${1:-comparator-existence.json}"
read -r PALOMAR_MODULE PALOMAR_THEOREM < <(
  python3 - "$PALOMAR_CONFIG" <<'CONFIG_PY'
import json
import sys
from pathlib import Path
config = json.loads(Path(sys.argv[1]).read_text())
print(config["challenge_module"], config["theorem_names"][0])
CONFIG_PY
)
case "$PALOMAR_MODULE" in
  ExistenceChallenge|ConstructionDiagonalChallenge) ;;
  *) echo "Unsupported negative-control module: $PALOMAR_MODULE" >&2; exit 2 ;;
esac
PALOMAR_CHALLENGE="$PALOMAR_MODULE.lean"
PALOMAR_CONTROL_DIR=$(mktemp -d "${TMPDIR:-/tmp}/hlawka-neg-ctrl-XXXXXX")
cp "$PALOMAR_CHALLENGE" "$PALOMAR_CONTROL_DIR/original.lean"

restore_boundary() {
  local result=$?
  trap - EXIT
  cp "$PALOMAR_CONTROL_DIR/original.lean" "$PALOMAR_CHALLENGE"
  echo "Restoring original Challenge and rebuilding ..."
  if ! lake build "$PALOMAR_MODULE" > "$PALOMAR_CONTROL_DIR/restore.log" 2>&1; then
    cat "$PALOMAR_CONTROL_DIR/restore.log"
    result=1
  fi
  rm -rf "$PALOMAR_CONTROL_DIR"
  exit "$result"
}
trap restore_boundary EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

echo "[1/3] Verifying baseline: $PALOMAR_CONFIG"
if ! bash scripts/run_comparator.sh "$PALOMAR_CONFIG" > "$PALOMAR_CONTROL_DIR/baseline.log" 2>&1; then
  cat "$PALOMAR_CONTROL_DIR/baseline.log"
  echo "FAIL: baseline comparator run failed"
  exit 1
fi
if ! grep -qi "Your solution is okay" "$PALOMAR_CONTROL_DIR/baseline.log"; then
  cat "$PALOMAR_CONTROL_DIR/baseline.log"
  echo "FAIL: baseline did not accept the solution"
  exit 1
fi
echo "      Baseline accepted"

echo "[2/3] Strengthening the selected Challenge theorem ..."
python3 - "$PALOMAR_CHALLENGE" "$PALOMAR_MODULE" <<'MUTATE_PY'
import sys
from pathlib import Path
path = Path(sys.argv[1])
text = path.read_text()
if sys.argv[2] == "ExistenceChallenge":
    before = "0 < m ∧ m ≤ M ∧"
    after = "0 < m ∧ M < m ∧"
else:
    before = "∀ p : ℝ, 256 ≤ p → ∀ n : ℕ,\n      HasHlawkaConstant"
    after = "∀ p : ℝ, 255 ≤ p → ∀ n : ℕ,\n      HasHlawkaConstant"
if text.count(before) != 1:
    raise SystemExit("Expected exactly one mutation target")
path.write_text(text.replace(before, after))
MUTATE_PY
lake build "$PALOMAR_MODULE" > "$PALOMAR_CONTROL_DIR/mutated-build.log" 2>&1 || {
  cat "$PALOMAR_CONTROL_DIR/mutated-build.log"
  exit 1
}

echo "[3/3] Checking rejection of $PALOMAR_THEOREM ..."
PALOMAR_MUTATED_STATUS=0
bash scripts/run_comparator.sh "$PALOMAR_CONFIG" > "$PALOMAR_CONTROL_DIR/mutated.log" 2>&1 || PALOMAR_MUTATED_STATUS=$?
tail -n 8 "$PALOMAR_CONTROL_DIR/mutated.log"
if (( PALOMAR_MUTATED_STATUS == 0 )); then
  echo "FAIL: comparator accepted the strengthened statement"
  exit 1
fi
if grep -Fq "Challenge and solution theorem statement do not match: '$PALOMAR_THEOREM'" \
    "$PALOMAR_CONTROL_DIR/mutated.log" ||
    grep -Fxq "FAIL $PALOMAR_THEOREM" "$PALOMAR_CONTROL_DIR/mutated.log"; then
  echo "PASS: comparator rejected the strengthened statement"
else
  echo "FAIL: no statement-mismatch rejection for the selected theorem"
  exit 1
fi
