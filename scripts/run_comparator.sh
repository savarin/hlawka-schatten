#!/usr/bin/env bash
set -euo pipefail

readonly PALOMAR_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly PALOMAR_REPO_ROOT="$(cd "$PALOMAR_SCRIPT_DIR/.." && pwd)"

if (( $# > 1 )); then
  echo "Usage: $0 [comparator-config.json]" >&2
  exit 2
fi

cd "$PALOMAR_REPO_ROOT"
config=${1:-comparator-existence.json}
if [[ -z "${COMPARATOR:-}" && -z "${LEAN4EXPORT:-}" ]]; then
  exec lake comparator --config "$config"
fi

: "${COMPARATOR:?Set COMPARATOR and LEAN4EXPORT together to use a standalone comparator.}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to an exporter built for the selected toolchain.}"
export COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT"
if [[ -n "${FAKE_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$FAKE_LANDRUN"
fi
exec lake env "$COMPARATOR" "$config"
