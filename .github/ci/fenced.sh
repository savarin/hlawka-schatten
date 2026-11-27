#!/usr/bin/env bash
# Run a command inside the memory fence made by prepare-runner.sh, logging memory use every two minutes.
set -euo pipefail
if [ -d /sys/fs/cgroup/lean-build ]; then
  echo $$ | sudo tee /sys/fs/cgroup/lean-build/cgroup.procs > /dev/null || echo "::warning::not fenced"
fi
( while sleep 120; do
    free -m | awk 'NR==2 {r=$3"/"$2} NR==3 {s=$3} END {print "[memory] RAM used " r " MB, swap used " s " MB"}'
  done ) &
logger=$!
trap 'kill "$logger" 2> /dev/null || true' EXIT
"$@"
