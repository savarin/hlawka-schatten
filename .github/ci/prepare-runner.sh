#!/usr/bin/env bash
# Make room on GitHub's standard runner for the certificate files: free about 20 GB of preinstalled
# tools and add 12 GB of swap (the vertex-corner files need more than the runner's memory).
set -euo pipefail
sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /opt/hostedtoolcache/CodeQL /usr/local/share/boost
sudo docker image prune --all --force > /dev/null || true
sudo fallocate -l 12G /mnt/swapfile
sudo chmod 600 /mnt/swapfile
sudo mkswap /mnt/swapfile > /dev/null
sudo swapon /mnt/swapfile
df -h /
free -h
# A memory fence for the build (see fenced.sh): processes started through fenced.sh are kept below the
# machine's memory minus 1.5 GB and spill into swap beyond it, so the runner's own agent always has memory.
# (The first run of this workflow lost its runner when the build used all of the memory.)
total_kb=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)
echo +memory | sudo tee /sys/fs/cgroup/cgroup.subtree_control > /dev/null 2>&1 || true
if sudo mkdir -p /sys/fs/cgroup/lean-build 2> /dev/null &&
   echo "$(( (total_kb - 1536 * 1024) * 1024 ))" | sudo tee /sys/fs/cgroup/lean-build/memory.high > /dev/null; then
  echo "memory fence: $(( total_kb / 1024 - 1536 )) MB for the build"
else
  echo "::warning::could not create the memory fence; the build runs without it"
fi
