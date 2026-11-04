#!/bin/sh
# Reproduce the seven named build roots in a prepared disposable workspace.
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: scripts/build.sh prepared-workspace' >&2
  exit 2
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$script_dir/verify_dependencies.py" "$1"
cd -- "$1"
mkdir -p results
lake env lean --version > results/toolchain.txt 2>&1
date -u '+%Y-%m-%dT%H:%M:%SZ' > results/build.started.txt
echo 'lake build UAudit PaperAudit UCAudit UCIndexedAudit UCReturn002Audit UCTargetScope UCScopeAudit' > results/build.command.txt
set +e
lake build UAudit PaperAudit UCAudit UCIndexedAudit UCReturn002Audit UCTargetScope UCScopeAudit > results/build.log 2>&1
result=$?
set -e
echo "$result" > results/build.exit.txt
date -u '+%Y-%m-%dT%H:%M:%SZ' > results/build.finished.txt
cat results/build.log
exit "$result"
