#!/bin/sh
# Preserve complete types, axioms and dependency checks for all six audit roots.
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: scripts/audit.sh prepared-workspace' >&2
  exit 2
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$script_dir/verify_dependencies.py" "$1"
cd -- "$1"
mkdir -p results/audits
for module in UAudit PaperAudit UCAudit UCIndexedAudit UCReturn002Audit UCScopeAudit; do
  echo "lake env lean $module.lean" > "results/audits/$module.command.txt"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "results/audits/$module.started.txt"
  set +e
  lake env lean "$module.lean" > "results/audits/$module.out" 2>&1
  result=$?
  set -e
  echo "$result" > "results/audits/$module.exit.txt"
  date -u '+%Y-%m-%dT%H:%M:%SZ' > "results/audits/$module.finished.txt"
  if [ "$result" -ne 0 ]; then
    cat "results/audits/$module.out"
    exit "$result"
  fi
done
python3 -B "$script_dir/check_audit_outputs.py" results/audits
