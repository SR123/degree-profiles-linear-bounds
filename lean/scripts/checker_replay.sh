#!/bin/sh
# Explicitly requested optional replay using an already installed checker binary.
set -eu
if [ "$#" -ne 2 ]; then
  echo 'Usage: LEAN4CHECKER=existing-binary LEAN4CHECKER_REVISION=actual-full-Git-SHA scripts/checker_replay.sh prepared-workspace non-fresh|fresh' >&2
  exit 2
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 -B "$script_dir/verify_dependencies.py" "$1"
checker=${LEAN4CHECKER:?Set LEAN4CHECKER to an existing Lean-4.26.0-compatible binary}
checker_revision=${LEAN4CHECKER_REVISION:?Supply the actual full checker source Git revision before requesting an optional replay}
python3 -c 'import re,sys; assert re.fullmatch("[0-9a-f]{40}",sys.argv[1]), "Checker revision must be its actual full 40-character Git SHA"' "$checker_revision"
test -x "$checker"
case "$2" in
  fresh) modules='UCIndexedClassification UCFreshVariable'; flag='--fresh' ;;
  non-fresh) modules='UCTarget UCTransfer UCClassification UCAudit UCIndexedTarget UCIndexedTransfer UCIndexedClassification UCFreshVariable UCIndexedAudit UCReturn002Audit LinearFinal FinalLinear TopPowerExactness TopPowerProjection RForce CompChain CompDetect CompFinal C017TypeAgreement RectangularDesign RectangularPC UUndecidable UPairs UPCDirect UWitEta PTransfer PaperAudit UAudit'; flag='' ;;
  *) echo 'Mode must be non-fresh or fresh' >&2; exit 2 ;;
esac
# Resolve the supplied binary before changing directory, and record its real hash.
checker=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$checker")
cd -- "$1"
mkdir -p "results/checker-$2"
echo "$checker_revision" > "results/checker-$2/source-revision.txt"
python3 -c 'from pathlib import Path; import hashlib,sys; p=Path(sys.argv[1]); print(hashlib.sha256(p.read_bytes()).hexdigest())' "$checker" > "results/checker-$2/binary.sha256.txt"
for module in $modules; do
  log="results/checker-$2/$module.log"
  printf 'command: lake env %s %s %s\n' "$checker" "$flag" "$module" > "$log"
  date -u '+start %Y-%m-%dT%H:%M:%SZ' >> "$log"
  set +e
  if [ -n "$flag" ]; then
    lake env "$checker" "$flag" "$module" >> "$log" 2>&1
  else
    lake env "$checker" "$module" >> "$log" 2>&1
  fi
  result=$?
  set -e
  printf 'exit %s\n' "$result" >> "$log"
  date -u '+finish %Y-%m-%dT%H:%M:%SZ' >> "$log"
  cat "$log"
  if [ "$result" -ne 0 ]; then exit "$result"; fi
done
