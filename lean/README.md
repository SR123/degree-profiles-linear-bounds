# Uniform consequence degree profiles: formal source packet

Coordinated release revision, 13 October 2026. This packet contains 199 preserved Lean modules: the September 27 baseline (186), Claude Return 001 (5), Claude Return 002 (6), and the final Independent 005 scope adapters (2). Every proof source is copied byte for byte. The exact Return 002 `lakefile.toml`, `lean-toolchain`, and `lake-manifest.json` are included. No new mathematical declaration, axiom, proof repair, Lean build, or kernel replay was made while preparing this packet.

The [endpoint table](ENDPOINTS.tsv) identifies the formal headline results. Full returned theorem types are in `evidence/producer_release_audit_2026-10-13/extracted/*.out`. Read [SCOPE.md](SCOPE.md) before interpreting a theorem name or a clean axiom report. The manuscript's injection degree-at-most-`n+1` certificate, its optimality deduction, and several size and teaching deductions remain written mathematics.

## Verify the download without installing Lean

From the extracted packet directory:

```sh
python3 -B scripts/verify_package.py
python3 -B scripts/check_audit_outputs.py evidence/producer_release_audit_2026-10-13/extracted
```

The first command checks every distributed file listed in `SHA256SUMS.txt`, exact source/configuration hashes, public evidence derivative hashes and redaction provenance, absence of private machine paths in public files/ZIP members, all 199 local module paths, and absence of local import cycles. External Lean and Mathlib imports require the pinned dependencies; this static check does not elaborate Lean. The second checks the six returned audit outputs: 164 targeted standard-foundation-only axiom reports and 102 exact transitive-dependency results. It reads preserved evidence and does not execute Lean. Successful results from those commands must not be described as a new independent proof replay.

## Rebuild in a new directory

Prerequisites are Python 3, Git, and an already installed Lean/Lake toolchain `leanprover/lean4:v4.26.0`. The recorded Lean commit is `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`. This packet contains no dependency checkouts, cached binaries, project `.olean` files, or checker executable. No network installation or dependency download was performed during release preparation.

Create a disposable workspace; its destination must not already exist:

```sh
python3 -B scripts/prepare_workspace.py ../lean-rebuild
```

This copies all proof sources and pins. It appends exactly two library declarations for `UCTargetScope` and `UCScopeAudit` to the scratch lakefile. The appended text and original lakefile hash are recorded in `workspace_generation.json`; the release lakefile remains the exact Return 002 file. No proof source changes. This reproduces the release audit's explicit scope-library registration.

Populate `../lean-rebuild/.lake/packages` with clean Git checkouts at the nine exact commits in `lake-manifest.json` and [provenance/pins.json](provenance/pins.json). Existing verified checkouts may be copied into this disposable tree. Alternatively, the following optional provisioning command fetches those exact upstream source revisions; it performs network access only when the reader chooses to run it:

```sh
cd ../lean-rebuild
python3 - <<'PY'
import json
import subprocess
from pathlib import Path
manifest = json.loads(Path('lake-manifest.json').read_text())
for dep in manifest['packages']:
    target = Path(manifest['packagesDir']) / dep['name']
    target.mkdir(parents=True, exist_ok=False)
    subprocess.run(['git', 'init', str(target)], check=True)
    subprocess.run(['git', '-C', str(target), 'remote', 'add', 'origin', dep['url']], check=True)
    subprocess.run(['git', '-C', str(target), 'fetch', '--depth', '1', 'origin', dep['rev']], check=True)
    subprocess.run(['git', '-C', str(target), 'checkout', '--detach', dep['rev']], check=True)
PY
cd -
python3 -B scripts/verify_dependencies.py ../lean-rebuild
```

Use the supplied manifest throughout. If external dependency binaries are already available for those exact sources, they may be reused and must be reported as such. The baseline producer recipe also permits `lake exe cache get` in the scratch workspace to obtain Mathlib's corresponding dependency cache; that optional command accesses the network. For a source-only dependency build, leave those dependency binaries absent. In both cases all project modules are compiled from the packaged sources.

Run the complete named build and preserve full audit output:

```sh
./scripts/build.sh ../lean-rebuild
./scripts/audit.sh ../lean-rebuild
```

The build command is:

```sh
lake build UAudit PaperAudit UCAudit UCIndexedAudit UCReturn002Audit UCTargetScope UCScopeAudit
```

The audit script separately runs `lake env lean MODULE.lean` on `UAudit`, `PaperAudit`, `UCAudit`, `UCIndexedAudit`, `UCReturn002Audit`, and `UCScopeAudit`. Their unchanged directives print exact definitions/theorem types, selected `#print axioms` reports, and the `#uses` transitive-dependency checks. Full logs, commands, UTC times, and exit codes go into the scratch workspace's `results/` directory. The final audit comparison checks all expected names and Boolean dependency results and rejects any reported axiom outside `propext`, `Classical.choice`, and `Quot.sound`. It does not compare presentation-dependent closure sizes.

## Optional checker replay

Use an existing Lean-4.26.0-compatible `lean4checker` binary. The October 13 audit records revision prefix `6744eac6`; the returned files do not supply the full checker commit or binary. This is an explicit provenance limitation, so the prefix is not presented as a full reproducibility pin. Optional replay requires a manual choice of checker and its actual full 40-character source Git revision. Obtain that revision with `git rev-parse HEAD` in the checker source checkout; do not extend the recorded prefix by guessing. The script requires the explicit revision, hashes the supplied binary and records the revision, actual command, times, output, and exit code. The revision identifies the new run; it is not evidence of the producer's unreturned full pin.

```sh
LEAN4CHECKER=/path/to/existing/lean4checker LEAN4CHECKER_REVISION=ACTUAL_FULL_GIT_SHA ./scripts/checker_replay.sh ../lean-rebuild non-fresh
LEAN4CHECKER=/path/to/existing/lean4checker LEAN4CHECKER_REVISION=ACTUAL_FULL_GIT_SHA ./scripts/checker_replay.sh ../lean-rebuild fresh
```

The first mode repeats the 28 listed module checks. The second explicitly requests the two expensive fresh import-closure replays, `UCIndexedClassification` and `UCFreshVariable`. A fresh replay checks the selected root's complete imported environment, including external dependencies; it does not cover all 199 packet modules. In particular, the separate scope adapters are outside those two closures. A compilation or a non-fresh checker run must retain its own evidence label.

## Evidence and release status

[EVIDENCE.md](EVIDENCE.md) distinguishes the original producer builds/replays, the recorded October 5 independent source builds, the October 13 Claude audit return, and this packet's static preparation checks. It links the unchanged independent correction review, which addresses the producer report's period, AI-disclosure, Harman-attribution and browser-evidence overstatements without a new Lean run. Public execution evidence copies are explicitly labelled derivatives: historical machine roots are replaced by declared placeholders, while types, axiom reports, exit statuses and all other content are preserved. [The redaction manifest](provenance/evidence_redactions.json) records each original/public hash, unchanged original's archive-relative location and mapping. The unchanged unsanitised execution originals remain in the existing project archives and are not bundled here. Authored instructions and manifests use relative archive paths. Exact verbatim claims apply to proof sources, pinned configuration and the explicitly identified independent correction review.

[RELEASE_POLICY.md](RELEASE_POLICY.md) records the remaining licence and hosting metadata choices. This is a curated local release candidate. No new public repository, stable public URL, journal submission, or redistribution licence is claimed.
