#!/usr/bin/env python3
"""Require exact clean Git dependency sources before running a rebuild."""
import argparse
import json
import subprocess
from pathlib import Path
from verify_package import check

parser = argparse.ArgumentParser()
parser.add_argument('workspace')
args = parser.parse_args()
workspace = Path(args.workspace)
check(workspace)
manifest = json.loads((workspace / 'lake-manifest.json').read_text())
for dependency in manifest['packages']:
    path = workspace / manifest['packagesDir'] / dependency['name']
    assert (path / '.git').exists(), f"Missing Git dependency: {dependency['name']}"
    revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    assert revision == dependency['rev'], f"Wrong revision: {dependency['name']}"
    status = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
    assert not status.strip(), f"Modified tracked sources: {dependency['name']}"
print('PASS: all nine dependency checkouts have the pinned revisions and clean tracked sources.')
