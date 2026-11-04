#!/usr/bin/env python3
"""Make a new rebuild directory without changing the immutable release packet."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path
from verify_package import PACKET, SCOPE_EXTENSION, check

parser = argparse.ArgumentParser()
parser.add_argument('destination', help='A directory that does not already exist')
args = parser.parse_args()
check()
destination = Path(args.destination)
destination.mkdir(parents=True, exist_ok=False)
sources = list(PACKET.glob('*.lean')) + list((PACKET / 'DegreeProfilesReview').glob('*.lean'))
for source in sources:
    target = destination / source.relative_to(PACKET)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
    shutil.copyfile(PACKET / name, destination / name)
original = (PACKET / 'lakefile.toml').read_text()
(destination / 'lakefile.toml').write_text(original + SCOPE_EXTENSION)
note = {'source_modules': 199, 'proof_source_modifications': 0,
        'lakefile_base_sha256': hashlib.sha256((PACKET / 'lakefile.toml').read_bytes()).hexdigest(),
        'lakefile_extension': SCOPE_EXTENSION,
        'reason': 'Register the two preserved Independent_005 scope adapters; the original Return_002 lakefile remains byte-identical in the release packet.'}
(destination / 'workspace_generation.json').write_text(json.dumps(note, indent=2) + '\n')
check(destination)
print('Prepared 199 unchanged source modules and the exact pinned configuration with two explicit scope-library stanzas.')
print('Dependencies and binaries are not copied or downloaded.')
