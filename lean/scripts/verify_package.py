#!/usr/bin/env python3
"""Check immutable packet bytes and local imports; optionally a prepared workspace."""
import argparse
import hashlib
import json
import re
import zipfile
from pathlib import Path

PACKET = Path(__file__).resolve().parent.parent
SCOPE_EXTENSION = '\n[[lean_lib]]\nname = "UCTargetScope"\n\n[[lean_lib]]\nname = "UCScopeAudit"\n'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stripped(text):
    """Remove nested Lean comments and strings before reading header imports."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            stop = text.find('\n', i)
            i = len(text) if stop < 0 else stop
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append('\n' if text[i] == '\n' else ' ')
                    i += 1
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)


def check(workspace=None):
    checksums = PACKET / 'SHA256SUMS.txt'
    assert checksums.is_file(), 'Missing packet checksum manifest'
    checked, listed = 0, set()
    for line in checksums.read_text().splitlines():
        digest, name = line.split('  ', 1)
        relative = Path(name)
        assert not relative.is_absolute() and '..' not in relative.parts
        assert name not in listed, f'Duplicate checksum entry: {name}'
        listed.add(name)
        assert sha(PACKET / relative) == digest, f'Checksum mismatch: {name}'
        checked += 1
    excluded = {'.lake', 'results', '__pycache__', '.git'}
    actual = {p.relative_to(PACKET).as_posix() for p in PACKET.rglob('*')
              if p.is_file() and not (set(p.relative_to(PACKET).parts) & excluded)
              and p.name != 'SHA256SUMS.txt' and p.suffix != '.pyc'}
    assert actual == listed, f'Checksum coverage differs: missing={sorted(actual-listed)}, absent={sorted(listed-actual)}'
    origins = json.loads((PACKET / 'provenance/source_origins.json').read_text())
    for entry in origins['entries']:
        assert sha(PACKET / entry['path']) == entry['sha256'], entry['path']
        assert entry['public_sha256'] == entry['sha256'], entry['path']
        if entry['verbatim']:
            assert entry['original_sha256'] == entry['public_sha256'], entry['path']
            assert (entry['path'].endswith('.lean') or entry['path'] in {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
                    or entry['processing'] == 'verbatim_independent_release_review')
    redactions = json.loads((PACKET / 'provenance/evidence_redactions.json').read_text())
    by_path = {entry['path']: entry for entry in origins['entries']}
    for record in redactions['evidence_records']:
        entry = by_path[record['public_path']]
        assert not entry['verbatim']
        assert record['original_sha256'] == entry['original_sha256']
        assert record['public_sha256'] == entry['public_sha256']
    review = redactions['unchanged_independent_correction_review']
    review_entry = by_path[review['public_path']]
    assert review_entry['verbatim'] and review_entry['processing'] == 'verbatim_independent_release_review'
    assert review['original_sha256'] == review['public_sha256'] == review_entry['sha256']
    private_path = re.compile(rb'/(?:Users|home)/[^/\s"\)]+|/(?:private/)?tmp/[^/\s"\)]+')
    for relative in listed:
        path = PACKET / relative
        if path.suffix == '.zip':
            with zipfile.ZipFile(path) as archive:
                for member in archive.namelist():
                    contents = archive.read(member)
                    assert not private_path.search(contents), f'Private path in public ZIP member: {member}'
                    extracted = path.parent / 'extracted' / member
                    assert extracted.read_bytes() == contents, f'ZIP/extracted derivative differs: {member}'
        else:
            assert not private_path.search(path.read_bytes()), f'Private machine path in public file: {relative}'
    sources = list(PACKET.glob('*.lean')) + list((PACKET / 'DegreeProfilesReview').glob('*.lean'))
    modules = {p.relative_to(PACKET).with_suffix('').as_posix().replace('/', '.'): p for p in sources}
    assert len(modules) == 199
    graph, external = {}, set()
    for module, path in modules.items():
        imports = []
        for line in stripped(path.read_text()).splitlines():
            if line.strip().startswith('import '):
                imports.extend(line.strip()[7:].split())
        graph[module] = []
        for name in imports:
            if name in modules:
                graph[module].append(name)
            else:
                assert name.split('.')[0] in {'Mathlib', 'Lean'}, f'Unresolved project import: {module}: {name}'
                external.add(name)
    active, visited = set(), set()

    def visit(module):
        assert module not in active, f'Local import cycle: {module}'
        if module in visited:
            return
        active.add(module)
        for dependency in graph[module]:
            visit(dependency)
        active.remove(module)
        visited.add(module)

    for module in graph:
        visit(module)
    configs = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']
    if workspace:
        workspace = Path(workspace)
        assert workspace.is_dir(), 'Missing prepared workspace'
        for path in sources:
            relative = path.relative_to(PACKET)
            assert (workspace / relative).read_bytes() == path.read_bytes(), f'Workspace source differs: {relative}'
        for name in configs[1:]:
            assert (workspace / name).read_bytes() == (PACKET / name).read_bytes(), name
        expected = (PACKET / 'lakefile.toml').read_text() + SCOPE_EXTENSION
        assert (workspace / 'lakefile.toml').read_text() == expected, 'Unexpected workspace lakefile'
    return {'status': 'PASS', 'packet_files_hashed': checked, 'provenance_entries': len(origins['entries']),
            'verbatim_source_configuration_entries': sum(entry['processing'] == 'verbatim_proof_source_or_pinned_configuration' for entry in origins['entries']),
            'verbatim_independent_correction_reviews': sum(entry['processing'] == 'verbatim_independent_release_review' for entry in origins['entries']),
            'public_evidence_derivative_entries': len(redactions['evidence_records']),
            'public_private_machine_paths': 0, 'redacted_zip_members_match_extracted_files': True,
            'lean_modules': len(modules), 'local_imports_resolve': True, 'local_import_cycles': 0,
            'external_imports': sorted(external), 'external_import_note': 'Paths in Lean/Mathlib are delegated to the pinned dependencies; this is a static package check, not Lean elaboration.',
            'prepared_workspace_checked': bool(workspace), 'new_lean_execution': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace')
    parser.add_argument('--json', action='store_true')
    args = parser.parse_args()
    report = check(args.workspace)
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"PASS: {report['packet_files_hashed']} checksums, 199 Lean modules, all local imports resolve, no local cycles.")
        print('No Lean build or kernel replay was performed by this command.')
