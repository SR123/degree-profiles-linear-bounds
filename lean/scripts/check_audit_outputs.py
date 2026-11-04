#!/usr/bin/env python3
"""Validate the named axiom and transitive-dependency reports in full audit logs."""
import argparse
import json
import re
from pathlib import Path

packet = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser()
parser.add_argument('output_directory')
args = parser.parse_args()
expected = json.loads((packet / 'provenance/audit_expectations.json').read_text())['modules']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
total_axioms = total_dependencies = 0
for module, checks in expected.items():
    text = (Path(args.output_directory) / (module + '.out')).read_text()
    found_axioms = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S)
    axioms = [[name, [x.strip() for x in values.split(',') if x.strip()]] for name, values in found_axioms]
    assert len(axioms) == len(checks['axiom_reports']), f'{module}: incomplete axiom reports'
    assert [name for name, _ in axioms] == [name for name, _ in checks['axiom_reports']], f'{module}: wrong audited names'
    for name, values in axioms:
        assert set(values) <= allowed, f'{module}: unexpected axioms for {name}: {values}'
    found_uses = re.findall(r'(?m)^(\S+) uses (\S+): (true|false)\s+\(closure size \d+\)', text)
    uses = [[a, b, value == 'true'] for a, b, value in found_uses]
    assert uses == checks['dependency_reports'], f'{module}: dependency results differ'
    total_axioms += len(axioms)
    total_dependencies += len(uses)
print(f'PASS: {total_axioms} targeted standard-foundation-only axiom reports and {total_dependencies} expected dependency reports.')
print('These checks cover the named audit declarations; they do not certify every manuscript sentence or every package declaration.')
