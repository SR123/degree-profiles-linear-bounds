"""Check this review package before editing it. Does not compile Lean."""
from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parent
expected=json.loads((root/'manifest.json').read_text())
errors=[]
for name,expected_hash in expected.items():
 p=root/name
 if not p.is_file():errors.append('MISSING '+name)
 elif hashlib.sha256(p.read_bytes()).hexdigest()!=expected_hash:errors.append('CHANGED '+name)
if errors:raise SystemExit('\n'.join(errors))
print(f'PASS: {len(expected)} file hashes match. No Lean build or proof replay performed.')
