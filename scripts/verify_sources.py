#!/usr/bin/env python3
"""Check the current source snapshot and the immutable research/reference baseline."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'evidence/source-manifest.json').read_text())
for name,wanted in manifest.items():
    path=root/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=wanted:
        raise SystemExit('Reviewed source mismatch: '+name)
lean_files={str(p.relative_to(root)) for p in (root/'formal').rglob('*.lean')
            if not {'.lake','.elan','.publication'} & set(p.parts)}
recorded={p for p in manifest if p.startswith('formal/') and p.endswith('.lean')}
if lean_files!=recorded:
    raise SystemExit('Lean source inventory mismatch: '+str(sorted(lean_files^recorded)))
original=json.loads((root/'evidence/original/source-manifest.json').read_text())
preserved={p:h for p,h in original.items() if p.startswith(('research/','reference/'))}
for name,wanted in preserved.items():
    if hashlib.sha256((root/name).read_bytes()).hexdigest()!=wanted:
        raise SystemExit('Original research/reference mismatch: '+name)
print(f'PASS: {len(manifest)} reviewed source files; {len(preserved)} original research/reference files unchanged')
