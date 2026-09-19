#!/usr/bin/env python3
"""Check the byte-identical baseline of formal/, research/, and reference/."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
manifest=json.loads((root/'evidence/source-manifest.json').read_text())
for name,wanted in manifest.items():
    path=root/name
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=wanted:
        raise SystemExit('Baseline source mismatch: '+name)
print(f'PASS: {len(manifest)} baseline source files unchanged')
