#!/usr/bin/env python3
"""Verify every requested axiom report, including the four final theorem names.

This checks captured Lean reports and does not substitute for mathematical signature review.
"""
from pathlib import Path
import json
import re
import sys

from check_axioms_log import check

root = Path(__file__).resolve().parents[1]
source = Path(sys.argv[1])
log = source.read_text()
check(log)
reports = {}
for match in re.finditer(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log, re.S):
    name = match.group(1)
    if name in reports:
        raise SystemExit("Duplicate axiom report: " + name)
    axioms = [a.strip() for a in (match.group(2) or "").split(",") if a.strip()]
    if set(axioms) - {"propext", "Classical.choice", "Quot.sound"}:
        raise SystemExit("Disallowed axiom: " + name)
    reports[name] = axioms
expected = re.findall(r"^#print axioms (\S+)", (root / "formal/Audit.lean").read_text(), re.M)
if len(expected) != len(set(expected)) or set(reports) != set(expected):
    raise SystemExit("Audit target mismatch")
out = root / "validation/final"
out.mkdir(exist_ok=True)
(out / "axiom_inventory.json").write_text(json.dumps({
    "scope": "All declarations listed in Audit.lean, including the four final theorems",
    "source_log": str(source.resolve().relative_to(root)),
    "declarations": reports,
}, indent=2) + "\n")
print(f"PASS: all {len(reports)} declarations have only permitted foundational axioms.")
