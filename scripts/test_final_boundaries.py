#!/usr/bin/env python3
"""Exact regression against preserved source data; not an independent Lean proof."""
from pathlib import Path
import csv
import json
from math import gcd, prod

root = Path(__file__).resolve().parents[1]
out = root / 'validation/final'
source = list(csv.DictReader((root / 'research/current/watanabe_v1_three_point_keys.csv').open()))
old = {tuple(int(r[k]) for k in ['delta', 'w1', 'w2', 'w3', 'h']) for r in source}
new = set()
for a in range(1, 7):
    rows = json.loads((out / f'cli/n3_a{a}.json').read_text())['equations']
    new.update((a, *map(int, r['weights']), int(r['relation_degree'])) for r in rows)
expected = {(3,4,10,13,30), (4,5,6,9,24), (5,6,8,19,38),
            (5,4,7,16,32), (5,4,7,12,28), (5,4,7,9,25)}
if len(source) != 51 or len(old) != 51 or old - new or new - old != expected:
    raise SystemExit('Watanabe v1 transcription comparison failed')

# The nonmaximal root from the preserved counterexample: scale 5, free nonzero
# cyclic action. These numerical conditions are checked exactly, not taken as a
# Lean proof of regularity of every local quotient.
p = [2,3,7,67]
P = prod(p)
w = [P // q for q in p]
defect = P - sum(w)
if defect != 25 or defect // 5 != 5 or any(gcd(x, 5) != 1 for x in w):
    raise SystemExit('Nonmaximal root counterexample data failed')
if any(k*x % 5 == 0 for k in range(1, 5) for x in w):
    raise SystemExit('Nontrivial cyclic element fixes a coordinate')
report = {
    'status': 'PASSED', 'proof_scope': 'Runtime integer/source-data regression',
    'watanabe_v1_transcription_count': 51, 'classifier_count_1_to_6': len(new),
    'six_additional_keys': sorted(expected), 'journal_or_later_corrections_checked': False,
    'nonmaximal_root': {'signature': p, 'index': 5, 'maximal_index': 25,
        'scale': 5, 'maximal_weights': w, 'cyclic_action_free_off_origin_checked': True,
        'lean_no_isolated_hypersurface_presentation_test': 'formal/HigherConverseTests.lean',
        'local_regular_quotient_theorem_formalized_for_this_example': False},
}
(out / 'boundary_regressions.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
