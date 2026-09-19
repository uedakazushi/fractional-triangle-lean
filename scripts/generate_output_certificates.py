#!/usr/bin/env python3
"""Translate captured CLI rows into explicit Lean data; Lean must prove every equality.

This generator is not trusted by the proof. Output byte hashes are external provenance.
"""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
cases = [(3, a) for a in range(1, 7)] + [(4, 1), (4, 5), (4, 25), (5, 1)]
lines = ['import CanonicalRoots.OutputCertificateChecker', 'import Certificates', '',
         'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '',
         'namespace CanonicalRoots.OutputCertificates', '']
hashes = []

def ints(values):
    return '[' + ','.join(ints(x) if isinstance(x, list) else str(int(x)) for x in values) + ']'

def row_term(row):
    witness = row['witness']
    fields = [str(int(row['n'])), str(int(row['a'])), ints(row['weights']),
              str(int(row['relation_degree'])), ints([t['exponents'] for t in row['polynomial']]),
              ints(witness['ordered_signature']), ints(witness['monomial_matrix']),
              ints(witness['common_monomial']), ints(witness['generator_permutation_new_to_old']),
              json.dumps(witness['standard_form_tag'])]
    return '⟨' + ', '.join(fields) + '⟩'

for n, a in cases:
    source = root / f'validation/final/cli/n{n}_a{a}.json'
    data = json.loads(source.read_text())
    assert data['status'] == 'ok'
    assert all(t['coefficient'] == '1' for row in data['equations'] for t in row['polynomial'])
    name = f'n{n}_a{a}'
    hashes.append({'input': [n, a], 'path': str(source.relative_to(root)),
                   'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                   'equation_data_theorem': f'CanonicalRoots.OutputCertificates.{name}_entire_list',
                   'count': len(data['equations'])})
    lines += [f'def {name}_input : Input := ⟨{n},{a},by decide,by decide⟩',
              f'def {name}_rows : List EquationData :=',
              '  [' + ',\n   '.join(row_term(r) for r in data['equations']) + ']', '',
              f'theorem {name}_entire_list : enumerate {name}_input = {name}_rows := by',
              f'  change enumerateCandidateEquations {n} {a} = _']
    cert = f'ternary_{a}_entire_list' if n == 3 else f'higher_{n}_{a}_entire_list'
    lines += ['  rw [enumerateCandidateEquations, ' + ('if_pos rfl' if n == 3 else 'if_neg (by decide)') +
              f', Certificates.{cert}]',
              '  cbv', '',
              f'theorem {name}_payload : decodeClassificationPayload (classificationPayload {name}_input) =',
              f'    some ({n},{a},{name}_rows) := by',
              f'  rw [cli_payload_correct, {name}_entire_list]', '  rfl', '']
lines += ['end CanonicalRoots.OutputCertificates', '']
source = root / 'formal/OutputCertificates.lean'
source.write_text('\n'.join(lines))
(root / 'validation/final/output_certificate_provenance.json').write_text(json.dumps({
    'scope': 'Exact decoded EquationData lists, not a kernel proof of OS bytes or SHA256',
    'source': str(source.relative_to(root)),
    'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'outputs': hashes}, indent=2) + '\n')
print(f'Generated {len(cases)} unverified whole-list proof obligations; compile OutputCertificates.lean.')
