#!/usr/bin/env python3
"""Check a scoped comparison with Watanabe's arXiv:1401.0789v1 list.

The CSV is a human transcription of the individual three-point entries,
not a PDF extraction. This program validates the arithmetic and set difference;
it does not certify that the source was transcribed exhaustively or prove
any mathematical classification theorem. All checks remain active with -O.
"""
from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import gcd, prod
from pathlib import Path

from verify_classification import (
    arithmetic_signature, det3, enumerate_triangles, exponent_matrix, require,
)

EXAMPLES = [
    ((4, 10, 13, 30), 'x*z^2 + y^3 + x^5*y',
     ((1, 0, 2), (0, 3, 0), (5, 1, 0)), (2, 4, 13)),
    ((5, 6, 9, 24), 'x^3*z + y*z^2 + y^4',
     ((3, 0, 1), (0, 1, 2), (0, 4, 0)), (3, 5, 9)),
    ((6, 8, 19, 38), 'z^2 + x*y^4 + x^5*y',
     ((0, 0, 2), (1, 4, 0), (5, 1, 0)), (2, 6, 8)),
    ((4, 7, 16, 32), 'z^2 + x*y^4 + x^4*z',
     ((0, 0, 2), (1, 4, 0), (4, 0, 1)), (4, 4, 7)),
    ((4, 7, 12, 28), 'x*z^2 + y^4 + x^4*z',
     ((1, 0, 2), (0, 4, 0), (4, 0, 1)), (4, 4, 12)),
    ((4, 7, 9, 25), 'y*z^2 + x^4*z + x*y^3',
     ((0, 1, 2), (4, 0, 1), (1, 3, 0)), (4, 7, 9)),
]


def verify(source_csv: Path) -> dict:
    listed = {d: set() for d in range(1, 7)}
    cases: set[str] = set()
    source_rows = []
    with source_csv.open(newline='', encoding='utf-8') as f:
        for row in csv.DictReader(f):
            d = int(row['delta'])
            require(d in listed, 'delta outside comparison scope')
            key = tuple(int(row[k]) for k in ('w1', 'w2', 'w3', 'h'))
            require(tuple(sorted(key[:3])) == key[:3], f'unsorted key: {key}')
            require(gcd(*key[:3]) == 1, f'nonprimitive key: {key}')
            require(key[3] - sum(key[:3]) == d, f'wrong a-invariant: {key}')
            require(row['source_case'] not in cases, 'duplicate source case')
            require(key not in listed[d], f'duplicate source key: {key}')
            cases.add(row['source_case'])
            listed[d].add(key)
            source_rows.append(row)
    computed = {d: enumerate_triangles(d) for d in range(1, 7)}
    expected = {key for key, _, _, _ in EXAMPLES}
    missing: set[tuple[int, ...]] = set()
    counts = []
    for d in range(1, 7):
        keys = set(computed[d])
        require(listed[d] <= keys, f'source keys not reproduced at delta {d}')
        delta_missing = keys - listed[d]
        missing.update(delta_missing)
        counts.append({'delta': d, 'source_entries': len(listed[d]),
                       'current_classes': len(keys),
                       'missing': [list(x) for x in sorted(delta_missing)]})
    require(missing == expected, f'unexpected set difference: {missing ^ expected}')
    require([r['source_entries'] for r in counts] == [14, 6, 7, 7, 17, 0],
            'source count mismatch')
    require([r['current_classes'] for r in counts] == [14, 6, 8, 8, 21, 0],
            'current census mismatch')

    checked_examples = []
    for key, formula, E, sig in EXAMPLES:
        w, h = key[:3], key[3]
        d = h - sum(w)
        require(all(sum(a*b for a, b in zip(e, w)) == h for e in E),
                f'not weighted homogeneous: {formula}')
        require(abs(det3(E)) == h, f'determinant mismatch: {formula}')
        require(gcd(*w) == 1 and d > 0, 'not positive primitive data')
        require(arithmetic_signature(w, h) == sig, 'signature mismatch')
        require(Fraction(d*h, prod(w)) == 1-sum((Fraction(1, p) for p in sig), Fraction()),
                'root numerical identity mismatch')
        witness = computed[d][key]
        require(tuple(witness['signature']) == sig, 'enumerator signature mismatch')
        S = exponent_matrix(witness['standard_form'], *witness['exponents'])
        variable_permutations = [
            perm for perm in permutations(range(3))
            if Counter(tuple(e[j] for j in perm) for e in E) == Counter(S)
        ]
        require(bool(variable_permutations), 'not equivalent to the stated standard form')
        checked_examples.append({'delta': d, 'weights': list(w), 'h': h,
                                 'polynomial': formula, 'exponent_matrix': E,
                                 'determinant': det3(E), 'signature': sig,
                                 'standard_form': witness['standard_form'],
                                 'exponents': witness['exponents'],
                                 'variable_permutation_to_standard_form': variable_permutations[0]})
    return {
        'source': 'Kei-ichi Watanabe, arXiv:1401.0789v1, 4 January 2014, Section 3',
        'scope': 'three-point canonical-root subclass; 1 <= delta <= 6; sorted primitive weight keys',
        'source_data_status': 'human transcription with source item and PDF page; not automatically extracted',
        'source_pdf_redistributed': False,
        'published_journal_version_checked': False,
        'source_entries': len(source_rows),
        'counts': counts,
        'examples': checked_examples,
        'checks_passed': True,
        'formal_proof': False,
    }


def main() -> None:
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-csv', type=Path,
                        default=base/'watanabe_v1_three_point_keys.csv')
    parser.add_argument('--output', type=Path, default=base/'watanabe_comparison_results.json')
    args = parser.parse_args()
    report = verify(args.source_csv)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in report.items() if k != 'examples'}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
