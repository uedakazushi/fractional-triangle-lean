#!/usr/bin/env python3
"""Reproduce the appendix tables from the compiled Lean classifier.

The comparison CSV is a cited transcription, not a Lean premise. --check reruns
the classifier and checks the committed JSON and every generated TeX fragment.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import math
import subprocess

ROOT = Path(__file__).resolve().parents[1]
INPUTS = [(n, a) for n in (3, 4, 5) for a in range(1, 7)]
EXPECTED_MISSING = {
    1: set(), 2: set(), 3: {(4, 10, 13, 30)}, 4: {(5, 6, 9, 24)},
    5: {(4, 7, 9, 25), (4, 7, 12, 28), (4, 7, 16, 32), (6, 8, 19, 38)},
    6: set(),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def collect():
    exe = ROOT / 'formal/.lake/build/bin/canonical_roots'
    cases = []
    for n, a in INPUTS:
        result = subprocess.run([str(exe), str(n), str(a)], check=True,
                                capture_output=True, text=True, timeout=60)
        payload = json.loads(result.stdout)
        require(payload['status'] == 'ok', f'Classification failed: {n}, {a}')
        rows = []
        for item in payload['equations']:
            w = list(map(int, item['weights']))
            h = int(item['relation_degree'])
            p = sorted(map(int, item['signature']))
            terms = [{'coefficient': int(t['coefficient']),
                      'exponents': list(map(int, t['exponents']))}
                     for t in item['polynomial']]
            require(int(item['n']) == n and int(item['a']) == a, 'Input mismatch')
            require(len(w) == n and w == sorted(w) and math.gcd(*w) == 1,
                    'Weights must be sorted and primitive')
            require(h - sum(w) == a, 'Gorenstein parameter mismatch')
            require(list(map(int, item['weight_key'])) == w + [h], 'Key mismatch')
            require(all(t['coefficient'] == 1 and len(t['exponents']) == n and
                        sum(e * v for e, v in zip(t['exponents'], w)) == h
                        for t in terms), 'Polynomial degree mismatch')
            require(len(terms) == n, 'Expected exactly n polynomial terms')
            if n == 3:
                e, f, g = [t['exponents'] for t in terms]
                det = (e[0] * (f[1] * g[2] - f[2] * g[1])
                       - e[1] * (f[0] * g[2] - f[2] * g[0])
                       + e[2] * (f[0] * g[1] - f[1] * g[0]))
                require(abs(det) == h, 'Principal determinant mismatch')
            if n >= 4:
                require(all(math.gcd(x, y) == 1 for i, x in enumerate(p)
                            for y in p[i + 1:]), 'Signature not pairwise coprime')
                require(h == math.prod(p) and w == sorted(h // x for x in p),
                        'Higher-dimensional Fermat data mismatch')
                require({tuple(t['exponents']) for t in terms} ==
                        {tuple(h // w[i] if j == i else 0 for j in range(n))
                         for i in range(n)}, 'Expected the stated Fermat equation')
            rows.append({'weights': w, 'h': h, 'signature': p, 'terms': terms})
        rows.sort(key=lambda row: row['weights'] + [row['h']])
        require(len(rows) == int(payload['count']), 'Count mismatch')
        require(len({tuple(r['weights'] + [r['h']]) for r in rows}) == len(rows),
                'Duplicate classification key')
        cases.append({'n': n, 'dimension': n - 1, 'a': a, 'count': len(rows), 'rows': rows})
    csv_path = ROOT / 'research/current/watanabe_v1_three_point_keys.csv'
    source = {a: {} for a in range(1, 7)}
    with csv_path.open(newline='') as stream:
        for r in csv.DictReader(stream):
            a = int(r['delta'])  # Original transcription header is preserved.
            key = tuple(int(r[k]) for k in ('w1', 'w2', 'w3', 'h'))
            require(key not in source[a], 'Duplicate transcribed key')
            source[a][key] = r['source_case']
    comparison = []
    for c in cases[:6]:
        a = c['a']
        actual = {tuple(r['weights'] + [r['h']]) for r in c['rows']}
        require(set(source[a]) <= actual, 'Transcribed entry missing from classifier')
        missing = actual - set(source[a])
        require(missing == EXPECTED_MISSING[a], 'Literature comparison changed')
        for r in c['rows']:
            r['source_case'] = source[a].get(tuple(r['weights'] + [r['h']]))
        comparison.append({'a': a, 'source_count': len(source[a]),
                           'classifier_count': c['count'],
                           'missing_keys': sorted(map(list, missing))})
    return {
        'generator': 'scripts/blueprint_tables.py',
        'source_manifest_sha256': hashlib.sha256(
            (ROOT / 'evidence/source-manifest.json').read_bytes()).hexdigest(),
        'comparison_source': 'https://arxiv.org/abs/1401.0789v1',
        'comparison_scope': 'Section 3, genus-zero three-point subclass, 1 <= a <= 6',
        'transcription_sha256': hashlib.sha256(csv_path.read_bytes()).hexdigest(),
        'cases': cases, 'comparison': comparison,
    }


def tup(xs):
    return '(' + ','.join(map(str, xs)) + ')'


def weight_key(r):
    return '(' + ','.join(map(str, r['weights'])) + ';' + str(r['h']) + ')'


def polynomial(r):
    terms = []
    for t in r['terms']:
        term = ''.join(v if e == 1 else v + '^{' + str(e) + '}'
                       for v, e in zip(('x', 'y', 'z'), t['exponents']) if e)
        terms.append(term or '1')
    return '+'.join(terms)


def tabular(columns, headers, rows):
    return '\n'.join([
        '% Generated by scripts/blueprint_tables.py; do not edit by hand.',
        r'\begin{tabular}{' + columns + '}', r'\hline',
        ' & '.join(headers) + r' \\', r'\hline',
        *(' & '.join(row) + r' \\' for row in rows), r'\hline', r'\end{tabular}', '',
    ])


def outputs(data):
    cases = {(c['n'], c['a']): c for c in data['cases']}
    out = {'blueprint/data/small_classifications.json': json.dumps(data, indent=2) + '\n'}
    out['blueprint/src/tables/counts.tex'] = tabular(
        'ccrrrrrr', ['$n$', r'$\dim R$'] + [f'$a={a}$' for a in range(1, 7)],
        [[str(n), str(n - 1)] + [str(cases[n, a]['count']) for a in range(1, 7)]
         for n in (3, 4, 5)])
    out['blueprint/src/tables/comparison.tex'] = tabular(
        'crrr', ['$a$', r'$N_{\mathrm{W}}$', r'$N_{\mathrm{Lean}}$', r'$N_{\mathrm{missing}}$'],
        [[str(c[k]) for k in ('a', 'source_count', 'classifier_count')] +
         [str(len(c['missing_keys']))] for c in data['comparison']])
    missing = []
    for a in range(1, 6):
        rows = cases[3, a]['rows']
        out[f'blueprint/src/tables/ternary_a{a}.tex'] = tabular(
            'clcc', ['$(w_1,w_2,w_3;h)$', '$f(x,y,z)$', '$(p_1,p_2,p_3)$', ''],
            [['$' + weight_key(r) + '$', '$' + polynomial(r) + '$',
              '$' + tup(r['signature']) + '$', r'$\ast$' if not r['source_case'] else '']
             for r in rows])
        missing.extend([[str(a), '$' + weight_key(r) + '$', '$' + polynomial(r) + '$',
                         '$' + tup(r['signature']) + '$'] for r in rows if not r['source_case']])
    out['blueprint/src/tables/missing.tex'] = tabular(
        'cclc', ['$a$', '$(w_1,w_2,w_3;h)$', '$f(x,y,z)$', '$(p_1,p_2,p_3)$'], missing)
    for n in (4, 5):
        out[f'blueprint/src/tables/higher_n{n}.tex'] = tabular(
            'ccc', ['$a$', r'$(p_1,\ldots,p_n)$', r'$(w_1,\ldots,w_n;h)$'],
            [[str(a), '$' + tup(r['signature']) + '$', '$' + weight_key(r) + '$']
             for a in range(1, 7) for r in cases[n, a]['rows']])
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--output-root', type=Path, default=ROOT)
    args = parser.parse_args()
    data = collect()
    for relative, expected in outputs(data).items():
        path = args.output_root / relative
        if args.check:
            require(path.is_file() and path.read_text() == expected, f'Stale table data: {path}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
    print(f'PASS: {len(data["cases"])} classifier inputs; '
          f'{sum(c["count"] for c in data["cases"])} rows; '
          '51 cited entries and six additional weight systems; appendix tables match')


if __name__ == '__main__':
    main()
