#!/usr/bin/env python3
"""Exact reference CLI. NOT a Lean-verified program.

Python >=3.10, standard library only. The original v02 enumerator is kept
unchanged. This wrapper adds explicit equations, consistent variable sorting,
root normal forms, and an integer-only higher-dimensional recurrence.
All integral JSON data are decimal strings to avoid precision loss in readers.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from math import gcd, lcm, prod
from pathlib import Path
import sys
from typing import Any

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'research/current/verify_classification.py'
spec = importlib.util.spec_from_file_location('v02_reference', SOURCE)
if spec is None or spec.loader is None:
    raise RuntimeError('cannot load the preserved reference implementation')
legacy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(legacy)


def require(ok: bool, msg: str) -> None:
    if not ok:
        raise ValueError(msg)


def higher_integer(n: int, a: int) -> list[tuple[int, ...]]:
    """Integer prefix recursion. A/P = 1 - sum(1/q for q in prefix)."""
    require(n >= 4 and a >= 1, 'expected n>=4 and a>=1')
    out: list[tuple[int, ...]] = []
    def visit(prefix: tuple[int, ...], P: int, A: int) -> None:
        if A <= 0:
            return
        remaining = n - len(prefix)
        require(remaining >= 1 and P > 0, 'invalid recursion state')
        lower = prefix[-1] + 1 if prefix else 2
        if remaining == 1:
            q, remainder = divmod(a + P, A)
            if remainder or q < lower or any(gcd(q, t) != 1 for t in prefix):
                return
            p = prefix + (q,)
            total = P*q
            require(total - sum(total//t for t in p) == a, 'leaf defect mismatch')
            out.append(p)
            return
        upper = ((remaining + a) * P) // A
        for q in range(lower, upper + 1):
            if any(gcd(q, t) != 1 for t in prefix):
                continue
            visit(prefix + (q,), P*q, A*q-P)
    visit((), 1, 1)
    return out


def root_normal_form(p: list[int], a: int) -> dict[str, Any]:
    N = lcm(*p)
    k = N - sum(N//q for q in p)
    require(k > 0 and k % a == 0 and gcd(a, N) == 1, 'no integral canonical root')
    residues = [(-pow(a, -1, q)) % q for q in p]
    carries = [(a*s+1)//q for s, q in zip(residues, p)]
    numerator = 1-sum(carries)
    require(numerator % a == 0, 'nonintegral coarse root coefficient')
    b = numerator//a
    require(a*b + sum(a*s//q for s, q in zip(residues, p)) == 1-len(p), 'root carry mismatch')
    require(all((a*s) % q == q-1 for s, q in zip(residues, p)), 'root residue mismatch')
    return {'c_coefficient': b, 'residues': residues,
            'signature_order': p, 'N': N, 'k': k, 'u': k//a}


def formula(E: list[list[int]]) -> str:
    terms = []
    for e in E:
        factors = [f'x{j+1}' + (f'^{v}' if v != 1 else '')
                   for j, v in enumerate(e) if v]
        terms.append('*'.join(factors) if factors else '1')
    return ' + '.join(terms) + ' = 0'


def equation_record(n: int, a: int, p: list[int], w: list[int], h: int,
                    E: list[list[int]], monomial_matrix: list[list[int]],
                    common: list[int], provenance: dict[str, Any]) -> dict[str, Any]:
    require(len(p) == len(w) == len(E) == n, 'dimension mismatch')
    require(all(len(row) == n for row in E), 'bad matrix')
    # new variable j is old variable order[j]
    order = sorted(range(n), key=lambda j: (w[j], j))
    ws = [w[j] for j in order]
    Es = [[row[j] for j in order] for row in E]
    Bs = [monomial_matrix[j] for j in order]
    require(h == a+sum(ws) and gcd(*ws) == 1, 'degree/primitivity mismatch')
    require(all(sum(ej*wj for ej, wj in zip(row, ws)) == h for row in Es), 'not homogeneous')
    require(all(sum(row) >= 2 for row in Es), 'nonminimal relation')
    # E rows retain their original ordering, corresponding to p.
    for i in range(n):
        require([sum(Es[i][k]*Bs[k][j] for k in range(n)) for j in range(n)]
                == [common[j] + (p[j] if i == j else 0) for j in range(n)], 'Cox permutation mismatch')
    return {
        'n': n, 'a': a, 'weights': ws, 'relation_degree': h,
        'weight_key': ws + [h],
        'polynomial': [{'coefficient': 1, 'exponents': row} for row in Es],
        'equation_text': formula(Es),
        'signature': sorted(p),
        'root': root_normal_form(p, a),
        'witness': {'generator_permutation_new_to_old': order,
                    'ordered_signature': p, 'monomial_matrix': Bs,
                    'common_monomial': common, **provenance},
    }


def enumerate_reference(n: int, a: int) -> list[dict[str, Any]]:
    require(isinstance(n, int) and not isinstance(n, bool) and n >= 3, 'n must be an integer >=3')
    require(isinstance(a, int) and not isinstance(a, bool) and a >= 1, 'a must be a positive integer')
    if n == 3:
        out = []
        for row in legacy.enumerate_triangles(a).values():
            E = [list(t) for t in legacy.exponent_matrix(row['standard_form'], *row['exponents'])]
            out.append(equation_record(n, a, row['ordered_signature'], row['ordered_weights'], row['h'],
                E, [list(t) for t in row['monomial_matrix']], list(row['common_monomial']),
                {'standard_form_tag': row['standard_form'], 'standard_form_exponents': row['exponents']}))
        return out
    out = []
    for pt in higher_integer(n, a):
        p = list(pt); P = prod(p)
        E = [[p[i] if i == j else 0 for j in range(n)] for i in range(n)]
        identity = [[int(i == j) for j in range(n)] for i in range(n)]
        out.append(equation_record(n, a, p, [P//q for q in p], P, E, identity, [0]*n,
                                  {'standard_form_tag': 'Fermat'}))
    return out


def decimal_data(value: Any) -> Any:
    """Encode integer fields as strings, preserving booleans and text."""
    if isinstance(value, bool) or value is None:
        return value
    if isinstance(value, int):
        return str(value)
    if isinstance(value, list) or isinstance(value, tuple):
        return [decimal_data(x) for x in value]
    if isinstance(value, dict):
        return {k: decimal_data(v) for k, v in value.items()}
    return value


def payload(n: int, a: int) -> dict[str, Any]:
    rows = enumerate_reference(n, a)
    return decimal_data({'schema': 'canonical-root-equations-reference-v1',
        'integer_encoding': 'decimal strings', 'status': 'ok',
        'verification_status': 'REFERENCE_ONLY_NOT_LEAN_VERIFIED',
        'scope': 'isolated hypersurface canonical-root rings; graded complex algebra isomorphism',
        'input': {'n': n, 'a': a}, 'count': len(rows), 'equations': rows})


def main() -> int:
    class JsonArgumentParser(argparse.ArgumentParser):
        def error(self, message: str) -> None:
            print(json.dumps({'status': 'invalid_input', 'message': message}), file=sys.stderr)
            raise SystemExit(2)
    parser = JsonArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('a', type=int)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--format', choices=['json', 'text'], default='json')
    args = parser.parse_args()
    if args.n < 3 or args.a < 1:
        print(json.dumps({'status': 'invalid_input', 'message': 'expected n>=3 and a>=1'}), file=sys.stderr)
        return 2
    try:
        result = payload(args.n, args.a)
        if args.format == 'json':
            text = json.dumps(result, ensure_ascii=False, indent=2)+'\n'
        else:
            lines = ['REFERENCE ONLY — NOT LEAN VERIFIED', f'n={args.n}, a={args.a}, count={result["count"]}']
            lines.extend(f'{i+1}. {r["equation_text"]}; weights={r["weights"]}; h={r["relation_degree"]}; p={r["signature"]}'
                         for i, r in enumerate(result['equations']))
            text = '\n'.join(lines)+'\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
        else:
            sys.stdout.write(text)
        return 0
    except (MemoryError, RecursionError, KeyboardInterrupt) as exc:
        print(json.dumps({'status': 'incomplete', 'error': type(exc).__name__}), file=sys.stderr)
        return 3
    except (OSError, ValueError) as exc:
        print(json.dumps({'status': 'error', 'message': str(exc)}), file=sys.stderr)
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
