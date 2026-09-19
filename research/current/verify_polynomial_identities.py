#!/usr/bin/env python3
"""Exact coefficient checks in Z[a,b,c] for all five Cox constructions.

This is a reference checker, not a Lean proof. It uses no floating point,
external symbolic algebra package, eval, or assert statements. Polynomial
identities are checked coefficient by coefficient for indeterminate a,b,c,
not by sampling numerical parameter values.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import reduce
from typing import Dict, Tuple, Union

Exponent = Tuple[int, int, int]

@dataclass
class P:
    terms: Dict[Exponent, int]

    def __post_init__(self) -> None:
        self.terms = {e: c for e, c in self.terms.items() if c}

    @staticmethod
    def coerce(x: Union[int, 'P']) -> 'P':
        if isinstance(x, P):
            return x
        if isinstance(x, int):
            return P({(0, 0, 0): x})
        raise TypeError(f'Expected int or polynomial, got {type(x)}')

    def __add__(self, other: Union[int, 'P']) -> 'P':
        other = P.coerce(other)
        d = self.terms.copy()
        for e, c in other.terms.items():
            d[e] = d.get(e, 0) + c
        return P(d)

    __radd__ = __add__

    def __neg__(self) -> 'P':
        return P({e: -c for e, c in self.terms.items()})

    def __sub__(self, other: Union[int, 'P']) -> 'P':
        return self + (-P.coerce(other))

    def __rsub__(self, other: Union[int, 'P']) -> 'P':
        return P.coerce(other) + (-self)

    def __mul__(self, other: Union[int, 'P']) -> 'P':
        other = P.coerce(other)
        d: Dict[Exponent, int] = {}
        for e, c0 in self.terms.items():
            for f, c1 in other.terms.items():
                g = tuple(e[i] + f[i] for i in range(3))
                d[g] = d.get(g, 0) + c0 * c1
        return P(d)

    __rmul__ = __mul__


def product(xs):
    return reduce(lambda x, y: x * y, xs, P.coerce(1))


def det(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
            - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))


def main() -> None:
    a, b, c = (P({(1, 0, 0): 1}), P({(0, 1, 0): 1}), P({(0, 0, 1): 1}))
    # Each row contains weights, degree, signature, exponent matrix,
    # Cox monomial matrix, common monomial, and the integer-degree certificate C.
    data = [
        ([b*c, a*c, a*b], a*b*c, [a, b, c],
         [[a,0,0],[0,b,0],[0,0,c]], [[1,0,0],[0,1,0],[0,0,1]], [0,0,0],
         [[b*c-b-c,c,b],[c,a*c-a-c,a],[b,a,a*b-a-b]]),
        ([c*(b-1), a*c, a*b], a*b*c, [a,c*(b-1),c],
         [[a,1,0],[0,b,0],[0,0,c]], [[1,0,0],[0,c,0],[0,1,1]], [0,c,0],
         [[b*c-b-c,1,b-1],[c,a*c-a-c,a],[b,a-1,a*b-a-b+1]]),
        ([c*(b-1), c*(a-1), a*b-1], c*(a*b-1), [c*(a-1),c*(b-1),c],
         [[a,1,0],[1,b,0],[0,0,c]], [[c,0,0],[0,c,0],[1,1,1]], [c,c,0],
         [[b*c-b-c,1,b-1],[1,a*c-a-c,a-1],[b-1,a-1,a*b-a-b+1]]),
        ([c*(b-1)+1, a*(c-1), a*b], a*b*c, [a,c*(b-1)+1,a*(c-1)],
         [[a,1,0],[0,b,1],[0,0,c]], [[1,0,1],[0,c,0],[0,1,a]], [0,c,a],
         [[b*c-b-c+1,1,b-1],[c-1,a*c-a-c,1],[b,a-1,a*b-a-b+1]]),
        ([c*(b-1)+1, a*(c-1)+1, b*(a-1)+1], a*b*c+1,
         [b*(a-1)+1,c*(b-1)+1,a*(c-1)+1],
         [[a,1,0],[0,b,1],[1,0,c]], [[b,0,1],[1,c,0],[0,1,a]], [b,c,a],
         [[b*c-b-c+1,1,b-1],[c-1,a*c-a-c+1,1],[1,a-1,a*b-a-b+1]])
    ]
    count = 0

    def check(lhs, rhs, label):
        nonlocal count
        d = P.coerce(lhs) - rhs
        if d.terms:
            raise ArithmeticError(f'{label}: nonzero difference {d.terms}')
        count += 1

    for kind, (w,h,p,E,B,m0,C) in enumerate(data, start=1):
        delta = h - sum(w)
        for i in range(3):
            check(sum(E[i][j]*w[j] for j in range(3)), h, f'{kind}: E w')
            check(sum(C[i]), w[i], f'{kind}: sum of row C')
            for j in range(3):
                check(p[j]*C[i][j], delta*B[i][j]+w[i], f'{kind}: integral L degree')
                check(sum(E[i][l]*B[l][j] for l in range(3)),
                      (p[i] if i == j else 0) + m0[j], f'{kind}: E B')
        check(det(E), h, f'{kind}: determinant E')
        check(delta*h*product(p), product(w)*(product(p)-sum(
            product([p[j] for j in range(3) if j != i]) for i in range(3))),
              f'{kind}: multiplicity identity')
        check(det(B)*product(w), h*product(p), f'{kind}: determinant B/group size')
    print(f'PASS: {count} polynomial identities in Z[a,b,c], checked coefficientwise.')
    print('No bounded parameter sampling and no external CAS are used in this checker.')
    print('This result is not a Lean kernel verification.')


if __name__ == '__main__':
    main()
