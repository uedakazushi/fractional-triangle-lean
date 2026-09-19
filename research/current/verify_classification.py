#!/usr/bin/env python3
"""Exact reference computations accompanying the Japanese manuscript.

This is a regression checker, NOT a Lean proof.  Only Python's standard
library is required.  Every validation is active under ``python -O``.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product, permutations
from math import gcd, lcm, prod
from pathlib import Path
import argparse
import csv
import json


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def weights(kind: int, a: int, b: int, c: int) -> tuple[tuple[int, int, int], int]:
    require(kind in range(1, 6) and min(a,b,c) >= 2, 'invalid standard form')
    if kind == 1: return (b*c, a*c, a*b), a*b*c
    if kind == 2: return (c*(b-1), a*c, a*b), a*b*c
    if kind == 3: return (c*(b-1), c*(a-1), a*b-1), c*(a*b-1)
    if kind == 4: return (c*(b-1)+1, a*(c-1), a*b), a*b*c
    return (c*(b-1)+1, a*(c-1)+1, b*(a-1)+1), a*b*c+1


def exponent_matrix(kind: int, a: int, b: int, c: int) -> tuple[tuple[int, ...], ...]:
    return {
        1: ((a,0,0),(0,b,0),(0,0,c)),
        2: ((a,1,0),(0,b,0),(0,0,c)),
        3: ((a,1,0),(1,b,0),(0,0,c)),
        4: ((a,1,0),(0,b,1),(0,0,c)),
        5: ((a,1,0),(0,b,1),(1,0,c)),
    }[kind]


def det3(m: tuple[tuple[int, ...], ...]) -> int:
    a,b,c=m
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])


def arithmetic_signature(w: tuple[int, int, int], h: int) -> tuple[int, ...]:
    """The multiset A(W) in the manuscript (finite integer arithmetic)."""
    r=[v for v in w if h % v != 0 and v > 1]
    for i,j in ((0,1),(0,2),(1,2)):
        d=gcd(w[i],w[j])
        if d == 1: continue
        m=sum((h-w[i]*a) % w[j] == 0 for a in range(h//w[i]+1))
        require(m >= 1, 'a binary restriction has no monomial')
        r.extend([d]*(m-1))
    return tuple(sorted(r))


def coordinate_signature(kind: int, a: int, b: int, c: int) -> tuple[int, ...]:
    w0,h0=weights(kind,a,b,c); q=gcd(*w0); w=tuple(v//q for v in w0)
    r=[]
    def add(numer: int, count: int=1) -> None:
        require(numer % q == 0, 'nonintegral coordinate order')
        value=numer//q
        if value > 1: r.extend([value]*count)
    if kind == 1:
        add(c*gcd(a,b),gcd(a,b)); add(b*gcd(a,c),gcd(a,c)); add(a*gcd(b,c),gcd(b,c))
    elif kind == 2:
        add(w0[0]); add(c*gcd(a,b-1),gcd(a,b-1)); add(a*gcd(b,c),gcd(b,c))
    elif kind == 3:
        add(w0[0]); add(w0[1]); add(c*gcd(a-1,b-1),gcd(a-1,b-1))
    elif kind == 4:
        add(w0[0]); add(w0[1]); add(a*gcd(b,c-1),gcd(b,c-1))
    else:
        for v in w0: add(v)
    return tuple(sorted(r))


def cox_data(kind: int, a: int, b: int, c: int):
    A=a-1; B=b-1; t=c-1
    return {
        1: ((a,b,c), ((1,0,0),(0,1,0),(0,0,1)), (0,0,0)),
        2: ((a,c*B,c), ((1,0,0),(0,c,0),(0,1,1)), (0,c,0)),
        3: ((c*A,c*B,c), ((c,0,0),(0,c,0),(1,1,1)), (c,c,0)),
        4: ((a,c*B+1,a*t), ((1,0,1),(0,c,0),(0,1,a)), (0,c,a)),
        5: ((b*A+1,c*B+1,a*t+1), ((b,0,1),(1,c,0),(0,1,a)), (b,c,a)),
    }[kind]


def nf(c0: int, e: tuple[int,...], p: tuple[int,...]) -> tuple[int, tuple[int,...]]:
    divs=[divmod(x,y) for x,y in zip(e,p)]
    return c0+sum(x[0] for x in divs), tuple(x[1] for x in divs)


def check_cox(kind: int, a: int, b: int, c: int) -> None:
    w,h=weights(kind,a,b,c); delta=h-sum(w)
    require(gcd(*w)==1 and delta>0, 'nonprincipal data passed to Cox checker')
    p,B,v0=cox_data(kind,a,b,c); E=exponent_matrix(kind,a,b,c)
    for i in range(3):
        left=tuple(sum(E[i][k]*B[k][j] for k in range(3)) for j in range(3))
        right=tuple(v0[j]+(p[j] if i==j else 0) for j in range(3))
        require(left==right, f'Cox identity failed: {kind,a,b,c}')
        # delta*deg(M_i) - w_i*(c - sum x_j) = 0 in L
        require(nf(-w[i],tuple(delta*B[i][j]+w[i] for j in range(3)),p)==(0,(0,0,0)), 'root degree identity failed')
    mu=Fraction(h,prod(w)); nu=1-sum((Fraction(1,v) for v in p),Fraction())
    require(delta*mu==nu and nu>0, 'defect identity failed')
    require(abs(det3(B))==mu*prod(p), 'kernel order mismatch')
    N=lcm(*p); k=N-sum(N//v for v in p)
    require(k%delta==0 and gcd(delta,N)==1, 'root criterion failed')
    require(tuple(sorted(p))==arithmetic_signature(w,h), 'signature mismatch')


def exceptional(kind: int, a: int, b: int, c: int) -> bool:
    if kind==1:
        for x,y,z in permutations((a,b,c)):
            if x==2 and y%2==0 and gcd(y,z)==1: return True
            if x==y==3 and gcd(3,z)==1: return True
    if kind==2:
        return (a==2 and b%2==1 and gcd(b,c)==1) or (c==2 and b%2==0 and gcd(a,b-1)==1)
    return False


def enumerate_triangles(delta: int) -> dict[tuple[int,...], dict]:
    require(delta>0, 'delta must be positive')
    classes={}
    for kind in range(1,6):
        for a,b,c in product(range(2,delta+7),repeat=3):
            w,h=weights(kind,a,b,c)
            if h-sum(w)!=delta or gcd(*w)!=1: continue
            check_cox(kind,a,b,c)
            key=(*sorted(w),h)
            p,B,v0=cox_data(kind,a,b,c)
            row={'delta':delta,'weights':list(sorted(w)),'h':h,'signature':list(sorted(p)),
                 'standard_form':kind,'exponents':[a,b,c], 'ordered_weights':list(w),
                 'ordered_signature':list(p),'monomial_matrix':B,'common_monomial':v0}
            if key in classes:
                require(classes[key]['signature']==row['signature'], 'one weight key has two signatures')
            else: classes[key]=row
    return dict(sorted(classes.items()))


def enumerate_higher(n: int, delta: int) -> list[tuple[int,...]]:
    require(n>=4 and delta>0,'expected n>=4, delta>0')
    out=[]
    def visit(prefix: tuple[int,...], c: Fraction, P: int) -> None:
        left=n-len(prefix)
        if c<=0: return
        lower=prefix[-1]+1 if prefix else 2
        if left==1:
            D=c*P
            require(D.denominator==1,'partial defect is not integral')
            x,rem=divmod(delta+P,int(D))
            if rem or x<lower or any(gcd(x,y)>1 for y in prefix): return
            p=prefix+(x,)
            require(prod(p)-sum(prod(p)//y for y in p)==delta,'higher equation failed')
            out.append(p); return
        upper=(left+delta)/c
        for x in range(lower,upper.numerator//upper.denominator+1):
            if any(gcd(x,y)>1 for y in prefix): continue
            visit(prefix+(x,),c-Fraction(1,x),P*x)
    visit((),Fraction(1),1)
    return out


def regression(scan: int=18, census_max: int=30) -> dict:
    tested=0; triangle=0
    for kind,a,b,c in product(range(1,6),range(2,scan+1),range(2,scan+1),range(2,scan+1)):
        w0,h0=weights(kind,a,b,c); q=gcd(*w0); w=tuple(v//q for v in w0);h=h0//q;delta=h-sum(w)
        require(abs(det3(exponent_matrix(kind,a,b,c)))==h0,'exponent determinant failed')
        if delta<=0: continue
        r=coordinate_signature(kind,a,b,c)
        require(r==arithmetic_signature(w,h),'arithmetic/coordinate signatures differ')
        ok=len(r)==3 and Fraction(delta*h,prod(w))==1-sum((Fraction(1,x) for x in r),Fraction())
        require(ok==(q==1 or exceptional(kind,a,b,c)),'primitive replacement list mismatch')
        if q==1:check_cox(kind,a,b,c)
        tested+=1; triangle+=int(ok)
    # One common exponent box, independent of the per-index loop.
    by_delta={d:{} for d in range(1,census_max+1)}
    for kind,a,b,c in product(range(1,6),range(2,census_max+7),range(2,census_max+7),range(2,census_max+7)):
        w,h=weights(kind,a,b,c);delta=h-sum(w)
        if not 1<=delta<=census_max or gcd(*w)!=1:continue
        check_cox(kind,a,b,c)
        key=(*sorted(w),h); p,B,v0=cox_data(kind,a,b,c)
        by_delta[delta].setdefault(key,{'delta':delta,'weights':list(sorted(w)),'h':h,'signature':list(sorted(p)),
                                      'standard_form':kind,'exponents':[a,b,c], 'ordered_weights':list(w),
                                      'ordered_signature':list(p),'monomial_matrix':B,'common_monomial':v0})
    # Compare with the actual per-index enumerator, not only a recorded census.
    for d in range(1, census_max + 1):
        per_index = enumerate_triangles(d)
        require(set(per_index) == set(by_delta[d]), 'per-index/common-box mismatch')
        for key, row in per_index.items():
            require(tuple(row['signature']) == tuple(by_delta[d][key]['signature']),
                    'per-index signature mismatch')
    expected=[14,6,8,8,21,0,29,11,12,6,37,0,36,10,9,11,40,2,46,11,12,9,55,3,28,16,18,10,52,0]
    counts=[len(by_delta[d]) for d in by_delta]
    require(counts[:min(30,census_max)]==expected[:min(30,census_max)],'recorded census mismatch')
    high={f'n={n},delta={d}':enumerate_higher(n,d) for n,d in ((4,1),(4,5),(4,25),(5,1))}
    return {'atomic_exponent_bound':scan,'positive_index_systems_checked':tested,
            'triangle_systems_in_box':triangle,'census':counts,
            'census_2_through_30':sum(counts[1:30]),'higher_examples':high,
            'classes':[row for d in by_delta for _,row in sorted(by_delta[d].items())]}


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('verification_results.json'))
    p.add_argument('--scan',type=int,default=18)
    p.add_argument('--census-max',type=int,default=30)
    args=p.parse_args()
    require(args.scan>=2 and args.census_max>=1,'invalid bounds')
    report=regression(args.scan,args.census_max)
    args.output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in report.items() if k!='classes'},ensure_ascii=False,indent=2))

if __name__=='__main__':main()
