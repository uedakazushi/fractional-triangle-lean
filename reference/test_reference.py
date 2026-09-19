#!/usr/bin/env python3
"""Regression tests, not formal proofs. All checks remain on under -O."""
from __future__ import annotations
from pathlib import Path
import argparse, json, subprocess, sys
from math import gcd, prod
from reference_cli import ROOT, legacy, higher_integer, enumerate_reference, payload, require


def determinant(m: list[list[int]]) -> int:
    # Fraction-free Bareiss elimination with row pivoting.
    a = [r[:] for r in m]; n=len(a); previous=1; sign=1
    if n == 0: return 1
    for k in range(n-1):
        pivot = next((i for i in range(k,n) if a[i][k]), None)
        if pivot is None: return 0
        if pivot != k:
            a[k],a[pivot]=a[pivot],a[k];sign=-sign
        pk=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                numerator=a[i][j]*pk-a[i][k]*a[k][j]
                require(numerator % previous == 0, 'nonexact Bareiss division')
                a[i][j]=numerator//previous
        for i in range(k+1,n): a[i][k]=0
        previous=pk
    return sign*a[-1][-1]


def check_record(r):
    E=[t['exponents'] for t in r['polynomial']];w=r['weights'];h=r['relation_degree'];n=r['n']
    require(abs(determinant(E))==h, 'determinant mismatch')
    require(h-sum(w)==r['a'] and gcd(*w)==1, 'weight mismatch')
    require(all(sum(x*y for x,y in zip(e,w))==h for e in E), 'column permutation mismatch')
    require(all(t['coefficient']==1 and sum(t['exponents'])>=2 for t in r['polynomial']), 'polynomial mismatch')
    if n==3:
        require(list(legacy.arithmetic_signature(tuple(w),h))==r['signature'], 'signature mismatch')
    else:
        p=r['signature'];P=prod(p)
        require(P-sum(P//q for q in p)==r['a'], 'higher defect mismatch')
        require(all(gcd(p[i],p[j])==1 for i in range(n) for j in range(i)), 'gcd mismatch')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-a',type=int,default=30)
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    require(1<=args.max_a<=30,'test bound must be between 1 and 30')
    saved=json.loads((ROOT/'research/current/verification_results.json').read_text())
    expected=[14,6,8,8,21,0,29,11,12,6,37,0,36,10,9,11,40,2,46,11,12,9,55,3,28,16,18,10,52,0]
    checked=0;counts=[]
    for a in range(1,args.max_a+1):
        rows=enumerate_reference(3,a);counts.append(len(rows))
        require(len(rows)==expected[a-1],f'count mismatch at {a}')
        keys={tuple(r['weight_key']) for r in rows}
        old={tuple(r['weights'])+(r['h'],) for r in saved['classes'] if r['delta']==a}
        require(keys==old and len(keys)==len(rows),'key/dedup mismatch')
        for r in rows:check_record(r);checked+=1
    comparisons=0;higher_counts={}
    for n in (4,5):
        for a in range(1,7):
            actual=higher_integer(n,a);old=legacy.enumerate_higher(n,a)
            require(actual==old,f'integer/Fraction recurrence mismatch: {n,a}')
            for r in enumerate_reference(n,a):check_record(r);checked+=1
            higher_counts[f'{n},{a}']=len(actual);comparisons+=1
    require((2,3,7,67) in higher_integer(4,25),'missing high example')
    # The example rejects the false assertion that det(f)=h is necessary for a given f.
    require(legacy.arithmetic_signature((12,8,3),24)==(3,3,4),'counterexample signature')
    require(legacy.det3(((2,0,0),(0,3,0),(0,0,8)))==48,'counterexample determinant')
    # Three terms, det != 0, positive weights, positive a, yet NOT isolated:
    # f=x^3*y + y*z^3 + y^4. Its gradient vanishes at (1,0,-1).
    E=[[3,1,0],[0,1,3],[0,4,0]];z=[1,0,-1]
    require(determinant(E)!=0,'branched example determinant')
    grad=[]
    for j in range(3):
        value=0
        for row in E:
            if not row[j]:continue
            value+=row[j]*prod(z[k]**(row[k]-int(k==j)) for k in range(3))
        grad.append(value)
    require(grad==[0,0,0] and z!=[0,0,0],'nonisolated witness incorrect')
    errors=0
    for n,a in ((2,1),(3,0),(-1,2),(4,-2)):
        result=subprocess.run([sys.executable,str(ROOT/'reference/reference_cli.py'),str(n),str(a)],capture_output=True,text=True)
        require(result.returncode==2 and json.loads(result.stderr)['status']=='invalid_input','invalid input reported as success');errors+=1
    empty=payload(3,6);require(empty['status']=='ok' and empty['count']=='0' and empty['equations']==[],'empty case')
    sample=payload(3,5);require(json.loads(json.dumps(sample))==sample,'JSON round trip')
    require(isinstance(sample['equations'][0]['relation_degree'],str),'decimal string policy')
    report={'formal_verification':False,'status':'REFERENCE_TESTS_PASSED',
        'n3_counts':counts,'equation_records_checked':checked,'higher_recurrence_comparisons':comparisons,
        'higher_counts':higher_counts,'invalid_inputs_checked':errors,
        'counterexamples_checked':['nonprincipal presentation','nonisolated three-term positive-weight polynomial'],
        'n3_total_1_to_30':sum(counts) if args.max_a==30 else None,
        'n3_total_2_to_30':sum(counts[1:]) if args.max_a==30 else None}
    text=json.dumps(report,ensure_ascii=False,indent=2)+'\n'
    if args.output:args.output.write_text(text,encoding='utf-8')
    print(text,end='')
if __name__=='__main__':main()
