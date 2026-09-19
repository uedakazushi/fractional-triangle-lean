#!/usr/bin/env python3
"""Check normal CLI outputs against preserved reference cases. NOT Lean verification."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'reference'))
from reference_cli import enumerate_reference,require
from test_reference import check_record

def integer(x):
    require(isinstance(x,str) and x==str(int(x)), 'expected a canonical decimal integer string')
    return int(x)

def check_file(path: Path,n: int,a: int):
    data=json.loads(path.read_text(encoding='utf-8'))
    require(data['status']=='ok','not a successful classification result')
    require(integer(data['input']['n'])==n and integer(data['input']['a'])==a,'input mismatch')
    rows=data['equations'];require(integer(data['count'])==len(rows),'count mismatch')
    converted=[]
    for row in rows:
        r={'n':integer(row['n']),'a':integer(row['a']),
            'weights':list(map(integer,row['weights'])),
            'relation_degree':integer(row['relation_degree']),
            'signature':list(map(integer,row['signature'])),
            'polynomial':[{'coefficient':integer(t['coefficient']),
                           'exponents':list(map(integer,t['exponents']))} for t in row['polynomial']]}
        require(r['n']==n and r['a']==a,'entry input mismatch')
        require(len(r['weights'])==n and len(r['polynomial'])==n,'bad data dimensions')
        require(all(len(t['exponents'])==n for t in r['polynomial']),'bad exponent length')
        check_record(r)
        converted.append(tuple(r['weights'])+(r['relation_degree'],))
    expected={tuple(row['weight_key']) for row in enumerate_reference(n,a)}
    require(len(converted)==len(set(converted)),'duplicate keys')
    require(set(converted)==expected,'missing or additional class key')
    return len(converted)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);args=ap.parse_args()
    try:
        for n,a in ((3,1),(3,6),(4,1)):
            count=check_file(args.directory/f'n{n}_a{a}.json',n,a)
            print(f'n={n}, a={a}: {count} reference entries matched')
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print(str(exc),file=sys.stderr);return 1
    print('Output regression passed. Not a proof of universal semantic completeness.')
    return 0
if __name__=='__main__':raise SystemExit(main())
