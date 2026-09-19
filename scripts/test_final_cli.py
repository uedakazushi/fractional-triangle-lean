#!/usr/bin/env python3
"""Normal CLI regressions; universal semantics are proved separately in Final.lean."""
from pathlib import Path
import sys,json,subprocess
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'reference'))
from reference_cli import enumerate_reference, require
from test_reference import check_record
exe=root/'formal/.lake/build/bin/canonical_roots'
out=root/'validation/final/cli';out.mkdir(parents=True,exist_ok=True)
def ints(v):
    if isinstance(v,str) and v.lstrip('-').isdigit():return int(v)
    if isinstance(v,list):return [ints(x) for x in v]
    if isinstance(v,dict):return {k:ints(x) for k,x in v.items()}
    return v
counts=[];checked=0
for n,a in [(3,a) for a in range(1,31)]+[(4,1),(4,5),(4,25),(5,1),(5,5)]:
    p=subprocess.run([str(exe),str(n),str(a)],capture_output=True,text=True,timeout=180)
    stem=f'n{n}_a{a}'
    (out/(stem+'.json')).write_text(p.stdout)
    (out/(stem+'.stderr.log')).write_text(p.stderr)
    (out/(stem+'.exit')).write_text(str(p.returncode)+'\n')
    require(p.returncode==0,'normal classification must return exit 0')
    raw=json.loads(p.stdout);require(raw['status']=='ok','missing normal classification status')
    got=ints(raw);rows=got['equations'];expected=enumerate_reference(n,a)
    keys={tuple(r['weight_key']) for r in rows}
    require(keys=={tuple(r['weight_key']) for r in expected},f'key mismatch {n,a}')
    require(len(keys)==len(rows),f'duplicate key {n,a}')
    for rr,r in zip(raw['equations'],rows):
        check_record(r)
        require(all(isinstance(x,str) for x in rr['weights']), 'integer encoding is not text')
        w=r['weights'];E=[t['exponents'] for t in r['polynomial']];B=r['witness']['monomial_matrix']
        pp=r['witness']['ordered_signature'];m0=r['witness']['common_monomial']
        for i in range(n):
            require([sum(E[i][k]*B[k][j] for k in range(n)) for j in range(n)]==
                    [m0[j]+(pp[j] if i==j else 0) for j in range(n)],'permutation mismatch')
        tau=r['root'];s=tau['residues'];b=tau['c_coefficient']
        require(all(0<=s[i]<pp[i] and (a*s[i]+1)%pp[i]==0 for i in range(n)),'root residue')
        require(a*b+sum((a*s[i]+1)//pp[i] for i in range(n))==1,'root c coefficient')
        checked+=1
    if n==3:counts.append(len(rows))
    print(f'PASS ({n},{a}): {len(rows)} classes',flush=True)
for args in [['2','1'],['3','0'],['-1','2'],['4','-2'],['x','1'],['3'],[]]:
    p=subprocess.run([str(exe),*args],capture_output=True,text=True)
    require(p.returncode==2 and json.loads(p.stdout)['status']=='invalid_input','input validation')
report={'status':'NORMAL_CLI_REGRESSIONS_PASSED','proof_scope':'Runtime regressions only; see Final.lean for universal semantics',
        'checked_records':checked,'counts_1_to_30':counts,'total_2_to_30':sum(counts[1:]),
        'high_examples':[[4,1],[4,5],[4,25],[5,1],[5,5]],'invalid_inputs':7}
require(counts[:6]==[14,6,8,8,21,0] and sum(counts[1:])==506,'counts')
(out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
