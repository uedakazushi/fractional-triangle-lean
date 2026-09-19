#!/usr/bin/env python3
"""Generate proof candidates; their truth is checked later by Lean's kernel."""
from pathlib import Path
from math import gcd
root=Path(__file__).resolve().parents[1]
def data(k,x,y,z):
    if k=='I':return [y*z,x*z,x*y],x*y*z
    if k=='II':return [z*(y-1),x*z,x*y],x*y*z
    if k=='III':return [z*(y-1),z*(x-1),x*y-1],z*(x*y-1)
    if k=='IV':return [z*(y-1)+1,x*(z-1),x*y],x*y*z
    return [z*(y-1)+1,x*(z-1)+1,y*(x-1)+1],x*y*z+1
text=['import CanonicalRoots.Candidates','', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '', 'namespace CanonicalRoots.Certificates', '']
for a in range(1,7):
    rows=[];keys=set()
    for k in ['I','II','III','IV','V']:
        for x in range(2,a+7):
            for y in range(2,a+7):
                for z in range(2,a+7):
                    w,h=data(k,x,y,z);key=tuple(sorted(w))+(h,)
                    if gcd(*w)==1 and h-sum(w)==a and key not in keys:
                        keys.add(key);rows.append(f'⟨.{k}, {x}, {y}, {z}⟩')
    text += [f'def explicitTernary{a} : List TernaryCandidate :=', '  ['+',\n   '.join(rows)+']',f'theorem ternary_{a}_entire_list :',f'    dedupCandidates (enumerateTernaryCandidates {a}) = explicitTernary{a} := by', '  unfold dedupCandidates candidateKey', '  simp only [List.mergeSort_eq_insertionSort]', '  decide +kernel','']
for n,a,ps in [(4,1,[[2,3,7,43]]),(4,5,[[2,3,7,47]]),(4,25,[[2,3,7,67]]),(5,1,[[2,3,7,43,1807],[2,3,7,47,395],[2,3,11,23,31]])]:
    text += [f'theorem higher_{n}_{a}_entire_list :',f'    enumerateHigherCandidates {n} {a} = {ps} := by','  decide +kernel','']
text+=['end CanonicalRoots.Certificates']
(root/'formal/Certificates.lean').write_text('\n'.join(text)+'\n')
print('Generated formal/Certificates.lean; not yet verified.')
