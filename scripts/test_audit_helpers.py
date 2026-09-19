#!/usr/bin/env python3
"""Synthetic unit tests for audit helper parsers, NOT proof logs from Lean."""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from audit_sources import strip_comments_strings,PATTERNS
from check_axioms_log import check,REQUIRED
import re

def require(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    good="\n".join(f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in REQUIRED)
    require(len(check(good))==4,'good fixture')
    denied=0
    for bad in (good.replace('propext','sorryAx',1),good.replace('propext','_native.fake',1),good.splitlines()[0],good+'\nerror: failing goal'):
        try:check(bad)
        except ValueError:denied+=1
        else:raise ValueError('bad fixture accepted')
    stripped=strip_comments_strings('/- outer /- sorry -/ comment -/\ndef s := "axiom"\n-- sorry\ntheorem t : True := by trivial\n')
    require(not any(re.search(p,stripped) for p in PATTERNS.values()),'comment/string fixture')
    for source in ('axiom bad : False','theorem t : True := by sorry','theorem t : True := by native_decide',
                   'set_option debug.skipKernelTC true in\ntheorem t : True := by trivial'):
        require(any(re.search(p,strip_comments_strings(source)) for p in PATTERNS.values()),'missed bad source fixture')
    print(f'PASS synthetic parser fixtures: {denied} bad axiom logs rejected; source scan fixtures passed.')
    print('These are unit-test fixtures, not axiom audit results from a Lean build.')
if __name__=='__main__':main()
