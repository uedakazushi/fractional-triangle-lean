#!/usr/bin/env python3
"""Check captured #print axioms output. Log sanity check, not independent proof replay."""
import argparse, re, sys
from pathlib import Path
ALLOWED={'propext','Quot.sound','Classical.choice'}
REQUIRED=['CanonicalRoots.enumerate_sound','CanonicalRoots.enumerate_complete',
          'CanonicalRoots.enumerate_pairwise_nonisomorphic','CanonicalRoots.cli_payload_correct']

def check(text: str) -> dict[str,list[str]]:
    if re.search(r'(?m)\berror:',text):raise ValueError('Lean error in audit output')
    seen={}
    for name in REQUIRED:
        pat=re.compile(r"['‘]"+re.escape(name)+r"['’]\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",re.S)
        matches=list(pat.finditer(text))
        if len(matches)!=1:raise ValueError(f'expected one axiom report for {name}, got {len(matches)}')
        ax=[a.strip() for a in (matches[0].group(1) or '').split(',') if a.strip()]
        bad=set(ax)-ALLOWED
        if bad:raise ValueError(f'forbidden axioms for {name}: {sorted(bad)}')
        seen[name]=ax
    return seen

def main():
 ap=argparse.ArgumentParser();ap.add_argument('log',type=Path);args=ap.parse_args()
 try:reports=check(args.log.read_text(encoding='utf-8'))
 except (OSError,ValueError) as exc:print(str(exc),file=sys.stderr);return 1
 for name,axioms in reports.items():print(name+': '+', '.join(axioms))
 print('Log format/allowlist passed. This does NOT check theorem meaning or replay proof terms.')
 return 0
if __name__=='__main__':raise SystemExit(main())
