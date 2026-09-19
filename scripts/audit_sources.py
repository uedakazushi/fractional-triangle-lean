#!/usr/bin/env python3
"""Conservative source pre-scan. NOT a replacement for kernel or signature audits."""
from pathlib import Path
import argparse, re, sys

def strip_comments_strings(text: str) -> str:
    out=[];i=0;depth=0;string=False;line=False
    while i<len(text):
        if line:
            c=text[i];out.append('\n' if c=='\n' else ' ');i+=1
            if c=='\n':line=False
        elif depth:
            if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
            elif text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif string:
            if text[i]=='\\' and i+1<len(text):out.extend('  ');i+=2
            elif text[i]=='"':out.append(' ');i+=1;string=False
            else:out.append('\n' if text[i]=='\n' else ' ');i+=1
        elif text.startswith('--',i):line=True;out.extend('  ');i+=2
        elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
        elif text[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    if depth or string:raise ValueError('unclosed Lean comment/string in source scan')
    return ''.join(out)

PATTERNS={
 'incomplete proof':r'\b(?:sorry|admit|sorryAx)\b',
 'custom axiom declaration':r'\baxiom\b',
 'native computation in proof':r'\bnative_decide\b|\bdecide\s*\+native\b',
 'unsafe custom code':r'\bunsafe\b',
 'runtime substitution':r'\bimplemented_by\b',
 'kernel bypass':r'\bskipKernelTC\b|\bdebug\.skipKernelTC\b',
}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path,nargs='?',default=Path(__file__).resolve().parents[1]/'formal')
 args=ap.parse_args();files=[p for p in args.root.rglob('*.lean') if '.lake' not in p.parts and '.elan' not in p.parts]
 if not files:print('No Lean source files to scan.',file=sys.stderr);return 1
 issues=[]
 for p in files:
  try:code=strip_comments_strings(p.read_text(encoding='utf-8'))
  except (OSError,ValueError) as exc:issues.append(f'{p}: {exc}');continue
  for kind,pattern in PATTERNS.items():
   for m in re.finditer(pattern,code):issues.append(f'{p}:{code.count(chr(10),0,m.start())+1}: {kind}')
 if issues:print('\n'.join(issues),file=sys.stderr);return 1
 print(f'No flagged source tokens in {len(files)} Lean files. NOT proof verification; theorem signatures and transitive axioms still require checking.')
 return 0
if __name__=='__main__':raise SystemExit(main())
