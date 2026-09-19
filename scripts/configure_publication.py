#!/usr/bin/env python3
"""Configure public URLs locally; never creates a remote or pushes."""
from pathlib import Path
import argparse,json,re
root=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--owner',required=True);args=ap.parse_args()
if not re.fullmatch(r'[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?',args.owner):raise SystemExit('Invalid GitHub owner')
meta=json.loads((root/'publication.json').read_text())
meta['repository_url']=f'https://github.com/{args.owner}/{meta["repository_name"]}'
if meta['role']=='canonical':
    meta.pop('companion_url',None)
else:
    meta['companion_url']=f'https://github.com/{args.owner}/fractional-triangle-lean'
(root/'publication.json').write_text(json.dumps(meta,ensure_ascii=False,indent=2)+'\n')
lock=root/'upstream.lock.json'
if lock.exists():
    value=json.loads(lock.read_text());value['repository']=f'https://github.com/{args.owner}/fractional-triangle-lean';lock.write_text(json.dumps(value,indent=2)+'\n')
readme=root/'README.md';text=readme.read_text().split('\n<!-- EDITION_LINKS -->')[0].rstrip()
if meta['role']=='canonical':
    readme.write_text(text+'\n')
else:
    readme.write_text(text+'\n\n<!-- EDITION_LINKS -->\n[English source](https://github.com/'+args.owner+'/fractional-triangle-lean)\n')
cff=root/'CITATION.cff';lines=[x for x in cff.read_text().splitlines() if not x.startswith('repository-code:')]
cff.write_text('\n'.join(lines)+'\nrepository-code: "'+meta['repository_url']+'"\n')
print('Configured local metadata for',meta['repository_url'])
