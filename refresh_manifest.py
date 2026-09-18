"""Refresh release file hashes after explicit staging, without changing proof-source pins.

Run `git add` for intended release files first. This tool never stages, commits,
pushes, or changes SOURCE_PROVENANCE.json. It refuses any frozen proof drift.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parent

def refresh():
    source=json.loads((ROOT/'SOURCE_PROVENANCE.json').read_text())
    for module in source['lean_modules']:
        name=f'lean/{module}.lean'
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=source['source_sha256'][name]:
            raise ValueError('frozen proof source changed: '+name)
    from experiment import check_pins
    check_pins()
    files=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode().split('\0')
    hashes={}
    for name in sorted(filter(None,files)):
        if name=='MANIFEST.json': continue
        p=ROOT/name
        if p.is_symlink() or not p.is_file(): raise ValueError('not a regular release file: '+name)
        hashes[name]=hashlib.sha256(p.read_bytes()).hexdigest()
    (ROOT/'MANIFEST.json').write_text(json.dumps({'description':
        'SHA-256 of staged/tracked release files, excluding this manifest. Original proof-source pins are checked separately.',
        'sha256':hashes},indent=2)+'\n')
    return {'files':len(hashes),'frozen_lean_modules':len(source['lean_modules']),'published':False}

if __name__=='__main__': print(json.dumps(refresh(),indent=2))
