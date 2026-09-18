"""Replay the stored addition matrix with independently anchored literal endpoints."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re

from independent_release_replay import replay
from official_verifier import core
from experiment import GOLDEN, UNLIMITED, check_pins


def reduce(w):
    out=[]
    for a in w:
        if out and out[-1]==-a: out.pop()
        else: out.append(a)
    return out


def pow_letter(a,n): return [a if n>=0 else -a]*abs(n)


def endpoints(name):
    if name=='height5-residual':
        return [[-2]*4+[1,1]+[2]*4+[-1],[-2,-2,-1,2,-1,-1]],[[1],[2]]
    if re.fullmatch(r'height5--?\d+',name):
        p=int(name[len('height5-'):]); N,s=11,5; target=[[1],[2]]
    else:
        match=re.fullmatch(r'period-(-?\d+)-(-?\d+)-(-?\d+)',name)
        sample=re.fullmatch(r'period-example-(-?\d+)-(-?\d+)',name)
        if match: N,p,s=map(int,match.groups())
        elif sample: p,s=map(int,sample.groups());N=2*s+1
        else: raise ValueError('unrecognized certificate name')
        target=[reduce([1,1]+pow_letter(2,-N)),
                reduce([1]+pow_letter(2,p+N)+[1]+pow_letter(2,-s)+[-1]+pow_letter(2,-p-N))]
    return [reduce([1,1]+pow_letter(2,-N)),
            reduce([1]+pow_letter(2,p)+[1]+pow_letter(2,-s)+[-1]+pow_letter(2,-p))],target


def verify(data):
    check_pins(); names=set(); totals=0
    for row in data['rows']:
        name=row['name']
        if name in names: raise ValueError('duplicate certificate')
        names.add(name);initial,target=endpoints(name)
        if row['initial_relators']!=initial or row['target_relators']!=target:
            raise ValueError('literal endpoint mismatch: '+name)
        state,peak,work=replay(initial,row['moves'])
        if state!=target: raise ValueError('independent replay failure: '+name)
        if row['multiplications']!=sum(2<=m<6 for m in row['moves']): raise ValueError('multiplication count')
        challenge={'challenge_id':name,'move_spec_version':core.MOVE_SPEC_VERSION,
                   'initial_relators':initial,'target_relators':target}
        for key,limits in (('golden_result',GOLDEN),('unlimited_result',UNLIMITED)):
            result=core.verify(challenge,row['moves'],core.MOVE_SPEC_VERSION,limits)
            if result!=row[key]: raise ValueError('official receipt differs: '+name)
        result=row['unlimited_result']
        if not result['ok'] or (result['length'],result['peak_total_relator_length'],result['work'])!=(len(row['moves']),peak,work):
            raise ValueError('independent cost mismatch')
        if name.startswith('period-') and row['multiplications']!=2: raise ValueError('period factor count')
        totals+=len(row['moves'])
    expected={'height5-residual'}|{f'height5-{p}' for p in range(-16,17)}
    expected|={f'period-{N}-{p}-{s}' for N in range(-3,4) for p in range(-3,4) for s in range(-2,3)}
    expected|={'period-example-4-5','period-example-2-6'}
    if names!=expected: raise ValueError('incomplete fixed matrix')
    return {'ok':True,'certificates':len(names),'ordinary_moves_replayed':totals,
            'literal_endpoints_anchored':True,'pinned_verifier_replay':True,
            'network_submission':False}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?',default=Path('receipts/v020/additions-replay.json'))
    args=parser.parse_args(); print(json.dumps(verify(json.loads(args.input.read_text())),indent=2))
