"""Generate kernel-checkable segments of the supplied height-five certificate.

This writes proof data, not a trusted solver. Each segment is checked by Lean's
kernel through ACCertificate.checkEncodedBetween_sound. No native_decide.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

from release_additions import seed_data
from word_engine import apply_move

ROOT=Path(__file__).resolve().parent

def render_seed(chunk_size: int=8) -> str:
    initial,moves=seed_data()
    state=[list(w) for w in initial]
    def lit(value): return json.dumps(value,separators=(',',':'))
    out=['import ACSquareResidueReduction','',
         '/-! Literal residual seed for G(4,5), segmented for kernel replay. -/','',
         'namespace AC.MillerSchupp.SquareFamily.HeightFive',
         'open AC.Certificate','',
         'set_option maxRecDepth 16384','set_option maxHeartbeats 8000000','',
         'theorem seed_encoded : EncodedSteps '+lit(state)+' 1285 [[1],[2]] := by']
    blocks=[]
    for start in range(0,len(moves),chunk_size):
        segment=moves[start:start+chunk_size]; before=state
        for mid in segment: state=apply_move(state,mid)
        index=len(blocks); blocks.append(f'h{index}')
        out += [f'  have h{index} : EncodedSteps {lit(before)} {len(segment)} {lit(state)} :=',
                f'    checkEncodedBetween_sound (ids := {lit(segment)}) (ms := {lit(segment)})',
                '      (by decide +kernel) (by decide +kernel)']
    chain=blocks[0]
    for name in blocks[1:]: chain=f'({chain}.trans {name})'
    out += ['  exact '+chain,'',
            'theorem seed_steps : Steps (pair (P2.root 4) (Residual.relation 1 2)) 1285 (standard 2) := by',
            '  rcases seed_encoded with ⟨R, S, hr, hs, path⟩',
            '  have ht : parseTuple [[1],[2]] = some target := by decide +kernel',
            '  have he : S = target := Option.some.inj (hs.symm.trans ht)',
            '  subst S',
            f'  have he : denote ((parseTuple {lit([list(w) for w in initial])}).getD target) =',
            '      pair (P2.root 4) (Residual.relation 1 2) := by',
            '    ext i',
            '    fin_cases i <;> decide +kernel',
            '  rw [hr, Option.getD_some] at he',
            '  simpa only [he, denote_target] using path','',
            'theorem square_four_five : Reachable (Diagonal.generalSquare 4 5) (standard 2) := by',
            '  have h := (Residual.square_residual_iff 4 1 1).mpr seed_steps.reachable',
            '  norm_num at h ⊢',
            '  exact h','',
            'end AC.MillerSchupp.SquareFamily.HeightFive','']
    return '\n'.join(out)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
    path=ROOT/'lean/ACSquareHeightFiveSeed.lean';data=render_seed()
    if args.check:
        if not path.exists() or path.read_text()!=data: raise SystemExit('height-five Lean seed is not reproducible')
        print('height-five Lean seed: exact regeneration')
    else:
        path.write_text(data);print(path)
