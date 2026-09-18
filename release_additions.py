"""Ordinary certificate constructors for the v0.2 square-family additions.

The original arithmetic exporter and proof-source files are not modified.
This module adds the residual seed, complete signed height-five paths, and
literal two-factor period paths. All outputs use the pinned ac-r2-v1 table.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Iterable

from experiment import GOLDEN, UNLIMITED, check_pins, construct, evaluate, square
from official_verifier import core
from root_constructor import apply_route, companion, iterated, map_concrete, replace, root
from witness import Compiler, Witness, X, Y, inv, mul, power

ROOT = Path(__file__).resolve().parent
SEED = ROOT / "certificates/G4_5_residual_letter.json"


def translate_letter_certificate(data: dict) -> tuple[tuple[tuple[int, ...], ...], list[int]]:
    alphabet = {"u": 1, "U": -1, "y": 2, "Y": -2}
    if data.get("schema") != "ordinary-ac-letter-v1":
        raise ValueError("unexpected source certificate schema")
    if data.get("input") != ["YYYYuuyyyyU", "YYUyUU"] or data.get("endpoint") != ["u", "y"]:
        raise ValueError("the height-five seed must have its specified literal endpoints")
    result = []
    for item in data["moves"]:
        slot = item.get("slot")
        if type(slot) is not int or slot not in (0, 1):
            raise ValueError("invalid relator slot")
        op = item.get("op")
        if op == "invert" and set(item) == {"op", "slot"}:
            result.append(slot)
        elif op == "multiply" and set(item) == {"op", "slot"}:
            result.append(2 + 2 * slot)
        elif op == "conjugate" and set(item) == {"op", "slot", "letter"}:
            if item["letter"] not in alphabet:
                raise ValueError("invalid conjugating letter")
            result.append(6 + 4 * slot + (1, -1, 2, -2).index(alphabet[item["letter"]]))
        else:
            raise ValueError("unexpected ordinary operation")
    initial = tuple(tuple(alphabet[a] for a in w) for w in data["input"])
    return initial, result


def seed_data() -> tuple[tuple[tuple[int, ...], ...], list[int]]:
    return translate_letter_certificate(json.loads(SEED.read_text()))


def apply_ids(c: Compiler, ids: Iterable[int], fx=X, fy=Y) -> None:
    """Transport numbered ordinary moves through an explicit homomorphism."""
    for move in ids:
        if type(move) is not int or not 0 <= move < 14:
            raise ValueError("invalid ordinary move id")
        if move < 2:
            c.invert(move)
        elif move < 6:
            c.zpow((move - 2) // 2, -1 if move % 2 else 1)
        else:
            slot, j = divmod(move - 6, 4)
            c.conj(slot, (fx, inv(fx), fy, inv(fy))[j])


def reverse_ids(ids: Iterable[int]) -> list[int]:
    return [core.INVERSE_MOVE[i] for i in reversed(list(ids))]


def residual_root_finish() -> Compiler:
    """A complete path from (B_4,A_5), including the new residual seed."""
    c = Compiler((root(4), companion(5)))
    c.conj(1, power(Y, 4))
    prefix = mul(power(Y, -2), inv(X), Y)
    w = Witness.refl(prefix).product(iterated(4, 1).inverse())
    replace(c, 1, w)
    initial, ids = seed_data()
    if c.state != initial:
        raise ValueError("the residual transport did not reach the seed")
    apply_ids(c, ids)
    if c.state != (X, Y):
        raise ValueError("residual seed did not finish at the basis")
    return c


def root_zero_finish(s: int) -> Compiler:
    c = Compiler((root(0), companion(s)))
    kill = Witness(inv(X), (), (((), True),))
    w = (Witness.refl(power(Y, -s-1)).product(kill)
         .product(Witness.refl(power(Y, s))).product(kill))
    replace(c, 1, w)
    c.invert(1)
    if c.state != (X, Y):
        raise ValueError("zero-degree root finish failed")
    return c


def lift_root_finish(p: int, s: int, rc: Compiler) -> Compiler:
    """Use the original affine entry and supply its ordinary basis correction."""
    c = Compiler(square(p, s))
    entry = json.loads((ROOT / "entry_route.json").read_text())
    apply_route(c, entry["route"], lambda w: evaluate(w, p, s))
    fx, fy = mul(power(Y, s+1-p), inv(X), power(Y, p)), inv(Y)
    image = lambda w: map_concrete(w, fx, fy)
    if c.state != tuple(image(w) for w in (root(p), companion(s))):
        raise ValueError("affine entry endpoint mismatch")
    apply_ids(c, rc.moves, fx, fy)
    if c.state != (fx, fy):
        raise ValueError("transported root solution did not reach its image basis")
    c.conj(0, power(Y, p-s-1))
    c.zpow(0, s+1)
    c.invert(0)
    c.invert(1)
    if c.state != (X, Y):
        raise ValueError("basis correction failed")
    return c


def period(p: int, s: int, N: int | None = None) -> Compiler:
    """Literal (S_N,T_{p,s}) -> (S_N,T_{p+N,s}), two multiplications."""
    if any(type(v) is not int for v in (p, s)) or (N is not None and type(N) is not int):
        raise ValueError("integer parameters required")
    if N is None:
        N = 2*s+1
    initial = (mul(power(X, 2), power(Y, -N)), square(p, s)[1])
    c = Compiler(initial)
    W = mul(power(Y, p), X, power(Y, -s), inv(X), power(Y, -p-N))
    g1 = mul(inv(W), inv(X), power(Y, -N))
    g2 = mul(inv(W), power(Y, -N))
    c.conj(1, power(Y, N))
    c.factor(1, (g1, True))
    c.factor(1, (g2, False))
    target = (initial[0], square(p+N, s)[1])
    if c.state != target or c.proof_primitives != 9:
        raise ValueError("two-factor period identity failed")
    if sum(2 <= i < 6 for i in c.moves) != 2:
        raise ValueError("period must contain two multiplications")
    return c


def mirror_negative(p: int, s: int) -> Compiler:
    N = 2*s+1
    mirror = mul(X, power(Y,p), X, power(Y,-p), inv(X), power(Y,-s))
    c = Compiler((mul(power(X,2), power(Y,-N)), mirror))
    c.conj(1, inv(mul(X,power(Y,p))))
    c.factor(1, (mul(power(Y,-p), inv(X), power(Y,s)), True))
    c.factor(1, (mul(power(Y,-p), inv(X)), False))
    if c.state != square(-p,s):
        raise ValueError("mirror-to-negative transport failed")
    return c


def representative(p: int) -> Compiler:
    if not -5 <= p <= 5:
        raise ValueError("representative must be in [-5,5]")
    if p == 0:
        return lift_root_finish(0,5,root_zero_finish(5))
    if p == 4:
        return lift_root_finish(4,5,residual_root_finish())
    if p > 0:
        return construct(p,5)[1]
    a, s, N = -p, 5, 11
    positive = representative(a)
    c = Compiler(square(p,s))
    apply_ids(c, reverse_ids(mirror_negative(a,s).moves))
    c.invert(0)
    c.conj(0, power(Y,-N))
    c.invert(1)
    c.conj(1, inv(mul(X,power(Y,a),X)))
    expected = tuple(map_concrete(w,inv(X),inv(Y)) for w in square(a,s))
    if c.state != expected:
        raise ValueError("mirror inversion endpoint mismatch")
    apply_ids(c, positive.moves, inv(X), inv(Y))
    c.invert(0)
    c.invert(1)
    if c.state != (X,Y):
        raise ValueError("negative-degree basis correction failed")
    return c


def height_five(p: int) -> Compiler:
    if type(p) is not int:
        raise ValueError("degree must be an integer, excluding booleans")
    residue = (p+5) % 11 - 5
    c = Compiler(square(p,5))
    current = p
    while current > residue:
        apply_ids(c,reverse_ids(period(current-11,5).moves))
        current -= 11
    while current < residue:
        apply_ids(c,period(current,5).moves)
        current += 11
    if c.state != square(residue,5):
        raise ValueError("period reduction failed")
    apply_ids(c,representative(residue).moves)
    if c.state != (X,Y):
        raise ValueError("height-five path has not reached the basis")
    return c


def checked_record(name: str, initial, c: Compiler) -> dict:
    challenge = {"challenge_id":name,"move_spec_version":core.MOVE_SPEC_VERSION,
                 "initial_relators":initial,"target_relators":c.state}
    unlimited = core.verify(challenge,c.moves,core.MOVE_SPEC_VERSION,UNLIMITED)
    golden = core.verify(challenge,c.moves,core.MOVE_SPEC_VERSION,GOLDEN)
    if not unlimited["ok"]:
        raise ValueError(f"pinned verifier rejected {name}: {unlimited}")
    return {"name":name,"initial_relators":initial,"target_relators":c.state,
            "moves":c.moves,"multiplications":sum(2<=i<6 for i in c.moves),
            "mathematical_primitive_schedule":c.proof_primitives,
            "unlimited_result":unlimited,"golden_result":golden}


def benchmark() -> dict:
    check_pins()
    initial, ids = seed_data()
    c = Compiler(initial)
    apply_ids(c,ids)
    rows = [checked_record("height5-residual",initial,c)]
    rows += [checked_record(f"height5-{p}",square(p,5),height_five(p)) for p in range(-16,17)]
    for N in range(-3,4):
        for p in range(-3,4):
            for s in range(-2,3):
                initial = (mul(power(X,2),power(Y,-N)),square(p,s)[1])
                rows.append(checked_record(f"period-{N}-{p}-{s}",initial,period(p,s,N)))
    for p,s in [(4,5),(2,6)]:
        rows.append(checked_record(f"period-example-{p}-{s}",square(p,s),period(p,s)))
    return {"claim":"Finite exact replay, not a quantified proof or a competition submission.",
            "base_commit":"16fd2c61570161f5fb5856d2e1d5c7fd67ee3a34",
            "source_seed_sha256":hashlib.sha256(SEED.read_bytes()).hexdigest(),
            "move_spec_version":core.MOVE_SPEC_VERSION,"rows":rows,
            "summary":{"cases":len(rows),"height5_complete_paths":33,"residual_paths":1,
                       "period_paths":247,"unlimited_passes":sum(r['unlimited_result']['ok'] for r in rows),
                       "golden_passes":sum(r['golden_result']['ok'] for r in rows)}}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    choose=parser.add_mutually_exclusive_group(required=True)
    choose.add_argument("--matrix",action="store_true")
    choose.add_argument("--height5",type=int,metavar="P")
    parser.add_argument("--allow-large",action="store_true")
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    try:
        check_pins()
        if args.matrix:
            result=benchmark()
        else:
            if abs(args.height5)>100 and not args.allow_large:
                parser.error("|P|>100 requires --allow-large; expanded paths may be large")
            result=checked_record(f"height5-{args.height5}",square(args.height5,5),height_five(args.height5))
    except (ValueError,KeyError) as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n")
    print(json.dumps(result.get("summary",{k:v for k,v in result.items() if k!='moves'}),indent=2))

if __name__=="__main__":
    main()
