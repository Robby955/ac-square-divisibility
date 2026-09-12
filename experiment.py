"""Construct ordinary AC paths for the proved divisibility subfamilies.

The numbered paths are replayed by unchanged, pinned SAIR verifier sources.
This program measures a witness construction, not shortest paths or new solves.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform
import time

from official_verifier import core
from root_constructor import (RecordingCompiler, apply_route, companion, map_concrete,
                              root, root_constructor)
from witness import Compiler, X, Y, inv, mul, power

HERE = Path(__file__).resolve().parent
GOLDEN = {"max_path_length": 100000, "max_total_relator_length": 10000, "max_work": 5000000}
UNLIMITED = {key: float("inf") for key in GOLDEN}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_pins() -> None:
    provenance = json.loads((HERE / "SOURCE_PROVENANCE.json").read_text())
    for name in ("core.py", "canon.py"):
        actual = digest((HERE / "official_verifier" / name).read_bytes())
        expected = provenance["source_sha256"][f"official/competition/tools/verifier/{name}"]
        if actual != expected:
            raise ValueError(f"Official source pin mismatch: {name}")


def evaluate(word, p: int, s: int):
    return mul(*(power(X if gen == "u" else Y, c + a*p + b*s)
                 for gen, (c, a, b) in word))


def square(p: int, s: int):
    return (mul(power(X, 2), power(Y, -2*s-1)),
            mul(X, power(Y, p), X, power(Y, -s), inv(X), power(Y, -p)))


def construct(p: int, s: int):
    if type(p) is not int or type(s) is not int or min(p, s) < 0:
        raise ValueError("p and s must be natural numbers, excluding booleans")
    if (p == 0 and s != 0) or (p > 0 and s % p not in (0, p-1)):
        raise ValueError("This constructor requires p dividing s or s+1")
    c = Compiler(square(p, s))
    entry = json.loads((HERE / "entry_route.json").read_text())
    apply_route(c, entry["route"], lambda w: evaluate(w, p, s))
    fx, fy = mul(power(Y, s+1-p), inv(X), power(Y, p)), inv(Y)
    image = lambda w: map_concrete(w, fx, fy)
    if c.state != tuple(image(w) for w in (root(p), companion(s))):
        raise ValueError("Entry endpoint does not match the supplied basis map")
    if p == 0:
        rc = RecordingCompiler((root(0), companion(0)))
        rc.zpow(1, 2)
        rc.invert(1)
    else:
        rc = root_constructor(s, p)
    if rc.state != (X, Y):
        raise ValueError("Root finish failed")
    apply_route(c, rc.route, image)
    if c.state != (fx, fy):
        raise ValueError("Transported path did not reach its image basis")
    c.conj(0, power(Y, p-s-1))
    c.zpow(0, s+1)
    c.invert(0)
    c.invert(1)
    if c.state != (X, Y):
        raise ValueError("Complete path did not reach the exact standard tuple")
    return square(p, s), c


def replay(initial, path, name, limits):
    challenge = {"challenge_id": name, "move_spec_version": core.MOVE_SPEC_VERSION,
                 "initial_relators": initial, "target_relators": [[1], [2]]}
    return core.verify(challenge, path, core.MOVE_SPEC_VERSION, limits)


def measure(p: int, s: int):
    began = time.perf_counter()
    initial, c = construct(p, s)
    build_seconds = time.perf_counter() - began
    began = time.perf_counter()
    golden = replay(initial, c.moves, f"square-{p}-{s}", GOLDEN)
    unlimited = golden if golden["ok"] else replay(initial, c.moves, f"square-{p}-{s}", UNLIMITED)
    return {"p": p, "s": s, "initial_relators": initial, "path": c.moves,
            "numbered_moves": len(c.moves), "primitive_counter": c.proof_primitives,
            "path_sha256": digest(json.dumps(c.moves, separators=(",", ":")).encode()),
            "golden_result": golden, "unlimited_result": unlimited,
            "build_seconds": build_seconds, "replay_seconds": time.perf_counter()-began}


def benchmark(cases):
    check_pins()
    rows = [measure(p, s) for p, s in cases]
    constructed = {(row["p"], row["s"]): row for row in rows}
    comparisons = []
    for saved in json.loads((HERE / "frozen_comparisons.json").read_text())["cases"]:
        key = saved["p"], saved["s"]
        if key not in constructed:
            continue
        result = replay(square(*key), saved["path"], f"frozen-{key[0]}-{key[1]}", GOLDEN)
        if not result["ok"]:
            raise ValueError("A frozen baseline failed official replay")
        comparisons.append({"p": key[0], "s": key[1], "frozen_length": len(saved["path"]),
                            "constructed_length": constructed[key]["numbered_moves"],
                            "frozen_official_result": result})
    if not all(row["unlimited_result"]["ok"] for row in rows):
        raise ValueError("A constructed path failed unlimited official replay")
    return {"claim": "Finite measurements of a proved uniform construction; no shortestness claim.",
            "python": platform.python_version(), "platform": platform.platform(),
            "move_spec_version": core.MOVE_SPEC_VERSION, "limits": GOLDEN,
            "unlimited_policy": "All three limits set to positive infinity inside the verifier.",
            "rows": rows, "comparisons": comparisons,
            "summary": {"cases": len(rows), "golden_passes": sum(r["golden_result"]["ok"] for r in rows),
                        "unlimited_passes": sum(r["unlimited_result"]["ok"] for r in rows),
                        "build_seconds": sum(r["build_seconds"] for r in rows),
                        "replay_seconds": sum(r["replay_seconds"] for r in rows),
                        "frozen_overlaps": len(comparisons),
                        "shorter_paths_on_overlaps": sum(r["constructed_length"] < r["frozen_length"]
                                                         for r in comparisons)}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", action="store_true", help="Run the fixed 50-case validation matrix")
    parser.add_argument("--p", type=int)
    parser.add_argument("--s", type=int)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.matrix:
        if args.p is not None or args.s is not None:
            parser.error("Choose --matrix or --p and --s")
        cases = sorted({(0, 0)} | {(2, s) for s in range(13)} |
                       {(p, p*m+r) for p in range(1, 7) for m in range(4) for r in (0, p-1)})
    else:
        if args.p is None or args.s is None:
            parser.error("Provide --matrix or both --p and --s")
        if not 0 <= args.p <= 100 or not 0 <= args.s <= 100 or (args.p and args.s // args.p > 8):
            parser.error("This finite exporter accepts p,s in 0..100 and quotient at most 8")
        cases = [(args.p, args.s)]
    try:
        receipt = benchmark(cases)
    except ValueError as error:
        parser.error(str(error))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, allow_nan=False) + "\n")
    print(json.dumps(receipt["summary"], indent=2))


if __name__ == "__main__":
    main()
