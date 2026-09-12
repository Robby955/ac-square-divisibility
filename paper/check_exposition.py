"""Check manuscript transcription on finite signed inputs, not prove its theorems.

Run from any directory. The quantified proofs remain in the pinned Lean files.
This script checks identities added to explain those proofs in the manuscript.
"""
from __future__ import annotations

from collections import Counter
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from witness import Compiler, X, Y, conjugate, inv, mul, power


def mapped(word, x_image, y_image):
    images = {1: x_image, -1: inv(x_image), 2: y_image, -2: inv(y_image)}
    return mul(*(images[letter] for letter in word))


def check():
    counts = Counter()

    def equal(label, actual, expected, parameters):
        if actual != expected:
            raise ValueError(f"{label} failed at {parameters}: {actual} != {expected}")
        counts[label] += 1

    def u(k):
        return power(X, k)

    def y(k):
        return power(Y, k)

    def root(p):
        return mul(y(-p), u(2), y(p), u(-1))

    def original(n, a, b, c):
        return (mul(u(-1), y(n), X, y(-n - 1)),
                mul(u(-1), y(a), X, y(b), u(-1), y(c)))

    for p in range(-3, 5):
        for s in range(-3, 5):
            params = {"p": p, "s": s}
            r0 = mul(u(-2), y(-p), X, y(-1), X, y(p))
            t0 = mul(u(-1), y(-p), X, y(s), u(-1), y(p))
            g0 = mul(y(-p), u(-1), Y, u(-1), y(p), X)
            r1 = mul(u(-1), y(-p), X, y(-s - 1), X, y(p))
            equal("entry_first_factor", mul(r0, conjugate(g0, inv(t0))), r1, params)

            r2 = mul(u(-2), y(-p), X, y(s))
            t2 = mul(u(-1), y(-p), X, y(p - s - 1), X, y(p))
            g2 = mul(y(-s), u(-1), y(p), X)
            r3 = mul(u(-1), y(-p), u(-1), y(-p + 2 * s + 1))
            equal("entry_second_factor", mul(r2, conjugate(g2, inv(t2))), r3, params)

            f = (mul(y(s + 1 - p), u(-1), y(p)), y(-1))
            fi = (mul(y(-p), u(-1), y(p - s - 1)), y(-1))
            for i, generator in enumerate((X, Y)):
                equal("basis_inverse_left", mapped(f[i], *fi), generator, params)
                equal("basis_inverse_right", mapped(fi[i], *f), generator, params)
            equal("basis_correction_forward",
                  inv(mul(conjugate(y(p - s - 1), f[0]), power(f[1], s + 1))), X, params)
            equal("basis_correction_inverse",
                  inv(mul(conjugate(y(p), fi[0]), power(fi[1], -s - 1))), X, params)

            # In the pinch notation, a=p and b=s; both signs are exercised.
            q = original(0, p, s, 0)[1]
            a0, z = mul(u(-1), y(p), X), mul(X, y(-s))
            equal("even_pinch_factor", mul(a0, conjugate(inv(z), inv(q))), z, params)
            equal("odd_pinch_factor", mul(X, y(s), u(-1), inv(q)), mul(y(-p), X), params)

            for t in (-2, 0, 3):
                before = original(2 * s + 1, p, s, -1)
                after = original(2 * s + 1, p, s, -1 - t)
                for a, b in zip(before, after):
                    equal("original_coordinate_shear",
                          conjugate(y(t), mapped(a, mul(X, y(t)), Y)), b,
                          {**params, "t": t})

        equal("basic_doubling",
              mul(conjugate(y(p), X), conjugate(mul(y(p), u(-1)), root(p))),
              u(2), {"p": p})
        for d in (1, 2, 4, 8, 16):
            v = mul(u(-1), y(p - 1), u(-d))
            q = mul(y(-p), v)
            equal("second_case_donor", mul(y(p), q), v, {"p": p, "d": d})
            equal("degree_change", mul(inv(v), u(2), v, u(-1)),
                  conjugate(u(d), root(p - 1)), {"p": p, "d": d})
            equal("second_case_companion", conjugate(y(p - 1), q),
                  mul(y(-1), u(-1), conjugate(y(p - 1), u(-d))),
                  {"p": p, "d": d})

    for g in ((), X, inv(Y), mul(u(-2), y(3))):
        for positive in (False, True):
            for slot in (0, 1):
                compiler = Compiler((X, Y))
                compiler.factor(slot, (g, positive))
                parameters = {"g": g, "positive": positive, "slot": slot}
                equal("factor_numbered_cost", len(compiler.moves),
                      2 * len(g) + 1 + 2 * (not positive), parameters)
                equal("factor_primitive_cost", compiler.proof_primitives,
                      3 if positive else 5, parameters)

    return {"ok": True, "purpose": "Finite checks of manuscript transcription only",
            "quantified_proof": "Pinned Lean development; unchanged by this revision",
            "checks": dict(sorted(counts.items())), "total": sum(counts.values())}


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
