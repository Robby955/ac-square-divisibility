"""Boundary, donor preservation, move semantics and frozen-path regression tests."""
import json
from pathlib import Path
import unittest

import experiment as e
from official_verifier import core
from root_constructor import apply_route, companion, iterated, map_concrete, root
from witness import Compiler, Witness, X, Y, conjugate, inv, mul, power
import word_engine


class ProofExportTests(unittest.TestCase):
    def test_all_move_ids_match_official(self):
        for state in (((1, 2, -1), (2, 1, -2)), ((), (1,)), ((-2, -1), (2, 2))):
            for move in range(14):
                ours = tuple(map(tuple, word_engine.apply_move(list(map(list, state)), move)))
                self.assertEqual(ours, core.apply_move(state, move))

    def test_affine_entry_arbitrary_integers(self):
        entry = json.loads((e.HERE / "entry_route.json").read_text())
        for p in (-3, 0, 1, 2, 5):
            for s in (-4, -1, 0, 3, 6):
                c = Compiler(e.square(p, s))
                apply_route(c, entry["route"], lambda w: e.evaluate(w, p, s))
                fx, fy = mul(power(Y, s+1-p), inv(X), power(Y, p)), inv(Y)
                self.assertEqual(c.state, tuple(map_concrete(w, fx, fy) for w in (root(p), companion(s))))
                self.assertEqual(c.proof_primitives, 61)

    def test_iterated_witness_identity_and_count(self):
        for p in (-2, 0, 1, 3):
            for m in range(6):
                w = iterated(p, m)
                w.verify(root(p))
                self.assertEqual(w.source, conjugate(power(Y, p*m), X))
                self.assertEqual(w.target, power(X, 2**m))
                self.assertEqual(len(w.factors), 2**m-1)

    def test_corrupt_witness_rejected(self):
        good = iterated(3, 2)
        with self.assertRaises(ValueError):
            Witness(good.source, good.target, good.factors[:-1]).verify(root(3))

    def test_factor_restores_donor(self):
        for slot in (0, 1):
            for sign in (False, True):
                c = Compiler((mul(X, Y), mul(inv(Y), X)))
                original = c.state
                c.factor(slot, (mul(Y, X), sign))
                self.assertEqual(c.state[1-slot], original[1-slot])
                self.assertEqual(c.state[slot], mul(original[slot], conjugate(mul(Y, X),
                                 original[1-slot] if sign else inv(original[1-slot]))))

    def test_input_boundaries(self):
        for p, s in ((True, 0), (1, False), (-1, 0), (1, -1), (0, 1), (3, 4), (4, 6)):
            with self.assertRaises(ValueError):
                e.construct(p, s)
        for p, s in ((0, 0), (1, 0), (2, 0), (3, 5), (3, 6), (6, 23)):
            initial, c = e.construct(p, s)
            self.assertEqual(c.state, (X, Y))
            self.assertTrue(e.replay(initial, c.moves, f"boundary-{p}-{s}", e.GOLDEN)["ok"])

    def test_paths_match_recorded_source(self):
        for row in json.loads((e.HERE / "construction_regression.json").read_text())["cases"]:
            _, c = e.construct(row["p"], row["s"])
            actual = e.digest(json.dumps(c.moves, separators=(",", ":")).encode())
            self.assertEqual(actual, row["path_sha256"])
            self.assertEqual(len(c.moves), row["numbered_moves"])

    def test_missing_last_move_fails(self):
        initial, c = e.construct(2, 3)
        self.assertFalse(e.replay(initial, c.moves[:-1], "truncated", e.GOLDEN)["ok"])

    def test_official_pins(self):
        e.check_pins()


if __name__ == "__main__":
    unittest.main()
