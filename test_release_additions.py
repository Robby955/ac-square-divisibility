"""Independent regression tests for the release additions and input boundaries."""
from copy import deepcopy
import json
from pathlib import Path
import unittest

import release_additions as add
from experiment import GOLDEN, check_pins, square
from official_verifier import core
from witness import Compiler, X, Y


from independent_release_replay import replay


class ReleaseAdditionsTests(unittest.TestCase):
    def test_source_pins(self):
        check_pins()

    def test_seed_literal_endpoint_and_counts(self):
        initial, ids = add.seed_data()
        state, peak, work = replay(initial,ids)
        self.assertEqual(state,[[1],[2]])
        self.assertEqual((len(ids),sum(2<=m<6 for m in ids),peak,work),(1285,63,263,152018))

    def test_seed_parser_rejects_corrupt_fields(self):
        original=json.loads(add.SEED.read_text())
        changes=[('schema','wrong'),('input',['u','y']),('endpoint',['y','u'])]
        for key,value in changes:
            with self.subTest(key=key):
                data=deepcopy(original);data[key]=value
                with self.assertRaises(ValueError): add.translate_letter_certificate(data)
        for change in ({'slot':True},{'op':'automorphism'},{'unused':'field'}):
            data=deepcopy(original);data['moves'][0].update(change)
            with self.assertRaises(ValueError): add.translate_letter_certificate(data)

    def test_seed_mutation_fails_replay(self):
        initial,ids=add.seed_data(); altered=ids+[0]
        self.assertNotEqual(replay(initial,altered)[0],[[1],[2]])
        challenge={'challenge_id':'negative-seed','move_spec_version':core.MOVE_SPEC_VERSION,
                   'initial_relators':initial,'target_relators':[[1],[2]]}
        self.assertFalse(core.verify(challenge,altered,core.MOVE_SPEC_VERSION,GOLDEN)['ok'])

    def test_complete_height_five_residue_system(self):
        for p in range(-5,6):
            with self.subTest(p=p):
                c=add.height_five(p); state,_,_=replay(square(p,5),c.moves)
                self.assertEqual(state,[[1],[2]])

    def test_signed_period_lifts(self):
        for p in (-16,-15,15,16):
            with self.subTest(p=p):
                c=add.height_five(p)
                self.assertEqual(replay(square(p,5),c.moves)[0],[[1],[2]])

    def test_period_signed_identity_and_counts(self):
        for N,p,s in ((-3,-2,1),(0,0,0),(5,2,-3),(11,4,5),(13,2,6)):
            with self.subTest(N=N,p=p,s=s):
                c=add.period(p,s,N)
                initial=(add.mul(add.power(X,2),add.power(Y,-N)),square(p,s)[1])
                self.assertEqual(replay(initial,c.moves)[0],[list(initial[0]),list(square(p+N,s)[1])])
                self.assertEqual(c.proof_primitives,9)
                self.assertEqual(sum(2<=m<6 for m in c.moves),2)

    def test_period_named_example(self):
        c=add.period(4,5)
        state,peak,work=replay(square(4,5),c.moves)
        self.assertEqual(state,[list(w) for w in square(15,5)])
        self.assertEqual((len(c.moves),peak,work),(165,105,10661))

    def test_ordinary_homomorphism_transport(self):
        initial,ids=add.seed_data(); c=Compiler(tuple(add.map_concrete(w,add.inv(X),add.inv(Y)) for w in initial))
        add.apply_ids(c,ids,add.inv(X),add.inv(Y));c.invert(0);c.invert(1)
        self.assertEqual(replay(tuple(add.map_concrete(w,add.inv(X),add.inv(Y)) for w in initial),c.moves)[0],[[1],[2]])

    def test_reverse_path(self):
        p=add.period(4,5)
        self.assertEqual(replay(p.state,add.reverse_ids(p.moves))[0],[list(w) for w in square(4,5)])

    def test_parameter_and_move_validation(self):
        for value in (True,1.0,'4',None):
            with self.assertRaises(ValueError): add.height_five(value)
        for args in ((True,1,None),(1,False,None),(1,1,False)):
            with self.assertRaises(ValueError): add.period(*args)
        for bad in (True,-1,14,'2'):
            with self.assertRaises(ValueError): add.apply_ids(Compiler((X,Y)),[bad])

    def test_generated_lean_matches_data(self):
        from generate_release_lean import render_seed
        self.assertEqual((Path(__file__).parent/'lean/ACSquareHeightFiveSeed.lean').read_text(),render_seed())

if __name__=='__main__': unittest.main()
