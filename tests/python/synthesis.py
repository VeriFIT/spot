# -*- mode: python; coding: utf-8 -*-
# Copyright (C) by the Spot authors, see the AUTHORS file for details.
#
# This file is part of Spot, a model checking library.
#
# Spot is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# Spot is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
# or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
# License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

import spot
from unittest import TestCase
tc = TestCase()

# A shared variable caused the 2nd call to ltl_to_game to give an incorrect
# result.
for i in range(0, 2):
    gi = spot.synthesis_info()
    gi.s = spot.synthesis_info.algo_LAR
    game = spot.ltl_to_game("(Ga) <-> (Fb)", ["b"], gi)
    tc.assertFalse(spot.solve_game(game))

# A game can have only inputs
game_ref = spot.automaton("""HOA: v1
States: 3
Start: 0
AP: 1 "a"
acc-name: Buchi
Acceptance: 1 Inf(0)
properties: trans-labels explicit-labels trans-acc complete
properties: deterministic
spot-state-player: 0 1 1
controllable-AP:
--BODY--
State: 0
[!0] 1
[0] 2 {0}
State: 1
[t] 0
State: 2
[t] 0 {0}
--END--""")

gi = spot.synthesis_info()
gi.dict = game_ref.get_dict()

game = spot.ltl_to_game("GFa", [], gi)

tc.assertTrue(spot.are_equivalent(game, game_ref))

# The synthesis_problem class, with the simplification stages disabled so
# that the decomposition really happens (as in the ltlsynt regression
# tests of item 1 of the report in issue #665).
def no_simplification():
    si = spot.synthesis_info()
    si.use_bypass = False
    si.polarity = spot.synthesis_info.simplification_stage_never
    si.global_equiv = spot.synthesis_info.simplification_stage_never
    return si

# In both specifications below the negation of the assumptions is
# realizable, so the specification is realizable by violating the
# assumptions.  Before the fix, the decomposition reported them as
# unrealizable.
for f, ins, outs in [
        ("(G(i -> o1) & G(o2 <-> j)) -> (G(i & o1) & F o2)",
         ["i", "j"], ["o1", "o2"]),
        ("(GF(p & (x->q)) & GF!(p & (x->q))) -> (X false & G(q->p))",
         ["x"], ["p", "q"])]:
    pr = spot.synthesis_problem(spot.formula(f), ins, outs, [],
                                no_simplification())
    tc.assertTrue(pr.is_realizable())
    tc.assertTrue(pr.assumptions_violated())
    # The pre-check solves the negation of the assumptions, so there is
    # no sub-specification to report.
    tc.assertEqual(len(pr.sub_specifications()), 0)
    tc.assertEqual(len(pr.sub_outputs()), 0)
    st = pr.strategy()
    tc.assertIsNotNone(st)
    # The strategy falsifies the assumptions, so it does not intersect
    # the negated specification.
    pr.verify_strategy()
    circuit = pr.aig("ite")
    tc.assertIsNotNone(circuit)
    pr.verify_aig(circuit)
    tc.assertIsNotNone(pr.statistics())

# The pre-check is only performed when the specification is decomposed.
# Without decomposition the ordinary solver is used, so the problem is
# reported as a single sub-specification, but the flag stays accurate:
# the strategy it returns still violates the assumptions.
si = no_simplification()
si.decompose = False
pr = spot.synthesis_problem(
    spot.formula("(GF(p & (x->q)) & GF!(p & (x->q))) -> "
                 "(X false & G(q->p))"),
    ["x"], ["p", "q"], [], si)
tc.assertTrue(pr.is_realizable())
tc.assertTrue(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 1)
tc.assertIsNotNone(pr.strategy())
pr.verify_strategy()

# A single conjunct never triggers the pre-check, yet the flag must
# report the strategy violating the assumptions: X false is only
# realizable by falsifying G(o1 <-> j).
pr = spot.synthesis_problem(spot.formula("G(o1 <-> j) -> X false"),
                            ["j"], ["o1"], [], no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertTrue(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 1)
tc.assertIsNotNone(pr.strategy())
pr.verify_strategy()

# Here the negation of the assumptions is not realizable, because i is
# an input and the specification cannot force it to be false.  The
# pre-check must decline, no strategy can violate the assumptions, and
# the usual strategy must be returned.
pr = spot.synthesis_problem(spot.formula("G(i) -> G(o1)"), ["i"], ["o1"],
                            [], no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertFalse(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 1)
tc.assertEqual(list(pr.sub_outputs()[0]), ["o1"])
tc.assertEqual(len(pr.games()), 1)
tc.assertTrue(pr.decompose())
pr.verify_strategy()

# The fine-tuning options are set on the problem itself, and are
# frozen as soon as a service has run.
pr = spot.synthesis_problem(spot.formula("G(i -> o)"), ["i"], ["o"])
tc.assertEqual(pr.algo(), spot.synthesis_info.algo_LAR)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Mealy)
pr.set_algo(spot.synthesis_info.algo_DPA_SPLIT)
pr.set_semantics(spot.synthesis_semantics_Moore)
pr.set_decompose(False)
tc.assertEqual(pr.algo(), spot.synthesis_info.algo_DPA_SPLIT)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Moore)
tc.assertFalse(pr.decompose())
tc.assertIsNotNone(pr.aig("ite"))
tc.assertRaises(RuntimeError, pr.set_semantics,
                spot.synthesis_semantics_Mealy)

# The proposition lists are read like ltlsynt's --ins and --outs: each
# element is either a name or a /regex/, None means the list was not
# specified, and the side that is not specified is inferred.
f = spot.formula("G(i1 <-> X o1)")
circuit = spot.synthesis_problem(f, ["i1"], ["o1"]).aig("ite")
tc.assertIsNotNone(circuit)
for ins, outs in [(["i1"], None),        # o1 is inferred to be output
                  (None, ["o1"]),        # i1 is inferred to be input
                  (["/^i/"], None)]:     # regex matching i1
    pr = spot.synthesis_problem(f, ins, outs)
    tc.assertEqual(pr.aig("ite").to_str(), circuit.to_str())

# When no list is given, propositions are classified by their first
# letter, as in ltlsynt.
tc.assertTrue(spot.synthesis_problem(spot.formula("G(i <-> X o)")
                                     ).is_realizable())

# An empty list is not an unspecified one: with an empty input list and
# an output list, the outputs must cover the whole specification.
tc.assertRaises(ValueError, spot.synthesis_problem, f, [], ["o1"])
# With an empty input list and no output list, the outputs are
# inferred, so the x of G(x) is an output (as with --ins=), and the
# specification is realizable.
tc.assertIsNotNone(spot.synthesis_problem(spot.formula("G(x)"),
                                          [], None).aig("ite"))
# With an empty output list and no input list, x is an input (as with
# --outs=), and the specification is unrealizable.
tc.assertIsNone(spot.synthesis_problem(spot.formula("G(x)"),
                                       None, []).aig("ite"))

# A proposition cannot belong to both sides, and both sides together
# must cover the specification.
for spec, ins, outs, unobs in [
        # p matches no list, although both are given
        ("G(i <-> X (o & p))", ["i"], ["o"], None),
        # o is listed in both
        ("G(o)", ["i", "o"], ["o"], None),
        # every proposition matches both patterns
        ("G(i -> o)", ["/./"], ["/./"], None),
        # u matches the unobservable and the output patterns
        ("G(u -> i)", None, ["/u/"], ["/u/"]),
        ]:
    tc.assertRaises(ValueError, spot.synthesis_problem,
                    spot.formula(spec), ins, outs, unobs)

# Without any list, a proposition whose first letter says nothing is
# ambiguous.
tc.assertRaises(ValueError, spot.synthesis_problem,
                spot.formula("G(p <-> X q)"))

# Unobservable inputs are also inputs, but they are declared apart; the
# side that is not specified is still inferred.
for ins in (["i"], None):
    pr = spot.synthesis_problem(spot.formula("G((i & u) -> o)"),
                                ins, ["o"], ["u"])
    tc.assertTrue(pr.is_realizable())
