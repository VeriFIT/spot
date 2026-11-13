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

import tempfile

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
si.decompose = spot.synthesis_info.decomposition_none
pr = spot.synthesis_problem(
    spot.formula("(GF(p & (x->q)) & GF!(p & (x->q))) -> "
                 "(X false & G(q->p))"),
    ["x"], ["p", "q"], [], si)
tc.assertTrue(pr.is_realizable())
tc.assertTrue(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 1)
tc.assertIsNotNone(pr.strategy())
pr.verify_strategy()

# A top-level implication is a disjunction: its negation is solved
# first, so X false is not even reached, and the strategy violating
# G(o1 <-> j) is accepted.  The flag is established by the
# disjunctive decomposition, without the conjunctive pre-check.
pr = spot.synthesis_problem(spot.formula("G(o1 <-> j) -> X false"),
                            ["j"], ["o1"], [], no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertTrue(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 0)
tc.assertIsNotNone(pr.strategy())
pr.verify_strategy()

# Here the negation of the assumptions is not realizable, because i is
# an input and the specification cannot force it to be false.  The
# disjunctive decomposition then finds a strategy for G(o1), which
# satisfies the implication whether or not the assumption holds.
pr = spot.synthesis_problem(spot.formula("G(i) -> G(o1)"), ["i"], ["o1"],
                            [], no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertFalse(pr.assumptions_violated())
tc.assertEqual(len(pr.sub_specifications()), 0)
tc.assertEqual(len(pr.sub_outputs()), 0)
tc.assertEqual(len(pr.games()), 1)
tc.assertEqual(pr.decompose(), spot.synthesis_info.decomposition_all)
pr.verify_strategy()

# The fine-tuning options are set on the problem itself, and are
# frozen as soon as a service has run.
pr = spot.synthesis_problem(spot.formula("G(i -> o)"), ["i"], ["o"])
tc.assertEqual(pr.algo(), spot.synthesis_info.algo_LAR)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Mealy)
pr.set_algo(spot.synthesis_info.algo_DPA_SPLIT)
pr.set_semantics(spot.synthesis_semantics_Moore)
pr.set_decompose(spot.synthesis_info.decomposition_none)
tc.assertEqual(pr.algo(), spot.synthesis_info.algo_DPA_SPLIT)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Moore)
tc.assertEqual(pr.decompose(),
               spot.synthesis_info.decomposition_none)
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

# Building a synthesis_problem from TLSF.  The factory parses and
# translates the specification, uses its INPUTS/OUTPUTS declarations
# unless they are overridden, and takes the controller model from
# TARGET.
tlsf_simple = """INFO {
  TITLE:       "tlsf test"
  DESCRIPTION: "used by tests/python/synthesis.py"
  SEMANTICS:   Mealy
  TARGET:      Mealy
}
GLOBAL {
  PARAMETERS {}
}
MAIN {
  INPUTS  { i; }
  OUTPUTS { o; }
  ASSUME  { G(i); }
  GUARANTEE { G(F(o)); }
}
"""

pr = spot.synthesis_problem.from_tlsf_string(tlsf_simple)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Mealy)
pr.set_algo(spot.synthesis_info.algo_DPA_SPLIT)
tc.assertEqual(pr.algo(), spot.synthesis_info.algo_DPA_SPLIT)
tc.assertTrue(pr.is_realizable())
tc.assertIsNotNone(pr.strategy())

# from_tlsf() reads the same specification from a file.
with tempfile.NamedTemporaryFile('w', dir='.', suffix='.tlsf',
                                 delete=True) as fp:
    fp.write(tlsf_simple)
    fp.flush()
    pr = spot.synthesis_problem.from_tlsf(fp.name)
    tc.assertTrue(pr.is_realizable())

# The partition declared by the file is used by default; overriding
# it as empty inputs plus two outputs makes the specification
# realizable.
tlsf_partition = """INFO {
  TITLE:       "tlsf test"
  DESCRIPTION: "used by tests/python/synthesis.py"
  SEMANTICS:   Mealy
  TARGET:      Mealy
}
GLOBAL {
  PARAMETERS {}
}
MAIN {
  INPUTS  { i; }
  OUTPUTS { o; }
  GUARANTEE { G(i) && G(o); }
}
"""
tc.assertFalse(spot.synthesis_problem.from_tlsf_string(
    tlsf_partition).is_realizable())
pr = spot.synthesis_problem.from_tlsf_string(tlsf_partition, None, [],
                                             ["i", "o"])
tc.assertTrue(pr.is_realizable())

# TARGET selects the controller model, as in ltlsynt.
tlsf_moore = """INFO {
  TITLE:       "tlsf test"
  DESCRIPTION: "used by tests/python/synthesis.py"
  SEMANTICS:   Moore
  TARGET:      Moore
}
GLOBAL {
  PARAMETERS {}
}
MAIN {
  INPUTS  { i; }
  OUTPUTS { o; }
  ASSUME  { G(i); }
  GUARANTEE { G(F(o)); }
}
"""
pr = spot.synthesis_problem.from_tlsf_string(tlsf_moore)
tc.assertEqual(pr.semantics(), spot.synthesis_semantics_Moore)
tc.assertTrue(pr.is_realizable())

# The parameter overrides reach both the parser (bus width) and the
# translator (index in the formula).
tlsf_param = """INFO {
  TITLE:       "tlsf test"
  DESCRIPTION: "used by tests/python/synthesis.py"
  SEMANTICS:   Mealy
  TARGET:      Mealy
}
GLOBAL {
  PARAMETERS { N = 2; }
}
MAIN {
  INPUTS  { event[N]; }
  OUTPUTS { done; }
  ASSUME  { G(event[N - 1]); }
  GUARANTEE { G(done); }
}
"""
for overrides, expected, unexpected in [(None, "event_1", "event_3"),
                                        ({}, "event_1", "event_3"),
                                        ({"N": 4}, "event_3", "event_1")]:
    pr = spot.synthesis_problem.from_tlsf_string(tlsf_param, overrides)
    # patch_game() requires the output-only restriction of the
    # global-equivalence simplification.
    pr.set_game_output_only(True)
    aps = list(pr.games()[0].ap())
    tc.assertIn(expected, aps)
    tc.assertNotIn(unexpected, aps)

# A specification that declares Finite semantics cannot be handled by
# synthesis_problem.
tlsf_finite = """INFO {
  TITLE:       "tlsf test"
  DESCRIPTION: "used by tests/python/synthesis.py"
  SEMANTICS:   Mealy,Finite
  TARGET:      Mealy
}
GLOBAL {
  PARAMETERS {}
}
MAIN {
  INPUTS  { i; }
  OUTPUTS { o; }
  GUARANTEE { G(o); }
}
"""
tc.assertRaises(ValueError, spot.synthesis_problem.from_tlsf_string,
                tlsf_finite)

# Parse errors are reported as RuntimeError, with the name used in
# diagnostics (the last argument of from_tlsf_string).
with tc.assertRaises(RuntimeError) as cm:
    spot.synthesis_problem.from_tlsf_string(
        "INFO {", None, None, None, None, "broken.tlsf")
tc.assertIn("broken.tlsf", str(cm.exception))

# Disjunctive decomposition: a strategy satisfying one disjunct of a
# disjunction satisfies the whole specification.  No sub-specification
# is solved then, and all the output propositions are still declared,
# so the AIG covers both even though the winning disjunct uses one.
pr = spot.synthesis_problem(spot.formula("!(o1 & o2)"),
                            ["i"], ["o1", "o2"], [],
                            no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertEqual(len(pr.sub_specifications()), 0)
tc.assertEqual(len(pr.sub_outputs()), 0)
st = pr.strategy()
tc.assertIsNotNone(st)
pr.verify_strategy()
circuit = pr.aig("ite")
tc.assertIsNotNone(circuit)
pr.verify_aig(circuit)

# Implications are disjunctions of the negation of their assumption
# and of their conclusion: a strategy violating the assumption is a
# strategy for the implication.
pr = spot.synthesis_problem(spot.formula("G(o1) -> G(o2)"),
                            ["i"], ["o1", "o2"], [],
                            no_simplification())
tc.assertTrue(pr.is_realizable())
tc.assertTrue(pr.assumptions_violated())
pr.verify_strategy()

# Disabling the disjunctive decomposition leaves the ordinary solver,
# which still handles the disjunction as a whole.
si = no_simplification()
si.decompose = spot.synthesis_info.decomposition_conjunctions
pr = spot.synthesis_problem(spot.formula("!(o1 & o2)"),
                            ["i"], ["o1", "o2"], [], si)
tc.assertTrue(pr.is_realizable())
tc.assertEqual(pr.decompose(),
               spot.synthesis_info.decomposition_conjunctions)
tc.assertEqual(len(pr.sub_specifications()), 1)
pr.verify_strategy()

# A disjunction can be realizable even when none of its disjuncts is:
# i is an input, so no strategy can force X i or X !i, but their
# disjunction is a tautology.  The disjunctive decomposition must fall
# back to the whole specification instead of reporting it unrealizable.
pr = spot.synthesis_problem(spot.formula("X i | X !i"), ["i"], [], [],
                            no_simplification())
tc.assertTrue(pr.is_realizable())

# When the disjuncts use disjoint inputs, the failure of every disjunct
# is conclusive: the adversary strategies falsifying each of them can
# be played simultaneously, so the whole disjunction is unrealizable
# and does not need to be solved as a whole.
pr = spot.synthesis_problem(spot.formula("X i | X j"), ["i", "j"], [], [],
                            no_simplification())
tc.assertFalse(pr.is_realizable())

# Disjuncts sharing an input are grouped and solved together, so the
# X i | X !i group is found realizable even though neither disjunct is,
# while the disjoint X j group does not need to be solved as a whole.
pr = spot.synthesis_problem(spot.formula("X i | X !i | X j"),
                            ["i", "j"], [], [], no_simplification())
tc.assertTrue(pr.is_realizable())
