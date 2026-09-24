#!/usr/bin/python3
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

# Make sure scc_filter preserves state-names (suggested by Juraj
# Major)

import buddy
import spot
from unittest import TestCase
tc = TestCase()

a = spot.automaton("""
HOA: v1.1
States: 3
Start: 1
AP: 1 "a"
acc-name: Buchi
Acceptance: 1 Inf(0)
spot.highlight.states: 0 0 2 3
--BODY--
State: 0 "baz"
[t] 0
State: 2 "foo" {0}
[0] 0
[0] 2
[!0] 2
State: 1 "bar"
[0] 2
--END--
""")

tc.assertEqual(spot.scc_filter(a, True).to_str('hoa', '1.1'), """HOA: v1.1
States: 2
Start: 0
AP: 1 "a"
acc-name: Buchi
Acceptance: 1 Inf(0)
properties: trans-labels explicit-labels state-acc !complete
properties: deterministic
spot.highlight.states: 1 3
--BODY--
State: 0 "bar"
[0] 1
State: 1 "foo" {0}
[t] 1
--END--""")

# scc_filter_susp() removes the states that are only usable on accepting
# cycles when a suspension predicate is not seen.
susp = buddy.bdd_ithvar(a.register_ap('s'))
tc.assertEqual(spot.scc_filter_susp(a, True, susp, buddy.bddfalse,
                                   False, None).num_states(), 2)
tc.assertEqual(spot.scc_filter_susp(a, True, susp, buddy.bddfalse,
                                   True, None).num_states(), 2)

# ----------------------------------------------------------------------------
# Exercise the 11 template instantiations of scc_filter_apply() in
# sccfilter.cc (three weak variants, two generalized-Bchi variants,
# two general-acceptance variants, two scc_filter_states variants and
# two scc_filter_susp variants), each time checking that the named
# properties (state-names, highlight-states, original-states,
# degen-levels) survive the filtering.  Each combination is also run
# with a supplied scc_info (so the scc_filter_apply() given_si branch
# is taken) and on an alternating automaton (to trigger the "does yet
# not support alternation" error).
# ----------------------------------------------------------------------------

def name_and_highlight(aut):
    n = aut.num_states()
    aut.set_state_names(["q{}".format(i) for i in range(n)])
    for i in range(n):
        aut.highlight_state(i, i % 3 + 1)
    return aut


def check_props(aut, name, want_orig):
    tc.assertIsNotNone(aut.get_state_names(), name + ": state-names lost")
    tc.assertEqual(len(aut.get_state_names()), aut.num_states(),
                   name + ": state-names size")
    for s in range(aut.num_states()):
        tc.assertIsNotNone(aut.get_highlight_state(s),
                           name + ": highlight missing for state " + str(s))
    if want_orig:
        tc.assertIsNotNone(aut.get_original_states(),
                           name + ": original-states lost")
        tc.assertEqual(len(aut.get_original_states()), aut.num_states(),
                       name + ": original-states size")


# Weak automaton with "t" acceptance (weak fast path in scc_filter()).
weak_t = name_and_highlight(spot.translate('Ga'))
# Weak automaton with generalized-Bchi acceptance; degeneralize()
# also records original-states and degen-levels.
weak_i = name_and_highlight(spot.degeneralize(spot.translate('Ga')))
# Non-weak automaton with generalized-Bchi acceptance and with
# original-states/degen-levels.
gba = name_and_highlight(spot.degeneralize(spot.translate('GFa')))
# Non-weak automaton with a parity acceptance that is not a
# generalized Bchi.
parity = name_and_highlight(spot.automaton("""HOA: v1
States: 2
Start: 0
AP: 1 "a"
Acceptance: 2 Fin(0) & Inf(1)
--BODY--
State: 0
[0] 0 {1}
[!0] 1 {0}
State: 1
[0] 0 {1}
--END--"""))
tc.assertFalse(parity.prop_inherently_weak().is_true(),
               "parity automaton should not be inherently weak")
# Sanity: scc_filter() goes through the general-acceptance branch and
# does not rewrite the acceptance to a generalized-Bchi one.
tc.assertEqual(spot.scc_filter(parity, False).get_acceptance(),
               parity.get_acceptance(),
               "parity acceptance should be preserved")

# Alternating automaton: scc_filter() must refuse to work on it.
alt = spot.automaton("""HOA: v1.1
States: 2
Start: 0
AP: 1 "p"
Acceptance: 1 Inf(0)
--BODY--
State: 0
[0] 0&1
State: 1 {0}
[t] 1
--END--""")
tc.assertFalse(alt.is_existential())

# (automaton, wants original-states, comment)
bases = [(weak_t, False, "weak-t"), (weak_i, True, "weak-inf"),
         (gba, True, "gba"), (parity, False, "parity")]

suspvar = buddy.bdd_ithvar(gba.register_ap('susp'))

# The 11 template instantiations, as (callable(a, si), base, name).
# The callable is invoked twice: with si=None and with a precomputed
# scc_info for the automaton.
combos = [
    (lambda a, si: spot.scc_filter(a)
     if si is None else spot.scc_filter(a, False, si), 0,
     "scc_filter weak-t"),
    (lambda a, si: spot.scc_filter(a)
     if si is None else spot.scc_filter(a, False, si), 1,
     "scc_filter weak-inf"),
    (lambda a, si: spot.scc_filter(a, False, None, True)
     if si is None else spot.scc_filter(a, False, si, True), 1,
     "scc_filter weak-inf keep-one-color"),
    (lambda a, si: spot.scc_filter(a, False)
     if si is None else spot.scc_filter(a, False, si), 2,
     "scc_filter gba"),
    (lambda a, si: spot.scc_filter(a, True)
     if si is None else spot.scc_filter(a, True, si), 2,
     "scc_filter gba all"),
    (lambda a, si: spot.scc_filter(a, False)
     if si is None else spot.scc_filter(a, False, si), 3,
     "scc_filter parity"),
    (lambda a, si: spot.scc_filter(a, True)
     if si is None else spot.scc_filter(a, True, si), 3,
     "scc_filter parity all"),
    (lambda a, si: spot.scc_filter_states(a, False)
     if si is None else spot.scc_filter_states(a, False, si), 2,
     "scc_filter_states"),
    (lambda a, si: spot.scc_filter_states(a, True)
     if si is None else spot.scc_filter_states(a, True, si), 2,
     "scc_filter_states all"),
    (lambda a, si: spot.scc_filter_susp(a, False, suspvar, buddy.bddfalse,
                                        False, None)
     if si is None else spot.scc_filter_susp(a, False, suspvar,
                                              buddy.bddfalse, False, si), 2,
     "scc_filter_susp"),
    (lambda a, si: spot.scc_filter_susp(a, True, suspvar, buddy.bddfalse,
                                        False, None)
     if si is None else spot.scc_filter_susp(a, True, suspvar,
                                              buddy.bddfalse, False, si), 2,
     "scc_filter_susp all"),
]

for (fun, base, name) in combos:
    tc.assertRaises(RuntimeError, fun, alt, None)
    aut = bases[base][0]
    res = fun(aut, None)
    check_props(res, name, bases[base][1])
    res = fun(aut, spot.scc_info(aut))
    check_props(res, name + " (given scc_info)", bases[base][1])
