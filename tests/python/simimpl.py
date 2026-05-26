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

# Test the simulation() overload that exports the implication vector.
#
# The implications vector has one entry per state of the output automaton.
# bdd_implies(implications[i], implications[j]) is True when state j
# simulates state i.

import spot
from buddy import bdd_implies
from unittest import TestCase
tc = TestCase()

aut = spot.automaton("""
HOA: v1
States: 3
Start: 0
AP: 1 "a"
acc-name: Buchi
Acceptance: 1 Inf(0)
--BODY--
State: 0
[0] 1
[!0] 1
[0] 2
State: 1
[t] 1 {0}
State: 2
[0] 2 {0}
--END--
""")

# After simulation, the output automaton has the same 3 states (none are
# equivalent, because L(1) ≠ L(2) and their simulation is not mutual).
#
# Simulation relation on the output automaton:
#   - state 1 simulates state 2
#   - state 1 simulates state 0
#   - neither state 0 nor state 2 simulates state 1

# Pass a vectorbdd as the output-parameter for the implications.
impl = spot.vectorbdd()
aut2 = spot.simulation(aut, impl)

# The output automaton is the reduced version of aut, but in this
# case it has the same number of states.
tc.assertEqual(aut2.num_states(), 3)
# implications has one entry per output state.
tc.assertEqual(len(impl), 3)

# Identify which output state is which by looking at the transitions:
# state with a 't' self-loop and an accepting mark → state 1 (accepts all)
# state with an 'a' self-loop and an accepting mark → state 2 (accepts a^ω)
# state with a 't' transition to another state (non-accepting) → state 0

def classify(aut):
    """Return (s_all, s_a, s_init) state indices for the 3-state automaton."""
    s_all = s_a = s_init = None
    for s in range(aut.num_states()):
        succs = list(aut.out(s))
        if len(succs) == 1 and succs[0].dst == s:
            # self-loop
            cond = succs[0].cond
            if cond == spot.buddy.bddtrue:
                s_all = s  # unconditional self-loop: accepts everything
            else:
                s_a = s    # conditional self-loop: accepts a^ω only
        else:
            s_init = s     # initial transient state
    return s_all, s_a, s_init

s_all, s_a, s_init = classify(aut2)
tc.assertIsNotNone(s_all)
tc.assertIsNotNone(s_a)
tc.assertIsNotNone(s_init)

# state s_all simulates state s_a
tc.assertTrue(bdd_implies(impl[s_a], impl[s_all]))
# The converse does not hold
tc.assertFalse(bdd_implies(impl[s_all], impl[s_a]))

# state s_all simulates state s_init
tc.assertTrue(bdd_implies(impl[s_init], impl[s_all]))
tc.assertFalse(bdd_implies(impl[s_all], impl[s_init]))

# s_a and s_init are incomparable
tc.assertFalse(bdd_implies(impl[s_a], impl[s_init]))
tc.assertFalse(bdd_implies(impl[s_init], impl[s_a]))
