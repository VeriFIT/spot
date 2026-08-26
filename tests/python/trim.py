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

gen = spot.randltl(4, output='ltl', ltl_priorities='strongX=1', tree_size=30)
for i in range(200):
   f = next(gen)
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1, a1b).is_empty(), f)

gen = spot.randltl(4, output='ltl', tree_size=15)
for i in range(100):
   f = spot.formula_And([next(gen), spot.formula_Not(next(gen)),
                         next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1, a1b).is_empty(), f)

for i in range(100):
   f = spot.formula_Or([next(gen), spot.formula_Not(next(gen)),
                        next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1, a1b).is_empty(), f)

##########################################################

# Deterministic test-case from a code review of trim_aux().  The
# automaton has an SCC {s3 -> s4 -> s5 -> s3} whose transitions are
# all rejecting, with two incoming transitions: s1 -> s3 (rejecting)
# and s2 -> s4 (the only accepting transition of the automaton).
#
# Since the SCC cannot reach any accepting transition, the rejecting
# transition s1 -> s3 must be replaced by s1 -> bddfalse.  Because
# s2 -> s4 is accepting, s4 -- and only s4 -- must be preserved from
# the SCC: s3 and s5 disappear, and s4's outgoing (rejecting)
# transitions become bddfalse.
#
# HOA state numbering: 0=s1 (initial), 1=s2, 2=s3, 3=s4, 4=s5.
hoa = """HOA: v1
name: "trim cex"
States: 5
Start: 0
AP: 1 "a"
Acceptance: 1 Inf(0)
--BODY--
State: 0
[0] 2
[!0] 1
State: 1
[0] 3 {0}
[!0] 1
State: 2
[0] 3
[!0] 2
State: 3
[0] 4
[!0] 3
State: 4
[0] 2
[!0] 4
--END--
"""
aut = spot.automaton(hoa)
dfa = spot.twadfa_to_mtdfa(aut)
tc.assertEqual(dfa.num_states(), 5)

t = spot.trim(dfa)
# Only s1, s2 and s4 remain.
tc.assertEqual(t.num_states(), 3)
# The trim must preserve the language.
tc.assertTrue(spot.product_xor(dfa, t).is_empty())

tw = t.as_twa()
tc.assertEqual(tw.num_states(), 3)
tc.assertEqual(tw.num_edges(), 3)

def cond_str(e):
   return spot.bdd_format_formula(tw.get_dict(), e.cond)

# s1 (state 0): its rejecting transition a -> s3 was replaced by
# bddfalse, so only the !a -> s2 edge remains.
out0 = list(tw.out(0))
tc.assertEqual(len(out0), 1)
tc.assertEqual(cond_str(out0[0]), "!a")
tc.assertEqual(out0[0].dst, 1)
# s2 (state 1): keeps its two edges, including the only accepting
# one, a -> s4.
out1 = list(tw.out(1))
tc.assertEqual(len(out1), 2)
tc.assertTrue(any(e.dst == 2 and e.acc == spot.mark_t([0])
                  and cond_str(e) == "a" for e in out1))
# s4 (state 2): its outgoing transitions were replaced by bddfalse.
tc.assertEqual(len(list(tw.out(2))), 0)
