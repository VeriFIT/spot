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
import buddy
from unittest import TestCase

tc = TestCase()


def copy_state(s):
    # The ba_state objects returned by init_state()/succ_as_ba_edges()
    # may reference data owned by a temporary vector; keep a plain copy.
    r = spot.ba_state()
    r.f = s.f
    r.m = s.m
    return r


def build_nba(f, from_bdd=False):
    """Expand the on-the-fly explorer spot.ltl_to_ba_otf into an NBA.

    The automaton uses state-based Büchi acceptance: every state with
    m == -1 is accepting, so all its outgoing edges carry acceptance
    set 0.
    """
    d = spot.make_bdd_dict()
    aut = spot.make_twa_graph(d)
    ba = spot.ltl_to_ba_otf(f, aut)
    idx = {}
    pending = []

    def add(s):
        key = (s.f, s.m)
        if key not in idx:
            idx[key] = aut.new_state()
            pending.append(copy_state(s))
        return idx[key]

    aut.set_init_state(add(ba.init_state()))
    while pending:
        s = pending.pop()
        src = idx[(s.f, s.m)]
        acc = spot.mark_t([0]) if s.m == -1 else spot.mark_t()
        if from_bdd:
            isop = spot.minato_isop(ba.succ_as_bdd(s))
            cube = isop.next()
            while cube != buddy.bddfalse:
                nxt = buddy.bdd_exist(cube, ba.var_set())
                cond = buddy.bdd_exist(cube, ba.next_set())
                dst = ba.state_from_var(buddy.bdd_var(nxt))
                aut.new_edge(src, add(dst), cond, acc)
                cube = isop.next()
        else:
            # Keep es alive while reading e.dst, which references it.
            es = ba.succ_as_ba_edges(s)
            for e in es:
                aut.new_edge(src, add(e.dst), e.cond, acc)
    aut.set_buchi()
    aut.prop_state_acc(True)
    return aut


# --- Basic API checks, on a formula with a single eventuality. ----------
f = spot.parse_formula('a U b')
d = spot.make_bdd_dict()
aut = spot.make_twa_graph(d)
ba = spot.ltl_to_ba_otf(f, aut)

tc.assertEqual(str(ba.orig_formula()), 'a U b')
s0 = ba.init_state()
tc.assertEqual(str(s0.f), 'a U b')
tc.assertEqual(s0.m, 0)
tc.assertFalse(ba.is_accepting(s0))

acc0 = spot.ba_state()
acc0.f = s0.f
acc0.m = -1
tc.assertTrue(ba.is_accepting(acc0))

# register_next_state / state_from_var round-trip.
v = ba.register_next_state(s0)
got = ba.state_from_var(v)
tc.assertEqual(str(got.f), 'a U b')
tc.assertEqual(got.m, 0)

# The symbolic view is non-empty and decomposable.
tc.assertTrue(ba.succ_as_bdd(s0) != buddy.bddfalse)

# --- Language equivalence, on a set of formulas. ----------------
formulas = [
    'G F p & G F q',
    'p U (q U r)',
    'G(Fa & ((a M b) U ((c U !d) M d)))',
    'F a & F b & F c',
    'a U b',
    '(a -> F b) & (b -> F a)',
    'G F a -> G F b',
    'F(a & X(!a & Fb))',
    '(a U b) | G c',
    'X a',
    'tt',
    'ff',
    'G F p',
    'G F (p & X q)',
    'F G p -> F G q',
    'G(a -> F b)',
    'F a | G b',
    'a W b',
    'a M b',
    'a R b',
    'G F(a | b) & G F(!a | !b)',
    'G(F a | F b)',
    'a U (b U (c U (d U e)))',
    'G F a & G F b & G F c & G F d',
    '((p U q) U r) & G F s',
    '! (G F p -> G F q)',
]
for text in formulas:
    f = spot.parse_formula(text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f)), text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, from_bdd=True)), text)

# --- Random formulas, both views. --------------------------------------
for f in spot.randltl(3, 50, seed=42):
    tc.assertTrue(spot.are_equivalent(f, build_nba(f)), str(f))
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, from_bdd=True)), str(f))
