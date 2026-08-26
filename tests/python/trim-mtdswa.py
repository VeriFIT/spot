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

import buddy
import spot
from unittest import TestCase
tc = TestCase()

trimmable = [
    "\\forall b: Ga & (Fa U c) & (d xor Xa)",
    "F(XG(F!c M Fc) W (c R a))",
    "X(((Xc xor (c U Ga)) | G!Gc) R c)",
    "(Gc | ((b W 0) xor !Xa)) M 1",
]
untrimmable = [
    "true",
    "false",
    "(FGc U (0 R a)) -> (Gb M 1)",  # didn't work before
    "F(!a <-> (F!c & XGF(c U b)))",  # requires color propagation
]
trimmable_twas = [spot.translate(f, "gen", "det", "complete", "SBAcc")
        for f in trimmable]
untrimmable_twas = [spot.translate(f, "gen", "det", "complete", "SBAcc")
        for f in untrimmable]
trimmable_mtdswas1 = [spot.dtwa_to_mtdswa(twa) for twa in trimmable_twas]
trimmable_mtdswas2 = [spot.dtwa_to_mtdswa(twa) for twa in trimmable_twas]
untrimmable_mtdswas1 = [spot.dtwa_to_mtdswa(twa) for twa in untrimmable_twas]
untrimmable_mtdswas2 = [spot.dtwa_to_mtdswa(twa) for twa in untrimmable_twas]


for i in range(len(trimmable)):
    m1 = trimmable_mtdswas1[i]
    m2 = trimmable_mtdswas2[i]
    spot.trim(m2, True)
    # Test that trim does not change the language of the automaton.
    pxor = spot.product_xor(m1.as_twa(), m2.as_twa())
    tc.assertTrue(pxor.is_empty(),
                  "Trimmed MTDSwA is not equivalent to original: "
                  + f"{trimmable[i]}")
    # Test that trim reduces the number of states in the automaton.
    tc.assertLess(m2.num_roots(), m1.num_roots(),
                  "Trimmed MTDSwA should have less states than original: "
                  + f"{trimmable[i]}")

for i in range(len(untrimmable)):
    m1 = untrimmable_mtdswas1[i]
    m2 = untrimmable_mtdswas2[i]
    spot.trim(m2, True)
    # Test that trim does not change the language of the automaton.
    pxor = spot.product_xor(m1.as_twa(), m2.as_twa())
    tc.assertTrue(pxor.is_empty(),
                  "Trimmed MTDSwA is not equivalent to original: "
                  + f"{untrimmable[i]}")
    # Test that trim does not reduce the number of states for these.
    tc.assertEqual(m2.num_roots(), m1.num_roots(),
                   "Trimmed MTDSwA should have same nb of states as original: "
                   + f"{untrimmable[i]}")


# Test all reductions of trim on a hand-built MTDSwA.

bdd_dict = spot.make_bdd_dict()

def make_test_mtdswa():
    term = buddy.bdd_terminal
    ite = buddy.bdd_ite
    m = spot.mtdswa(bdd_dict)
    a = buddy.bdd_ithvar(0)
    b = buddy.bdd_ithvar(1)
    states = [
        ite(a, ite(b, term(7), term(2)), ite(b, term(14), term(15))),
        ite(a, term(1), term(8)), ite(a, term(3), term(6)),
        ite(a, term(5), term(9)), term(1), ite(a, term(3), term(5)),
        buddy.bddfalse, ite(a, term(1), term(0)), ite(a, term(1), term(8)),
        term(5), ite(a, term(10), term(11)), ite(a, term(12), term(13)),
        ite(a, term(10), buddy.bddtrue), ite(a, term(13), buddy.bddtrue),
        ite(a, term(14), term(12)), ite(a, term(6), term(11)),
        ite(a, ite(b, term(16), term(17)), buddy.bddfalse), term(16),
        ]
    for s in states:
        m.states.append(s)
    colors = [[], [0], [], [0], [], [1], [], [], [], [], [0], [], [], [0],
              [0, 1], [0], [], []]
    for col in colors:
        m.colors.append(spot.mark_t(col))
    m.acc = spot.acc_cond('Inf(0) & Fin(1)')
    return m

m = make_test_mtdswa()

# Default trim: remove unreachable states
m1 = make_test_mtdswa()
spot.trim(m1)
pxor = spot.product_xor(m.as_twa(), m1.as_twa())
tc.assertTrue(pxor.is_empty(),
              "Trimmed MTDSwA is not equivalent to original (default trim)")
tc.assertEqual(m1.num_roots(), 15,
               "Trimmed MTDSwA should have 15 states after default trim")
# Check that re-trimming does not change the MTDSwA
spot.trim(m1)
tc.assertEqual(m1.num_roots(), 15,
               "MTDSwA should not change after re-trimming (default trim)")

# Full trim: also remove useless states
m2 = make_test_mtdswa()
spot.trim(m2, True)
pxor = spot.product_xor(m.as_twa(), m2.as_twa())
tc.assertTrue(pxor.is_empty(),
              "Trimmed MTDSwA is not equivalent to original (full trim)")
tc.assertEqual(m2.num_roots(), 13,
               "Trimmed MTDSwA should have 13 states after full trim")
spot.trim(m2, True)
tc.assertEqual(m2.num_roots(), 13,
               "MTDSwA should not change after re-trimming (full trim)")

# The order of the two modes should not matter.
m3 = make_test_mtdswa()
spot.trim(m3, True)
spot.trim(m1, True)   # m1 was default-trimmed first
spot.trim(m2)          # m2 was full-trimmed first
pxor = spot.product_xor(m.as_twa(), m3.as_twa())
tc.assertTrue(pxor.is_empty(),
              "Trimmed MTDSwA is not equivalent to original (full trim)")
tc.assertEqual(m3.num_roots(), 13,
               "Trimmed MTDSwA should have 13 states after full trim")
tc.assertEqual(m1.num_roots(), 13,
               "Trimmed MTDSwA should have 13 states after default trim "
               "then full trim")
tc.assertEqual(m2.num_roots(), 13,
               "Trimmed MTDSwA should have 13 states after full trim "
               "then default trim")
spot.trim(m3, True)
tc.assertEqual(m3.num_roots(), 13,
               "MTDSwA should not change after re-trimming (full trim)")
