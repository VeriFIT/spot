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

f = spot.formula('GF(a & b) -> (FG(a & b) & Gc)')
m = spot.relabeling_map()
g = spot.relabel_bse(f, spot.Pnn, m)
res = ""
for old, new in m.items():
    res += f"#define {old} {new}\n"
res += str(g)
tc.assertEqual(res, """#define p0 a & b
#define p1 c
GFp0 -> (FGp0 & Gp1)""")

h = spot.relabel_apply(g, m)
tc.assertEqual(h, f)

autg = g.translate()
spot.relabel_here(autg, m)
tc.assertEqual(str(autg.ap()), \
    '(spot.formula("a"), spot.formula("b"), spot.formula("c"))')
tc.assertTrue(spot.isomorphism_checker.are_isomorphic(autg, f.translate()))

a = spot.formula('a')
u = spot.formula('a U b')
m[a] = u
try:
    spot.relabel_here(autg, m)
except RuntimeError as e:
    tc.assertIn("new labels", str(e))

m = spot.relabeling_map()
m[u] = a
try:
    spot.relabel_here(autg, m)
except RuntimeError as e:
    tc.assertIn("old labels", str(e))

f = spot.parse_infix_sere("(p9;p21|p22):(p1&p2;p11&p22;p1&p2)").f
g = spot.relabel_bse(f, spot.Abc)
tc.assertEqual(str(g), "(a;(b | c)):(d;(c & e);d)")

# A Boolean formula whose atomic propositions all occur inside it can
# be relabeled as a whole, even if they occur several times.
tc.assertEqual(str(spot.relabel_bse(spot.formula('a & (b <-> a)'),
                                    spot.Pnn)), 'p0')
# The same goes for a formula whose operands are not disjoint: it used
# to be relabeled as "p0 & p1" with p0 = c & (a <-> b) and p1 = a,
# hiding the fact that both share the atomic proposition a.
tc.assertEqual(str(spot.relabel_bse(spot.formula('a & c & (a <-> b)'),
                                    spot.Pnn)), 'p0')

# Check that the relabeling is legal on a few representative formulas:
# two relabeled subformulas may never share an atomic proposition, the
# relabeling map must restore the original formula, and the number of
# atomic propositions may only decrease.
formulas = ['a & (b <-> a)',
            'a & c & (a <-> b)',
            'GF(a & b) -> (FG(a & b) & Gc)',
            '(a & b & c) U (!c & d & e)',
            '(a & b & c & d) U X(c & d)',
            '((a | b) & c & d) U (!d & e & f)',
            '(a & b) U (a & !b)',
            '(a & b & c) U !(a & b & c)',
            'G(d & e) | FG(Xf | !c) | h | i',
            'a & Xb & c',
            '(a <-> b) & X(b -> c)']
for s in formulas:
    f = spot.formula(s)
    m = spot.relabeling_map()
    g = spot.relabel_bse(f, spot.Pnn, m)
    tc.assertEqual(spot.relabel_apply(g, m), f, s)
    tc.assertLessEqual(spot.ap_count(g), spot.ap_count(f), s)
    bodies = [set(map(str, spot.atomic_prop_collect(v))) for v in m.values()]
    for i in range(len(bodies)):
        for j in range(i + 1, len(bodies)):
            tc.assertEqual(bodies[i] & bodies[j], set(), s)

# Renaming must not hide the unsatisfiability (or the validity) of a
# piece: a contradictory subformula is kept as false, and a tautology
# as true, instead of being replaced by a fresh atomic proposition that
# could be satisfied freely.
tc.assertEqual(str(spot.relabel_bse(spot.formula('(a & !a) | (b & !b)'),
                                    spot.Pnn)), '0')
tc.assertEqual(str(spot.relabel_bse(spot.formula('(a & !b) | (a -> b)'),
                                    spot.Pnn)), '1')
# The contradictory operand below is not given a name, only c is,
# and 'p0 U false' is correctly recognized as false.
f = spot.formula('c U ((a & !a) | (b & !b))')
m = spot.relabeling_map()
g = spot.relabel_bse(f, spot.Pnn, m)
tc.assertEqual([str(o) for o in m.values()], ['c'])
tc.assertEqual(str(g), '0')
