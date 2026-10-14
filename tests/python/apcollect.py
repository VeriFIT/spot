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

# Test atomic_prop_collect_as_bdd
aut = spot.make_twa_graph(spot.make_bdd_dict())
f = spot.formula('a & b & Xc')
b = spot.atomic_prop_collect_as_bdd(f, aut)
# The BDD should be a conjunction of a, b, and c variables.
tc.assertNotEqual(b, buddy.bddtrue)
tc.assertNotEqual(b, buddy.bddfalse)
# The automaton should now have 3 registered APs.
tc.assertEqual(len(aut.ap()), 3)

# Test collect_aps_with_polarities
f = spot.formula('G(a -> b) & X(!b & c)')
pol = spot.collect_aps_with_polarities(f)
tc.assertEqual(len(pol), 3)
# a appears only negatively (as part of a->b which is !a|b)
tc.assertEqual(pol[spot.formula('a')], 0b01)   # negative
# b appears both positively and negatively
tc.assertEqual(pol[spot.formula('b')], 0b11)   # both
# c appears only positively
tc.assertEqual(pol[spot.formula('c')], 0b10)   # positive

# Test with simple positive formula
f = spot.formula('a & b & c')
pol = spot.collect_aps_with_polarities(f)
tc.assertEqual(len(pol), 3)
tc.assertEqual(pol[spot.formula('a')], 0b10)
tc.assertEqual(pol[spot.formula('b')], 0b10)
tc.assertEqual(pol[spot.formula('c')], 0b10)

# Test with negated formula
f = spot.formula('!a & !b')
pol = spot.collect_aps_with_polarities(f)
tc.assertEqual(len(pol), 2)
tc.assertEqual(pol[spot.formula('a')], 0b01)
tc.assertEqual(pol[spot.formula('b')], 0b01)

# Test with both polarities (equiv)
f = spot.formula('a <-> b')
pol = spot.collect_aps_with_polarities(f)
tc.assertEqual(len(pol), 2)
tc.assertEqual(pol[spot.formula('a')], 0b11)
tc.assertEqual(pol[spot.formula('b')], 0b11)

# Test with quantifier: quantified APs not in body are ignored
f = spot.formula('\\exists a: G(b -> c) & X(!b & d)')
pol = spot.collect_aps_with_polarities(f)
tc.assertEqual(len(pol), 3)
tc.assertEqual(pol[spot.formula('b')], 0b01)
tc.assertEqual(pol[spot.formula('c')], 0b10)
tc.assertEqual(pol[spot.formula('d')], 0b10)
# 'a' is quantified and absent from body, so it should NOT appear

# Test atomic_prop_collect_as_bdd with no APs
aut2 = spot.make_twa_graph(spot.make_bdd_dict())
f = spot.formula('1')
b = spot.atomic_prop_collect_as_bdd(f, aut2)
tc.assertEqual(b, buddy.bddtrue)
tc.assertEqual(len(aut2.ap()), 0)

# Test collect_literals() on some formulas.
for f, lits in [(spot.formula('(a & b) | c'), ['a', 'b', 'c']),
                (spot.formula('a'), ['a']),
                (spot.formula('F(a & Gb)'), ['a', 'b'])]:
    tc.assertEqual(sorted(str(x) for x in spot.collect_literals(f)), lits)

# Test the apid<->name round trip.
for f in [spot.formula('a'), spot.formula('b')]:
    tc.assertEqual(spot.formula.apname_from_apid(f.apid()), f.ap_name())
try:
    spot.formula.apname_from_apid(123456)
    exit(2)
except RuntimeError as e:
    tc.assertIn('incorrect id', str(e))

# list_formula_props() lists the elementary properties of a formula.
props = [p for p in spot.list_formula_props(spot.formula('F G a'))]
for p in ['without Boolean sugar', 'in negative normal form',
          'syntactic stutter invariant', 'LTL formula', 'PSL formula']:
    tc.assertIn(p, props)
leaf = [p for p in spot.list_formula_props(spot.formula('a'))]
tc.assertIn('without Boolean sugar', leaf)
tc.assertIn('LTL formula', leaf)
tc.assertIn('syntactic stutter invariant', leaf)

# Test ap_count()
for f, n in [(spot.formula('1'), 0),
             (spot.formula('a'), 1),
             (spot.formula('a & b | !a'), 2),
             (spot.formula('(a & Xa) | (b U Ga)'), 2),
             (spot.formula('F(a & G(b & X(a | c)))'), 3),
             (spot.formula('X(a | !a)'), 1)]:
    tc.assertEqual(spot.ap_count(f), n)

# Quantified atomic propositions are counted, like atomic_prop_collect()
# does.
f = spot.formula('\\exists x: G(y)')
tc.assertEqual(spot.ap_count(f), 2)
tc.assertEqual(len(spot.atomic_prop_collect(f)), 2)

# Test ap_count_exceeds(): the limit can be exceeded, or not, and it can
# be larger than the number of APIDs that exist (in which case the
# formula cannot use that many propositions and is not even inspected).
f = spot.formula('a & b & c')
for lim, res in [(0, True), (2, True), (3, False), (4, False),
                 (100, False)]:
    tc.assertEqual(spot.ap_count_exceeds(f, lim), res)

# ap_count() agrees with atomic_prop_collect() on a larger formula.
f = spot.formula('G(p0 -> q0) & F(p1 & X(p2 | q1))')
tc.assertEqual(spot.ap_count(f), len(spot.atomic_prop_collect(f)))
tc.assertEqual(spot.ap_count(f), 5)
