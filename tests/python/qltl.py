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

# Quick test for collect_quantified_apids
# We do these first, because the upcoming tests might
# reorder variables depending on when garbage collection occurs.
f = spot.formula("∃ a: ∀ c, d: ∃c: a U b U c U d")
v = spot.collect_quantified_apids(f)
tc.assertEqual(str(v), "(1, 3, 2, 0)")
tc.assertEqual(str(spot.formula.apid_map()), '["a", "c", "d", "b"]')
g = spot.normalize_quantifiers(f)
v = spot.collect_quantified_apids(g)
tc.assertEqual(str(v), "(0, 0, 0, 0)")

def test(f1, f2):
    f1 = spot.formula(f1)
    f2 = spot.formula(f2)
    f1 = spot.normalize_quantifiers(f1)
    tc.assertEqual(f1, f2)

# These tests are for spot::normalize_quantifiers().
# Similar tests in core/qltl.test are testing spot::tl_simplifier.
test("∃ a: a U b", "1 U b")
test("\\exists a, b: a U b", "1")
test("∀ a: ∃ b: a U b", "1")
test("∃ b: ∀ a: a U b", "1")
test("\\forall a, b: a U b", "0")
test("\\exists c: a U b", "a U b")
test("\\exists a, c: a U b", "1 U b")
test("\\forall a, e: \\exists b, c: (a -> b) & (c xor d)", "∃ c: c xor d")
