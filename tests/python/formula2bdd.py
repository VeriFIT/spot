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

import buddy
import spot
from unittest import TestCase
tc = TestCase()

d = spot._bdd_dict


# -------------------------------------------------------------------------
# formula_to_bdd() only works on boolean formulas: any temporal or PSL
# operator must be rejected.
# -------------------------------------------------------------------------

for s in ['Ga', 'Fa', 'Xa', 'a U b', 'a R b', 'a W b', 'a M b',
          '{a;b}', '{a[*]}']:
    tc.assertRaises(RuntimeError, spot.formula_to_bdd,
                    spot.formula(s), d, None)

# Boolean formulas are accepted and can be read back.
for s in ['a', '!a', 'a & b', 'a | b', 'a xor b', 'a <=> b',
          'a -> b']:
    f = spot.formula(s)
    b = spot.formula_to_bdd(f, d, None)
    tc.assertTrue(spot.are_equivalent(f, spot.bdd_to_formula(b)), s)
    tc.assertTrue(spot.are_equivalent(f, spot.bdd_to_cnf_formula(b)), s)

# The DNF/CNF forms of a lone conjunction are identical.
f = spot.formula('a & b')
b = spot.formula_to_bdd(f, d, None)
tc.assertEqual(spot.bdd_to_formula(b), spot.bdd_to_cnf_formula(b))
# Edge cases.
tc.assertEqual(spot.bdd_to_formula(buddy.bddfalse), spot.formula.ff())
tc.assertEqual(spot.bdd_to_cnf_formula(buddy.bddtrue), spot.formula.tt())


# -------------------------------------------------------------------------
# bdd_to_formula() must reject variables that are not registered as an
# atomic proposition in the dictionary (e.g. anonymous variables).
# -------------------------------------------------------------------------

av = d.register_anonymous_variables(1, None)
tc.assertRaises(RuntimeError, spot.bdd_to_formula, buddy.bdd_ithvar(av))
tc.assertRaises(RuntimeError, spot.bdd_to_cnf_formula,
                buddy.bdd_ithvar(av))