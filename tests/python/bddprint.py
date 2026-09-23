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

# Exercise the BDD formatting functions declared in spot/twa/bddprint.hh.
# These take a BDD and the BDD dictionary of an automaton (which maps
# atomic-proposition names to BDD variables) and produce a
# human-readable representation of the Boolean function encoded by the
# BDD.

import buddy
import spot
from unittest import TestCase

tc = TestCase()

aut = spot.translate('GF(a) & GF(b)')
d = aut.get_dict()

# register_ap() adds the atomic proposition to the automaton (and to
# its BDD dictionary) and returns the index of the BDD variable that
# encodes it.
va = aut.register_ap('a')
vb = aut.register_ap('b')
a = buddy.bdd_ithvar(va)
b = buddy.bdd_ithvar(vb)

# bdd_format_formula(dict, bdd) returns a string representation of the
# Boolean formula encoded by the BDD, using the names of the atomic
# propositions registered in the dictionary.
tc.assertEqual(spot.bdd_format_formula(d, a & b), 'a & b')
tc.assertEqual(spot.bdd_format_formula(d, a | b), 'a | b')
tc.assertEqual(spot.bdd_format_formula(d, a), 'a')
tc.assertEqual(spot.bdd_format_formula(d, b), 'b')

# bdd_format_set(dict, bdd) does the same, but prints the BDD using
# the same notation as the acceptance-set batches used internally by
# Spot: each variable is displayed as "name:index".
tc.assertEqual(spot.bdd_format_set(d, a & b), '<a:1, b:1>')
tc.assertEqual(spot.bdd_format_set(d, a), '<a:1>')

# These two functions are also available as bdd_format_accset(dict,
# bdd), to format sets of acceptance sets.  An acceptance set is
# represented by one BDD variable as well.  We cannot build such a
# variable without using the dictionary machinery directly, so here we
# just check that the function exists.
tc.assertTrue(hasattr(spot, 'bdd_format_accset'))
