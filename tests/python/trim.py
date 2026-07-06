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
   print(f)
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1, a1b).is_empty());

gen = spot.randltl(4, output='ltl', tree_size=15)
for i in range(100):
   f = spot.formula_And([next(gen), spot.formula_Not(next(gen)),
                         next(gen), spot.formula_Not(next(gen))])
   print(f)
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1b, a1b).is_empty());

for i in range(100):
   f = spot.formula_Or([next(gen), spot.formula_Not(next(gen)),
                        next(gen), spot.formula_Not(next(gen))])
   print(f)
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.trim(a1)
   tc.assertTrue(spot.product_xor(a1b, a1b).is_empty());
