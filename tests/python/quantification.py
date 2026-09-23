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
   a1b = spot.quantify_exists(a1, "p0")
   b1 = spot.formula("\\exists p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

gen = spot.randltl(4, output='ltl', tree_size=15)
for i in range(100):
   f = spot.formula_And([next(gen), spot.formula_Not(next(gen)),
                         next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.quantify_exists(a1, "p0")
   b1 = spot.formula("\\exists p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

for i in range(100):
   f = spot.formula_Or([next(gen), spot.formula_Not(next(gen)),
                        next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.quantify_exists(a1, "p0")
   b1 = spot.formula("\\exists p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

##########################################################

gen = spot.randltl(4, output='ltl', tree_size=30)
for i in range(200):
   f = next(gen)
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.quantify_forall(a1, "p0")
   b1 = spot.formula("\\forall p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

gen = spot.randltl(4, output='ltl', tree_size=15)
for i in range(100):
   f = spot.formula_And([next(gen), spot.formula_Not(next(gen)),
                         next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.quantify_forall(a1, "p0")
   b1 = spot.formula("\\forall p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

for i in range(100):
   f = spot.formula_Or([next(gen), spot.formula_Not(next(gen)),
                        next(gen), spot.formula_Not(next(gen))])
   a1 = spot.ltlf_to_mtdfa(f)
   a1b = spot.quantify_forall(a1, "p0")
   b1 = spot.formula("\\forall p0: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a1b, b1b).is_empty(), f)

##########################################################

# Test the bdd and vector overloads of quantify_exists and
# quantify_forall.  Quantifying several variables in one pass
# should produce the same language as quantifying them one at
# a time, or as the direct translation of a quantified formula.

import buddy

gen = spot.randltl(4, output='ltl', tree_size=15)
for i in range(50):
   f = next(gen)
   a1 = spot.ltlf_to_mtdfa(f)
   # One-pass quantification of {p0, p1} using the vector overload.
   a_vec = spot.quantify_exists(a1, [spot.formula.ap("p0"),
                                     spot.formula.ap("p1")])
   # Sequential quantification, one variable at a time.
   a_seq = spot.quantify_exists(spot.quantify_exists(a1, "p0"), "p1")
   tc.assertTrue(spot.product_xor(a_vec, a_seq).is_empty(), f)
   # Compare with the direct translation of the quantified formula.
   b1 = spot.formula("\\exists p0: \\exists p1: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a_vec, b1b).is_empty(), f)

for i in range(50):
   f = next(gen)
   a1 = spot.ltlf_to_mtdfa(f)
   a_vec = spot.quantify_forall(a1, [spot.formula.ap("p0"),
                                     spot.formula.ap("p1")])
   a_seq = spot.quantify_forall(spot.quantify_forall(a1, "p0"), "p1")
   tc.assertTrue(spot.product_xor(a_vec, a_seq).is_empty(), f)
   b1 = spot.formula("\\forall p0: \\forall p1: " + str(f))
   b1b = spot.ltlf_to_mtdfa(b1)
   tc.assertTrue(spot.product_xor(a_vec, b1b).is_empty(), f)

# The bdd cube overload should match the formula overload.
a1 = spot.ltlf_to_mtdfa("F(p0 & Fp1)")
d = a1.get_dict()
cube = buddy.bdd_ithvar(d.register_proposition(spot.formula.ap("p0"), a1))
tc.assertTrue(spot.product_xor(spot.quantify_exists(a1, cube),
                              spot.quantify_exists(a1, "p0")).is_empty())
tc.assertTrue(spot.product_xor(spot.quantify_forall(a1, cube),
                              spot.quantify_forall(a1, "p0")).is_empty())

# Quantifying an unregistered atomic proposition leaves the automaton
# unchanged.
a1 = spot.ltlf_to_mtdfa("F(p0)")
tc.assertTrue(spot.product_xor(spot.quantify_exists(a1, "unused"),
                              a1).is_empty())
tc.assertTrue(spot.product_xor(spot.quantify_forall(a1, "unused"),
                              a1).is_empty())

# Formula-level quantification via formula.quantify().
qf = spot.formula.quantify(spot.op_exists, spot.formula('a'),
                           spot.formula('F(a)'))
tc.assertEqual(str(qf), r'\exists a: Fa')
qf2 = spot.formula.quantify(spot.op_forall,
                            [spot.formula('a'), spot.formula('b')],
                            spot.formula('a & b'))
tc.assertEqual(str(qf2), r'\forall a, b: (a & b)')
# Quantifying an atomic proposition factorizes a conjunction.
qf3 = spot.formula.quantify(spot.op_exists, spot.formula('a'),
                            spot.formula('a & b'))
tc.assertEqual(str(qf3), r'\exists a: (a & b)')
