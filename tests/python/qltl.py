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

# Tests for obligation_to_mtdswa() with quantified LTL.
#
# We use formulas where the quantified AP has mixed polarity, so
# normalize_quantifiers cannot trivially eliminate it.
d = spot.make_bdd_dict()

def check_equiv(f_str, expected_str):
    """Assert obligation_to_mtdswa(f) is language-equivalent to expected."""
    f   = spot.formula(f_str)
    exp = spot.formula(expected_str)
    # The formula must stay quantified after normalize_quantifiers,
    # confirming the AP is not trivially eliminated.
    tc.assertTrue(spot.normalize_quantifiers(f).is_quantified(),
                  f"{f_str!r} should remain quantified")
    aut     = spot.obligation_to_mtdswa(f,   dict=d)
    exp_aut = spot.obligation_to_mtdswa(exp, dict=d)
    tc.assertTrue(spot.are_equivalent(aut.as_twa(), exp_aut.as_twa()),
                  f"obligation_to_mtdswa({f_str!r}) not equiv"
                  f" to {expected_str!r}")
    # same with LTLf translation
    aut1 = spot.ltlf_to_mtdfa(f, dict=d)
    aut2 = spot.ltlf_to_mtdfa(exp, dict=d)
    tc.assertTrue(spot.product_xor(aut1, aut2).is_empty(),
                  f"ltlf_to_mtdfa({f_str!r}) not equiv"
                  f" to {expected_str!r}")

check_equiv("\\exists a: G(a | b) & G(!a | c)", "G(b | c)")
check_equiv("\\forall a: G(a | b) & G(!a | c)", "Gb & Gc")
check_equiv("\\exists a: \\forall b: G(a | b) & G(!a | !b | c)", "Gc")

# Larger tests using the duality property:
#
#   L(∀a:∃b:f(a,b)) = complement(L(∃a:∀b:¬f(a,b)))
#
# This avoids the need to find an equivalent quantifier-free formula:
# we simply build both automata and verify they recognize complementary
# languages.  The formulas below were selected (via randltl | ltlfilt)
# so that a and b both have mixed polarity and normalize_quantifiers
# does not eliminate the quantifiers.

def check_dual(f_str):
    """Check ∀a:∃b:f and ∃a:∀b:¬f produce complementary automata."""
    fa = spot.formula("\\forall a: \\exists b: " + f_str)
    fb = spot.formula("\\exists a: \\forall b: !(" + f_str + ")")
    tc.assertTrue(spot.normalize_quantifiers(fa).is_quantified(),
                  f"∀a:∃b:f should remain quantified for: {f_str}")
    tc.assertTrue(spot.normalize_quantifiers(fb).is_quantified(),
                  f"∃a:∀b:¬f should remain quantified for: {f_str}")
    # LTL
    aut1 = spot.obligation_to_mtdswa(fa, dict=d)
    aut2 = spot.obligation_to_mtdswa(fb, dict=d)
    tc.assertTrue(
        spot.are_equivalent(aut1.as_twa(),
                            spot.complement(aut2.as_twa())),
        f"Duality check failed for: {f_str}")
    # LTLf
    aut1 = spot.ltlf_to_mtdfa(fa, dict=d)
    aut2 = spot.ltlf_to_mtdfa(fb, dict=d)
    tc.assertTrue(spot.product_xnor(aut1, aut2).is_empty(),
                  "LTLf duality check failed for: {f_str}")

# 10/11 states
check_dual(
    "(Gd & (Fa U c) & ((b & X!a) | (!b & Xa)))"
    " | ((G!a R !c) & (F!d | (b & Xa) | (!b & X!a)))")
# 7/5 states
check_dual(
    "((!c U !b) & (!c W Gd) & XG!a)"
    " | ((c M F!d) & ((c R b) | XFa))")
# 4/3 states
check_dual(
    "(Gc & ((a & ((!b & F!d) | (b & Gd)))"
    "      | (!a & ((!b & Gd) | (b & F!d)))))"
    " | (F!c & ((a & ((!b & Gd) | (b & F!d)))"
    "          | (!a & ((!b & F!d) | (b & Gd)))))")


# Some LTL translations
f2 = spot.formula("\\forall a: \\exists b: (Gd & (Fa U c) & (b xor Xa))")
a2 = spot.obligation_synthesis(f2, ["c"], realizability=True, dict=d)

try:
    f3 = spot.formula("\\exists b: \\forall a: (Gd & (Fa U c) & (b xor Xa))")
    a3 = spot.obligation_synthesis(f3, ["c"], realizability=True, dict=d)
except RuntimeError as e:
    tc.assertEqual("quantified variable was already registered "
                   "with an incompatible level",
                   str(e))
else:
    raise RuntimeError("missing exception")

a2b = spot.obligation_to_mtdswa(f2, dict=d)
a3b = spot.obligation_to_mtdswa(f3, dict=d)
tc.assertFalse(a2b.as_twa().is_empty())
tc.assertTrue(a3b.as_twa().is_empty())

# The same translations, but for LTLf
a2 = spot.ltlf_to_mtdfa_for_synthesis(f2, ["c"], realizability=True, dict=d)
try:
    a3 = spot.ltlf_to_mtdfa_for_synthesis(f3, ["c"], realizability=True, dict=d)
except RuntimeError as e:
    tc.assertEqual("quantified variable was already registered "
                   "with an incompatible level",
                   str(e))
else:
    raise RuntimeError("missing exception")

a2b = spot.ltlf_to_mtdfa(f2, dict=d)
a3b = spot.ltlf_to_mtdfa(f3, dict=d)
tc.assertFalse(a2b.is_empty())
tc.assertFalse(a3b.is_empty())  # unlike in LTL!
