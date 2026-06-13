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


def up(s):
    return spot.unit_propagate(spot.formula(s))


def check(input_str, expected_str):
    result = up(input_str)
    expected = spot.formula(expected_str)
    tc.assertEqual(result, expected,
                   f'unit_propagate({input_str!r})'
                   f' = {str(result)!r}, expected {str(expected)!r}')


# -- And: local facts from atoms --

# !a is locally true → a is locally false → (a | b) = b
check('!a & (a | b)', '!a & b')

# a is locally true → (a | b) = tt → result is just a
check('a & (a | b)', 'a')

# a is locally true → !a is locally false → (!a | b) = b
check('a & (!a | b)', 'a & b')

# a and b are locally true → (a | b | c) = tt
check('a & b & (a | b | c)', 'a & b')

# -- And: G facts (globally true) --

# G(a) makes a globally true → (a | b) = tt → whole And = G(a)
check('G(a) & (a | b)', 'G(a)')

# a globally true → inside F: F(a) = F(tt) = tt → And = G(a)
check('G(a) & F(a)', 'G(a)')

# G(a & b & F(c)): adds a, b, F(c) as global facts → (a | b) = tt
check('G(a & b & F(c)) & (a | b)', 'G(a & b & F(c))')

# G(a) & G(a | b): a is globally true → inside G: (a | b) = tt → G(tt)=tt
check('G(a) & G(a | b)', 'G(a)')

# The source G(a) must NOT simplify itself using its own fact.
# G(a) contributes 'a' globally; F(a) and (G(a)|b) are simplified.
check('G(a) & (G(a) | b) & F(a)', 'G(a)')

# G(a U b) makes (a U b) globally true;
# inside GF(c xor (a U b)): (a U b) -> 1, c xor 1 -> !c
check('G(a U b) & G(F(c xor (a U b)))', 'G(a U b) & G(F(!c))')

# -- And: R/M: right operand is locally true --

# (a R b) contributes b as locally true → b = tt → (a R b)
check('(a R b) & b', 'a R b')

# (a M b) contributes b as locally true
check('(a M b) & b', 'a M b')

# -- Or: local false facts from atoms --

# a is locally false → (!a & b) = b
check('a | (!a & b)', 'a | b')

# !a is locally false → a is locally true → (a & b) = b
check('!a | (a & b)', '!a | b')

# -- Or: F facts (globally false) --

# F(a) makes a globally false → inside G: (!a & b): !a = tt → b
# More precisely: a is globally false, so inside (!a & b):
#   !a (Not(a)): Not of a globally-false → Not(ff) = tt → dropped
#   b: not affected → b
# So (!a & b) → b, and Or result = F(a) | b
check('F(a) | (!a & b)', 'F(a) | b')

# F(a) makes a globally false; inside (a U b): b is locally false from U
check('F(a) | (a U b)', 'F(a) | b')

# -- Or: U/W: right operand is locally false --

# (a U b) contributes b as locally false → b = ff → (a U b)
check('(a U b) | b', 'a U b')

# (a W b) contributes b as locally false
check('(a W b) | b', 'a W b')

# -- U/W: right operand known true --

# b is locally true, so (a U b) = tt → dropped from And
check('b & (a U b)', 'b')

# a is locally true but b is NOT, so (a U b) stays
check('a & (a U b)', 'a & (a U b)')

# b is locally true, so (a W b) = tt → dropped
check('b & (a W b)', 'b')

# G(b) makes b globally true, so (a U b) = tt → dropped
check('G(b) & (a U b)', 'G(b)')

# G(b) makes b globally true, so (a W b) = tt → dropped
check('G(b) & (a W b)', 'G(b)')

# (a U b) with b locally true in an Or: (a U b) = tt, but b | (a U b) ≡ a U b
# since b ∨ (b ∨ (a ∧ X…)) ≡ b ∨ (a ∧ X…) ≡ a U b
check('b | (a U b)', 'a U b')

# W-specific: left operand globally true → G a holds → (a W b) = tt
check('G(a) & (a W b)', 'G(a)')

# U does NOT share the left-operand check: a U b stays (not tt),
# but a → tt still propagates through recursion, giving (1 U b)
check('G(a) & (a U b)', 'G(a) & (1 U b)')

# U-specific: b globally false from G!b in an And context
# G!b makes b globally false → (a U b) = ff → And = ff
check('G!b & (a U b)', '0')

# W is not U: b globally false does NOT make (a W b) = ff directly,
# but b → ff still propagates through the recursion, giving (a W 0)
check('G!b & (a W b)', 'G!b & (a W 0)')

# R/M in And with !b: !b makes b locally false → (a R b) = ff → And = ff
check('!b & (a R b)', '0')

# Same for M
check('!b & (a M b)', '0')

# G!b makes b globally false → (a R b) = ff → And short-circuits to ff
check('G!b & (a R b)', '0')

# G!b makes b globally false → (a M b) = ff → And short-circuits to ff
check('G!b & (a M b)', '0')

# R-specific: b globally true (from G(b)) → (a R b) = tt → dropped
check('G(b) & (a R b)', 'G(b)')

# M does NOT share the right-operand global-true check
# but b → tt propagates through recursion, giving (a M 1)
check('G(b) & (a M b)', 'G(b) & (a M 1)')

# M-specific: left operand globally false → F a ≡ ff → (a M b) = ff
# → And short-circuits to 0
check('G!a & (a M b)', '0')

# R does NOT share the left-operand check,
# but a → ff still propagates through recursion, giving (0 R b)
check('G!a & (a R b)', 'G!a & (0 R b)')

# -- Implies: cross-propagation --

# β = b is false for α: b becomes ff in (a | b), leaving a
check('(a | b) -> b', 'a -> b')

# α = a is true for β: a becomes tt in (a & b), leaving b
check('a -> (a & b)', 'a -> b')

# -- And: a & F(a) -> a (child of F is locally true) --

# a is locally true -> F(a): child 'a' is locally true -> F(a)=tt -> dropped
check('a & F(a)', 'a')

# b & (a & F(a)): same, with extra conjunct
check('b & a & F(a)', 'b & a')

# G(a) & F(a) -> G(a): a is globally true -> F(a)=tt -> dropped
check('G(a) & F(a)', 'G(a)')

# -- Or: F(a) | a -> F(a) (a is locally false, already handled) --

# a is locally false -> a simplifies to ff -> dropped, leaving F(a)
check('F(a) | a', 'F(a)')

# F(a) | (a & b): a is locally false -> (a & b) = ff -> dropped
check('F(a) | (a & b)', 'F(a)')

# -- And: G(a) & a -> G(a) (a is globally true from G) --

# G(a) makes a globally true -> a simplifies to tt in And -> dropped
check('G(a) & a', 'G(a)')

# -- G: local true ≠ global true: but when another child G(!a)
# contributes !a as GLOBALLY true, the standalone !a simplifies to tt.
check('!a & G(!a)', 'G!a')

# -- Or: Boolean absorption A | (A & B) = A --

check('G!a | (G!a & !b)', 'G!a')
check('a | (a & b)', 'a')

# -- Nested R/M: recursive decomposition in add_true --

# (a R (b R c)): inner b R c contributes c as locally true
check('(a R (b R c)) & c', 'a R (b R c)')
check('(a R (b R c)) & Fc', 'a R (b R c)')
check('(a R (b R c)) & XFc', 'a R (b R c) & XFc')

# (a M (b M c)): inner b M c contributes c as locally true
check('(a M (b M c)) & c', 'a M (b M c)')
check('(a M (b M c)) & Fc', 'a M (b M c)')
check('(a M (b M c)) & XFc', 'a M (b M c) & XFc')

# Cross-nested: R with inner M
check('(a R (b M c)) & c', 'a R (b M c)')
check('(a R (b M c)) & Fc', 'a R (b M c)')
check('(a R (b M c)) & XFc', 'a R (b M c) & XFc')

# 3 levels deep: d propagates through two nested R operators
check('(a R (b R (c R d))) & d', 'a R (b R (c R d))')
check('(a R (b R (c R d))) & (e U d)', 'a R (b R (c R d))')

# G(a R b) makes a R b globally true, which makes b globally true
check('G(a R b) & b', 'G(a R b)')

# -- Nested U/W: recursive decomposition in add_false --

# (a U (b U c)): inner b U c contributes c as locally false
check('(a U (b U c)) | c', 'a U (b U c)')

# (a W (b W c)): inner b W c contributes c as locally false
check('(a W (b W c)) | c', 'a W (b W c)')

# Cross-nested: U with inner W
check('(a U (b W c)) | c', 'a U (b W c)')

# F(a U b) makes a U b globally false, which makes b globally false
check('F(a U b) | b', 'F(a U b)')

# c locally false from nested U simplifies (c | d) to d
check('(a U (b U c)) | (c | d)', '(a U (b U c)) | d')

# -- Local facts do not cross temporal operators --

# b is locally true in outer And, but G(b | c) drops local facts:
# b is NOT visible inside G(b|c), so it should remain unchanged.
check('b & G(b | c)', 'b & G(b | c)')

# Globals from different branches do not interact
check('(Ga & (a | b)) | (Gc & (a & c))', 'Ga | (a & Gc)')

print('unit_propagate: all tests passed')

# -- Soundness check on random formulas --
# Verify that unit_propagate produces equivalent formulas.
gen = spot.randltl(3, simplify=0)
for i in range(200):
    f = next(gen)
    g = spot.unit_propagate(f)
    tc.assertTrue(spot.are_equivalent(f, g),
                  f'unit_propagate({f}) = {g} is not equivalent')

print('unit_propagate: soundness check passed')

# -- Idempotence check --
gen = spot.randltl(3, simplify=0)
for i in range(200):
    f = next(gen)
    g = spot.unit_propagate(f)
    h = spot.unit_propagate(g)
    tc.assertEqual(g, h,
                   f'unit_propagate not idempotent: {f} -> {g} -> {h}')

print('unit_propagate: idempotence check passed')
