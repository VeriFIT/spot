#!/usr/bin/env python3
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

# to_dca() is a convenient sink for the co-Büchi automaton
# constructions in spot/twaalgos/cobuchi.hh.  It takes a
# nondeterministic automaton and returns an equivalent
# *deterministic* co-Büchi automaton (DCA).  The translate() function
# may produce a nondeterministic automaton for our formula, so the
# equivalence check is meaningful.
f = spot.formula('F(G(a)|G(b))')
aut = spot.translate(f)
dca = spot.to_dca(aut)
tc.assertTrue(dca.is_deterministic())
tc.assertTrue(dca.acc().is_co_buchi())
tc.assertTrue(spot.are_equivalent(aut, dca))

# A second argument, when True, tells to_dca() to keep the
# implications between the variables during the subset construction.
# This can increase the size of the resulting automaton compared to
# the previous one, but it preserves the equivalence.
dca2 = spot.to_dca(aut, True)
tc.assertTrue(dca2.is_deterministic())
tc.assertTrue(dca2.acc().is_co_buchi())
tc.assertTrue(spot.are_equivalent(aut, dca2))

# nsa_to_dca() is a variant that requires its input to be a
# "nondeterministic safety automaton" (NSA): a nondeterministic
# automaton whose accepting and non-accepting runs all reject the
# same words (an automaton whose acceptance can be replaced by the
# initial co-Büchi acceptance without changing the language).  to_dca()
# internally converts its argument, so nsa_to_dca() can be applied to
# any automaton; here we reuse our translated automaton and check that
# the result is again a DCA equivalent to it.
dca3 = spot.nsa_to_dca(aut)
tc.assertTrue(dca3.is_deterministic())
tc.assertTrue(dca3.acc().is_co_buchi())
tc.assertTrue(spot.are_equivalent(aut, dca3))

# nsa_to_dca(aut, keep_implications) is also valid.
dca4 = spot.nsa_to_dca(aut, True)
tc.assertTrue(dca4.is_deterministic())
tc.assertTrue(dca4.acc().is_co_buchi())
tc.assertTrue(spot.are_equivalent(aut, dca4))
