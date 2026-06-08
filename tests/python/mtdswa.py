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

formulas = [
    "true",
    "false",
    "p2 -> p0",
    "p0 | Xp1",
    "Go",
    "G(!p0 U (p0 & X!p0))",
    "\\forall p0: Gp1 <-> p2Up0",
    "GFp0 <-> p2",
    "G(G!p2 R !p2) U G(F(p0 | p1) U p2)",
    "X(0) | X(Gp2 xor !GFp0)",
    "(p0 U p1) & GFp0 & GFp1 & FGp2"
]
twas = [spot.translate(f, "generic", "deterministic", "complete", "SBAcc")
        for f in formulas]
mtdswas = [spot.dtwa_to_mtdswa(twa) for twa in twas]

# Tests products functions for MTDSwAs
def test_mtdswa_products():
    for i in range(len(formulas)):
        for j in range(i, len(formulas)):
            # test all products that exist for both twas and mtdswas
            for prod in [spot.product, spot.product_or, spot.product_xor,
                         spot.product_xnor]:
                m12 = prod(mtdswas[i], mtdswas[j])
                a12 = prod(twas[i], twas[j])
                # Check that the two products are equivalent
                pxor = spot.product_xor(m12.as_twa(True, True, True), a12)
                tc.assertTrue(pxor.is_empty(), "Product of MTDSwAs "
                              + "is not equivalent to product of DTWAs: "
                              + f"{formulas[i]} {prod.__name__} {formulas[j]}")

test_mtdswa_products()