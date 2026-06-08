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

a = spot.translate("!(p2->p0)", "generic", "deterministic", "complete", "SBAcc")
m = spot.dtwa_to_mtdswa(a)
m.sinks_as_states()
am = m.as_twa(False, True, False)
pxor = spot.product_xor(am, a)

tc.assertTrue(pxor.is_empty(), "MTDSwA as TWA "
              + "is not equivalent to original TWA")