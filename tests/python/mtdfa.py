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

# twadfa_to_mtdfa() in Spot 2.14.1 was not registering atomic
# proposition correctly, causing the following two tests to fail.

a = spot.twadfa_to_mtdfa(spot.translate('a R b', 'deterministic'));

tc.assertEqual(sorted(a.ap_name() for a in a.aps), ['a', 'b'])

hoa = a.as_twa().to_str('hoa')
tc.assertEqual(hoa, '''HOA: v1
States: 2
Start: 0
AP: 2 "a" "b"
acc-name: Buchi
Acceptance: 1 Inf(0)
properties: trans-labels explicit-labels trans-acc colored
properties: deterministic
--BODY--
State: 0
[!0&1] 0 {0}
[0&1] 1 {0}
State: 1
[t] 1 {0}
--END--''')
