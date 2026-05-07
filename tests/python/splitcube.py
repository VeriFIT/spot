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

# Tests for bdd_splitcube (issue #644): split a cube into the part
# using variables in a given set and the part using the rest.

import buddy

buddy.bdd_init(10000, 10000)
buddy.bdd_setvarnum(4)

import spot
from unittest import TestCase
tc = TestCase()

p = [buddy.bdd_ithvar(i) for i in range(4)]

def varset(*indices):
    r = buddy.bddtrue
    for i in indices:
        r &= p[i]
    return r


cube = p[0] & p[1] & -p[2] & p[3]
var = varset(0, 2)
res_in, res_out = buddy.bdd_splitcube(cube, var)
tc.assertEqual(res_in, buddy.bdd_existcomp(cube, var))
tc.assertEqual(res_out, buddy.bdd_exist(cube, var))
tc.assertEqual(res_in & res_out, cube)

var_all = varset(0, 1, 2, 3)
res_in, res_out = buddy.bdd_splitcube(cube, var_all)
tc.assertEqual(res_in, cube)
tc.assertEqual(res_out, buddy.bddtrue)

res_in, res_out = buddy.bdd_splitcube(cube, buddy.bddtrue)
tc.assertEqual(res_in, buddy.bddtrue)
tc.assertEqual(res_out, cube)

res_in, res_out = buddy.bdd_splitcube(buddy.bddtrue, var)
tc.assertEqual(res_in, buddy.bddtrue)
tc.assertEqual(res_out, buddy.bddtrue)

res_in, res_out = buddy.bdd_splitcube(p[0], varset(0))
tc.assertEqual(res_in, p[0])
tc.assertEqual(res_out, buddy.bddtrue)

res_in, res_out = buddy.bdd_splitcube(-p[1], varset(1))
tc.assertEqual(res_in, - p[1])
tc.assertEqual(res_out, buddy.bddtrue)

res_in, res_out = buddy.bdd_splitcube(p[2], varset(0))
tc.assertEqual(res_in, buddy.bddtrue)
tc.assertEqual(res_out, p[2])

f = (p[0] | p[1]) & (p[2] | -p[3])
var02 = varset(0, 2)
isop = spot.minato_isop(f)
cube = isop.next()
while cube != buddy.bddfalse:
    res_in, res_out = buddy.bdd_splitcube(cube, var02)
    tc.assertEqual(res_in, buddy.bdd_existcomp(cube, var02))
    tc.assertEqual(res_out, buddy.bdd_exist(cube, var02))
    tc.assertEqual(res_in & res_out, cube)
    cube = isop.next()
