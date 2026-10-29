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

import buddy
import random
import sys

buddy.bdd_init(10000, 10000)
buddy.bdd_setvarnum(6)

a = buddy.bdd_ithvar(0)
b = buddy.bdd_ithvar(1)
c = buddy.bdd_ithvar(2)

w = -a & -b | -c & b | a & -b

import spot

from unittest import TestCase
tc = TestCase()


def cubes(isop):
    """Consume an isop and return its list of cubes."""
    res = []
    i = isop.next()
    while i != buddy.bddfalse:
        res.append(i)
        i = isop.next()
    return res


def support_vars(f):
    res = set()
    s = buddy.bdd_support(f)
    while s != buddy.bddtrue:
        res.add(buddy.bdd_var(s))
        s = buddy.bdd_high(s)
    return res


def cube_of(vs):
    res = buddy.bddtrue
    for v in sorted(vs):
        res = buddy.bdd_and(res, buddy.bdd_ithvar(v))
    return res


def is_positive_unate(f, v):
    # bdd_restrict by !v (resp. v) is exactly the cofactor f|v=0
    # (resp. f|v=1), so this is f|v=0 -> f|v=1.
    return bool(buddy.bdd_implies(
        buddy.bdd_restrict(f, buddy.bdd_nithvar(v)),
        buddy.bdd_restrict(f, buddy.bdd_ithvar(v))))


# The historical test.  w = !b | !c.
l = cubes(spot.minato_isop(w))
for i in l:
    buddy.bdd_printset(i)
    spot.nl_cout()
tc.assertEqual(l, [-b, -c])

# a&b|c is positive-unate in b and c.
f = a & b | c
tc.assertEqual(cubes(spot.minato_isop(f)),
              cubes(spot.minato_isop(f, buddy.bdd_support(f), b & c)))

# The positive-unate shortcut must never emit a negative literal for
# a declared positive variable.  In a cube BDD, a negative literal is
# a node whose high branch is false, so walking the high branches of
# a positive cube reaches bddtrue, while a negative literal reaches
# bddfalse.
for cube in cubes(spot.minato_isop(f, buddy.bdd_support(f), b & c)):
    cur = cube
    while cur != buddy.bddtrue and cur != buddy.bddfalse:
        tc.assertNotEqual(buddy.bdd_high(cur), buddy.bddfalse)
        cur = buddy.bdd_high(cur)

# bddtrue means "no positive variable" and must be a no-op.
tc.assertEqual(cubes(spot.minato_isop(f)),
              cubes(spot.minato_isop(f, buddy.bdd_support(f), buddy.bddtrue)))

# The (input_min, input_max) constructor is unaffected.
tc.assertEqual(cubes(spot.minato_isop(f)),
              cubes(spot.minato_isop(f, f, True)))

# Randomised check: whenever we declare the variables in which f is
# really positive-unate, the shortcut must return exactly the same
# sequence of cubes as the general algorithm.  This also exercises
# nodes where f_min != f_max.
random.seed(20261028)
nvars = 6
for trial in range(300):
    f = buddy.bddfalse
    for _ in range(random.randint(1, 8)):
        cube = buddy.bddtrue
        for v in range(nvars):
            r = random.random()
            if r < 0.3:
                cube = buddy.bdd_and(cube, buddy.bdd_ithvar(v))
            elif r < 0.6:
                cube = buddy.bdd_and(cube, buddy.bdd_nithvar(v))
        f = buddy.bdd_or(f, cube)
    if f == buddy.bddfalse or f == buddy.bddtrue:
        continue
    sup = support_vars(f)
    positive = {v for v in sup if is_positive_unate(f, v)}
    if not positive:
        continue
    pos_cube = cube_of(positive)
    expected = cubes(spot.minato_isop(f))
    got = cubes(spot.minato_isop(f, buddy.bdd_support(f), pos_cube))
    tc.assertEqual(got, expected)
    for cube in got:
        cur = cube
        while cur != buddy.bddtrue and cur != buddy.bddfalse:
            v = buddy.bdd_var(cur)
            if v in positive:
                tc.assertNotEqual(buddy.bdd_high(cur), buddy.bddfalse)
            cur = buddy.bdd_high(cur)
    # Also check that the shortcut composes with a restricted VARS.
    subset = set(random.sample(sorted(sup),
                               random.randint(1, len(sup))))
    expected = cubes(spot.minato_isop(f, cube_of(subset)))
    got = cubes(spot.minato_isop(f, cube_of(subset),
                                 cube_of(positive & subset)))
    tc.assertEqual(got, expected)

sys.exit(0)
