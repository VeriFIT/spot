#!/usr/bin/python3
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

# -------------------------------------------------------------------------
# nesting_depth() over formula, with the single-character operator list.
# The character used in the list select which operators to count; "~"
# asks for the formula to be put in negative normal form first.
# -------------------------------------------------------------------------

f = spot.formula('(a -> b) <-> (c & (X d | !e))')
g = spot.formula('(a R b) W (c U (d M F e))')

# All the accepted operator letters must be usable, alone or together.
for ff in [f, g]:
    tc.assertEqual(ff.nesting_depth('X'),
                   spot.nesting_depth(ff, 'X'))
    tc.assertEqual(ff.nesting_depth('~!&|eFGiMRUWX'),
                   spot.nesting_depth(ff, '~!&|eFGiMRUWX'))
    tc.assertEqual(ff.nesting_depth('~!&|eFGiMRUWX'),
                   ff.nesting_depth('~!&|FGiMRUWXe'))

# Any unknown character raises an error.
tc.assertRaises(RuntimeError, spot.nesting_depth, f, '!|?')
tc.assertRaises(RuntimeError, spot.nesting_depth, f, 'no')

# -------------------------------------------------------------------------
# mp_class(): classification in the Manna & Pnueli hierarchy, with or
# without the 'v' (verbose) and 'w' (wide) options.
# -------------------------------------------------------------------------

classes = [
    ('a', 'B', 'guarantee safety',
     'guarantee safety obligation persistence recurrence reactivity'),
    ('FGa', 'P', 'persistence', 'persistence reactivity'),
    ('GFa', 'R', 'recurrence', 'recurrence reactivity'),
    ('a U b', 'G', 'guarantee',
     'guarantee obligation persistence recurrence reactivity'),
    ('Ga', 'S', 'safety',
     'safety obligation persistence recurrence reactivity'),
    ('Fa', 'G', 'guarantee',
     'guarantee obligation persistence recurrence reactivity'),
    ('G(a U b)', 'R', 'recurrence', 'recurrence reactivity'),
]

for s, cls, verb, wideverb in classes:
    f = spot.formula(s)
    tc.assertEqual(spot.mp_class(f), cls, s)
    tc.assertEqual(f.mp_class('v'), verb, s)
    tc.assertEqual(f.mp_class('wv'), wideverb, s)

# Unknown options are rejected.
tc.assertRaises(RuntimeError, spot.mp_class, spot.formula('Ga'), 'bogus')
tc.assertRaises(RuntimeError, spot.mp_class, spot.formula('Ga'), 'vx')