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

# Test the "Rabin-like" and "Streett-like" acceptance patterns
# understood by acc_cond::acc_code's string constructor (and
# consequently by randaut's -A option).
#
# Unlike "Rabin RANGE"/"Streett RANGE" (where RANGE is a number of
# acceptance pairs, each using two fresh acceptance sets),
# "Rabin-like RANGE"/"Streett-like RANGE" use RANGE as the number of
# distinct acceptance sets ("colors") to use: each color is used at
# least once, and, with an optional trailing PROBABILITY (0 by
# default), may be reused one or more additional times.  A shuffled
# list of all occurrences of these colors is then split into
# consecutive pairs to build the Fin/Inf terms of the Rabin/Streett
# clauses; if there is an odd number of occurrences, the last one is
# used alone, contributing a lone Fin(x) term.

import spot
from unittest import TestCase
tc = TestCase()

spot.srand(0)

# Without a probability, "Rabin-like n"/"Streett-like n" always use
# each of the n colors exactly once, so the acceptance uses exactly
# n sets.  The resulting formula has (n // 2) Fin/Inf pair-clauses,
# plus one extra lone Fin(x) clause if n is odd; for n == 0 the
# formula degenerates to the neutral element (f for Rabin-like, t
# for Streett-like).
for n in range(0, 9):
    pairs = n // 2
    clauses = pairs + (n % 2)
    seps = max(clauses - 1, 0)
    for kind, sep in (('Rabin-like', '|'), ('Streett-like', '&')):
        c = spot.acc_code(f'{kind} {n}')
        tc.assertEqual(c.used_sets().count(), n)
        tc.assertEqual(str(c).count(sep), seps)

# Rabin-like/Streett-like with 0 colors is the same as Rabin/Streett
# with 0 pairs.
tc.assertEqual(str(spot.acc_code('Rabin-like 0')), 'f')
tc.assertEqual(str(spot.acc_code('Streett-like 0')), 't')
tc.assertEqual(str(spot.acc_code('Rabin 0')), 'f')
tc.assertEqual(str(spot.acc_code('Streett 0')), 't')

# With an odd number of colors, one clause of the formula should be
# a lone Fin(x) (i.e., the trailing, unpaired color).
for kind in ('Rabin-like', 'Streett-like'):
    for n in (1, 3, 5, 7):
        c = spot.acc_code(f'{kind} {n}')
        tc.assertEqual(c.used_sets().count(), n)
        terms = str(c).split(' | ' if kind == 'Rabin-like' else ' & ')
        lone_fin = [t for t in terms if t.startswith('Fin(')
                    and '&' not in t]
        tc.assertEqual(len(lone_fin), 1)

# RANGE always gives the exact number of distinct colors used (each
# color is used at least once), regardless of the reuse probability:
# a high PROBABILITY does not change the number of distinct sets, it
# only makes some colors appear more than once, which increases the
# number of Fin/Inf clauses in the formula.  Check that, on average,
# a higher probability yields more clauses (i.e., more occurrences
# of the colors) than a probability of 0.
def count_clauses(kind, n, p):
    c = spot.acc_code(f'{kind} {n} {p}')
    tc.assertEqual(c.used_sets().count(), n)
    sep = '|' if kind == 'Rabin-like' else '&'
    return str(c).count(sep) + 1

trials = 200
for kind in ('Rabin-like', 'Streett-like'):
    base = sum(count_clauses(kind, 6, 0) for _ in range(trials))
    reused = sum(count_clauses(kind, 6, 0.9) for _ in range(trials))
    tc.assertGreater(reused, base)

# A PROBABILITY of exactly 1 (or more) is rejected.
for kind in ('Rabin-like', 'Streett-like', 'random'):
    for p in ('1', '1.0'):
        try:
            spot.acc_code(f'{kind} 3 {p}')
        except spot.parse_error as e:
            tc.assertIn('should be <1', str(e))
        else:
            raise RuntimeError('missing exception for '
                                f'"{kind} 3 {p}"')
    # Probabilities out of [0,1] are rejected for a different reason.
    try:
        spot.acc_code(f'{kind} 3 2')
    except spot.parse_error as e:
        tc.assertIn('between 0 and 1', str(e))
    else:
        raise RuntimeError(f'missing exception for "{kind} 3 2"')

# Sanity check: "Rabin-like n" and "Streett-like n" are recognized as
# valid acceptance conditions usable with an acc_cond.
a = spot.acc_cond(6, 'Rabin-like 6')
tc.assertEqual(a.num_sets(), 6)
a = spot.acc_cond(6, 'Streett-like 6')
tc.assertEqual(a.num_sets(), 6)
