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


def analyze(formula, outputs):
    aut = spot.translate(formula)
    out_vars = [aut.register_ap(ap) for ap in outputs]
    dep = list(spot.analyze_dependent_output(aut, out_vars))
    nondep = [v for v in out_vars if v not in dep]
    return {
        "dep": dep,
        "nondep": nondep,
        "by_name": dict(zip(outputs, out_vars)),
    }


# Temporal dependency case:
# G(o1 <-> Xo2) should identify o2 as dependent on o1 (via history).
r = analyze('G(o1 <-> Xo2)', ['o1', 'o2'])
tc.assertEqual(r['dep'], [r['by_name']['o2']])
tc.assertEqual(r['nondep'], [r['by_name']['o1']])


# Mixed temporal/Boolean case with one-hot outputs:
# o0 is dependent on {o1,o2}.
r = analyze('FG(!i -> (GF(o0)|(GF(o1)&GF(o2)))) & '
            'G((o0&!o1&!o2)|(!o0&o1&!o2)|(!o0&!o1&o2))',
            ['o0', 'o1', 'o2'])
tc.assertEqual(r['dep'], [r['by_name']['o0']])
tc.assertEqual(r['nondep'], [r['by_name']['o1'], r['by_name']['o2']])
