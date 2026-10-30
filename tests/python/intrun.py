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

# This issue was reported by Florian Renkin.  The reduce() call used in
# intersecting_run() was bogus, and could incorrectly reduce a word
# intersecting the product into a word not intersecting the product if the
# acceptance condition uses some Fin.
a, b = spot.automata("""HOA: v1 States: 5 Start: 0 AP: 2 "p0" "p1" acc-name:
Rabin 2 Acceptance: 4 (Fin(0) & Inf(1)) | (Fin(2) & Inf(3)) properties:
trans-labels explicit-labels trans-acc complete properties: deterministic
--BODY-- State: 0 [t] 3 State: 1 [t] 4 {1} State: 2 [0] 2 {1} [!0] 1 {0} State:
3 [t] 1 {1} State: 4 [!0&1] 4 {3} [!0&!1] 3 [0] 2 {0} --END-- HOA: v1 States: 5
Start: 0 AP: 2 "p0" "p1" Acceptance: 3 Inf(2) | (Fin(0) & Inf(1)) properties:
trans-labels explicit-labels trans-acc complete properties: deterministic
--BODY-- State: 0 [t] 3 State: 1 [t] 4 {1 2} State: 2 [0] 2 {1 2} [!0] 1 {0 2}
State: 3 [t] 1 {1 2} State: 4 [!0&1] 4 {2} [!0&!1] 3 {2} [0] 2 {0 2} --END--""")
r = b.intersecting_run(spot.complement(a));
c = spot.twa_word(r).as_automaton()
tc.assertTrue(c.intersects(b))
tc.assertFalse(c.intersects(a))

# The next test came from Philipp Schlehuber-Caissier: running
# as_twa() on a run built from a A.intersecting_run(B) failed to build
# the automaton because it tried to rebuild the run on A and did not
# find transitions matching exactly.  Additionally the idea of merging
# states in as_twa() seems to be a way to create some disasters, so we
# removed that too.
a = spot.translate("a");
b = spot.translate("{a;1;a}");
r = a.intersecting_run(b)
tc.assertEqual(str(r), """Prefix:
  1
  |  a
  0
  |  1
  0
  |  a
Cycle:
  0
  |  1
""")
tc.assertEqual(r.as_twa().to_str(), """HOA: v1
States: 4
Start: 0
AP: 1 "a"
acc-name: all
Acceptance: 0 t
properties: trans-labels explicit-labels state-acc deterministic
--BODY--
State: 0
[0] 1
State: 1
[t] 2
State: 2
[0] 3
State: 3
[t] 3
--END--""")

# spot.intersects() and spot.intersecting_run() work directly on
# explicit automata, without building their product.  Both automata
# are read from the same stream so that they share their BDD dict.
x, y = spot.automata(spot.translate('F a').to_str()
                     + spot.translate('F !a').to_str())
tc.assertTrue(spot.intersects(x, y))
tc.assertTrue(x.intersects(y))
r = spot.intersecting_run(x, y)
tc.assertTrue(r is not None)
w = spot.twa_word(r).as_automaton()
tc.assertTrue(w.intersects(x))
tc.assertTrue(w.intersects(y))

x, y = spot.automata(spot.translate('G a').to_str()
                     + spot.translate('G !a').to_str())
tc.assertFalse(spot.intersects(x, y))
tc.assertEqual(spot.intersecting_run(x, y), None)

# Automata that do not share their BDD dict cannot be intersected: the
# BDD variables would denote different atomic propositions in the two
# automata, so the product would be meaningless.
x = spot.translate('F a')
y = spot.translate('F a', dict=spot.make_bdd_dict())
tc.assertNotEqual(x.get_dict(), y.get_dict())
with tc.assertRaises(RuntimeError) as cm:
    spot.intersects(x, y)
tc.assertIn('bdd_dict', str(cm.exception))
with tc.assertRaises(RuntimeError) as cm:
    spot.intersecting_run(x, y)
tc.assertIn('bdd_dict', str(cm.exception))
