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

import spot, buddy
from unittest import TestCase
tc = TestCase()

g = spot.automaton("""HOA: v1 States: 9 Start: 0 AP: 2 "a" "b"
acc-name: Streett 1 Acceptance: 2 Fin(0) | Inf(1) properties:
trans-labels explicit-labels state-acc spot-state-player: 0 1 0 1 0 1
0 1 1 --BODY-- State: 0 {1} [1] 1 [1] 3 State: 1 {1} [1] 2 State: 2
{1} [0] 8 State: 3 {1} [1] 4 State: 4 {1} [0] 5 State: 5 {1} [0] 6
State: 6 {1} [1] 7 State: 7 State: 8 {1} [0] 2 --END--""")

tc.assertFalse(spot.solve_parity_game(g))

s = spot.highlight_strategy(g).to_str("HOA", "1.1")
tc.assertEqual(s, """HOA: v1.1
States: 9
Start: 0
AP: 2 "a" "b"
acc-name: Streett 1
Acceptance: 2 Fin(0) | Inf(1)
properties: trans-labels explicit-labels state-acc !complete
properties: !deterministic exist-branch
spot.highlight.states: 0 5 1 4 2 4 3 5 4 5 5 5 6 5 7 5 8 4
spot.highlight.edges: 2 5 3 4 6 5 8 5 9 4
spot.state-player: 0 1 0 1 0 1 0 1 1
--BODY--
State: 0 {1}
[1] 1
[1] 3
State: 1 {1}
[1] 2
State: 2 {1}
[0] 8
State: 3 {1}
[1] 4
State: 4 {1}
[0] 5
State: 5 {1}
[0] 6
State: 6 {1}
[1] 7
State: 7
State: 8 {1}
[0] 2
--END--""")

# Prefer the current subgame over an already solved exit.  This is the
# situation where a sink is still being solved and has no subgame number yet.
short_cycle = spot.automaton("""HOA: v1
States: 4
Start: 0
AP: 0
acc-name: parity max odd 1
Acceptance: 1 Inf(0)
properties: trans-acc explicit-labels spot-state-player: 0 1 0 0
--BODY--
State: 0
[t] 1 {0}
[t] 2 {0}
State: 1
[t] 3 {0}
State: 2
[t] 0 {0}
State: 3
[t] 3 {0}
--END--""")
spot.solve_parity_game(short_cycle)
short_strategy = spot.get_strategy(short_cycle)
tc.assertEqual(short_strategy[0], 2)

# The accepting-edge strategy path should prefer the current winning
# attractor over an older exit, without changing the winning region.
issue649 = spot.formula("(F(i0 & X(i1)) <-> Fo)").translate('parity', 'det')
issue649 = spot.split_2step(
    issue649, buddy.bdd_ithvar(issue649.register_ap('o')))
spot.solve_game(issue649)
issue649_strategy = spot.get_strategy(issue649)
tc.assertEqual(issue649_strategy[10], 19)

# Testing case where parity_game optimization
# lead to wrong results
si = spot.synthesis_info()

game = spot.automaton("""HOA: v1
States: 27
Start: 7
AP: 11 "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k"
acc-name: parity max odd 3
Acceptance: 3 Fin(2) & (Inf(1) | Fin(0))
properties: trans-labels explicit-labels trans-acc colored
properties: deterministic
spot-state-player: 0 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
controllable-AP: 0 1 2 3 4 5 6 7
--BODY--
State: 0
[t] 8 {0}
State: 1
[8&9] 8 {0}
[!8&!10 | !9&!10] 9 {0}
[!8&10 | !9&10] 10 {0}
State: 2
[8&9] 8 {0}
[!8&!10 | !9&!10] 11 {0}
[!8&10 | !9&10] 12 {0}
State: 3
[8&9] 8 {0}
[!9&!10] 13 {0}
[!8&10 | !9&10] 14 {0}
[!8&9&!10] 15 {0}
State: 4
[8&9] 8 {0}
[!8&!10 | !9&!10] 16 {0}
[!8&!9&10] 17 {0}
[!8&9&10] 18 {0}
[8&!9&10] 19 {0}
State: 5
[8&9] 8 {0}
[!9&!10] 20 {0}
[!8&10 | !9&10] 21 {0}
[!8&9&!10] 22 {0}
State: 6
[8&9] 8 {0}
[!8&!10 | !9&!10] 23 {0}
[!8&!9&10] 24 {0}
[!8&9&10] 25 {0}
[8&!9&10] 26 {0}
State: 7
[8&9] 8 {0}
[!9&!10] 13 {0}
[!8&9&!10] 15 {0}
[!8&!9&10] 17 {0}
[!8&9&10] 18 {0}
[8&!9&10] 19 {0}
State: 8
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 |
!0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 | !0&1&!2&!3&4&!5&!6&7 |
!0&1&!2&!3&4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
 0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 0 {1}
State: 9
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 1 {2}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 |
!0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {2}
State: 10
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 0 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 |
!0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {2}
State: 11
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 0 {1}
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {2}
State: 12
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {2}
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {2}
State: 13
[!0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7] 1 {1}
[!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&4&!5&!6&7] 3 {1}
[!0&!1&2&3&!4&!5&!6&7] 5 {1}
State: 14
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 0 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 |
!0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
State: 15
[!0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7] 1 {1}
[!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&4&!5&!6&7] 4 {1}
[!0&!1&2&3&!4&!5&!6&7] 6 {1}
State: 16
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 1 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 |
!0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
State: 17
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 0 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&3&!4&!5&!6&7] 6 {1}
State: 18
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 0 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&3&!4&!5&!6&7] 5 {1}
State: 19
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&!1&2&!3&4&!5&!6&7 |
!0&!1&2&!3&4&!5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7] 0 {1}
[!0&!1&2&3&!4&!5&!6&7 | !0&!1&2&3&!4&!5&6&!7 | !0&1&!2&3&!4&!5&!6&7 |
0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&3&!4&!5&6&!7] 6 {1}
State: 20
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 0 {1}
[!0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&!4&5&!6&7] 3 {1}
State: 21
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 2 {1}
State: 22
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 0 {1}
[!0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 | !0&1&!2&!3&!4&5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&!4&5&!6&7] 4 {1}
State: 23
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&!3&4&!5&6&!7 |
!0&1&!2&3&!4&!5&!6&7 | !0&1&!2&3&!4&!5&6&!7 | 0&!1&!2&!3&4&!5&!6&7 |
0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 | 0&!1&!2&3&!4&!5&6&!7] 0 {1}
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
!0&1&!2&!3&!4&5&6&!7 | 0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
State: 24
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&6&!7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 |
0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&!3&!4&5&!6&7] 4 {1}
[!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&3&!4&!5&!6&7] 6 {1}
State: 25
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&6&!7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&6&!7 | !0&1&!2&3&!4&!5&6&!7 |
0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 |
0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&!3&!4&5&!6&7] 3 {1}
[!0&1&!2&!3&4&!5&!6&7 | !0&1&!2&3&!4&!5&!6&7] 5 {1}
State: 26
[!0&!1&2&!3&!4&5&!6&7 | !0&!1&2&!3&!4&5&6&!7 | !0&1&!2&!3&!4&5&!6&7 |
0&!1&!2&!3&!4&5&!6&7 | 0&!1&!2&!3&!4&5&6&!7] 1 {1}
[!0&!1&2&!3&4&!5&!6&7 | !0&!1&2&!3&4&!5&6&!7 | !0&!1&2&3&!4&!5&!6&7 |
!0&!1&2&3&!4&!5&6&!7 | !0&1&!2&!3&4&!5&!6&7 | !0&1&!2&3&!4&!5&!6&7 |
0&!1&!2&!3&4&!5&!6&7 | 0&!1&!2&!3&4&!5&6&!7 | 0&!1&!2&3&!4&!5&!6&7 |
0&!1&!2&3&!4&!5&6&!7] 2 {1}
[!0&1&!2&!3&!4&5&6&!7] 4 {1}
[!0&1&!2&!3&4&!5&6&!7 | !0&1&!2&3&!4&!5&6&!7] 6 {1}
--END--""")

tc.assertTrue(spot.solve_game(game, si))

games = spot.split_edges(game)
spot.set_state_players(games, spot.get_state_players(game))
tc.assertTrue(spot.solve_game(games, si))

g = spot.translate("GF(a&X(a)) -> GFb")
a = buddy.bdd_ithvar(g.register_ap("a"))
b = buddy.bdd_ithvar(g.register_ap("b"))
gdpa = spot.tgba_determinize(spot.degeneralize_tba(g),
                             False, True, True, False)
spot.change_parity_here(gdpa, spot.parity_kind_max, spot.parity_style_odd)
gsdpa = spot.split_2step(gdpa, b, True)
spot.colorize_parity_here(gsdpa, True)
tc.assertTrue(spot.solve_parity_game(gsdpa))
gsdpa_solved_ref = spot.automaton(
    """HOA: v1.1
States: 18
Start: 0
AP: 2 "a" "b"
acc-name: parity max odd 5
Acceptance: 5 Fin(4) & (Inf(3) | (Fin(2) & (Inf(1) | Fin(0))))
properties: trans-labels explicit-labels trans-acc colored complete
properties: deterministic
spot.highlight.states: 0 4 1 4 2 4 3 4 4 4 5 4 6 4 7 4 8 4 9 4 """
    +"""10 4 11 4 12 4 13 4 14 4 15 4 16 4 17 4
spot.highlight.edges: 15 4 17 4 20 4 22 4 24 4 26 4 28 4 30 4 31 4 32 4 33 4
spot.state-player: 0 0 0 0 0 0 0 1 1 1 1 1 1 1 1 1 1 1
controllable-AP: 1
--BODY--
State: 0
[!0] 7 {0}
[0] 8 {0}
State: 1
[!0] 9 {3}
[0] 10 {3}
State: 2
[!0] 11 {1}
[0] 12 {1}
State: 3
[!0] 9 {3}
[0] 13 {4}
State: 4
[!0] 11 {1}
[0] 14 {2}
State: 5
[!0] 15 {3}
[0] 16 {3}
State: 6
[!0] 15 {3}
[0] 17 {4}
State: 7
[!1] 1 {0}
[1] 2 {0}
State: 8
[!1] 3 {0}
[1] 4 {0}
State: 9
[!1] 1 {3}
[1] 5 {3}
State: 10
[!1] 3 {3}
[1] 6 {3}
State: 11
[!1] 2 {1}
[1] 2 {3}
State: 12
[!1] 4 {1}
[1] 4 {3}
State: 13
[!1] 3 {4}
[1] 4 {4}
State: 14
[!1] 4 {2}
[1] 4 {3}
State: 15
[t] 5 {3}
State: 16
[t] 6 {3}
State: 17
[t] 4 {4}
--END--"""
)
tc.assertTrue(spot.solve_parity_game(gsdpa_solved_ref))

# Check for the same language
tc.assertTrue(spot.are_equivalent(gsdpa, gsdpa_solved_ref))
# Check if the winning regions are the same for env states
# Env states should by construction have the same number as before
players_new = spot.get_state_players(gsdpa)
players_ref = spot.get_state_players(gsdpa_solved_ref)
# States maybe renumbered, but remain in the same "class"
tc.assertEqual(players_new, players_ref)
# Check that env states have the same winner
winners_new = spot.get_state_winners(gsdpa)
winners_ref = spot.get_state_winners(gsdpa_solved_ref)

tc.assertTrue(all([wn == wr for (wn, wr, p) in
                   zip(winners_new, winners_ref, players_ref)
                  if not p]))

def maximize_colors(aut, is_max):
    ns = aut.num_sets()
    v = []
    if is_max:
        for c in range(ns+1):
            v.append(spot.mark_t(list(range(c))))
        for e in aut.edges():
            e.acc = v[e.acc.max_set()]
    else:
        for c in range(ns+1):
            v.append(spot.mark_t(list(range(c, ns))))
        v.insert(0, spot.mark_t([]))
        for e in aut.edges():
            e.acc = v[e.acc.min_set()]

# Test the different parity conditions
gdpa = spot.tgba_determinize(spot.degeneralize_tba(g),
                             False, True, True, False)

g_test = spot.change_parity(gdpa, spot.parity_kind_max, spot.parity_style_odd)
g_test_split = spot.split_2step(g_test, b, True)
sp = spot.get_state_players(g_test_split)
g_test_split_c = spot.colorize_parity(g_test_split)
spot.set_state_players(g_test_split_c, sp)
tc.assertTrue(spot.solve_parity_game(g_test_split_c))
c_strat = spot.get_strategy(g_test_split_c)
# All versions of parity need to result in the same strategy
for kind in [spot.parity_kind_min, spot.parity_kind_max]:
    for style in [spot.parity_style_even, spot.parity_style_odd]:
        g_test_split1 = spot.change_parity(g_test_split, kind, style)
        spot.set_state_players(g_test_split1, sp)
        tc.assertTrue(spot.solve_parity_game(g_test_split1))
        c_strat1 = spot.get_strategy(g_test_split1)
        tc.assertTrue(c_strat == c_strat1)
        # Same test, but adding a lot of useless colors in the game
        g_test_split2 = spot.change_parity(g_test_split, kind, style)
        maximize_colors(g_test_split2, kind == spot.parity_kind_max)
        spot.set_state_players(g_test_split2, sp)
        tc.assertTrue(spot.solve_parity_game(g_test_split2))
        c_strat2 = spot.get_strategy(g_test_split2)
        tc.assertTrue(c_strat == c_strat2)


# Check the strategy contract for all solved states.  Entries for states
# whose owner is not the winner are intentionally unspecified.
def check_strategy_contract(aut, global_solve=False):
    spot.solve_parity_game(aut, global_solve)
    winners = spot.get_state_winners(aut)
    owners = spot.get_state_players(aut)
    strategy = spot.get_strategy(aut)
    edges = list(aut.edges())
    edge_numbers = {aut.edge_number(e): e for e in edges}
    for state in range(aut.num_states()):
        if not global_solve and state not in reachable_states(aut):
            continue
        if owners[state] == winners[state]:
            tc.assertIn(strategy[state], edge_numbers)
            edge = edge_numbers[strategy[state]]
            tc.assertEqual(edge.src, state)
            tc.assertEqual(winners[edge.dst], winners[state])


def reachable_states(aut):
    seen = set()
    todo = [aut.get_init_state_number()]
    while todo:
        state = todo.pop()
        if state in seen:
            continue
        seen.add(state)
        todo.extend(e.dst for e in aut.out(state))
    return seen


# Test that strategies are not appended
# if solve is called multiple times
aut = spot.make_twa_graph()
aut.set_buchi()
aut.new_states(2)
aut.new_edge(0,1,buddy.bddtrue, [0])
aut.new_edge(1,0,buddy.bddtrue, [])
spot.set_state_players(aut, [False, True])
spot.solve_game(aut)
S1 = list(spot.get_strategy(aut))
spot.solve_game(aut)
S2 = list(spot.get_strategy(aut))
tc.assertEqual(S1, S2)

# Strategy entries are valid in local and global mode.
check_strategy_contract(aut)
aut.new_states(1)
# The new state is unreachable and must be solved only globally.
spot.set_state_players(aut, [False, True, False])
aut.new_edge(2, 2, buddy.bddtrue, [0])
check_strategy_contract(aut, True)

# Empty marks are supported: they are normalized as the lowest priority for
# max-parity (the solver's internal equivalent representation uses -1).
empty = spot.make_twa_graph()
empty.set_buchi()
empty.new_states(1)
empty.new_edge(0, 0, buddy.bddtrue, [])
spot.set_state_players(empty, [True])
tc.assertFalse(spot.solve_parity_game(empty))

# A parity game with a dead end is outside the solver's precondition.
# Keep this test as documentation of the currently unsupported input rather
# than asserting a result whose finite-play semantics are not defined.

# The strategy/winner getters and setters.
strat = [0] * g.num_states()
spot.set_strategy(g, strat)
spot.set_state_winners(g, [True] * g.num_states())
spot.set_state_winner(g, 0, True)
tc.assertEqual(len(spot.get_strategy(g)), g.num_states())
tc.assertTrue(spot.get_state_winner(g, 0))
try:
    spot.set_state_winner(g, 100, True)
    exit(1)
except RuntimeError as e:
    tc.assertIn('invalid state number', str(e))
try:
    spot.set_strategy(g, [0] * (g.num_states() - 3))
    exit(1)
except RuntimeError as e:
    tc.assertIn('same size as the automaton', str(e))
