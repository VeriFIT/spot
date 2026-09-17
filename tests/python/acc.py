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

a = spot.acc_cond('parity min odd 5')
tc.assertEqual(str(a.fin_unit_one_split()),
               f'(0, {a!r}, spot.acc_cond(5, "f"))')

a.set_acceptance('Rabin 3')
tc.assertEqual(str(a.fin_unit_one_split()),
               '(0, spot.acc_cond(5, "Inf(1)"), '
               'spot.acc_cond(5, "(Fin(2) & Inf(3)) | (Fin(4) & Inf(5))"))')

a.set_acceptance('(Fin(0)|Inf(3))&(Fin(1)|Inf(4))&(Fin(2)|Inf(5)) |\
(Fin(0)|Inf(4))&(Fin(1)|Inf(5))&(Fin(2)|Inf(3)) |\
(Fin(0)|Inf(5))&(Fin(1)|Inf(3))&(Fin(2)|Inf(4))')

tc.maxDiff = None
tc.assertEqual(str(a.fin_unit_one_split()),
               '(0, spot.acc_cond(5, '
               '"((Fin(1) | Inf(4)) & (Fin(2) | Inf(5))) | '
               '((Fin(1) | Inf(5)) & (Fin(2) | Inf(3))) | '
               '((Fin(1) | Inf(3)) & (Fin(2) | Inf(4)))"), '
               'spot.acc_cond(5, '
               '"(Inf(3) & (Fin(1) | Inf(4)) & (Fin(2) | Inf(5))) | '
               '(Inf(4) & (Fin(1) | Inf(5)) & (Fin(2) | Inf(3))) | '
               '(Inf(5) & (Fin(1) | Inf(3)) & (Fin(2) | Inf(4)))"))')

a = a.remove([4], True)
tc.assertEqual(str(a.fin_unit_one_split()),
               '(1, spot.acc_cond(5, '
               '"(Fin(0) | Inf(3)) & (Fin(2) | Inf(5))"), '
               'spot.acc_cond(5, '
               '"(Fin(0) & (Fin(1) | Inf(5)) & (Fin(2) | Inf(3))) | '
               '((Fin(0) | Inf(5)) & (Fin(1) | Inf(3)) & Fin(2))"))')


a = spot.acc_cond('Fin(0)|Fin(1)|Fin(0)&Inf(0)')
tc.assertEqual(str(a.fin_unit_one_split()),
               '(0, spot.acc_cond(2, "t"), '
               'spot.acc_cond(2, "Fin(1)"))')
tc.assertEqual(str(a.fin_unit_one_split_improved()),
               '(0, spot.acc_cond(2, "t"), '
               'spot.acc_cond(2, "Fin(1)"))')

a = spot.acc_cond('Fin(0)&Inf(2) | Fin(1)&Inf(3)')
tc.assertEqual(str(a.fin_one_split()),
               '(0, spot.acc_cond(4, "Inf(2)"), '
               'spot.acc_cond(4, "Fin(1) & Inf(3)"))')

a = spot.acc_cond('Fin(0)|Fin(1)|(Fin(0)&Inf(2))')
tc.assertEqual(str(a.fin_one_split()),
               '(0, spot.acc_cond(3, "t"), '
               'spot.acc_cond(3, "Fin(1)"))')
tc.assertEqual(str(a.fin_unit_one_split()),
               '(0, spot.acc_cond(3, "t"), '
               'spot.acc_cond(3, "Fin(1)"))')
tc.assertEqual(str(a.fin_unit_one_split_improved()),
               '(0, spot.acc_cond(3, "t"), '
               'spot.acc_cond(3, "Fin(1)"))')

a = spot.acc_cond('(Fin(0)&Inf(3)) | '
                  '(Fin(0)&Inf(2)) | '
                  '(Fin(4)&(Fin(0)|Inf(1))) |'
                  '(Inf(5)&(Fin(0)|Inf(1)))')
tc.assertEqual(str(a.fin_unit_one_split()),
               '(0, spot.acc_cond(6, "Inf(3) | Inf(2)"), '
               'spot.acc_cond(6, "(Fin(4) & (Fin(0) | Inf(1))) '
               '| (Inf(5) & (Fin(0) | Inf(1)))"))')
tc.assertEqual(str(a.fin_unit_one_split_improved()),
               '(0, spot.acc_cond(6, "Inf(3) | Inf(2) | Inf(5)"), '
               'spot.acc_cond(6, "(Fin(4) & (Fin(0) | Inf(1))) '
               '| (Inf(1)&Inf(5))"))')


a = spot.acc_cond('Fin(0) & Inf(1) | Fin(2) & Inf(3)')
tc.assertEqual([(str(m), str(c)) for m, c in a.mafins_split()],
               [('{0}', '(4, Fin(0) & Inf(1))'),
                ('{2}', '(4, Fin(2) & Inf(3))')])

code = a.get_acceptance()
tc.assertEqual([(str(m), str(c)) for m, c in code.mafins_split()],
               [('{0}', 'Fin(0) & Inf(1)'), ('{2}', 'Fin(2) & Inf(3)')])


a = spot.acc_cond('Fin(0) & Inf(1) | Fin(2) & Inf(3)')
tc.assertEqual([str(c) for c in a.fins_split()],
               ['(4, Fin(0) & Inf(1))', '(4, Fin(2) & Inf(3))'])
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()],
               ['Fin(0) & Inf(1)', 'Fin(2) & Inf(3)'])

# Disjuncts that share a Fin(i) must end in the same group, and this
# must work transitively even though only the first disjunct where a
# given Fin(i) occurred is connected to later ones sharing it.
a = spot.acc_cond('(Inf(0)&Fin(1)) | (Fin(1)&Fin(2)) | '
                   '(Fin(3)&Inf(4)) | Inf(5)')
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()],
               ['(Fin(1) & Fin(2)) | (Inf(0) & Fin(1))',
                'Fin(3) & Inf(4)',
                'Inf(5)'])

# A single "lone Fin(M)" disjunct (the compact internal representation
# of Fin(i)|Fin(j)|Fin(k)) is split among the groups of the other
# disjuncts that share one of its Fin(i)'s, or turned into its own
# singleton group when no other disjunct shares any of its Fin(i)'s.
a = spot.acc_cond('(Fin(0)&Inf(1)) | Fin(2) | (Fin(2)&Inf(3)) | Fin(4)')
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()],
               ['Fin(0) & Inf(1)', 'Fin(2) | (Fin(2) & Inf(3))', 'Fin(4)'])

# When every disjunct is a lone Fin(M), the whole formula stays as
# one single group, using the compact internal representation.
a = spot.acc_cond('Fin(0)|Fin(1)|Fin(2)')
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()],
               ['Fin(0)|Fin(1)|Fin(2)'])

# t() and non-disjunction acceptance conditions are returned as-is.
a = spot.acc_cond('t')
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()], ['t'])

a = spot.acc_cond('Inf(0)')
tc.assertEqual([str(c) for c in a.get_acceptance().fins_split()], ['Inf(0)'])

# f() has no disjuncts, so fins_split() returns an empty list.
a = spot.acc_cond('f')
tc.assertEqual(list(a.get_acceptance().fins_split()), [])
tc.assertEqual(list(a.fins_split()), [])

# fins_split_improved() further annotates each group with its
# mafins(), merging all groups with an empty mafins() into a single
# last entry (since fins_split() already guarantees that the fins()
# -- and hence the mafins() -- of distinct groups are disjoint,
# non-empty mafins() can never clash between groups).
a = spot.acc_cond('Fin(0) & Inf(1) | Fin(2) & Inf(3)')
tc.assertEqual([(str(m), str(c)) for m, c in a.fins_split_improved()],
               [('{0}', '(4, Fin(0) & Inf(1))'),
                ('{2}', '(4, Fin(2) & Inf(3))')])
tc.assertEqual([(str(m), str(c))
                for m, c in a.get_acceptance().fins_split_improved()],
               [('{0}', 'Fin(0) & Inf(1)'), ('{2}', 'Fin(2) & Inf(3)')])

a = spot.acc_cond('(Inf(0)&Fin(1)) | (Fin(1)&Fin(2)) | '
                   '(Fin(3)&Inf(4)) | Inf(5)')
tc.assertEqual([(str(m), str(c))
                for m, c in a.get_acceptance().fins_split_improved()],
               [('{1}', '(Fin(1) & Fin(2)) | (Inf(0) & Fin(1))'),
                ('{3}', 'Fin(3) & Inf(4)'),
                ('{}', 'Inf(5)')])

# Groups with no mandatory fin (empty mafins()) are merged together
# into a single group, even when there is more than one of them.
a = spot.acc_cond('Inf(0) | Inf(1)')
tc.assertEqual([(str(m), str(c))
                for m, c in a.get_acceptance().fins_split_improved()],
               [('{}', 'Inf(1) | Inf(0)')])

# t() and f() behave as with fins_split().
a = spot.acc_cond('t')
tc.assertEqual([(str(m), str(c))
                for m, c in a.get_acceptance().fins_split_improved()],
               [('{}', 't')])

a = spot.acc_cond('f')
tc.assertEqual(list(a.get_acceptance().fins_split_improved()), [])
tc.assertEqual(list(a.fins_split_improved()), [])


def report_missing_exception():
    raise RuntimeError("missing exception")

a.set_acceptance("Inf(0)")
try:
    a.fin_one_split()
except RuntimeError as e:
    tc.assertIn('no Fin', str(e))
else:
    report_missing_exception()
