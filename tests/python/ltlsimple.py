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
import sys
from unittest import TestCase
tc = TestCase()

# CPython uses reference counting, so that automata are destructed
# when we expect them to be.   However other implementations like
# PyPy may call destructors later, causing different output.
from platform import python_implementation
if python_implementation() == 'CPython':
    def gcollect():
        pass
else:
    import gc
    def gcollect():
        # For some reason PyPy 7.3.20 (only version tested)
        # requires double collection() for this test to pass.
        # That's odd, because collect() is supposed to perform
        # a full collection pass according to the doc.
        gc.collect()
        gc.collect()

# Some of the tests here assume timely destructor calls, as they occur
# in the reference-counted CPython implementation.  Other
# implementation such as PyPy, should skip those tests.
from platform import python_implementation
is_cpython = python_implementation() == 'CPython'

# ----------------------------------------------------------------------
a = spot.formula.ap('a')
b = spot.formula.ap('b')
c = spot.formula.ap('c')
c2 = spot.formula.ap('c')

tc.assertEqual(c, c2)

op = spot.formula.And(a, b)
op2 = spot.formula.And(op, c)
op3 = spot.formula.And([a, c, b])

tc.assertEqual(op2, op3)

# The symbol for a subformula which hasn't been cloned is better
# suppressed, so we don't attempt to reuse it elsewhere.
del op, c

sys.stdout.write('op2 = %s\n' % str(op2))

del a, b, c2

sys.stdout.write('op3 = %s\n' % str(op3))
tc.assertEqual(op2, op3)

op4 = spot.formula.Or(op2, op3)

sys.stdout.write('op4 = %s\n' % str(op4))
tc.assertEqual(op4, op2)

op5 = spot.formula.Or([op2, op3, op3])

sys.stdout.write('op5 = %s\n' % str(op5))
tc.assertEqual(op5, op2)

tc.assertEqual(spot.formula.apid_count(), 3)
tc.assertEqual(str(spot.formula.apid_map()), '["a", "b", "c"]')

del op2, op3, op4, op5

gcollect()

tc.assertEqual(spot.formula.apid_count(), 0)
tc.assertEqual(str(spot.formula.apid_map()), '[]')

# ----------------------------------------------------------------------
a = spot.formula.ap('a')
b = spot.formula.ap('b')
c = spot.formula.ap('c')
T = spot.formula.tt()
F = spot.formula.ff()

f1 = spot.formula.Equiv(c, a)
f2 = spot.formula.Implies(a, b)
f3 = spot.formula.Xor(b, c)
f4 = spot.formula.Not(f3)
del f3
f5 = spot.formula.Xor(F, c)

del a, b, c, T, F, f1, f2, f4, f5

gcollect()
tc.assertTrue(spot.fnode_instances_check())

# ----------------------------------------------------------------------
tc.assertEqual(str([str(x) for x in spot.formula('a &b & c')]),
               "['a', 'b', 'c']")


def switch_g_f(x):
    if x._is(spot.op_G):
        return spot.formula.F(switch_g_f(x[0]))
    if x._is(spot.op_F):
        return spot.formula.G(switch_g_f(x[0]))
    return x.map(switch_g_f)


f = spot.formula('GFa & XFGb & Fc & G(a | b | Fd)')
tc.assertEqual(str(switch_g_f(f)), 'FGa & XGFb & Gc & F(a | b | Gd)')

x = 0


def count_g(f):
    global x
    if f._is(spot.op_G):
        x += 1


f.traverse(count_g)
tc.assertEqual(x, 3)

# ----------------------------------------------------------------------

# The example from tut01.org

formula = spot.formula('a U b U "$strange[0]=name"')
res = """\
Default output:    {f}
Spin syntax:       {f:s}
(Spin syntax):     {f:sp}
Default for shell: echo {f:q} | ...
LBT for shell:     echo {f:lq} | ...
Default for CSV:   ...,{f:c},...
Wring, centered:   {f:w:~^50}""".format(f=formula)

tc.assertEqual(res, """\
Default output:    a U (b U "$strange[0]=name")
Spin syntax:       a U (b U ($strange[0]=name))
(Spin syntax):     (a) U ((b) U ($strange[0]=name))
Default for shell: echo 'a U (b U "$strange[0]=name")' | ...
LBT for shell:     echo 'U "a" U "b" "$strange[0]=name"' | ...
Default for CSV:   ...,"a U (b U ""$strange[0]=name"")",...
Wring, centered:   ~~~~~(a=1) U ((b=1) U ("$strange[0]=name"=1))~~~~~""")


opt = spot.tl_simplifier_options(False, True, True,
                                 True, True, True,
                                 False, False, False)

for (input, output) in [('(a&b)<->b', 'b->(a&b)'),
                        ('b<->(a&b)', 'b->(a&b)'),
                        ('(a&b)->b', '1'),
                        ('b->(a&b)', 'b->(a&b)'),
                        ('(!(a&b)) xor b', 'b->(a&b)'),
                        ('(a&b) xor !b', 'b->(a&b)'),
                        ('b xor (!(a&b))', 'b->(a&b)'),
                        ('!b xor (a&b)', 'b->(a&b)')]:
    f = spot.tl_simplifier(opt).simplify(input)
    tc.assertEqual(f, output)
    tc.assertTrue(spot.are_equivalent(input, output))


def myparse(input):
    env = spot.default_environment.instance()
    pf = spot.parse_infix_psl(input, env)
    return pf.f


# This used to fail, because myparse would return a pointer
# to pf.f inside the destroyed pf.
tc.assertEqual(myparse('a U b'), spot.formula('a U b'))


tc.assertTrue(spot.is_liveness('a <-> GFb'))
tc.assertFalse(spot.is_liveness('a & GFb'))

gcollect()

tc.assertEqual(spot.formula('a').apid(), 0)
tc.assertEqual(spot.formula('b').apid(), 1)
tc.assertEqual(spot.formula.apid_count(), 5)
tc.assertEqual(str(spot.formula.apid_map()),
               '["a", "b", None, None, "\\"$strange[0]=name\\""]')

del formula
gcollect()

tc.assertEqual(str(spot.formula.apid_map()), '["a", "b", None, None]')
tc.assertEqual(repr(spot.formula.apid_map()),
               '[spot.formula("a"), spot.formula("b"), None, None]')

tc.assertEqual(str(spot.formula.ap_from_apid(0)), 'a')

# ----------------------------------------------------------------------
# Satisfiability tests
# ----------------------------------------------------------------------

satisfiability_tests = [
    ('a', True),
    ('Xa', True),
    ('Fa', True),
    ('Ga', True),
    ('a U b', True),
    ('a R b', True),
    ('a W b', True),
    ('a M b', True),
    ('FGa', True),
    ('GFa', True),
    ('G(a U b)', True),
    ('F(a R b)', True),
    ('a | b', True),
    ('Fa | Gb', True),
    ('(a U b) | (c R d)', True),
    ('Ga | F!a', True),
    ('FGa | GFb', True),
    ('GFa & GFb', True),
    ('GFa & GFb & GFc', True),
    ('G(a -> Fb)', True),
    ('GFa & (b U c)', True),
    ('Ga & GFb', True),
    ('FGb & GFb', True),
    ('(!a U a) & FGa', True),
    ('(!a U Ga) & GF!a', False),
    ('FGa | GFb', True),
    ('FG(a | b)', True),
    ('G(a | Fb)', True),
    ('(a U !a) & (!a U a)', True),  # witness: [!a, a]
    ('(a & X!a) | (!a & Xa)', True),
    ('(a -> Xb) & (b -> Xa) & Fa', True),
    ('a U (b R c)', True),
    ('G(a | b) & F!a', True),
    ('F(a & X!a)', True),
    ('0', False),
    ('a & !a', False),
    ('G a & F !a', False),
    ('F a & G !a', False),
    ('a U b & a U !b & G!a', False),
    ('G(!a & !b) & a U b', False),
    ('(G a & F !a) | (G b & F !b)', False),
    ('GFa & FG!a', False),
    ('(!a U Ga) & GF!a', False),
    ('GFa & GF!a & G(a -> b) & FG!b', False),
    ('GFa & GFb & FG!a', False),
    ('G(a | b) & FG!a & FG!b', False),
    ('GFa & G(a <-> b) & FG!b', False),
    ('G!a & Fa', False),
    ('G!c & a U (b R c)', False),
    ('G(a <-> X!a) & FGa', False),
]

for fstr, expected in satisfiability_tests:
    tc.assertEqual(spot.ltl_satisfiable(fstr), expected,
                   f"ltl_satisfiable('{fstr}') should be {expected}")
    tc.assertEqual(spot.translate(fstr).is_empty(), not expected,
                   f"translate('{fstr}').is_empty() should be {not expected}")

# ----------------------------------------------------------------------
# QLTL satisfiability tests
# ----------------------------------------------------------------------

# Quantifiers are always at the top level, and consecutive identical
# quantifiers are automatically merged (e.g., "\exists a: \exists b: \u03c6"
# becomes "\exists a, b: \u03c6").
#
# The on-the-fly (OTF) satisfiability check handles formulas that are
# unquantified, or have only existential quantifiers at the top with an
# unquantified body.  Formulas with universal quantifiers or quantifier
# alternations are delegated to the translator.

qtl_sat_tests = [
    # ---- Purely existential (OTF path) ----
    #
    # Formulas where the existentially quantified APs appear with
    # constant polarity may be simplified by the realizability
    # simplifier (e.g., "\exists a: a" reduces to "1"), which is
    # correct for satisfiability and still produces the right answer.
    # To exercise the OTF path through a quantifier, the quantified AP
    # must have mixed polarity so it survives simplification.

    # Constant-polarity APs (simplified before OTF):
    ('\\exists a: a', True),
    ('\\exists a: a & !a', False),
    ('\\exists a: F a', True),
    ('\\exists a: G a', True),
    # Mixed-polarity APs (survive through to OTF):
    ('\\exists a: Xa & !a', True),
    ('\\exists a: G a & F !a', False),
    ('\\exists a, b: a U b', True),
    ('\\exists a, b: G a & G !b', True),
    ('\\exists a: G a & G !a', False),

    # \\exists over a disjunction: each disjunct re-wrapped with the
    # quantifier and checked independently.
    ('\\exists a: (Xa & !a) | G a', True),
    ('\\exists a: (G a & F !a) | (G a & G !a)', False),
    ('\\exists a: F a | (X!a & a)', True),

    # ---- Single universal (translator path) ----
    #
    # Formulas where the ∀-quantified AP has constant polarity
    # are NO LONGER simplified away by the realizability simplifier;
    # they reach the translator which handles them correctly.

    # Constant positive polarity.
    ('\\forall a: a', False),
    ('\\forall a: G a', False),
    ('\\forall a: Xa', False),
    # Constant negative polarity.
    ('\\forall a: !a', False),
    ('\\forall a: G !a', False),
    # Mixed polarity for comparison (should still work).
    ('\\forall a: a | !a', True),
    ('\\forall a: Xa | X!a', True),
    ('\\forall a: G (a | !a)', True),
    ('\\forall a: F a | F !a', True),
    ('\\forall a: a & !a', False),
    ('\\forall a: a U !a', False),
    ('\\forall a: (a & X!a) | (!a & Xa)', False),
    # \forall with body independent of the quantified AP (vacuous).
    ('\\forall a: b | !b', True),
    ('\\forall a: G b | F !b', True),

    # ---- Quantifier alternations (translator path) ----
    # \exists a: \forall b: \u03c6
    ('\\exists a: \\forall b: b -> a', True),
    ('\\exists a: \\forall b: a <-> b', False),
    # \forall a: \\exists b: \u03c6
    ('\\forall a: \\exists b: a -> b', True),
    ('\\forall a: \\exists b: (a & b) | (!a & !b)', True),
    ('\\forall a: \\exists b: a U !a', False),
    # Vacuous inner quantifier.
    ('\\exists a: \\forall b: a', True),

    # ---- Equivalence simplification with quantified APs ----
    #
    # {a,b,c} are equivalent; a is quantified, so excluded from
    # representative selection. {b,c} are free and simplified
    # among themselves by the equivalence simplifier.
    ('\\exists a: G(a -> b) & G(b -> c) & G(c -> a)', True),
]

for fstr, expected in qtl_sat_tests:
    tc.assertEqual(spot.ltl_satisfiable(fstr), expected,
                   f"ltl_satisfiable('{fstr}') should be {expected}")
    # Cross-check with translate().  For \forall, translation may involve
    # complementation which can fail on very complex automata; the simple
    # formulas here should all succeed.
    try:
        tc.assertEqual(spot.translate(fstr).is_empty(), not expected,
                       f"translate({fstr}) should be {not expected}")
    except RuntimeError as e:
        if 'run_q' in str(e) or 'complementation' in str(e):
            sys.stderr.write(f"warning: translate('{fstr}') failed: {e}\n")
        else:
            raise

# ----------------------------------------------------------------------
# relabel_apply with quantifiers
# ----------------------------------------------------------------------

# When relabel_apply replaces a quantifier-bound variable with a non-AP
# formula (like ff() or tt()), the variable should be dropped from the
# quantifier list rather than kept unchanged.  If all bound variables
# are dropped, the quantifier is removed entirely.

a = spot.formula.ap('a')
b = spot.formula.ap('b')

# AP-to-AP renaming: \\exists a: a with a -> b becomes \\exists b: b.
rm = spot.relabeling_map()
rm[a] = b
tc.assertEqual(str(spot.relabel_apply(spot.formula('\\exists a: a'),
                                     rm)),
               '\\exists b: b')

# Replacement with ff(): \\exists a: a with a -> ff() becomes ff().
rm2 = spot.relabeling_map()
rm2[a] = spot.formula.ff()
tc.assertEqual(str(spot.relabel_apply(spot.formula('\\exists a: a'),
                                     rm2)),
               '0')

# Replacement with tt(): \\exists a: !a with a -> tt() becomes ff().
# (!tt() = ff())
rm3 = spot.relabeling_map()
rm3[a] = spot.formula.tt()
tc.assertEqual(str(spot.relabel_apply(spot.formula('\\exists a: !a'),
                                     rm3)),
               '0')    # Mixed: \\exists a, b: (a & !b) with a -> b, b -> tt().
    # Body: a & !b -> b & !tt() = ff().  Qvars: a renamed to b (AP),
    # b dropped (tt() is non-AP).  Result: \\exists b: ff() = ff().
rm4 = spot.relabeling_map()
rm4[a] = b
rm4[b] = spot.formula.tt()
tc.assertEqual(str(spot.relabel_apply(
    spot.formula('\\exists a, b: a & !b'), rm4)),
               '0')

# No replacement for quantified variable: \\exists a: b with b -> tt().
# Only b in the body is replaced; a stays in the quantifier list.
# \\exists a: 1 simplifies to 1.
rm5 = spot.relabeling_map()
rm5[b] = spot.formula.tt()
tc.assertEqual(str(spot.relabel_apply(spot.formula('\\exists a: b'),
                                     rm5)),
               '1')

del a, b, rm, rm2, rm3, rm4, rm5
