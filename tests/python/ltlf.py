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

lcc = spot.language_containment_checker()

formulas = ['GFa', 'FGa', '(GFa) U b',
            '(a U b) U c', 'a U (b U c)',
            '(a W b) W c', 'a W (b W c)',
            '(a R b) R c', 'a R (b R c)',
            '(a M b) M c', 'a M (b M c)',
            '(a R b) U c', 'a U (b R c)',
            '(a M b) W c', 'a W (b M c)',
            '(a U b) R c', 'a R (b U c)',
            '(a W b) M c', 'a M (b W c)',
            ]

# The rewriting assume the atomic proposition will not change
# once we reach the non-alive part.
cst = spot.formula('G(X!alive => ((a <=> Xa) && (b <=> Xb) && (c <=> Xc)))')

for f in formulas:
    f1 = spot.formula(f)
    f2 = f1.unabbreviate()
    f3 = spot.formula_And(spot.from_ltlf(f1), cst)
    f4 = spot.formula_And(spot.from_ltlf(f2), cst)
    # print(f"{f1}\t=>\t{f3}")
    # print(f"{f2}\t=>\t{f4}")
    tc.assertTrue(lcc.equal(f3, f4))
    print()


ls = spot.ltlf_simplifier()

for i, j in [('!X!X!a', 'X[!]X!a'),
             ('X!X!a', 'XX[!]a'),
             ('!(a U (b W (c R (d M e))))', '!a R (!b M (!c U (!d W !e)))'),
             ('!GFGa', 'FGF!a'),
             ('(Fa & Fb) | (Fa & Fc)', 'Fa & F(b | c)'),
             ('(Ga & Gb & Gd) | (Ga & Gc & Gd)', 'G(a & b & d) | G(a & c & d)'),
             ('(Xa & Fb & Gd) | (Xa & X[!]c & Gd) | Gd', 'Gd'),
             ('(Xa | Gb) & (Xa | Fc)', 'Xa | (Gb & Fc)'),
             ('(Xa | Fb | Gd ) & (Xa | Fc | Gd)', 'Xa | Gd | (Fb & Fc)'),
             ('(Xa | Fb | Gd) & (Xa | Fc | Gd) & Gd', 'Gd'),
             ('!Xa -> b', 'Xa | b'),
             ('Xa -> Gb', 'Xa -> Gb'),
             ('Xa -> !Gb', 'Xa -> F!b'),
             ('!Xa -> !Gb', 'Xa | F!b'),
             ('!(Xa -> Gb)', 'Xa & F!b'),
             ('!(!Xa -> Gb)', 'X[!]!a & F!b'),
             ('!(Xa -> !Gb)', 'Xa & Gb'),
             ('!(!Xa -> !Gb)', 'X[!]!a & Gb'),
             ('(Ga -> b) & (Gb -> c) & (Ga -> d) & Gf & Gg',
              '(F!a | (b & d)) & (c | F!b) & G(f & g)'),
             ('(a -> Gb) | (c -> Gd) | (Fe -> Gb) | Fg | Fh',
              '!a | !c | Gb | Gd | F(g | h) | G!e'),
             ('Xa <->Gb', 'Xa<->Gb'),
             ('!Xa xor Gb', 'Xa<->Gb'),
             ('!Xa <-> !Gb', 'Xa<->Gb'),
             ('!Xa xor Gb', 'Xa<->Gb'),
             ('Xa <-> !Gb', 'Xa xor Gb'),
             ('X(a) | X(!b) | Gc | Fd | Fe', 'X(a | !b) | Gc | F(d | e)'),
             ('X(a) & X(!b) & Gc & Gd & Fe & Ff',
              'X(a & !b) & G(c & d) & Fe & Ff'),
             ('X(a) & G(!b) & GFc & GFd & Fe & Ff',
              'X(a) & G(!b & F(c & d)) & Fe & Ff'),
             ]:
    f1 = spot.formula(i)
    f2 = spot.formula(j)
    f3 = ls.simplify(f1)
    # print(f1, "  =>  ", f3)
    tc.assertEqual(f2, f3)
    a = spot.ltlf_to_mtdfa(f1)
    b = spot.ltlf_to_mtdfa(f2)
    tc.assertTrue(spot.product_xor(a, b).is_empty())

# Test the new syntactic-obligation translation (algo=1) and semantic
# equivalence with the original De Giacomo & Vardi translation (algo=0).
lcc2 = spot.language_containment_checker()

formulas_o = [
    'G(a)', 'F(a)', 'a U b', 'a R b', 'a W b', 'a M b',
    'G(F(a))', 'F(G(a))',
    'G(a U b)', 'G(a R b)', 'G(a W b)', 'G(a M b)',
    'F(a U b)', 'F(a R b)', 'F(a W b)', 'F(a M b)',
    'F(a) U b', 'G(a) U b', 'F(a) R b', 'G(a) R b',
    'F(a) W b', 'G(a) W b', 'F(a) M b', 'G(a) M b',
    'a U F(b)', 'a U G(b)', 'a R F(b)', 'a R G(b)',
    'a W F(b)', 'a W G(b)', 'a M F(b)', 'a M G(b)',
    '(a U b) U c', '(a U b) R c', '(a U b) W c', '(a U b) M c',
    '(a R b) U c', '(a R b) R c', '(a R b) W c', '(a R b) M c',
    '(a W b) U c', '(a W b) R c', '(a W b) W c', '(a W b) M c',
    '(a M b) U c', '(a M b) R c', '(a M b) W c', '(a M b) M c',
    'a U (b U c)', 'a U (b R c)', 'a U (b W c)', 'a U (b M c)',
    'a R (b U c)', 'a R (b R c)', 'a R (b W c)', 'a R (b M c)',
    'a W (b U c)', 'a W (b R c)', 'a W (b W c)', 'a W (b M c)',
    'a M (b U c)', 'a M (b R c)', 'a M (b W c)', 'a M (b M c)',
    'G(F(G(a)))', 'F(G(F(a)))', 'G(F(G(F(a))))',
    'G(a U G(b))', 'F(a R F(b))', 'G(a W G(b))', 'F(a M F(b))',
    '(G(a) U b) W c', 'a M (G(b) R c)',
    'G(a) & F(b)', 'F(a) | G(b)',
    '(a U b) & G(c)', '(a R b) | F(c)',
    'G(a & F(b))', 'F(a | G(b))',
]

for s in formulas_o:
    f = spot.formula(s)
    old = spot.from_ltlf(f, 'alive', 0)   # De Giacomo & Vardi translation
    new = spot.from_ltlf(f, 'alive', 1)   # syntactic-obligation translation
    tc.assertTrue(lcc2.equal(old, new),
                  f"Semantic mismatch for {s!r}: old={old}, new={new}")
    tc.assertTrue(new.is_syntactic_obligation(),
                  f"Not syntactic obligation for {s!r}: {new}")

gen = spot.randltl(['a', 'b', 'c'], seed=42, tree_size=(15, 20))
for i, f in enumerate(gen):
    if i >= 100:
        break
    old = spot.from_ltlf(f, 'alive', 0)
    new = spot.from_ltlf(f, 'alive', 1)
    tc.assertTrue(lcc2.equal(old, new),
                  f"Semantic mismatch for {f!r}: old={old}, new={new}")
    tc.assertTrue(new.is_syntactic_obligation(),
                  f"Not syntactic obligation for {f!r}: {new}")

# ---------- Tests for t_B (xor/<-> handling in LTL_B contexts) ----------
#
# t_B (the Bottom class) handles xor and <-> homomorphically, while
# t_G and t_S must expand them into complex combinations involving
# both t_G and t_S calls (mutual recursion).  Dispatch to t_B occurs
# when a formula is both syntactic safety and syntactic guarantee
# (i.e., belongs to LTL_B).
#
# The formulas below place xor/<-> under temporal operators that enter
# t_G (F, right of U, left of M) or t_S (G, right of R, left of W).
# Without the t_B dispatch, each xor/<-> would be expanded into a
# combination of t_G/t_S calls; with t_B the translation stays compact.
lcc3 = spot.language_containment_checker()

# Wrapper components used by from_ltlf() to encode finite-trace semantics.
# algo=1: And(t_O(f), alive, F(!alive), W(alive, G(!alive)))
# algo=0: And(dv_aux(f), alive, U(alive, G(!alive)))
_alv = spot.formula('alive')
_nalv = spot.formula.Not(_alv)
_f_nalv = spot.formula.F(_nalv)
_w_alv_gnalv = spot.formula.W(_alv, spot.formula.G(_nalv))
_u_alv_gnalv = spot.formula.U(_alv, spot.formula.G(_nalv))
_new_wrapper = {_alv, _f_nalv, _w_alv_gnalv}
_old_wrapper = {_alv, _u_alv_gnalv}

def _strip_wrapper(res, wrapper_parts):
    """Strip the finite-trace wrapper from a from_ltlf() result."""
    if res.kind() == spot.op_And:
        children = [res[i] for i in range(res.size())]
        core = [c for c in children if c not in wrapper_parts]
        if len(core) == 1:
            return core[0]
        # Flattened And: combine remaining children back into one.
        return spot.formula.And(core)
    return res

tB_formulas = [
    # xor/<-> under unary temporal operators: enter t_G or t_S
    'F(a xor b)',                    # t_G dispatches to t_B
    'F(X(a xor b))',                 # t_G dispatches X(a xor b) to t_B
    'G(a <-> b)',                    # t_S dispatches to t_B
    'G(X[!](a <-> b))',              # t_S dispatches X[!](a <-> b) to t_B
    'F(a <-> b)',                    # t_G dispatches to t_B
    'G(a xor b)',                    # t_S dispatches to t_B
    # xor/<-> as arguments of binary temporal operators
    '(a xor b) U c',                 # t_G(left side) dispatches to t_B
    '(X(a xor b)) U c',              # t_G dispatches X(a xor b) to t_B
    '(a <-> b) R c',                 # t_S(left side) dispatches to t_B
    '(X[!](a <-> b)) R c',           # t_S dispatches X[!](a <-> b) to t_B
    '(a xor b) W c',                 # t_S(left side) dispatches to t_B
    '(X(a xor b)) W c',              # t_S dispatches X(a xor b) to t_B
    '(a <-> b) M c',                 # t_G(left side) dispatches to t_B
    'c U (a xor b)',                 # t_G(right side) dispatches to t_B
    'c R (a <-> b)',                 # t_S(right side) dispatches to t_B
    # Deeply nested xor: each level stays in LTL_B, so t_B avoids
    # exponential expansion in t_G/t_S.
    '(((a xor b) xor c) xor d) U e',
    'F((a xor b) xor c)',
    'G((a <-> b) <-> c)',
    'F(X(a xor b) xor X(c xor d))',  # nested X inside xor: t_G → t_B
    # xor/<-> under X: enters t_O directly (not t_G/t_S), but
    # subformulas may enter t_G/t_S.
    'X(G(a xor b))',                 # t_S dispatches to t_B
    'X(F(a <-> b))',                 # t_G dispatches to t_B
]

for s in tB_formulas:
    f = spot.formula(s)
    old = spot.from_ltlf(f, 'alive', 0)   # DG&V
    new = spot.from_ltlf(f, 'alive', 1)   # syntactic-obligation
    tc.assertTrue(lcc3.equal(old, new),
                  f"Semantic mismatch for {s!r}: old={old}, new={new}")
    tc.assertTrue(new.is_syntactic_obligation(),
                  f"Not syntactic obligation for {s!r}: {new}")
    # For LTL_B formulas, the core translations should be structurally
    # identical: only the finite-trace wrapper differs.
    old_core = _strip_wrapper(old, _old_wrapper)
    new_core = _strip_wrapper(new, _new_wrapper)
    tc.assertEqual(old_core, new_core,
                   f"Core mismatch for {s!r}: "
                   f"dv_aux={old_core}, t_O={new_core}")

# Demonstrate that t_B keeps the result compact for deeply nested xor.
# Without t_B dispatch, each xor in t_G or t_S would be expanded into a
# combination of t_G and t_S calls (doubling the formula at each level);
# with t_B dispatch the translation stays comparable to the DG&V baseline.
# A generous margin (2x + 20 chars) catches any exponential blow-up while
# tolerating structural differences between the two algorithms.
f = spot.formula('(((a xor b) xor c) xor d) U e')
old = spot.from_ltlf(f, 'alive', 0)
new = spot.from_ltlf(f, 'alive', 1)
tc.assertLessEqual(len(str(new)), len(str(old)) * 2 + 20,
                   f"t_B dispatch should prevent exponential blow-up: "
                   f"new has {len(str(new))} chars, old has {len(str(old))}")
tc.assertTrue(new.is_syntactic_obligation(),
              f"Not syntactic obligation: {new}")


# ---------- Tests for quantified formulas in from_ltlf() ----------
#
# from_ltlf() should preserve outermost quantifiers (forall/exists)
# wrapping them around the translated body.  The alive wrapper goes
# inside the quantifiers, i.e., from_ltlf(forall x, body) returns
# forall x, (alive & ... & t_O(body)).

quantified_cases = [
    '\\forall u: G(u -> X o)',                 # simple universal
    '\\forall u: \\forall v: G(u & v -> X o)',  # nested universal (flattened)
    '\\exists x: F(x)',                         # existential
]

for s in quantified_cases:
    qf = spot.formula(s)
    for algo in [0, 1]:
        result = spot.from_ltlf(qf, 'alive', algo)
        # Quantifier structure should be preserved at the top.
        tc.assertTrue(result.kind() == spot.op_forall or
                      result.kind() == spot.op_exists,
                      f"{s} algo={algo}: expected quantifier, got {result}")
        # The body (last child of the outermost quantifier) should
        # contain the alive wrapper (an And with alive, F(!alive), etc.).
        body_under_q = result[result.size() - 1]
        tc.assertTrue(body_under_q.kind() == spot.op_And,
                      f"{s} algo={algo}: body should be alive And, "
                      f"got {body_under_q}")
        # algo=0 and algo=1 should be semantically equivalent.
        if algo == 0:
            res0 = result
        else:
            tc.assertTrue(spot.are_equivalent(res0, result),
                          f"Semantic mismatch for {s}: "
                          f"algo=0={res0}, algo=1={result}")

# Nested quantifier structure.  formula::forall flattens nested quantifiers
# into a single forall with multiple variables, so after from_ltlf() we
# expect forall({u, v}, translated_body).  Variable order may differ from
# the parse order, so we check the set of APs rather than exact positions.
qf = spot.formula('\\forall u: \\forall v: G(u & v -> X o)')
result = spot.from_ltlf(qf, 'alive', 1)
tc.assertEqual(result.kind(), spot.op_forall)
tc.assertEqual(result.size(), 3)   # two variables + body
qvars = {str(result[0]), str(result[1])}
tc.assertEqual(qvars, {'u', 'v'})
# The body (last child) should be the alive wrapper.
inner_body = result[result.size() - 1]
tc.assertTrue(inner_body.kind() == spot.op_And)

# ----------------------------------------------------------------------------
# Error paths and unsupported operators in from_ltlf(),
# ltlf_one_step_sat_rewrite() and ltlf_one_step_unsat_rewrite(), and
# the quantified-formula case of ltlf_simplifier::simplify().
# ----------------------------------------------------------------------------

# from_ltlf() only supports LTL formulas; PSL formulas must be rejected.
tc.assertRaises(RuntimeError, spot.from_ltlf, spot.formula('{a;b}'))
tc.assertRaises(RuntimeError, spot.from_ltlf,
                spot.formula('{a[*]}'), 'alive', 0)
tc.assertRaises(RuntimeError, spot.from_ltlf,
                spot.formula('{a;b}'), 'alive', 1)

# ltlf_one_step_sat_rewrite() does not know the PSL operators.
for psl in ['{a;b}', '{a[*]}']:
    tc.assertRaises(RuntimeError, spot.ltlf_one_step_sat_rewrite,
                    spot.formula(psl))
# ... nor the quantifiers.
tc.assertRaises(RuntimeError, spot.ltlf_one_step_sat_rewrite,
                spot.formula('\\exists x: F(x)'))
tc.assertRaises(RuntimeError, spot.ltlf_one_step_sat_rewrite,
                spot.formula('\\forall x: G(x)'))

# Same for ltlf_one_step_unsat_rewrite(), including its two-argument
# (negated) overload.
for psl in ['{a;b}', '{a[*]}']:
    tc.assertRaises(RuntimeError, spot.ltlf_one_step_unsat_rewrite,
                    spot.formula(psl))
    tc.assertRaises(RuntimeError, spot.ltlf_one_step_unsat_rewrite,
                    spot.formula(psl), True)
tc.assertRaises(RuntimeError, spot.ltlf_one_step_unsat_rewrite,
                spot.formula('\\exists x: F(x)'))
tc.assertEqual(spot.ltlf_one_step_unsat_rewrite(spot.formula('!Xa'), True),
               spot.formula.tt())

# ltlf_simplifier::simplify() handles quantified formulas by keeping
# the quantifier and simplifying under it.
ls2 = spot.ltlf_simplifier()
tc.assertEqual(ls2.simplify(spot.formula('\\exists x: F(x)')),
               spot.formula('\\exists x: Fx'))
tc.assertEqual(ls2.simplify(spot.formula('\\forall x: G(x)')),
               spot.formula('\\forall x: Gx'))
tc.assertEqual(ls2.simplify(spot.formula('\\exists x: Fx')),
               spot.formula('\\exists x: Fx'))
