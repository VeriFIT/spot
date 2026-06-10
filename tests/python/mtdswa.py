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
import buddy
from unittest import TestCase
tc = TestCase()

formulas = [
    "true",
    "false",
    "p2 -> p0",
    "p0 | Xp1",
    "Go",
    "G(!p0 U (p0 & X!p0))",
    "\\forall p0: Gp1 <-> p2Up0",
    "GFp0 <-> p2",
    "G(G!p2 R !p2) U G(F(p0 | p1) U p2)",
    "X(0) | X(Gp2 xor !GFp0)",
    "(p0 U p1) & GFp0 & GFp1 & FGp2"
]
twas = [spot.translate(f, "generic", "deterministic", "complete", "SBAcc")
        for f in formulas]
mtdswas = [spot.dtwa_to_mtdswa(twa) for twa in twas]

# Helper: build a Büchi automaton (GFa) and degenerate t/f TWAs + MTDSwAs
# sharing the same dictionary.  Returns (twa_buchi, twa_t, twa_f,
# m_buchi, m_t, m_f).
def _setup_degenerate_aut():
    twa_buchi = spot.translate('GFa', 'generic', 'deterministic',
                               'complete', 'SBAcc')
    d = twa_buchi.get_dict()

    twa_t = spot.make_twa_graph(d)
    twa_t.set_acceptance(0, "t")
    twa_t.new_states(1)
    twa_t.set_init_state(0)
    twa_t.new_edge(0, 0, buddy.bddtrue)

    twa_f = spot.make_twa_graph(d)
    twa_f.set_acceptance(0, "f")
    twa_f.new_states(1)
    twa_f.set_init_state(0)
    twa_f.new_edge(0, 0, buddy.bddtrue)

    m_buchi = spot.dtwa_to_mtdswa(twa_buchi)
    m_t = spot.dtwa_to_mtdswa(twa_t)
    m_f = spot.dtwa_to_mtdswa(twa_f)
    return twa_buchi, twa_t, twa_f, m_buchi, m_t, m_f

# Tests products functions for MTDSwAs
def test_mtdswa_products():
    for i in range(len(formulas)):
        for j in range(i, len(formulas)):
            # test all products that exist for both twas and mtdswas
            for prod in [spot.product, spot.product_or, spot.product_xor,
                         spot.product_xnor]:
                m12 = prod(mtdswas[i], mtdswas[j])
                a12 = prod(twas[i], twas[j])
                # Check that the two products are equivalent
                pxor = spot.product_xor(m12.as_twa(True, True, True), a12)
                tc.assertTrue(pxor.is_empty(), "Product of MTDSwAs "
                              + "is not equivalent to product of DTWAs: "
                              + f"{formulas[i]} {prod.__name__} {formulas[j]}")

# Tests degenerate product code paths with hand-built t/f acceptance MTDSwA.
# translate('true') and translate('false') give Büchi Inf(0) but with
# both accepting and rejecting states - these don't trigger the degenerate
# code paths.  Here we build automata with actual t/f acceptance.
def test_degenerate_products():
    twa_buchi, twa_t, twa_f, m_buchi, m_t, m_f = _setup_degenerate_aut()
    twa_dual = spot.dualize(twa_buchi)

    # AND/OR/XOR/XNOR: validate against TWA product.
    for name, prod in [('and', spot.product),
                       ('or', spot.product_or),
                       ('xor', spot.product_xor),
                       ('xnor', spot.product_xnor)]:
        m_prod = prod(m_buchi, m_t)
        m_twa = m_prod.as_twa(True, True, True)
        twa_prod = prod(twa_buchi, twa_t)
        pxor = spot.product_xor(m_twa, twa_prod)
        tc.assertTrue(pxor.is_empty(),
                      f'{name}(Buchi, t): MTDSwA != TWA')

    # IMPLIES: product_implies(A, B) = product_or(dualize(A), B).
    for label, m_deg, twa_deg in [('t', m_t, twa_t), ('f', m_f, twa_f)]:
        m_imp = spot.product_implies(m_buchi, m_deg)
        m_twa = m_imp.as_twa(True, True, True)
        twa_imp = spot.product_or(twa_dual, twa_deg)
        pxor = spot.product_xor(m_twa, twa_imp)
        tc.assertTrue(pxor.is_empty(),
                      f'implies(Buchi, {label}): MTDSwA != TWA')

    # Test with f (unsatisfiable) acceptance for AND/OR/XOR/XNOR.
    for name, prod in [('and', spot.product),
                       ('or', spot.product_or),
                       ('xor', spot.product_xor),
                       ('xnor', spot.product_xnor)]:
        m_prod = prod(m_buchi, m_f)
        m_twa = m_prod.as_twa(True, True, True)
        twa_prod = prod(twa_buchi, twa_f)
        pxor = spot.product_xor(m_twa, twa_prod)
        tc.assertTrue(pxor.is_empty(),
                      f'{name}(Buchi, f): MTDSwA != TWA')

    # Verify acceptance formulas for degenerate cases.
    # With t (tautology): AND/OR keep A.acc; IMPLIES: Inf(1)|!A.acc;
    # EQUIV: (Inf(1)&A.acc)|(Fin(1)&!A.acc); XOR: (Inf(1)&!A.acc)|(Fin(1)&A.acc)
    pand = spot.product(m_buchi, m_t)
    tc.assertEqual(str(pand.acc.get_acceptance()), 'Inf(0)',
                   'AND(Buchi, t) should keep A.acc')
    por = spot.product_or(m_buchi, m_t)
    tc.assertEqual(str(por.acc.get_acceptance()), 'Inf(0)',
                   'OR(Buchi, t) should keep A.acc')
    pim = spot.product_implies(m_buchi, m_t)
    tc.assertEqual(str(pim.acc.get_acceptance()),
                   'Fin(0) | Inf(1)',
                   'IMPLIES(Buchi, t) acc formula')
    pxn = spot.product_xnor(m_buchi, m_t)
    tc.assertEqual(str(pxn.acc.get_acceptance()),
                   '(Fin(0) & Fin(1)) | (Inf(0)&Inf(1))',
                   'XNOR(Buchi, t) acc formula')
    px = spot.product_xor(m_buchi, m_t)
    tc.assertEqual(str(px.acc.get_acceptance()),
                   '(Inf(0) & Fin(1)) | (Fin(0) & Inf(1))',
                   'XOR(Buchi, t) acc formula')

    # With f (unsatisfiable): AND->f; OR/A.acc; IMPLIES->!A.acc;
    # EQUIV->Fin(1)|!A.acc; XOR->A.acc
    pand_f = spot.product(m_buchi, m_f)
    tc.assertEqual(str(pand_f.acc.get_acceptance()), 'f',
                   'AND(Buchi, f) should be f')
    por_f = spot.product_or(m_buchi, m_f)
    tc.assertEqual(str(por_f.acc.get_acceptance()), 'Inf(0)',
                   'OR(Buchi, f) should keep A.acc')
    pim_f = spot.product_implies(m_buchi, m_f)
    tc.assertEqual(str(pim_f.acc.get_acceptance()), 'Fin(0)',
                   'IMPLIES(Buchi, f) should be !A.acc')
    pxn_f = spot.product_xnor(m_buchi, m_f)
    tc.assertEqual(str(pxn_f.acc.get_acceptance()),
                   'Fin(0)|Fin(1)',
                   'XNOR(Buchi, f) acc formula')
    px_f = spot.product_xor(m_buchi, m_f)
    tc.assertEqual(str(px_f.acc.get_acceptance()), 'Inf(0)',
                   'XOR(Buchi, f) should keep A.acc')

# Symmetric test: degenerate automaton on the left side (swa1) to exercise
# the swa1_taut_ and swa1_unsatis_ code paths in colors_of_product_state.
def test_degenerate_products_swa1():
    twa_buchi, twa_t, twa_f, m_buchi, m_t, m_f = _setup_degenerate_aut()
    # Duals of degenerate TWAs for IMPLIES validation:
    #   product_implies(deg, A) = product_or(dualize(deg), A)
    twa_t_dual = spot.dualize(twa_t)   # t → f
    twa_f_dual = spot.dualize(twa_f)   # f → t

    # Commutative operators: validate against TWA product (order swapped).
    for name, prod in [('and', spot.product),
                       ('or', spot.product_or),
                       ('xor', spot.product_xor),
                       ('xnor', spot.product_xnor)]:
        for label, m_deg, twa_deg in [('t', m_t, twa_t), ('f', m_f, twa_f)]:
            m_prod = prod(m_deg, m_buchi)
            m_twa = m_prod.as_twa(True, True, True)
            twa_prod = prod(twa_deg, twa_buchi)
            pxor = spot.product_xor(m_twa, twa_prod)
            tc.assertTrue(pxor.is_empty(),
                          f'{name}({label}, Buchi): MTDSwA != TWA')

    # IMPLIES: product_implies(deg, A) = product_or(dualize(deg), A).
    # IMPLIES(t, A) = product_or(f, A) = A (Buchi).
    m_imp_t = spot.product_implies(m_t, m_buchi)
    m_twa = m_imp_t.as_twa(True, True, True)
    twa_imp_t = spot.product_or(twa_t_dual, twa_buchi)
    pxor = spot.product_xor(m_twa, twa_imp_t)
    tc.assertTrue(pxor.is_empty(), 'implies(t, Buchi): MTDSwA != TWA')

    # IMPLIES(f, A) = product_or(t, A) = always accepting.
    m_imp_f = spot.product_implies(m_f, m_buchi)
    m_twa = m_imp_f.as_twa(True, True, True)
    twa_imp_f = spot.product_or(twa_f_dual, twa_buchi)
    pxor = spot.product_xor(m_twa, twa_imp_f)
    tc.assertTrue(pxor.is_empty(), 'implies(f, Buchi): MTDSwA != TWA')

    # Verify acceptance formulas (swa1 degenerate).
    # IMPLIES: differs from swa2 because it's not commutative.
    pand = spot.product(m_t, m_buchi)
    tc.assertEqual(str(pand.acc.get_acceptance()), 'Inf(0)',
                   'AND(t, Buchi) should keep A.acc')
    por = spot.product_or(m_t, m_buchi)
    tc.assertEqual(str(por.acc.get_acceptance()), 'Inf(0)',
                   'OR(t, Buchi) should keep A.acc')
    pim = spot.product_implies(m_t, m_buchi)
    tc.assertEqual(str(pim.acc.get_acceptance()),
                   'Inf(0) | Fin(1)',
                   'IMPLIES(t, Buchi): B.acc | Fin(status)')
    pxn = spot.product_xnor(m_t, m_buchi)
    tc.assertEqual(str(pxn.acc.get_acceptance()),
                   '(Fin(0) & Fin(1)) | (Inf(0)&Inf(1))',
                   'XNOR(t, Buchi) acc formula')
    px = spot.product_xor(m_t, m_buchi)
    tc.assertEqual(str(px.acc.get_acceptance()),
                   '(Inf(0) & Fin(1)) | (Fin(0) & Inf(1))',
                   'XOR(t, Buchi) acc formula')

    pand_f = spot.product(m_f, m_buchi)
    tc.assertEqual(str(pand_f.acc.get_acceptance()), 'f',
                   'AND(f, Buchi) should be f')
    por_f = spot.product_or(m_f, m_buchi)
    tc.assertEqual(str(por_f.acc.get_acceptance()), 'Inf(0)',
                   'OR(f, Buchi) should keep A.acc')
    pim_f = spot.product_implies(m_f, m_buchi)
    tc.assertEqual(str(pim_f.acc.get_acceptance()), 't',
                   'IMPLIES(f, Buchi) should be t')
    pxn_f = spot.product_xnor(m_f, m_buchi)
    tc.assertEqual(str(pxn_f.acc.get_acceptance()),
                   'Fin(0)|Fin(1)',
                   'XNOR(f, Buchi) acc formula')
    px_f = spot.product_xor(m_f, m_buchi)
    tc.assertEqual(str(px_f.acc.get_acceptance()), 'Inf(0)',
                   'XOR(f, Buchi) should keep A.acc')

# Test that degenerate acceptances with unused color sets
# (e.g. Inf(0)|Fin(0) for tautology, Inf(0)&Fin(0) for unsatisfiable)
# are treated as if they had pure t/f acceptance with 0 sets.
def test_degenerate_with_colors():
    twa_buchi, _, _, m_buchi, m_t, m_f = _setup_degenerate_aut()
    d = twa_buchi.get_dict()

    # TWA with Inf(0)|Fin(0) acceptance (tautology using 1 color set).
    twa_tau = spot.make_twa_graph(d)
    twa_tau.set_acceptance(1, "Inf(0)|Fin(0)")
    twa_tau.prop_state_acc(True)
    twa_tau.new_states(1)
    twa_tau.set_init_state(0)
    twa_tau.new_edge(0, 0, buddy.bddtrue)

    # TWA with Inf(0)&Fin(0) acceptance (unsatisfiable using 1 color set).
    twa_unsat = spot.make_twa_graph(d)
    twa_unsat.set_acceptance(1, "Inf(0)&Fin(0)")
    twa_unsat.prop_state_acc(True)
    twa_unsat.new_states(1)
    twa_unsat.set_init_state(0)
    twa_unsat.new_edge(0, 0, buddy.bddtrue)

    m_tau = spot.dtwa_to_mtdswa(twa_tau)
    m_unsat = spot.dtwa_to_mtdswa(twa_unsat)

    # --- Tautology (Inf(0)|Fin(0)) ---

    # Verify Inf(0)|Fin(0) produces identical formulas to pure t
    # on both sides, confirming the degenerate max_color is zeroed.
    for pos, (l, r) in [('right', (m_buchi, m_tau)),
                        ('left', (m_tau, m_buchi))]:
        pand = spot.product(l, r)
        tc.assertEqual(str(pand.acc.get_acceptance()), 'Inf(0)',
                       f'AND({pos} tau) should be Inf(0)')
        por = spot.product_or(l, r)
        tc.assertEqual(str(por.acc.get_acceptance()), 'Inf(0)',
                       f'OR({pos} tau) should be Inf(0)')
        pim = spot.product_implies(l, r)
        if pos == 'right':
            tc.assertEqual(str(pim.acc.get_acceptance()),
                           'Fin(0) | Inf(1)',
                           f'IMPLIES({pos} tau) acc formula')
        else:
            tc.assertEqual(str(pim.acc.get_acceptance()),
                           'Inf(0) | Fin(1)',
                           f'IMPLIES({pos} tau) acc formula')
        pxn = spot.product_xnor(l, r)
        tc.assertEqual(str(pxn.acc.get_acceptance()),
                       '(Fin(0) & Fin(1)) | (Inf(0)&Inf(1))',
                       f'XNOR({pos} tau) acc formula')
        px = spot.product_xor(l, r)
        tc.assertEqual(str(px.acc.get_acceptance()),
                       '(Inf(0) & Fin(1)) | (Fin(0) & Inf(1))',
                       f'XOR({pos} tau) acc formula')

    # MTDSwA products: Inf(0)|Fin(0) vs t should be equivalent.
    for name, prod in [('and', spot.product),
                       ('or', spot.product_or),
                       ('xor', spot.product_xor),
                       ('xnor', spot.product_xnor)]:
        for pos, (l_d, r_b, l_p, r_p) in [
                ('right', (m_buchi, m_tau, m_buchi, m_t)),
                ('left', (m_tau, m_buchi, m_t, m_buchi))]:
            m_d = prod(l_d, r_b)
            m_p = prod(l_p, r_p)
            pxor = spot.product_xor(m_d.as_twa(True, True, True),
                                    m_p.as_twa(True, True, True))
            tc.assertTrue(pxor.is_empty(),
                          f'{name}({pos} tau) != {name}({pos} t)')

    for pos, (l_d, r_b, l_p, r_p) in [
            ('right', (m_buchi, m_tau, m_buchi, m_t)),
            ('left', (m_tau, m_buchi, m_t, m_buchi))]:
        m_d = spot.product_implies(l_d, r_b)
        m_p = spot.product_implies(l_p, r_p)
        pxor = spot.product_xor(m_d.as_twa(True, True, True),
                                m_p.as_twa(True, True, True))
        tc.assertTrue(pxor.is_empty(),
                      f'implies({pos} tau) != implies({pos} t)')

    # --- Unsatisfiable (Inf(0)&Fin(0)) ---

    # Verify Inf(0)&Fin(0) produces identical formulas to pure f.
    for pos, (l, r) in [('right', (m_buchi, m_unsat)),
                         ('left', (m_unsat, m_buchi))]:
        pand = spot.product(l, r)
        tc.assertEqual(str(pand.acc.get_acceptance()), 'f',
                       f'AND({pos} unsat) should be f')
        por = spot.product_or(l, r)
        tc.assertEqual(str(por.acc.get_acceptance()), 'Inf(0)',
                       f'OR({pos} unsat) should be Inf(0)')
        pim = spot.product_implies(l, r)
        if pos == 'right':
            tc.assertEqual(str(pim.acc.get_acceptance()), 'Fin(0)',
                           f'IMPLIES({pos} unsat) should be Fin(0)')
        else:
            tc.assertEqual(str(pim.acc.get_acceptance()), 't',
                           f'IMPLIES({pos} unsat) should be t')
        pxn = spot.product_xnor(l, r)
        tc.assertEqual(str(pxn.acc.get_acceptance()), 'Fin(0)|Fin(1)',
                       f'XNOR({pos} unsat) acc formula')
        px = spot.product_xor(l, r)
        tc.assertEqual(str(px.acc.get_acceptance()), 'Inf(0)',
                       f'XOR({pos} unsat) should be Inf(0)')

    # MTDSwA products: Inf(0)&Fin(0) vs f should be equivalent.
    for name, prod in [('and', spot.product),
                       ('or', spot.product_or),
                       ('xor', spot.product_xor),
                       ('xnor', spot.product_xnor)]:
        for pos, (l_d, r_b, l_p, r_p) in [
                ('right', (m_buchi, m_unsat, m_buchi, m_f)),
                ('left', (m_unsat, m_buchi, m_f, m_buchi))]:
            m_d = prod(l_d, r_b)
            m_p = prod(l_p, r_p)
            pxor = spot.product_xor(m_d.as_twa(True, True, True),
                                    m_p.as_twa(True, True, True))
            tc.assertTrue(pxor.is_empty(),
                          f'{name}({pos} unsat) != {name}({pos} f)')

    for pos, (l_d, r_b, l_p, r_p) in [
            ('right', (m_buchi, m_unsat, m_buchi, m_f)),
            ('left', (m_unsat, m_buchi, m_f, m_buchi))]:
        m_d = spot.product_implies(l_d, r_b)
        m_p = spot.product_implies(l_p, r_p)
        pxor = spot.product_xor(m_d.as_twa(True, True, True),
                                m_p.as_twa(True, True, True))
        tc.assertTrue(pxor.is_empty(),
                      f'implies({pos} unsat) != implies({pos} f)')

test_mtdswa_products()
test_degenerate_products()
test_degenerate_products_swa1()
test_degenerate_with_colors()

# Tests products functions and complement for MTDSwAs.
for i in range(len(formulas)):
    mcomp = spot.complement(mtdswas[i])
    acomp = spot.complement(twas[i])
    # Check that the two complements are equivalent.
    pxor = spot.product_xor(mcomp.as_twa(True, True, True), acomp)
    tc.assertTrue(pxor.is_empty(), "Complement of MTDSwA "
                  + "is not equivalent to complement of DTWA: "
                  + f"{formulas[i]}")

    for j in range(i, len(formulas)):
        # Test all products that exist for both twas and mtdswas.
        for prod in [spot.product, spot.product_or, spot.product_xor,
                        spot.product_xnor]:
            m12 = prod(mtdswas[i], mtdswas[j])
            a12 = prod(twas[i], twas[j])
            # Check that the two products are equivalent.
            pxor = spot.product_xor(m12.as_twa(True, True, True), a12)
            tc.assertTrue(pxor.is_empty(), "Product of MTDSwAs "
                            + "is not equivalent to product of DTWAs: "
                            + f"{formulas[i]} {prod.__name__} {formulas[j]}")

# ==============================================================================
# Test quantification functions for MTDSwAs.
# ==============================================================================

obligations = [
    "true",
    "p2",
    "p2 -> p0",
    "p0 | Xp1",
    "Gp0",
    "Xp0 xor (!p2 | G((p1 | p2) xor Xp1))",
    "Gp1 <-> p2Up0",
    "Gp0 xor Fp2",
    "F(p1 & XFp0) -> (!p1 U p2)",
    "(p0 U p1) & Fp0 & Gp1 & Fp2"
]

oblimtdswas = [spot.obligation_to_mtdswa(spot.formula(f)) for f in obligations]
oblimtdswas_ex = [spot.obligation_to_mtdswa(spot.formula("\\exists p0: " + f))
                  for f in obligations]
oblimtdswas_fa = [spot.obligation_to_mtdswa(spot.formula("\\forall p0: " + f))
                  for f in obligations]

for i in range(len(obligations)):
    # Test existential quantification.
    m_ex = spot.quantify_exists(oblimtdswas[i], spot.formula.ap('p0'))
    pxor = spot.product_xor(m_ex, oblimtdswas_ex[i])
    tc.assertTrue(pxor.as_twa().is_empty(),
                  "Existential quantification of MTDSwA "
                  + "is not equivalent to LTL existential quantification: "
                  + f"{obligations[i]}")

    # Test universal quantification.
    m_fa = spot.quantify_forall(oblimtdswas[i], spot.formula.ap('p0'))
    pxor = spot.product_xor(m_fa, oblimtdswas_fa[i])
    tc.assertTrue(pxor.as_twa().is_empty(),
                  "Universal quantification of MTDSwA "
                  + "is not equivalent to LTL universal quantification: "
                  + f"{obligations[i]}")
