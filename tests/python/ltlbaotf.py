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

# CPython use reference counting, so that automata are destructed
# when we expect them to be.   However other implementations like
# PyPy may call destructors latter, causing different output.
from platform import python_implementation
if python_implementation() == 'CPython':
    def gcollect():
        pass
else:
    import gc
    def gcollect():
        gc.collect()

tc = TestCase()

_keepalive = []


def copy_state(s):
    # The ba_state objects returned by init_state()/succ_as_ba_edges()
    # may reference data owned by a temporary vector; keep a plain copy.
    r = spot.ba_state()
    r.f = s.f
    r.m = s.m
    return r


def build_nba(f, from_bdd=False, opts=None, **kwargs):
    """Expand the on-the-fly explorer spot.ltl_to_ba_otf into an NBA.

    The automaton uses state-based Büchi acceptance: every state with
    m == -1 is accepting, so all its outgoing edges carry acceptance
    set 0.  When no options object is given, extra keyword arguments
    are passed to the explorer as translation options.
    """
    d = spot.make_bdd_dict()
    aut = spot.make_twa_graph(d)
    if opts is None:
        ba = spot.ltl_to_ba_otf(f, dict=d, **kwargs)
    else:
        ba = spot.ltl_to_ba_otf(f, opts, dict=d)
    # No owner was passed, so the dict variables die with the
    # explorer: keep it alive while aut is in use.  (A C++ caller
    # could instead pass aut as the owner argument.)
    _keepalive.append(ba)
    idx = {}
    pending = []

    def add(s):
        key = (s.f, s.m)
        if key not in idx:
            idx[key] = aut.new_state()
            pending.append(copy_state(s))
        return idx[key]

    aut.set_init_state(add(ba.init_state()))
    while pending:
        s = pending.pop()
        src = idx[(s.f, s.m)]
        acc = spot.mark_t([0]) if s.m == -1 else spot.mark_t()
        if from_bdd:
            isop = spot.minato_isop(ba.succ_as_bdd(s))
            cube = isop.next()
            while cube != buddy.bddfalse:
                nxt = buddy.bdd_exist(cube, ba.var_set())
                cond = buddy.bdd_exist(cube, ba.next_set())
                dst = ba.state_from_var(buddy.bdd_var(nxt))
                aut.new_edge(src, add(dst), cond, acc)
                cube = isop.next()
        else:
            # Keep es alive while reading e.dst, which references it.
            es = ba.succ_as_ba_edges(s)
            for e in es:
                aut.new_edge(src, add(e.dst), e.cond, acc)
    aut.set_buchi()
    aut.prop_state_acc(True)
    return aut


# --- Basic API checks, on a formula with a single eventuality. ----------
f = spot.parse_formula('a U b')
d = spot.make_bdd_dict()
aut = spot.make_twa_graph(d)
ba = spot.ltl_to_ba_otf(f, dict=d)

# The bdd_dict is an optional named argument that defaults to the
# global spot._bdd_dict.  (bdd_dict.__eq__ compares the underlying
# dictionaries, not the Python proxies.)
tc.assertTrue(spot.ltl_to_ba_otf(f).get_dict() == spot._bdd_dict)
tc.assertTrue(spot.ltl_to_tgba_fm_otf(f).get_dict() == spot._bdd_dict)
tc.assertTrue(spot.ltl_to_ba_otf(f, dict=d).get_dict() == d)
tc.assertFalse(spot.ltl_to_ba_otf(f).get_dict() == d)

tc.assertEqual(str(ba.orig_formula()), 'a U b')
s0 = ba.init_state()
tc.assertEqual(str(s0.f), 'a U b')
tc.assertEqual(s0.m, 0)
tc.assertFalse(ba.is_accepting(s0))

acc0 = spot.ba_state()
acc0.f = s0.f
acc0.m = -1
tc.assertTrue(ba.is_accepting(acc0))

# register_next_state / state_from_var round-trip.
v = ba.register_next_state(s0)
got = ba.state_from_var(v)
tc.assertEqual(str(got.f), 'a U b')
tc.assertEqual(got.m, 0)

# The symbolic view is non-empty and decomposable.
tc.assertTrue(ba.succ_as_bdd(s0) != buddy.bddfalse)

# --- Language equivalence, on a set of formulas. ----------------
formulas = [
    'G F p & G F q',
    'p U (q U r)',
    'G(Fa & ((a M b) U ((c U !d) M d)))',
    'F a & F b & F c',
    'a U b',
    '(a -> F b) & (b -> F a)',
    'G F a -> G F b',
    'F(a & X(!a & Fb))',
    '(a U b) | G c',
    'X a',
    'tt',
    'ff',
    'G F p',
    'G F (p & X q)',
    'F G p -> F G q',
    'G(a -> F b)',
    'F a | G b',
    'a W b',
    'a M b',
    'a R b',
    'G F(a | b) & G F(!a | !b)',
    'G(F a | F b)',
    'a U (b U (c U (d U e)))',
    'G F a & G F b & G F c & G F d',
    '((p U q) U r) & G F s',
    '! (G F p -> G F q)',
]
for text in formulas:
    f = spot.parse_formula(text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f)), text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, from_bdd=True)), text)

# --- Random formulas, both views. --------------------------------------
for f in spot.randltl(3, 50, seed=42):
    tc.assertTrue(spot.are_equivalent(f, build_nba(f)), str(f))
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, from_bdd=True)), str(f))


# --- Translation options. ------------------------------------------
# The translation options are the C++ struct
# spot::ltl_to_tgba_fm_otf_options (spelled ltl_to_tgba_fm_otf::options
# and ltl_to_ba_otf::options in C++).  SWIG cannot expose nested
# classes, so it is also re-attached to both explorers as a class
# attribute, mirroring the C++ names.
opts = spot.ltl_to_tgba_fm_otf_options()
tc.assertFalse(opts.exprop)
tc.assertTrue(opts.symb_merge)          # C++ default
tc.assertTrue(spot.ltl_to_tgba_fm_otf.options
              is spot.ltl_to_tgba_fm_otf_options)
tc.assertTrue(spot.ltl_to_ba_otf.options
              is spot.ltl_to_tgba_fm_otf_options)

# The options are forwarded to the C++ explorer: turning on exprop,
# branching postponement and the unambiguous translation keeps the
# language intact.
opts.exprop = True
opts.branching_postponement = True
for text in ('a U b', 'G F a & G F b', 'F(a & X(!a & F b))'):
    f = spot.parse_formula(text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, opts=opts)), text)
    tc.assertTrue(spot.are_equivalent(f, build_nba(f, from_bdd=True,
                                                   opts=opts)), text)
unam = spot.ltl_to_ba_otf.options()
unam.unambiguous = True
f = spot.parse_formula('F(a & X(!a & F b))')
tc.assertTrue(spot.are_equivalent(f, build_nba(f, opts=unam)))

# force_obligation is visible as a change in the allocated colors.
obl = spot.ltl_to_tgba_fm_otf.options()
obl.force_obligation = True
f = spot.parse_formula('G F a & G F b')
tc.assertEqual(spot.ltl_to_ba_otf(f).num_colors(), 2)
tc.assertEqual(spot.ltl_to_ba_otf(f, obl).num_colors(), 1)

# The fields of the options struct can also be given as keyword
# arguments, both to the options constructor and to the explorers.
kwd = spot.ltl_to_tgba_fm_otf_options(exprop=True, symb_merge=False)
tc.assertTrue(kwd.exprop)
tc.assertFalse(kwd.symb_merge)
tc.assertFalse(kwd.unambiguous)         # untouched fields keep defaults
tc.assertEqual(spot.ltl_to_ba_otf(f, force_obligation=True).num_colors(), 1)
tc.assertEqual(spot.ltl_to_tgba_fm_otf(f, obl).num_colors(), 1)
tc.assertEqual(spot.ltl_to_tgba_fm_otf(f,
                                       force_obligation=True).num_colors(), 1)

# build_nba() forwards its keyword arguments to the explorer.
for text in ('a U b', 'G F a & G F b', 'F(a & X(!a & F b))'):
    f = spot.parse_formula(text)
    tc.assertTrue(spot.are_equivalent(
        f, build_nba(f, exprop=True, branching_postponement=True)), text)

# Unknown options, and mixing a positional options object with option
# keywords, are reported as errors.
tc.assertRaises(TypeError, spot.ltl_to_tgba_fm_otf_options,
                no_such_option=True)
tc.assertRaises(TypeError, spot.ltl_to_tgba_fm_otf, f, no_such_option=True)
tc.assertRaises(TypeError, spot.ltl_to_ba_otf, f, kwd, exprop=True)

# --- Owner identity. --------------------------------------------------
# The owner argument is an opaque identity under which the explorer
# registers its BDD variables.  It must be the address of the C++
# owner object (typically the automaton being built), so that this
# object's destructor can release the variables.  It used to be the
# address of the SWIG shared_ptr wrapper instead, so the variables
# leaked and the bdd_dict destructor aborted with "some maps are not
# empty".
def all_vars_free(d):
    ostr = spot.ostringstream()
    d.dump(ostr)
    # A variable with at least one owner is printed as " xN { ... }",
    # while a free variable is printed as " Free".
    return '{' not in ostr.str()


f = spot.parse_formula('G F a & G F b')

d = spot.make_bdd_dict()
aut = spot.make_twa_graph(d)
ba = spot.ltl_to_ba_otf(f, owner=aut, dict=d)
ba.succ_as_ba_edges(ba.init_state())
del ba
del aut
gcollect()
tc.assertTrue(all_vars_free(d))

d = spot.make_bdd_dict()
aut = spot.make_twa_graph(d)
ex = spot.ltl_to_tgba_fm_otf(f, owner=aut, dict=d)
ex.succ_as_edges(ex.init_state())
del ex
del aut
gcollect()
tc.assertTrue(all_vars_free(d))

# The TGBA explorer's edge vectors are usable from Python too.
ex = spot.ltl_to_tgba_fm_otf(spot.parse_formula('a U b & X c'), opts)
edges = ex.succ_as_edges(ex.init_state())
tc.assertTrue(len(edges) > 0)
tc.assertTrue(all(isinstance(e, spot.fm_edge) for e in edges))
tc.assertTrue(all(isinstance(e.dst, spot.formula) for e in edges))
tc.assertTrue(all(isinstance(e.acc, spot.mark_t) for e in edges))
raw = ex.succ_as_raw_edges(ex.init_state())
tc.assertTrue(all(isinstance(e, spot.fm_edge) for e in raw))
simple = ex.succ_as_acc_and_dest(ex.init_state())
tc.assertTrue(len(simple) > 0)
tc.assertTrue(all(isinstance(e, spot.fm_simple_edge) for e in simple))
tc.assertTrue(all(isinstance(e.dst, spot.formula) for e in simple))

# ap() lists the atomic propositions discovered by the exploration, in
# order of discovery.  This is what ltl_to_tgba_fm() uses to declare
# the propositions of the automaton it builds.
ex = spot.ltl_to_tgba_fm_otf(spot.parse_formula('a | b'),
                             dict=spot.make_bdd_dict())
ex.succ_as_edges(ex.init_state())
tc.assertEqual({str(p) for p in ex.ap()}, {'a', 'b'})


# --- Dot rendering. -------------------------------------------------
def print_ltlbaotf(formula_text):
    """Return the output of print_dot() for an explored spot.ltl_to_ba_otf."""
    ba = spot.ltl_to_ba_otf(spot.parse_formula(formula_text))
    ostr = spot.ostringstream()
    ba.print_dot(ostr)
    return ostr.str()


dot = print_ltlbaotf('a U b')
tc.assertTrue(dot.startswith('digraph ltl_to_ba_otf'), dot)
tc.assertIn('(a U b, 0)', dot)          # the initial state
for s in ('(a U b, -1)', '(b, -1)', '(1, -1)'):
    if s in dot:
        break
else:
    tc.fail('no accepting state in the dot output')
tc.assertIn('peripheries=2', dot)       # doubled border for (f, -1)
tc.assertIn('"a"', dot)                 # BDD node for the AP a

# State (formula "Xf") has no successor: its BDD is bddfalse.
dot = print_ltlbaotf('Xf')
tc.assertIn('B0 [shape=square', dot)


def print_ltl_to_tgba(formula_text):
    """Return print_dot() output for an explored ltl_to_tgba_fm_otf."""
    ex = spot.ltl_to_tgba_fm_otf(spot.parse_formula(formula_text))
    ostr = spot.ostringstream()
    ex.print_dot(ostr)
    return ostr.str()


# AP, promise, and Next nodes in the same graph.
dot = print_ltl_to_tgba('a U b & X c')
tc.assertTrue(dot.startswith('digraph ltl_to_tgba_fm_otf'), dot)
tc.assertIn('label="a"', dot)                 # AP node
tc.assertIn('label="P(1)"', dot)              # acceptance promise
# (a U b & X c is syntactically persistent, so the translation uses a
# single acceptance set, registered as Acc(1).)
tc.assertIn('shape=diamond', dot)             # ... as a diamond
tc.assertIn('label="a U b"', dot)             # Next variable
tc.assertIn('label="c"', dot)                 # AP and Next var for c
# Only the BDD terminal 1 has a doubled border.
tc.assertTrue(dot.count('peripheries=2') == 1, dot)

# A formula with two promises (non-persistent, so not single-acc).
dot = print_ltl_to_tgba('G F a & G F b')
tc.assertIn('label="P(a)"', dot)
tc.assertIn('label="P(b)"', dot)

# An unsatisfiable formula has no successor: its BDD is bddfalse.
dot = print_ltl_to_tgba('Xf')
tc.assertIn('B0 [shape=square', dot)
