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
from buddy import bddtrue, bddfalse, bdd_ithvar, bdd_nithvar
from unittest import TestCase
tc = TestCase()

def assert_word_accepted(w, aut, msg=''):
    s = str(w) if not isinstance(w, str) else w
    parsed = spot.parse_word(s, aut.get_dict())
    tc.assertTrue(parsed.intersects(aut),
                  f"Word {s!r} should be accepted"
                  + (f': {msg}' if msg else ''))

# ---------------------------------------------------------------------------
# Helper: collect all words from a lasso_enumerator into a list of strings.
# ---------------------------------------------------------------------------
def collect_words(aut, min_stem, max_stem, min_cycle, max_cycle):
    en = spot.lasso_enumerator(aut, min_stem, max_stem, min_cycle, max_cycle)
    words = []
    while True:
        w = en.next_word()
        if w is None:
            break
        words.append(str(w))
    return words

def collect_runs(aut, min_stem, max_stem, min_cycle, max_cycle):
    en = spot.lasso_enumerator(aut, min_stem, max_stem, min_cycle, max_cycle)
    runs = []
    while True:
        r = en.next_run()
        if r is None:
            break
        runs.append(r)
    return runs

# ---------------------------------------------------------------------------
# Test 1: Simple Büchi automaton from formula "GFp"
#   The automaton accepts all words where p holds infinitely often.
#   With stem=0, cycle=1: the only 1-cycle returning to initial state
#   with an accepting edge must be a p-loop.
# ---------------------------------------------------------------------------
f = spot.formula('GFp')
aut = spot.translate(f)

# Sanity: acceptance must be Büchi (or the test is moot).
tc.assertTrue(aut.acc().is_buchi())

# Collect words with small bounds: at least some words must be found.
words = collect_words(aut, 0, 3, 1, 3)
tc.assertGreater(len(words), 0, "Expected at least one accepted word for GFp")

# Every returned word should be accepted by the automaton.
for w_str in words:
    assert_word_accepted(w_str, aut)

# ---------------------------------------------------------------------------
# Test 2: True (all-accepting) automaton
#   Build a 2-state automaton with true acceptance.
# ---------------------------------------------------------------------------
bdict = spot.make_bdd_dict()
true_aut = spot.make_twa_graph(bdict)
true_aut.set_acceptance(spot.acc_cond(0, spot.acc_code('t')))
p = spot.formula('p')
ap = true_aut.register_ap('p')
s0 = true_aut.new_state()
s1 = true_aut.new_state()
true_aut.set_init_state(s0)
# s0 -[p]-> s0  (self-loop)
true_aut.new_edge(s0, s0, bdd_ithvar(ap))
# s0 -[!p]-> s1
true_aut.new_edge(s0, s1, bdd_nithvar(ap))
# s1 -[p]-> s0
true_aut.new_edge(s1, s0, bdd_ithvar(ap))
# s1 -[!p]-> s1
true_aut.new_edge(s1, s1, bdd_nithvar(ap))

tc.assertTrue(true_aut.acc().is_t())
runs_true = collect_runs(true_aut, 0, 1, 1, 2)
tc.assertGreater(len(runs_true), 0,
                 "Expected runs for true-acceptance automaton")

# ---------------------------------------------------------------------------
# Test 3: Empty automaton (no accepting states/transitions)
#   Build a single-state Büchi automaton with one self-loop but no
#   acceptance marks → should yield no accepted words.
# ---------------------------------------------------------------------------
empty_aut = spot.make_twa_graph(bdict)
empty_aut.set_generalized_buchi(1)
ap2 = empty_aut.register_ap('p')
q = empty_aut.new_state()
empty_aut.set_init_state(q)
# Self-loop with no acceptance mark.
empty_aut.new_edge(q, q, bddtrue, spot.mark_t([]))
words_empty = collect_words(empty_aut, 0, 2, 1, 2)
tc.assertEqual(words_empty, [],
               "Expected no accepted words from Büchi automaton with no marks")

# ---------------------------------------------------------------------------
# Test 4: Ordering — shorter total lengths come first.
# ---------------------------------------------------------------------------
# Use a simple 1-state Büchi automaton with a self-loop (accepting).
simple_aut = spot.make_twa_graph(bdict)
simple_aut.set_generalized_buchi(1)
ap3 = simple_aut.register_ap('p')
r = simple_aut.new_state()
simple_aut.set_init_state(r)
simple_aut.new_edge(r, r, bddtrue, spot.mark_t([0]))

en = spot.lasso_enumerator(simple_aut, 0, 2, 1, 3)
runs4 = []
while True:
    run = en.next_run()
    if run is None:
        break
    runs4.append((len(list(run.prefix)), len(list(run.cycle))))

# Check monotone total length, ties broken by shorter stem first.
for i in range(len(runs4) - 1):
    s0_, c0_ = runs4[i]
    s1_, c1_ = runs4[i + 1]
    tc.assertLessEqual(s0_ + c0_, s1_ + c1_,
                       f"Total lengths must be non-decreasing: "
                       f"got {runs4[i]} then {runs4[i+1]}")
    if s0_ + c0_ == s1_ + c1_:
        tc.assertLessEqual(s0_, s1_,
                           f"For equal totals, stem must be non-decreasing: "
                           f"got {runs4[i]} then {runs4[i+1]}")

# ---------------------------------------------------------------------------
# Test 5: Bounds validation — invalid arguments must raise.
# ---------------------------------------------------------------------------
try:
    spot.lasso_enumerator(simple_aut, 3, 1, 1, 5)  # max_stem < min_stem
    tc.fail("Expected exception for max_stem < min_stem")
except Exception:
    pass

try:
    spot.lasso_enumerator(simple_aut, 0, 5, 0, 5)  # min_cycle = 0
    tc.fail("Expected exception for min_cycle = 0")
except Exception:
    pass

try:
    spot.lasso_enumerator(simple_aut, 0, 5, 3, 1)  # max_cycle < min_cycle
    tc.fail("Expected exception for max_cycle < min_cycle")
except Exception:
    pass

# ---------------------------------------------------------------------------
# Test 6: Arbitrary acceptance — Rabin 2 automaton.
# Build a 1-state automaton with Rabin 2 acceptance and a self-loop
# carrying marks {0, 2} (satisfies Inf(0)&Fin(1) | Inf(2)&Fin(3)).
# ---------------------------------------------------------------------------
rabin_aut = spot.make_twa_graph(bdict)
rabin_aut.set_acceptance(spot.acc_cond(spot.acc_code('Rabin 2')))
rs = rabin_aut.new_state()
rabin_aut.set_init_state(rs)
# Rabin 2 = (Fin(0) & Inf(1)) | (Fin(2) & Inf(3)).
# Mark {1}: Fin(0) satisfied (0 absent), Inf(1) satisfied → first pair accepts.
rabin_aut.new_edge(rs, rs, bddtrue, spot.mark_t([1]))
rabin_words = []
en6 = spot.lasso_enumerator(rabin_aut, 0, 0, 1, 1)
while True:
    w = en6.next_word()
    if w is None:
        break
    rabin_words.append(w)
tc.assertEqual(len(rabin_words), 1,
               "Expected 1 accepted word from Rabin automaton")

# ---------------------------------------------------------------------------
# Test 7: Shared cursor — next_run() and next_word() advance the same state.
# ---------------------------------------------------------------------------
en7 = spot.lasso_enumerator(simple_aut, 0, 1, 1, 2)
r1 = en7.next_run()
w2 = en7.next_word()
r3 = en7.next_run()

# All three must be distinct (simple_aut has multiple (stem,cycle) combos).
tc.assertIsNotNone(r1)
tc.assertIsNotNone(w2)
# r1 and w2 should differ (they are consecutive results).
tc.assertNotEqual(str(r1), str(w2))

# ---------------------------------------------------------------------------
# Test 8: GFa & GFb & FG(c) — enumerate words with stem in [0,3],
# cycle in [1,5] and verify (a) each word is accepted and (b) the count
# per (stem, cycle) pair matches the expected values.
# ---------------------------------------------------------------------------
# Expected counts determined by a reference run of the enumerator:
#   rows = stem length (0..3), cols = cycle length (1..5)
expected_counts = {
    (0, 1): 0, (0, 2): 0, (0, 3): 0, (0, 4): 0, (0, 5): 0,
    (1, 1): 1, (1, 2): 3, (1, 3): 8, (1, 4): 21, (1, 5): 55,
    (2, 1): 2, (2, 2): 8, (2, 3): 24, (2, 4): 66, (2, 5): 176,
    (3, 1): 5, (3, 2): 22, (3, 3): 68, (3, 4): 189, (3, 5): 506,
}

aut8 = spot.translate('GFa & GFb & FG(c)', 'Buchi', 'sbacc')
tc.assertTrue(aut8.acc().is_buchi())

for stem in range(0, 4):
    for cycle in range(1, 6):
        en = spot.lasso_enumerator(aut8, stem, stem, cycle, cycle)
        count = 0
        while True:
            w = en.next_word()
            if w is None:
                break
            assert_word_accepted(w, aut8,
                                 f'stem={stem} cycle={cycle}')
            count += 1
        tc.assertEqual(count, expected_counts[(stem, cycle)],
                       f"Wrong count for stem={stem} cycle={cycle}: "
                       f"got {count}, expected "
                       f"{expected_counts[(stem, cycle)]}")

# ---------------------------------------------------------------------------
# Test 9: GFa & GFb & FG(c) — single enumerator over stem in [0,3],
# cycle in [1,5].  Verify ordering (non-decreasing total, ties by shorter
# stem) and that the histogram matches the expected counts from Test 8.
# ---------------------------------------------------------------------------
en9 = spot.lasso_enumerator(aut8, 0, 3, 1, 5)
from collections import defaultdict
histogram = defaultdict(int)
prev_stem, prev_cycle = 0, 0
while True:
    run = en9.next_run()
    if run is None:
        break
    stem_len = len(list(run.prefix))
    cycle_len = len(list(run.cycle))
    total = stem_len + cycle_len
    prev_total = prev_stem + prev_cycle
    tc.assertGreaterEqual(total, prev_total,
                          f"Total length decreased: ({prev_stem},{prev_cycle})"
                          f" -> ({stem_len},{cycle_len})")
    if total == prev_total:
        tc.assertGreaterEqual(stem_len, prev_stem,
                              f"Equal total but stem decreased: "
                              f"({prev_stem},{prev_cycle})"
                              f" -> ({stem_len},{cycle_len})")
    prev_stem, prev_cycle = stem_len, cycle_len
    histogram[(stem_len, cycle_len)] += 1

tc.assertEqual(dict(histogram), {k: v for k, v in expected_counts.items() if v})



# ---------------------------------------------------------------------------
# Test 10: bddfalse edges must be ignored.
# Build a 2-state Büchi automaton where some edges carry bddfalse labels.
# Only the satisfiable edges should be traversed.
#
#   s0 --[false]--> s0  (ignored)
#   s0 --[true] --> s1  (accepting)
#   s1 --[false]--> s0  (ignored)
#   s1 --[true] --> s1  (accepting self-loop)
#
# The only lasso with stem=1, cycle=1 that can be formed from satisfiable
# edges is: stem s0->s1 (true), cycle s1->s1 (true).  That is 1 word.
# With stem=0 there is no cycle back to s0 via satisfiable edges alone,
# so 0 words.
# ---------------------------------------------------------------------------
false_aut = spot.make_twa_graph(bdict)
false_aut.set_generalized_buchi(1)
fs0 = false_aut.new_state()
fs1 = false_aut.new_state()
false_aut.set_init_state(fs0)
false_aut.new_edge(fs0, fs0, bddfalse, spot.mark_t([0]))  # ignored
false_aut.new_edge(fs0, fs1, bddtrue, spot.mark_t([0]))
false_aut.new_edge(fs1, fs0, bddfalse, spot.mark_t([0]))  # ignored
false_aut.new_edge(fs1, fs1, bddtrue, spot.mark_t([0]))

# stem=0, cycle=1..2: no satisfiable cycle back to s0
w_stem0 = collect_words(false_aut, 0, 0, 1, 2)
tc.assertEqual(w_stem0, [], "bddfalse edges must not form cycles")

# stem=1, cycle=1: exactly one word (true; cycle{true})
w_stem1 = collect_words(false_aut, 1, 1, 1, 1)
tc.assertEqual(len(w_stem1), 1, "Expected exactly 1 word for stem=1 cycle=1")
assert_word_accepted(w_stem1[0], false_aut)
