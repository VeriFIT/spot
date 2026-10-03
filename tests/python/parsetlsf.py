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

import os
import random
import spot
from unittest import TestCase
tc = TestCase()


def parse_tlsf(source, opts=None):
    """spot.parse_tlsf() with the mandatory-INFO check disabled.

    Most fixtures below are stripped-down specifications that only
    spell out the INFO items the test they belong to is about, so
    requiring TITLE, DESCRIPTION, SEMANTICS, and TARGET on all of them
    would only add noise.  The check itself is exercised by the
    check_info tests further down."""
    if opts is None:
        opts = spot.tlsf_parser_options()
    opts.check_info = False
    return spot.parse_tlsf(source, opts)


def formulas_in_section(canonical, keyword):
    """Semicolon-terminated lines inside the `KEY { ... }` block of a
    tlsf_print canonical output.  Each formula of a MAIN subsection is
    printed on its own ';'-terminated line, so this recovers the number
    of formulas parsed into that section without reaching into the
    opaque AST."""
    inside = False
    found = []
    for line in canonical.splitlines():
        if line == '  ' + keyword + ' {':
            inside = True
        elif inside:
            if line == '  }':
                break
            if line.endswith(';'):
                found.append(line)
    return found

contents = """\
INFO {
  TITLE:       "simple arbiter"
  DESCRIPTION: "A small TLSF file used by tests/python/parsetlsf.py"
  SEMANTICS:   Mealy
  TARGET:      Mealy
}
GLOBAL {
  PARAMETERS {
    N = 2;
  }
  DEFINITIONS {
    Pos(grid, i, j) = grid[(i + j) * N];
  }
}
MAIN {
  INPUTS {
    request[N];
    grant[N];
  }
  OUTPUTS {
    done;
  }
  GUARANTEE {
    G((!request[0]) || F(grant[0]));
    G((!request[1]) || F(grant[1]));
  }
}
"""

# chomp.tlsf, tictactoe.tlsf, and scutella1.tlsf, are specifications
# embedded here round-trip and translation fixtures below do not
# depend on a copy of the file living in the source tree.
chomp_contents = """\
INFO {
  TITLE:       "Chomp Game"
  DESCRIPTION: "Parameteric Chomp Game over a NxM grid"
  SEMANTICS:   Mealy,Finite
  TARGET:      Mealy
}

GLOBAL {
  PARAMETERS {
    N = 3;
    M = 3;
  }
  DEFINITIONS {
    Pos(grid, i, j) = grid[i + j * N];
    PickOne(sel) = ||[0 <= k < (SIZEOF sel)] sel[k];
    // if sel[i] is true, sel[i+1] should be too.
    AboveToo(sel) = &&[0 <= i < ((SIZEOF sel) - 1)] (sel[i] -> sel[i+1]);
    // if it's the other's turn, all values of sel should be false
    OtherTurn(other, sel) = other -> (&&[0 <= k < (SIZEOF sel)](!sel[k]));
    // if it's the other's turn and square (0,0) still exists, our
    // choices for sx and sy on next turn depend on what square is
    // available in the grid.
    NextChoices(grid, other, sx, sy) =
      (Pos(grid, 0, 0) && other) ->
        (||[0 <= x < N] ||[0 <= y < M] (Pos(grid, x, y) && X(sx[x] && sy[y])));
    // Rules that both players should obey
    PlayerRules(grid, other, sx, sy) =
       AboveToo(sx) &&
       AboveToo(sy) &&
       OtherTurn(other, sx) &&
       OtherTurn(other, sy) &&
       NextChoices(grid, other, sx, sy);
  }
}

MAIN {
  INPUTS {
    // When it's the input player's turn, they
    // use ix[I] iy[J] to select square (I,J).
    ix[N];
    iy[M];
  }
  OUTPUTS {
    // When it's the output player's turn, they
    // use ox[I] oy[J] to select square (I,J).
    ox[N];
    oy[M];
    // whether a square is available
    os[N*M];
    // turn
    oti; // input turn
    oto; // output turn
  }
  PRESET {
    // The output player is the first player.
    !oti && oto;
    // The output player has to choose a square.
    PickOne(ox);
    PickOne(oy);
    // The squares that are taken initially depend on the first choice.
    &&[0 <= i < N] &&[0 <= j < M] (Pos(os, i, j) <-> !(ox[i] && oy[j]));

    // Turns alternate between players.
    // (Writing G(oto <-> X oti) would be ok in LTL, but not LTLf.)
    G(oti <-> !oto);
    G(oto -> X oti);
    G(oti -> X oto);
  }
  REQUIRE {
    PlayerRules(os, oto, ix, iy);
  }
  ASSERT {
    PlayerRules(os, oti, ox, oy);
    // If (i,j) is selected by either player, then (i,j) should become false.
    &&[0 <= i < N] &&[0 <= j < M]
      (((ox[i] && oy[j]) || (ix[i] && iy[j])) -> !Pos(os,i,j));
    // if (i,j) is not available now, it's not available on next turn.
    &&[0 <= i < N] &&[0 <= j < M] ((!Pos(os,i,j)) -> X !(Pos(os,i,j)));
    // if (i,j) is available now, it might not be on next turn.
    &&[0 <= i < N] &&[0 <= j < M]
      (Pos(os,i,j) -> X(Pos(os,i,j) || (ox[i] && oy[j]) || (ix[i] && iy[j])));
  }
  GUARANTEE {
    // The game finishes once square (0, 0) has been taken, and since
    // this square is poisonous, we want the input player to take it.
    Pos(os,0,0) U (!Pos(os,0,0) && oti);
  }
}
"""

tictactoe_contents = """\
INFO {
  TITLE:       "Tic Tac Toe"
  DESCRIPTION: "Tic Tac Toe Game, Finite version"
  SEMANTICS:   Mealy,Finite
  TARGET:      Mealy
}

GLOBAL {
  DEFINITIONS {
    PickOne(A) = (||[0 <= i < 9] A[i]) &&
      (&&[0 <= i < 9] (A[i] -> &&[i <= j < 9]!A[j]));
    // Keep the value of A[b...e] for next step.
    NoChange(A,b,e) = &&[b <= i < e] ((A[i] && X(A[i])) || (!A[i] && X(!A[i])));
    // change a single cell in A that isn't used in B.
    ChangeOne(A, B) = (||[0 <= i < 9] ((!A[i] && !B[i]) -> X(A[i]))) &&
      (&&[0 <= i < 9] ((!A[i] && X(A[i])) -> NoChange(A, i+1, 9)));
    // all cells are taken by one of the player
    AllTaken(A, B) = &&[0 <= i < 9] (A[i] || B[i]);
    // check for three aligned cells
    Aligned(A) = (A[0] && A[1] && A[2]) ||
                 (A[3] && A[4] && A[5]) ||
                 (A[6] && A[7] && A[8]) ||
                 (A[0] && A[3] && A[6]) ||
                 (A[1] && A[4] && A[7]) ||
                 (A[2] && A[5] && A[8]) ||
                 (A[0] && A[4] && A[8]) ||
                 (A[2] && A[4] && A[6]);
  }
}

MAIN {
  // The cells are numbered as follows:
  //   0 1 2
  //   3 4 5
  //   6 7 8
  // pi[n] is true iff the input player marked cell n.
  // po[n] is true iff the output player marked cell n.
  INPUTS {
    pi[9];
  }
  OUTPUTS {
    po[9];
    turno; // false = input's turn, true = output's turn
  }
  PRESET {
    // The output player is the first player.
    turno;
    // Turn alternate betwen players
    // (The number of turns is odd, so it's OK to use an equivalence
    // with weak X here, it means that if turno is false the next step must
    // exist.)
    G(turno <-> X !turno);
    // The player should select a single cell.
    PickOne(po);
  }
  INITIALLY {
    // the input player does not select any value on first turn.
    &&[0 <= i < 9] !pi[i];
  }
  REQUIRE {
    // if the next turn is the input's player turn, they
    // should change exactly one cell that isn't taken by any player
    X(!turno) -> ChangeOne(pi, po);
    // If it not the input's turn, we do not want to see any change.
    X(turno) -> NoChange(pi, 0, 9);
  }
  ASSERT {
    // if the next turn is the outut's player turn, they
    // should change exactly one cell that isn't taken by any player
    X[!](turno) -> ChangeOne(po, pi);
    // If it not the output's turn, we do not want to see any change.
    X[!](!turno) -> NoChange(po, 0, 9);
  }
  GUARANTEE {
    // The game finishes all cells are taken, or if the output player
    // has aligned 3 cells.
    F(AllTaken(pi,po) || Aligned(po));
    // The output player should never align 3 cells.
    G(!Aligned(pi));
  }
}
"""

scutella1_contents = """\
INFO {
  TITLE:       "Scutellà's counterexample"
  DESCRIPTION: "LTLf version of a counterexample by Scutellà"
  SEMANTICS:   Moore,Finite
  TARGET:      Moore
}
GLOBAL {
  DEFINITIONS {
    ExactlyOne(x) = (||[0 <= i < (SIZEOF x)] x[i])
      && (&&[1 <= i < (SIZEOF x)] (x[i] -> (&&[0 <= j < i] !x[j])));
  }
}

MAIN {
  INPUTS {
    a;
  }
  OUTPUTS {
    s[5]; // five states
    b;
  }
  PRESET {
    s[0]; // we start in state 0
  }
  ASSERT {
    ExactlyOne(s); // only one state is active at all time
    // transition structure:
    s[0] -> ((a && X(s[3])) || (!a && X(s[1])));
    s[1] -> X(s[2]);
    s[2] -> ((!b && X(s[3])) || (b && X(s[4])));
    s[3] -> X(s[1]);
  }
  GUARANTEE {
    // The game must reach state 4
    F(s[4]);
  }
}
"""

filename = 'parsetlsf.tlsf'
with open(filename, 'w') as f:
    f.write(contents)

try:
    parsed = parse_tlsf(filename)
    tc.assertFalse(parsed.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in parsed.errors]}")

    # INFO
    tc.assertEqual(parsed.title, "simple arbiter")
    tc.assertEqual(parsed.description,
                   "A small TLSF file used by tests/python/parsetlsf.py")
    tc.assertEqual(parsed.semantics, spot.tlsf_semantics_Mealy)
    tc.assertEqual(parsed.target, spot.tlsf_target_Mealy)

    # MAIN inputs / outputs
    tc.assertEqual(list(parsed.inputs), ["request", "grant"])
    tc.assertEqual(list(parsed.outputs), ["done"])

    # parsed_tlsf does not expose the MAIN bodies (they live in the
    # opaque AST); the per-section shapes are pinned below on the
    # canonical printed form.  GUARANTEE holds 2 formulas.
    tc.assertEqual(parsed.filename, filename)

    # Round-trip via spot.tlsf_print.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed)
    canonical = ostr.str()
    tc.assertIn("INFO {\n", canonical)
    tc.assertIn("PARAMETERS {\n", canonical)
    tc.assertIn("DEFINITIONS {\n", canonical)
    tc.assertIn("INPUTS {\n", canonical)
    tc.assertIn("OUTPUTS {\n", canonical)
    tc.assertIn("GUARANTEE {\n", canonical)
    tc.assertIn("F grant[0]", canonical)
    tc.assertIn("F grant[1]", canonical)
    tc.assertEqual(formulas_in_section(canonical, 'INITIALLY'), [])
    tc.assertEqual(formulas_in_section(canonical, 'PRESET'), [])
    tc.assertEqual(formulas_in_section(canonical, 'REQUIRE'), [])
    tc.assertEqual(formulas_in_section(canonical, 'ASSERT'), [])
    tc.assertEqual(formulas_in_section(canonical, 'ASSUME'), [])
    tc.assertEqual(len(formulas_in_section(canonical, 'GUARANTEE')), 2,
                   "expected 2 formulas in GUARANTEE")

    parsed2 = parse_tlsf(canonical)

    tc.assertFalse(parsed2.errors)
    tc.assertEqual(parsed2.title, parsed.title)
    tc.assertEqual(parsed2.description, parsed.description)
    tc.assertEqual(parsed2.semantics, parsed.semantics)
    tc.assertEqual(parsed2.target, parsed.target)
    tc.assertEqual(list(parsed2.inputs), list(parsed.inputs))
    tc.assertEqual(list(parsed2.outputs), list(parsed.outputs))
    # The canonical form must re-deparse byte-identically.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed2)
    tc.assertEqual(ostr.str(), canonical)

    # Translation: tlsf_to_ltl produces a formula whose APs are the
    # bus-flattened `request_0`/`request_1`/`grant_0`/`grant_1`, and
    # whose inputs list mirrors those names in declaration order
    # (signals are registered eagerly).
    res = spot.tlsf_to_ltl(parsed)
    tc.assertTrue(bool(res.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr = str(res.full_formula)
    tc.assertIn('request_0', fstr)
    tc.assertIn('grant_0',  fstr)
    tc.assertIn('request_1', fstr)
    tc.assertIn('grant_1',  fstr)
    tc.assertEqual(list(res.inputs),
                   ['request_0', 'request_1', 'grant_0', 'grant_1'])
    # `done` is declared but never used; it is still registered.
    tc.assertEqual(list(res.outputs), ['done'])
    # Errors are surfaced on the parsed AST, not on the result.
    tc.assertFalse(parsed.errors,
                   f"errors: {[(e.first, e.second) for e in parsed.errors]}")
    # tlsf_translation_result carries one LTL formula per MAIN
    # section plus the composed full_formula.  Only GUARANTEE is
    # non-empty here.
    for section in (res.initially, res.preset, res.require,
                    res.assertion, res.assume):
        tc.assertTrue(section.is_tt(),
                      "empty MAIN section should translate to true; "
                      f"got: {section}")
    tc.assertTrue(res.guarantee.equivalent_to(spot.parse_infix_psl(
        'G(!request_0 | F grant_0) & G(!request_1 | F grant_1)').f),
        f"unexpected guarantee section formula: {res.guarantee}")
    tc.assertTrue(res.full_formula.equivalent_to(res.guarantee),
                  f"full formula should match the sole non-empty "
                  f"section; got: {res.full_formula}")

    # Empty spec.
    empty = parse_tlsf("INFO {} GLOBAL {} MAIN {}\n")

    tc.assertFalse(empty.errors)
    tc.assertEqual(empty.title, "")
    tc.assertEqual(list(empty.inputs), [])
    tc.assertEqual(list(empty.outputs), [])
    empty_canon = spot.ostringstream()
    spot.tlsf_print(empty_canon, empty)
    tc.assertEqual(formulas_in_section(empty_canon.str(), 'GUARANTEE'),
                   [])

    # Bogus file.
    bogus = parse_tlsf("/nonexistent/path.tlsf")
    tc.assertTrue(bogus.errors)

    # Malformed file.
    broken = parse_tlsf("INFO { TITLE: \"oops\"\n")

    tc.assertTrue(broken.errors)

    # TRANSITIONS is not a TLSF section and must not be accepted as
    # a Spot-specific extension.
    transitions = parse_tlsf(
        "INFO {} GLOBAL {} MAIN { TRANSITIONS { a; } }\n")

    tc.assertTrue(
        transitions.errors,
        "TRANSITIONS must be rejected as a non-TLSF extension")
    # Test bool/mixed-binary operators and quantifier bodies.
    val = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a[2]; }\n"
            "  OUTPUTS { b[2]; }\n"
            "  REQUIRE {\n"
            "    G((!a[0]) || (b[0] -> F a[1]));\n"
            "    &&[0 <= i < N - 1] (b[i] || !b[i + 1]);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(val.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, val)
    can2 = ostr.str()
    # 2 REQUIRE formulas are recoverable from the canonical print.
    tc.assertEqual(len(formulas_in_section(can2, 'REQUIRE')), 2,
                   "expected 2 formulas in REQUIRE")
    tc.assertIn("a[0]", can2)
    tc.assertIn("b[0]", can2)
    tc.assertIn("F a[1]", can2)
    tc.assertIn("&&[0 <= i < N - 1]", can2)
    # Round-trip: re-parse the canonical and verify the second
    # deparse matches the first (idempotence).
    val2 = parse_tlsf(can2)

    tc.assertFalse(val2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, val2)
    can3 = ostr.str()
    tc.assertEqual(can3, can2)

    # Test associativity-aware parenthesis wrapping in the printer:
    # right-assoc operators in LHS/RHS position, cross-precedence,
    # and a quantifier under a BinaryOp.  Deparse-on-deparse must be
    # idempotent.
    assoc = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a; b; c; p; q; }\n"
            "  ASSERT {\n"
            # Right-assoc -> :
            "    a -> b -> c;\n"
            # Tighter LHS:
            "    a && b -> c;\n"
            # Tighter RHS:
            "    a -> b && c;\n"
            # Quantifier body extends with ->:
            "    &&[0 <= i < N - 1] p -> q;\n"
            # Source parens preserved:
            "    (a -> b) -> c;\n"
            # Left-assoc parent, looser-precedence RHS:
            "    a && (b -> c);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(assoc.errors,
                   f"errors: {[(e.first, e.second) for e in assoc.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, assoc)
    can_ass = ostr.str()
    assoc2 = parse_tlsf(can_ass)

    tc.assertFalse(assoc2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, assoc2)
    can_ass2 = ostr.str()
    tc.assertEqual(can_ass2, can_ass)

    # Test operator precedence and associativity per the TLSF v1.2
    # specification: U/W are separate right-associative tiers, R is a
    # lower left-associative tier, / and % are right-associative and
    # weaker than MUL, and quantifiers share the unary-LTL tier.
    precedence = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a; b; c; d; e; f; g; h; i; j; }\n"
            "  ASSERT {\n"
            "    a U b W c;\n"
            "    a R b U c;\n"
            "    a / b / c;\n"
            "    &&[0 <= i < N - 1] p -> q;\n"
            "    a -> b <-> c;\n"
            "    a || b && c;\n"
            "  }\n"
            "}\n")

    tc.assertFalse(precedence.errors,
                   f"precedence fixture must parse cleanly; "
                   f"errors: {[(e.first, e.second) for e in precedence.errors]}"
                   )
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, precedence)
    can_prec = ostr.str()
    # These spellings are unambiguous under the TLSF precedence and
    # associativity rules and must be stable through round-trips.
    tc.assertIn("a U b W c;", can_prec)
    tc.assertIn("a R b U c;", can_prec)
    tc.assertIn("a / b / c;", can_prec)
    tc.assertIn("&&[0 <= i < N - 1] p -> q;", can_prec)
    tc.assertIn("a -> b <-> c;", can_prec)
    tc.assertIn("a || b && c;", can_prec)
    precedence2 = parse_tlsf(can_prec)

    tc.assertFalse(precedence2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, precedence2)
    tc.assertEqual(ostr.str(), can_prec)

    # Test Finite semantics with bus inputs/outputs: the `X[!]` strong-next
    # operator is accepted (and later emitted as strong_X), while the
    # bare `X!` is NOT a token -- it parses as `X !` (next + bang), and
    # Spot's printer happens to render the result as `X!p`.
    finite = parse_tlsf(
            "INFO {\n"
            "  SEMANTICS:   Mealy,Finite\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 2; }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { event[N]; }\n"
            "  OUTPUTS { ack[N]; }\n"
            "  GUARANTEE {\n"
            "    X[!] ack[0] || !ack[1] || !event[0] || !event[1];\n"
            "  }\n"
            "}\n")

    tc.assertFalse(finite.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in finite.errors]}")
    tc.assertEqual(finite.semantics, spot.tlsf_semantics_MealyFinite)
    tc.assertEqual(finite.target, spot.tlsf_target_Mealy)
    tc.assertEqual(list(finite.inputs), ["event"])
    tc.assertEqual(list(finite.outputs), ["ack"])
    # The GUARANTEE section carries the single X[!]-formula; visible
    # through the canonical print.
    finite_canon = spot.ostringstream()
    spot.tlsf_print(finite_canon, finite)
    tc.assertEqual(len(formulas_in_section(finite_canon.str(),
                                           'GUARANTEE')), 1)

    # Finite semantics emits spot::formula::strong_X, rendered as `X[!]`
    # by both the `repr` and 'spot' printer.
    res_fin = spot.tlsf_to_ltl(finite)
    tc.assertTrue(bool(res_fin.full_formula),
                  "tlsf_to_ltl returned a null formula")
    repr_str = repr(res_fin.full_formula)
    tc.assertIn('X[!]', repr_str,
                f"Finite semantics should preserve X[!] "
                f"as strong_X; got: {repr_str}")
    spot_str = res_fin.full_formula.to_str('spot')
    tc.assertIn('X[!]', spot_str,
                f"to_str('spot') should still emit X[!]; "
                f"got: {spot_str}")

    # Bus flattening on the four BusRef occurrences (ack[0], ack[1],
    # event[0], event[1]) yields index APs, recorded on the result
    # lists in first-use order.
    tc.assertEqual(list(res_fin.inputs), ["event_0", "event_1"])
    tc.assertEqual(list(res_fin.outputs), ["ack_0", "ack_1"])

    # Semantics modifier order follows SyFCo: either the player or
    # modifier may appear first.  This is a parser-only compatibility
    # check; the translator semantics checks below cover X[!].
    for semantics_text, expected_semantics in (
            ("Finite,Moore", spot.tlsf_semantics_MooreFinite),
            ("Moore,Finite", spot.tlsf_semantics_MooreFinite),
            ("Finite,Mealy", spot.tlsf_semantics_MealyFinite),
            ("Strict,Mealy", spot.tlsf_semantics_MealyStrict),
            ("Strict,Moore", spot.tlsf_semantics_MooreStrict)):
        ordered = parse_tlsf("INFO { SEMANTICS: " + semantics_text + " }\n"
                    "GLOBAL {} MAIN { OUTPUTS { done; } }\n")

        tc.assertFalse(ordered.errors,
                       f"{semantics_text} should parse cleanly; got: "
                       f"{[(e.first, e.second) for e in ordered.errors]}")
        tc.assertEqual(ordered.semantics, expected_semantics)

    # Non-finite semantics must reject strong next; finite preserves it
    # as strong_X.
    nonfinite = parse_tlsf("INFO { SEMANTICS: Mealy }\n"
                "GLOBAL {} MAIN { OUTPUTS { done; }\n"
                "  GUARANTEE { X[!] done; } }\n")

    tc.assertFalse(nonfinite.errors)
    nonfinite_errors = spot.parse_aut_error_list()
    nonfinite_result = spot.tlsf_to_ltl(
        nonfinite, spot.tlsf_translator_options(), nonfinite_errors)
    tc.assertFalse(bool(nonfinite_result.full_formula))
    tc.assertTrue(any("requires finite semantics" in e.second
                      for e in nonfinite_errors),
                  f"expected finite-semantics diagnostic; got: "
                  f"{[e.second for e in nonfinite_errors]}")

    # The `!`-marked stacked next and bounded operators (TLSF v1.2
    # SS4.8) accept the marker on either side of the brackets, print
    # as the trailing-`!` spelling whatever they were parsed from, and
    # lower to strong next.  The expected LTL is what syfco
    # -f ltlxba-fin prints for the same guarantee.
    for source, printed, expected in (
            ("X[!2] done", "X[2!] done", "X[!]X[!]done"),
            ("X[2!] done", "X[2!] done", "X[!]X[!]done"),
            ("X[!n] done", "X[n!] done", "X[!]X[!]X[!]done"),
            ("X[n!] done", "X[n!] done", "X[!]X[!]X[!]done"),
            ("F[!1:3] done", "F[1:3!] done",
             "X[!](done | X[!](done | X[!]done))"),
            ("F[1:3!] done", "F[1:3!] done",
             "X[!](done | X[!](done | X[!]done))"),
            ("G[!1:3] done", "G[1:3!] done",
             "X[!](done & X[!](done & X[!]done))"),
            ("G[1:3!] done", "G[1:3!] done",
             "X[!](done & X[!](done & X[!]done))"),
            ("F[!3:1] done", "F[3:1!] done", "1"),
    ):
        spec = parse_tlsf("INFO { SEMANTICS: Mealy,Finite }\n"
                          "GLOBAL { PARAMETERS { n = 3; } }\n"
                          "MAIN { OUTPUTS { done; }\n"
                          f"  GUARANTEE {{ {source}; }} }}\n")

        tc.assertFalse(spec.errors,
                       f"{source} should parse cleanly; got: "
                       f"{[(e.first, e.second) for e in spec.errors]}")

        # The canonical print picks the trailing-`!` spelling, and
        # re-printing the re-parsed form reproduces it byte for byte.
        ostr = spot.ostringstream()
        spot.tlsf_print(ostr, spec)
        canonical = ostr.str()
        tc.assertIn(printed, canonical,
                    f"{source} should print as `{printed}`; got: "
                    f"{canonical}")
        tc.assertFalse(parse_tlsf(canonical).errors,
                       f"`{printed}` should re-parse cleanly; got: "
                       f"{[(e.first, e.second) for e in spec.errors]}")
        ostr2 = spot.ostringstream()
        spot.tlsf_print(ostr2, parse_tlsf(canonical))
        tc.assertEqual(ostr2.str(), canonical,
                        f"printing `{source}` should be stable")

        res = spot.tlsf_to_ltl(spec)
        tc.assertTrue(bool(res.full_formula),
                      f"tlsf_to_ltl({source}) returned a null formula")
        tc.assertEqual(str(res.full_formula), expected,
                        f"{source} should lower to {expected}; got: "
                        f"{res.full_formula}")

    # Both markers at once, and a `!` that is not glued to its bracket,
    # are syntax errors -- and none of them may silently fall back to
    # the plain `[a:b]` reading.
    for bad in ("F[!1:3!] done", "G[!1:3!] done", "X[!2!] done",
                "F[!1:3", "X[!2", "F[1:3! ] done"):
        spec = parse_tlsf("INFO { SEMANTICS: Mealy,Finite }\n"
                          "GLOBAL {} MAIN { OUTPUTS { done; }\n"
                          f"  GUARANTEE {{ {bad}; }} }}\n")

        tc.assertTrue(spec.errors,
                      f"`{bad}` should be a syntax error")

    # The strong flavours need a finite run just like `X[!]` does.
    for bad in ("X[!2] done", "X[2!] done", "F[!1:3] done",
                "F[1:3!] done", "G[!1:3] done", "G[1:3!] done"):
        spec = parse_tlsf("INFO { SEMANTICS: Mealy }\n"
                          "GLOBAL {} MAIN { OUTPUTS { done; }\n"
                          f"  GUARANTEE {{ {bad}; }} }}\n")

        tc.assertFalse(spec.errors,
                       f"`{bad}` should parse cleanly; got: "
                       f"{[(e.first, e.second) for e in spec.errors]}")
        errs = spot.parse_aut_error_list()
        res = spot.tlsf_to_ltl(spec, spot.tlsf_translator_options(), errs)
        tc.assertFalse(bool(res.full_formula),
                       f"`{bad}` should not translate under Mealy")
        tc.assertTrue(any("requires finite semantics" in e.second
                          for e in errs),
                      f"`{bad}` should need finite semantics; got: "
                      f"{[e.second for e in errs]}")

    # Negative test for the dropped `X!` token: `X!done` parses as
    # `X (!done)` (weak next of NOT, not strong next).  Spot's default
    # printer renders this as `X!done` -- a textual coincidence, but a
    # useful confirmation that the operator is unchanged.
    weak = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  OUTPUTS { done; }\n"
            "  GUARANTEE { X! done; }\n"
            "}\n")

    tc.assertFalse(weak.errors,
                   f"X! should still parse as X(!...); "
                   f"errors: {[(e.first, e.second) for e in weak.errors]}")
    res_w = spot.tlsf_to_ltl(weak)
    tc.assertTrue(bool(res_w.full_formula),
                  "tlsf_to_ltl returned a null formula")
    repr_w = repr(res_w.full_formula)
    # Strong-next ('X[!]') must NOT appear in the result:
    # the dropped token rule means X!done is X(!done), not X[!]done.
    tc.assertNotIn('X[!]', repr_w,
                   f"X!done must not carry spot::formula::strong_X "
                   f"under the dropped-token rule; got: {repr_w}")
    tc.assertIn('done', repr_w,
                f"X!done should still encode 'done' inside the "
                f"formula; got: {repr_w}")

    # Test PARAMETERS end-to-end.  `event[N - 1]` makes the resolved
    # value of N participate directly in the bus index.  Translating
    # once with no override (declared N=2 -> event_1) and once with a
    # translate-time override (N=4 -> event_3) pins that declared
    # defaults come first, then opts.overrides on top.
    param = parse_tlsf(
            "INFO {\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 2; }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { event[N]; }\n"
            "  OUTPUTS { done[N]; }\n"
            "  GUARANTEE { event[N - 1]; }\n"
            "}\n")

    tc.assertFalse(param.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in param.errors]}")
    tc.assertEqual(list(param.inputs), ["event"])
    tc.assertEqual(list(param.outputs), ["done"])

    # Translate with no override: declared N=2 wins, so
    # `N - 1` resolves to 1 and the only emitted AP is event_1.
    res_decl = spot.tlsf_to_ltl(param)
    tc.assertTrue(bool(res_decl.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr_decl = str(res_decl.full_formula)
    tc.assertIn("event_1", fstr_decl,
                f"declared N=2 should produce 'event_1'; "
                f"got: {fstr_decl}")
    tc.assertNotIn("event_2", fstr_decl,
                   f"declared N=2 must NOT produce 'event_2'; "
                   f"got: {fstr_decl}")
    tc.assertNotIn("event_3", fstr_decl,
                   f"declared N=2 must NOT produce 'event_3'; "
                   f"got: {fstr_decl}")
    # The formula only mentions event_1, but the declared bus widths
    # (N=2) are registered eagerly, so both bits of each bus are
    # listed.
    tc.assertEqual(list(res_decl.inputs), ["event_0", "event_1"])
    tc.assertEqual(list(res_decl.outputs), ["done_0", "done_1"])

    # Translate with translate-time override {N: 4}: the override
    # wins over the declared default, so `N - 1` resolves to 3
    # and the only emitted AP is event_3.
    opts = spot.tlsf_translator_options()
    opts.overrides["N"] = 4
    res_ovr = spot.tlsf_to_ltl(param, opts)
    tc.assertTrue(bool(res_ovr.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr_ovr = str(res_ovr.full_formula)
    tc.assertIn("event_3", fstr_ovr,
                f"override N=4 should produce 'event_3'; "
                f"got: {fstr_ovr}")
    tc.assertNotIn("event_1", fstr_ovr,
                   f"override N=4 must NOT produce 'event_1'; "
                   f"got: {fstr_ovr}")
    tc.assertNotIn("event_2", fstr_ovr,
                   f"override N=4 must NOT produce 'event_2' in the "
                   f"formula; got: {fstr_ovr}")
    # The override widens the declared buses to 4 bits; eager
    # registration lists the whole declared range even though the
    # formula only uses event_3.
    tc.assertEqual(list(res_ovr.inputs),
                   ["event_0", "event_1", "event_2", "event_3"])
    tc.assertEqual(list(res_ovr.outputs),
                   ["done_0", "done_1", "done_2", "done_3"])

    # Test that parser-time overrides are mirrored onto
    # parsed_tlsf::overrides.  The spec body is intentionally simple
    # so the only thing under test is the override mirror.
    p_opts = spot.tlsf_parser_options()
    p_opts.overrides["N"] = 7
    parsed7 = parse_tlsf(
            "INFO {\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS {}\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { go; }\n"
            "  OUTPUTS { ack; }\n"
            "  GUARANTEE { go -> F ack; }\n"
            "}\n", p_opts)
    tc.assertFalse(parsed7.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in parsed7.errors]}")
    # Pin the parser-time override mirror.
    # Use subscript (not .get()) because SWIG's std::map<string,int>
    # proxy exposes __getitem__ and __iter__ but not the .get method.
    tc.assertEqual(parsed7.overrides["N"], 7,
                   f"expected N=7 in parsed.overrides; got: "
                   f"{parsed7.overrides['N']}")
    # Defense-in-depth: keys are exactly what the caller passed.
    keys = list(parsed7.overrides)
    tc.assertEqual(keys, ["N"],
                   f"expected keys=['N']; got: {keys}")

    # Test comparison-chain ranges and nested quantifier ranges.
    # The outer range binds i and the inner range binds j.
    ranges = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 3;\n"
            "    M = 2;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a[5]; }\n"
            "  GUARANTEE {\n"
            "    &&[0 <= i < N] (||[1 <= j <= M] a[i + j]);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(ranges.errors,
                   f"comparison-chain ranges must parse cleanly; "
                   f"errors: {[(e.first, e.second) for e in ranges.errors]}")
    range_result = spot.tlsf_to_ltl(ranges)
    tc.assertTrue(bool(range_result.full_formula),
                  "nested comparison-chain ranges must translate")
    range_text = str(range_result.full_formula)
    for index in (1, 2, 3, 4):
        tc.assertIn(f"a_{index}", range_text,
                    f"nested range should emit a_{index}; got: "
                    f"{range_text}")
    tc.assertEqual(set(range_result.inputs),
                   # a_0 is never used in the formula, but the
                   # declared width (5) is registered eagerly.
                   {"a_0", "a_1", "a_2", "a_3", "a_4"})

    # Test arithmetic PARAMETERS: expression parsing, recursive
    # parameter lookup, and the same evaluator in both bus-size and
    # quantifier contexts.
    arithmetic = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    A = 2 + 1;\n"
            "    B = A * 2;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { b[B]; }\n"
            "  GUARANTEE { &&[0 <= k < B] b[k]; }\n"
            "}\n")

    tc.assertFalse(arithmetic.errors,
                   f"arithmetic parameters must parse cleanly; "
                   f"errors: {[(e.first, e.second) for e in arithmetic.errors]}"
                   )
    arithmetic_result = spot.tlsf_to_ltl(arithmetic)
    tc.assertTrue(bool(arithmetic_result.full_formula),
                  "arithmetic parameters must translate")
    tc.assertEqual(set(arithmetic_result.inputs),
                   {"b_0", "b_1", "b_2", "b_3", "b_4", "b_5"})

    # Test that parser-time overrides flow into translation, where the
    # translation-time value remains the more specific override.
    parser_options = spot.tlsf_parser_options()
    parser_options.overrides["N"] = 4
    # Test that the parser override is not treated as a declaration.
    parsed_override = parse_tlsf(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN { INPUTS { a[8]; }\n"
            "  GUARANTEE { &&[0 <= i < N] a[i]; } }\n", parser_options)
    tc.assertFalse(parsed_override.errors)
    parser_result = spot.tlsf_to_ltl(parsed_override)
    # a[8] is declared eagerly even though the formula only uses
    # a_0..a_3.
    tc.assertEqual(set(parser_result.inputs),
                   {f"a_{i}" for i in range(8)})
    translator_options = spot.tlsf_translator_options()
    translator_options.overrides["N"] = 2
    translator_result = spot.tlsf_to_ltl(parsed_override, translator_options)
    tc.assertEqual(set(translator_result.inputs),
                   {f"a_{i}" for i in range(8)})

    # Test DEFINITIONS expansion: with `Gplus(x) = G x`, calls are
    # expanded structurally so `Gplus(a)` and `Gplus(b)` translate to
    # G(a) and G(b).
    deftest = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    Gplus(x) = G x;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; b; }\n"
            "  GUARANTEE { Gplus(a) && Gplus(b); }\n"
            "}\n")

    tc.assertFalse(deftest.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in deftest.errors]}")
    res_d = spot.tlsf_to_ltl(deftest)
    tc.assertTrue(bool(res_d.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr_d = str(res_d.full_formula)
    tc.assertIn("G", fstr_d,
                f"expected G operator after expansion; got: {fstr_d}")
    tc.assertIn("a", fstr_d,
                f"expected AP 'a' after expansion; got: {fstr_d}")
    tc.assertIn("b", fstr_d,
                f"expected AP 'b' after expansion; got: {fstr_d}")
    # Expansion should not emit diagnostics.
    tc.assertFalse(deftest.errors,
                   f"errors after expansion: "
                   f"{[(e.first, e.second) for e in deftest.errors]}")

    # Negative test: two definitions with the same name (here `Both`,
    # one unary and one binary) violate "one symbol = one definition"
    # and are rejected with two diagnostics: "shadowed" at the FIRST
    # location and "already defined" at the SECOND.
    arity = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            # Both(x, y): definition formal parameters are
            # comma-separated.
            '    Both(x) = G x;\n'
            '    Both(x, y) = G x && y;\n'
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; b; c; }\n"
            "  OUTPUTS { ok; }\n"
            "  GUARANTEE { G a; }\n"
            "}\n")
    tc.assertTrue(arity.errors,
                  f"parse_tlsf should reject same-name "
                  f"DEFINITIONS with a diagnostic; got none")
    err_strs = [e.second for e in arity.errors]
    # Exactly two diagnostics are expected, but the count is not pinned
    # here: grammar recovery rules could add extra "syntax error"
    # entries on future regressions.
    tc.assertTrue(any("already defined" in s for s in err_strs),
                  f"expected an 'already defined' diagnostic at "
                  f"the second definition's location; got: {err_strs}")
    tc.assertTrue(any("shadowed" in s for s in err_strs),
                  f"expected a 'shadowed' diagnostic at the first "
                  f"definition's location; got: {err_strs}")

    # Negative test: a translator-side arity mismatch.  `Bar(x)` is
    # unique so the spec parses cleanly, but the call `Bar(a, b)`
    # supplies the wrong number of arguments, so translation yields a
    # null formula and a diagnostic.
    mismatch = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            '    Bar(x) = G x;\n'
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; b; }\n"
            "  GUARANTEE { Bar(a, b); }\n"
            "}\n")

    tc.assertFalse(mismatch.errors,
                   f"unique-name spec should parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in mismatch.errors]}")
    translation_errors = spot.parse_aut_error_list()
    res_m = spot.tlsf_to_ltl(mismatch, spot.tlsf_translator_options(),
                             translation_errors)
    tc.assertFalse(bool(res_m.full_formula),
                   f"arity-mismatch call should yield a null "
                   f"formula (translator sets failed_ on the "
                   f"arity-mismatch diagnostic); got formula: "
                   f"{res_m.full_formula}")
    tc.assertTrue(any("expects 1 argument" in e.second
                    for e in translation_errors),
                  f"translator diagnostic must be returned through "
                  f"errors_out; got: "
                  f"{[e.second for e in translation_errors]}")

    # Bus validation: indexed references must resolve to declared,
    # positive-sized buses and stay inside their evaluated bounds.
    valid_bus = parse_tlsf(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { a[0] && a[0] && a[N - 1]; }\n"
            "}\n")

    tc.assertFalse(valid_bus.errors)
    valid_bus_errors = spot.parse_aut_error_list()
    valid_bus_result = spot.tlsf_to_ltl(
        valid_bus, spot.tlsf_translator_options(), valid_bus_errors)
    tc.assertTrue(bool(valid_bus_result.full_formula))
    # `scalar` is declared but unused; eager registration (fixture
    # 23) lists it after the bus bits.
    tc.assertEqual(list(valid_bus_result.inputs),
                   ["a_0", "a_1", "scalar"])
    tc.assertFalse(valid_bus_errors)

    invalid_index = parse_tlsf(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { a[N]; }\n"
            "}\n")

    tc.assertFalse(invalid_index.errors)
    invalid_index_errors = spot.parse_aut_error_list()
    invalid_index_result = spot.tlsf_to_ltl(
        invalid_index, spot.tlsf_translator_options(), invalid_index_errors)
    tc.assertFalse(bool(invalid_index_result.full_formula))
    tc.assertTrue(any("outside bus 'a'" in e.second
                      for e in invalid_index_errors),
                  f"expected out-of-range diagnostic; got: "
                  f"{[e.second for e in invalid_index_errors]}")

    scalar_index = parse_tlsf(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { scalar[0]; }\n"
            "}\n")

    tc.assertFalse(scalar_index.errors)
    scalar_index_errors = spot.parse_aut_error_list()
    scalar_index_result = spot.tlsf_to_ltl(
        scalar_index, spot.tlsf_translator_options(), scalar_index_errors)
    tc.assertFalse(bool(scalar_index_result.full_formula))
    tc.assertTrue(any("scalar AP 'scalar'" in e.second
                      for e in scalar_index_errors),
                  f"expected scalar-index diagnostic; got: "
                  f"{[e.second for e in scalar_index_errors]}")

    negative_index = parse_tlsf(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; }\n"
            "  GUARANTEE { a[N - 3]; }\n"
            "}\n")

    tc.assertFalse(negative_index.errors)
    negative_index_errors = spot.parse_aut_error_list()
    negative_index_result = spot.tlsf_to_ltl(
        negative_index, spot.tlsf_translator_options(), negative_index_errors)
    tc.assertFalse(bool(negative_index_result.full_formula))
    tc.assertTrue(any("outside bus 'a'" in e.second
                      for e in negative_index_errors),
                  f"expected negative-index diagnostic; got: "
                  f"{[e.second for e in negative_index_errors]}")

    # Round-trip regression for chomp.tlsf (embedded above): clean
    # parse, canonical print, clean re-parse, idempotent deparse.
    # chomp.tlsf omits the trailing `;` on INFO items; a `;` after
    # any INFO item is a syntax error (the TLSF grammar treats `;`
    # as optional there).
    parsed_chomp = parse_tlsf(chomp_contents)

    errs_chomp = list(parsed_chomp.errors)
    tc.assertFalse(
        errs_chomp,
        f'chomp.tlsf should parse cleanly (0 errors); got '
        f'{len(errs_chomp)}: '
        f'{[(e.first, e.second) for e in errs_chomp]!r}.  '
        f'If a future regression introduces parse errors '
        f'(e.g., a grammar change rejecting a previously-'
        f'accepted construct), this assertion surfaces the '
        f'divergence and the deparser/grammar contract needs '
        f'investigation.')

    # Round-trip: deparse to the canonical form, re-parse, then
    # deparse again; the two canonical forms must be byte-identical.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_chomp)
    canonical = ostr.str()
    # Structural pins: section skeletons always appear in the
    # canonical form (comments and blank lines are not preserved).
    tc.assertIn('INFO {', canonical)
    tc.assertIn('GLOBAL {', canonical)
    tc.assertIn('MAIN {', canonical)
    tc.assertIn('PARAMETERS {', canonical)
    tc.assertIn('DEFINITIONS {', canonical)
    tc.assertIn('INPUTS {', canonical)
    tc.assertIn('OUTPUTS {', canonical)
    tc.assertIn('PRESET {', canonical)
    tc.assertIn('REQUIRE {', canonical)
    tc.assertIn('ASSERT {', canonical)
    tc.assertIn('GUARANTEE {', canonical)
    parsed_rt = parse_tlsf(canonical)

    errs_rt = list(parsed_rt.errors)
    tc.assertFalse(
        errs_rt,
        f'chomp.tlsf round-trip (parse+deparse+reparse) should '
        f'produce 0 errors; got {len(errs_rt)}: '
        f'{[(e.first, e.second) for e in errs_rt]!r}.  A '
        f'non-zero error count means the deparser emitted a '
        f'form the parser cannot ingest -- a deparser/'
        f'grammar divergence this fixture must catch.')
    # Idempotence: a second deparse must produce the same canonical
    # form.
    ostr2 = spot.ostringstream()
    spot.tlsf_print(ostr2, parsed_rt)
    canonical2 = ostr2.str()
    tc.assertEqual(
        canonical2, canonical,
        f'chomp.tlsf deparse-on-deparse must be idempotent; '
        f'first canonical:\n{canonical!r}\n\n'
        f'second canonical:\n{canonical2!r}')

    # Benchmark translation smoke checks.  These fixtures use the
    # comparison-chain, nested-range, arithmetic-size, and finite
    # strong-next features exercised above in realistic definitions.
    # All three benchmarks are embedded above (chomp_contents,
    # tictactoe_contents, scutella1_contents) so the checks run
    # everywhere, without depending on files living outside the
    # source tree.
    benchmark_sources = [(chomp_contents, 'chomp.tlsf'),
                         (tictactoe_contents, 'tictactoe.tlsf'),
                         (scutella1_contents, 'scutella1.tlsf')]
    for benchmark_source, benchmark_name in benchmark_sources:
        benchmark = parse_tlsf(benchmark_source)
        tc.assertFalse(list(benchmark.errors),
                       f"{benchmark_name} must parse cleanly; got: "
                       f"{[(e.first, e.second) for e in benchmark.errors]}")
        benchmark_errors = spot.parse_aut_error_list()
        benchmark_result = spot.tlsf_to_ltl(
            benchmark, spot.tlsf_translator_options(), benchmark_errors)
        tc.assertTrue(bool(benchmark_result.full_formula),
                      f"{benchmark_name} native translation failed")
        tc.assertFalse(list(benchmark_errors),
                       f"{benchmark_name} translation produced errors: "
                       f"{[(e.first, e.second) for e in benchmark_errors]}")

    # Test support for the INFO TAGS line: a comma-separated
    # IDENTIFIER list, mirrored on parsed.tags, kept through
    # round-trips, and optional (absent -> empty list).
    tagged = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"with tags\"\n"
            "  DESCRIPTION: \"fixture 12: TAGS keyword pin\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "  TAGS:        arbiter, synth\n"
            "}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS  { request; }\n"
            "  OUTPUTS { grant; }\n"
            "  GUARANTEE { G(!request || F grant); }\n"
            "}\n")

    tc.assertFalse(tagged.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in tagged.errors]}")
    tc.assertEqual(list(tagged.tags), ["arbiter", "synth"],
                   f"expected tags ['arbiter','synth']; got: "
                   f"{list(tagged.tags)}")
    # `parsed.ast` is not exposed (the tags are mirrored onto
    # `parsed.tags`); deparse + reparse must round-trip the
    # comma-separated list without new diagnostics.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, tagged)
    can_tags = ostr.str()
    tc.assertIn("TAGS:", can_tags,
                f"deparser should emit TAGS: line; got: {can_tags}")
    tagged2 = parse_tlsf(can_tags)

    tc.assertFalse(tagged2.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in tagged2.errors]}")
    tc.assertEqual(list(tagged2.tags), list(tagged.tags),
                   f"round-tripped tags should match source; "
                   f"got: {list(tagged2.tags)}")
    # TAGS is optional: a spec with no TAGS line yields the empty list.
    untagged = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"untagged\"\n"
            "  DESCRIPTION: \"fixture 12 neg: TAGS omitted\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  GUARANTEE { G p; }\n"
            "}\n")

    tc.assertFalse(untagged.errors,
                   f"TAGS omission must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in untagged.errors]}")
    tc.assertEqual(list(untagged.tags), [])

    # An entry of a TAGS list is an identifier and nothing else: syfco
    # reads each one with a raw identifier parser, so a tag may be
    # spelled like any word of the language, and even like the key that
    # follows the list.  The list is scanned in a state of its own in
    # which no keyword is recognized.
    words = ["G", "U", "AND", "true", "MAIN", "TAGS", "Mealy", "o'biter"]
    wtagged = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"word tags\"\n"
            "  DESCRIPTION: \"fixture 12: TAGS is a list of identifiers\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "  TAGS:        " + ", ".join(words) + "\n"
            "}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G p; }\n"
            "}\n")

    tc.assertFalse(wtagged.errors,
                   f"tags named after words must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in wtagged.errors]}")
    tc.assertEqual(list(wtagged.tags), words,
                   f"expected tags {words}; got: {list(wtagged.tags)}")
    # The deparser has to emit them, and re-parsing what it emits must
    # give the same list back: the canonical print is the only way a
    # word-shaped tag is observable.
    wostr = spot.ostringstream()
    spot.tlsf_print(wostr, wtagged)
    can_words = wostr.str()
    tc.assertIn("TAGS:        " + ", ".join(words) + "\n", can_words,
                f"word-shaped tags must round-trip; got: {can_words}")
    wtagged2 = parse_tlsf(can_words)

    tc.assertFalse(wtagged2.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in wtagged2.errors]}")
    tc.assertEqual(list(wtagged2.tags), words,
                   f"round-tripped tags should match source; "
                   f"got: {list(wtagged2.tags)}")
    # A tag names nothing that the translation looks at, so the
    # LTL formula must not depend on the list at all.
    tc.assertEqual(str(spot.tlsf_to_ltl(wtagged).full_formula),
                   str(spot.tlsf_to_ltl(untagged).full_formula),
                   f"the tag list must not reach the translation; got: "
                   f"{spot.tlsf_to_ltl(wtagged).full_formula}")
    # syfco's list is built with `commaSep`, which takes no element at
    # all, so a bare `TAGS:` is valid and yields no tag.
    etagged = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"empty tags\"\n"
            "  DESCRIPTION: \"fixture 12: an empty TAGS list\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "  TAGS:\n"
            "}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G p; }\n"
            "}\n")

    tc.assertFalse(etagged.errors,
                   f"an empty TAGS list must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in etagged.errors]}")
    tc.assertEqual(list(etagged.tags), [],
                   f"an empty TAGS list must yield no tag; "
                   f"got: {list(etagged.tags)}")

    # Test support for the plural MAIN keywords (REQUIREMENTS,
    # INVARIANTS, GUARANTEES, ASSUMPTIONS): each alias fills the same
    # body vector as its singular counterpart.
    plurals = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"plurals\"\n"
            "  DESCRIPTION: \"fixture 13: plural MAIN keywords\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 2; }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; b; }\n"
            "  OUTPUTS { ok; }\n"
            # ASSUME + ASSUMPTIONS.
            "  ASSUME {\n"
            "    G(!a);\n"
            "  }\n"
            "  ASSUMPTIONS {\n"
            "    b;\n"
            "  }\n"
            # REQUIREMENTS > REQUIRE.
            "  REQUIREMENTS {\n"
            "    G(a -> F b);\n"
            "  }\n"
            # INVARIANTS > ASSERT.
            "  INVARIANTS {\n"
            "    G(ok || !ok);\n"
            "  }\n"
            # GUARANTEES > GUARANTEE.
            "  GUARANTEES {\n"
            "    G(b -> F ok);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(plurals.errors,
                   f"plural MAIN keywords must parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in plurals.errors]}")
    # The aliases funnel into the same MAIN sections; the body
    # shapes are read back from the canonical print.
    plurals_canon = spot.ostringstream()
    spot.tlsf_print(plurals_canon, plurals)
    plurals_text = plurals_canon.str()
    tc.assertEqual(len(formulas_in_section(plurals_text, 'ASSUME')), 2,
                   "expected 2 formulas in ASSUME "
                   "(one from ASSUMPTIONS)")
    tc.assertEqual(len(formulas_in_section(plurals_text, 'REQUIRE')), 1,
                   "expected 1 formula in REQUIRE (from REQUIREMENTS)")
    tc.assertEqual(len(formulas_in_section(plurals_text, 'ASSERT')), 1,
                   "expected 1 formula in ASSERT (from INVARIANTS)")
    tc.assertEqual(len(formulas_in_section(plurals_text,
                                           'GUARANTEE')), 1,
                   "expected 1 formula in GUARANTEE (from GUARANTEES)")
    # Mixed singular + plural keywords for the same body type funnel
    # into the same vector.
    mixed = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"mixed sing/pl\"\n"
            "  DESCRIPTION: \"fixture 13: mixed singulars+plurals\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  ASSERT {\n"
            "    G(a);\n"
            "  }\n"
            "  INVARIANTS {\n"
            "    G(b);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(mixed.errors,
                   f"mixed singular/plural MUST parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in mixed.errors]}")
    mixed_canon = spot.ostringstream()
    spot.tlsf_print(mixed_canon, mixed)
    tc.assertEqual(len(formulas_in_section(mixed_canon.str(), 'ASSERT')),
                   2,
                   "expected 2 formulas in ASSERT "
                   "(ASSERT + INVARIANTS)")

    # Negative test: an un-braced quantifier range `&&[lo..hi]` is NOT
    # valid TLSF.  A parser recovery rule swallows the bad bound, resumes
    # parsing on the body, and diagnoses the binder list; every head has
    # such a rule, and its message names no particular mistake.
    qrange = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"quant range\"\n"
            "  DESCRIPTION: \"fixture 14: &&[lo..hi] rejected\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 4; }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; }\n"
            "  OUTPUTS { ok; }\n"
            "  GUARANTEE {\n"
            "    &&[1..5] a;\n"
            "    ||[0..3] a;\n"
            "  }\n"
            "}\n")

    # Each bad list yields Bison's own syntax error and the recovery
    # rule's diagnostic: 4 entries for 2 lists.
    tc.assertEqual(len(list(qrange.errors)), 4,
                   f"un-braced quantifier ranges must yield exactly "
                   f"2 diagnostics; errors: "
                   f"{[(e.first, e.second) for e in qrange.errors]}")
    msgs = [e.second for e in qrange.errors]
    tc.assertEqual(sum('malformed binder list' in m for m in msgs), 2,
                   f"both bad lists must be recovered by the head's rule; "
                   f"errors: {msgs}")

    # Positive cross-check: a braced set literal and a braced range are
    # valid set expressions, so they parse as such.  Using one as a
    # *bound* is a separate matter, covered below: here they are named by
    # set-valued parameters and consumed by membership bounds.
    set_explicit = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    p = {1, 2, 3};\n"
            "    q = {1..5};\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; }\n"
            "  GUARANTEE { && [i IN p] a; && [j IN q] a; }\n"
            "}\n")

    tc.assertFalse(set_explicit.errors,
                   f"braced set bounds (regression pin) must stay "
                   f"clean; got: "
                   f"{[(e.first, e.second) for e in set_explicit.errors]}")

    # Negative test: TLSF v1.2 SS4.7-4.8 gives a binder one of two
    # shapes, `id IN set` and the range `lo <= i < N`, so a bound
    # without an iteration variable is a syntax error rather than
    # something diagnosed later: set literals, un-braced ranges, the
    # infix set algebra, empty sets, and bare counts are all rejected
    # while parsing.  The bracket spellings `CUP[`/`CAP[`/`SETMINUS[` are
    # big operators taking a binder list, so the set algebra appears
    # here in its infix form.
    set_cases = [
        "&&[{0, 2, 4}] a[i];",
        "&&[{1..3}] a[i];",
        "&&[{0} CUP {2, 4}] a[i];",
        "&&[{0, 2} CAP {2, 4}] a[i];",
        "&&[{0, 2, 4} SETMINUS {2}] a[i];",
        "&&[3] a[i];",
        "&&[i > 0] a[i];",
        "&&[i == 0] a[i];",
    ]
    for set_body in set_cases:
        set_case = parse_tlsf("INFO {}\n"
                    "GLOBAL {}\n"
                    "MAIN { INPUTS { a[5]; }\n"
                    "  GUARANTEE { " + set_body + " } }\n")

        messages = [e.second for e in set_case.errors]
        tc.assertTrue(
            any("invalid binder; a binder must have the form" in message
                for message in messages),
            f"missing binder diagnostic for {set_body}; got: {messages}")

    # An empty set is no different: it parses as a real SetExplicit node
    # but names no iteration variable, so the binder is rejected.
    empty_set = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN { INPUTS { a; }\n"
                "  GUARANTEE { &&[{}] a; ||[{}] a; } }\n")

    empty_set_messages = [e.second for e in empty_set.errors]
    tc.assertTrue(
        any("invalid binder; a binder must have the form" in message
            for message in empty_set_messages),
        f"missing binder diagnostic for empty sets; got: "
        f"{empty_set_messages}")

    # A binder list that does not parse is reported by the head's own
    # recovery rule, one diagnostic per list, and names no particular
    # mistake.  Every head has one, including the big operators.
    for head in ("&&", "||", "AND", "OR", "FORALL", "EXISTS", "CUP", "CAP",
                 "SETMINUS", "(+)", "(*)", "(-)", "SUM", "+", "PROD", "*"):
        bad_list = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN { INPUTS { a; }\n"
                    "  GUARANTEE { " + head + "[0..2] a; } }\n")
        messages = [e.second for e in bad_list.errors]
        tc.assertTrue(any("malformed binder list" in message
                          for message in messages),
                      f"missing recovery diagnostic for {head}[0..2]; "
                      f"got: {messages}")

    # Only the shape is checked while parsing.  A well shaped range whose
    # ends are not integers is a translation diagnostic instead, so a set
    # literal in a range still reaches eval_int.
    bad_end = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN { INPUTS { a[5]; }\n"
                         "  GUARANTEE { &&[{0} <= i < 3] a; } }\n")
    tc.assertFalse(bad_end.errors,
                   f"a range with a non-integer end must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in bad_end.errors]}")
    bad_end_errors = spot.parse_aut_error_list()
    bad_end_result = spot.tlsf_to_ltl(
        bad_end, spot.tlsf_translator_options(), bad_end_errors)
    tc.assertFalse(bool(bad_end_result.full_formula),
                   "a range whose end is a set must be diagnosed")
    tc.assertTrue(any("set is not an integer expression" in e.second
                      for e in bad_end_errors),
                  f"missing non-integer diagnostic; got: "
                  f"{[e.second for e in bad_end_errors]}")

    # Membership bounds DO carry an explicit variable and must
    # translate.  The set on the right may be a literal, a range, or a
    # set-algebra combination; the body is expanded over its elements
    # in set order.
    membership = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN {\n"
                "  INPUTS { a[5]; b[3]; }\n"
                "  GUARANTEE {\n"
                "    &&[i IN {0, 2, 4}] a[i];\n"
                "    ||[j IN {1..2}] b[j];\n"
                "    &&[k IN {0} CUP {3}] a[k];\n"
                "  }\n}\n")

    tc.assertFalse(membership.errors,
                   f"membership must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in membership.errors]}")
    membership_result = spot.tlsf_to_ltl(membership)
    tc.assertTrue(bool(membership_result.full_formula),
                  "membership-bound quantifiers must translate")
    membership_text = str(membership_result.full_formula)
    for index in (0, 2, 4):
        tc.assertIn(f"a_{index}", membership_text,
                    f"membership && should emit a_{index}; got: "
                    f"{membership_text}")
    for index in (1, 2):
        tc.assertIn(f"b_{index}", membership_text,
                    f"membership || should emit b_{index}; got: "
                    f"{membership_text}")
    # Declared widths (a[5], b[3]) are registered eagerly even where
    # the formula skips an index.
    tc.assertEqual(set(membership_result.inputs),
                   {f"a_{i}" for i in range(5)}
                   | {f"b_{i}" for i in range(3)})
    # A membership bound must round-trip through the deparser.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, membership)
    membership_canonical = ostr.str()
    tc.assertIn("&&[i IN {0, 2, 4}] a[i]", membership_canonical,
                f"membership bound must stay printable; got: "
                f"{membership_canonical}")
    membership_rt = parse_tlsf(membership_canonical)

    tc.assertFalse(membership_rt.errors,
                   f"membership canonical form must reparse cleanly; got: "
                   f"{[(e.first, e.second) for e in membership_rt.errors]}")

    # A count bound (`&&[3]`) is variable-less too, and is rejected even
    # when the body mentions `i`: naming `i` in the body does not turn
    # the bound into one.
    count_bound = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN {\n"
                "  GUARANTEE {\n"
                "    &&[3] (i IN {0, 2});\n"
                "    ||[3] (i IN {0, 2});\n"
                "  }\n}\n")

    count_messages = [e.second for e in count_bound.errors]
    tc.assertTrue(
        any("invalid binder; a binder must have the form" in message
            for message in count_messages),
        f"missing binder diagnostic for count bounds; got: "
        f"{count_messages}")

    # Printer round-trip for the set algebra.  It is normalized to the
    # canonical binary spelling because the AST stores set algebra as
    # BinaryOp nodes.  The head takes a binder list, so the algebra
    # appears on the right of an `IN` inside it.
    set_operator_case = parse_tlsf("INFO {}\nGLOBAL {}\nMAIN {\n"
                                   "  INPUTS { a[5]; }\n"
                                   "  GUARANTEE {\n"
                                   "    SUM[i IN {0} CUP {2, 4}] i == 6;\n"
                                   "  }\n}\n")
    tc.assertFalse(set_operator_case.errors,
                   f"set algebra in a membership bound must parse cleanly; "
                   f"got: "
                   f"{[(e.first, e.second) for e in set_operator_case.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, set_operator_case)
    set_canonical = ostr.str()
    tc.assertIn(" CUP ", set_canonical,
                f"set algebra must remain printable; got: {set_canonical}")
    set_roundtrip = parse_tlsf(set_canonical)

    tc.assertFalse(set_roundtrip.errors,
                   f"set canonical form must reparse cleanly; got: "
                   f"{[(e.first, e.second) for e in set_roundtrip.errors]}")

    # Test textual operator aliases (PLUS, MUL, DIV, MOD, MINUS,
    # LE/LEQ/GE/GEQ, NOT, IMPLIES, EQUIV): they lower to the same
    # AST operators as punctuation and work in integer, comparison,
    # and quantifier-chain contexts.
    aliases = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 1;\n"
            "    p_plus = N PLUS 1;\n"
            "    p_mul = p_plus MUL 2;\n"
            "    p_div = p_mul DIV 2;\n"
            "    p_mod = p_div MOD 2;\n"
            "    p_minus = p_plus MINUS 1;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a[p_plus]; b[p_minus]; }\n"
            "  GUARANTEE {\n"
            "    NOT a[0] OR (a[0] AND a[1]);\n"
            "    FORALL[0 <= i LE 1] a[i];\n"
            "    EXISTS[0 LEQ i LEQ 1] a[i];\n"
            "    OR[0 <= i <= 1] a[i];\n"
            "    AND[1 LEQ i LEQ 1] a[i];\n"
            "    a[1 EQ 1];\n"
            "    a[1 NEQ 2];\n"
            "    a[1 GE 0];\n"
            "    a[1 GEQ 1];\n"
            "    a[0] IMPLIES a[1];\n"
            "    a[0] EQUIV a[1];\n"
            "    G(b[0]);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(aliases.errors,
                   f"textual aliases must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in aliases.errors]}")
    alias_errors = spot.parse_aut_error_list()
    alias_result = spot.tlsf_to_ltl(
        aliases, spot.tlsf_translator_options(), alias_errors)
    tc.assertTrue(bool(alias_result.full_formula),
                  f"textual aliases must translate; got: "
                  f"{[e.second for e in alias_errors]}")
    tc.assertFalse(alias_errors,
                   f"textual aliases must translate cleanly; got: "
                   f"{[e.second for e in alias_errors]}")
    tc.assertEqual(list(alias_result.inputs), ["a_0", "a_1", "b_0"],
                   f"textual arithmetic aliases must work in bus sizes; "
                   f"got: {list(alias_result.inputs)}")
    alias_print = spot.ostringstream()
    spot.tlsf_print(alias_print, aliases)
    tc.assertIn("a[0] -> a[1]", alias_print.str(),
                "printer must canonicalize IMPLIES")
    tc.assertNotIn(" IMPLIES ", alias_print.str(),
                   "printer must not preserve textual aliases")
    # Negative tests: integer overflow and invalid arithmetic must
    # diagnose instead of relying on signed-overflow wrap-around.
    overflow = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 9223372036854775807;\n"
            "    p_add = N + 1;\n"
            "    p_mul = N * 2;\n"
            "    p_div = (0 - N - 1) / (0 - 1);\n"
            "    p_zero = N / (N - N);\n"
            "    p_modzero = N % (N - N);\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a[2]; }\n"
            "  GUARANTEE {\n"
            "    G(a[0]);\n"
            "    a[SUM(N, 1)];\n"
            "    a[PROD(N, 2)];\n"
            "  }\n"
            "}\n")

    tc.assertFalse(overflow.errors,
                   f"overflow fixture must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in overflow.errors]}")
    overflow_errors = spot.parse_aut_error_list()
    overflow_result = spot.tlsf_to_ltl(
        overflow, spot.tlsf_translator_options(), overflow_errors)
    tc.assertFalse(bool(overflow_result.full_formula),
                   "invalid integer arithmetic must null the formula")
    overflow_messages = [e.second for e in overflow_errors]
    tc.assertTrue(any("integer overflow in addition" in message
                      for message in overflow_messages),
                  f"missing addition overflow diagnostic: "
                  f"{overflow_messages}")
    tc.assertTrue(any("integer overflow in multiplication" in message
                      for message in overflow_messages),
                  f"missing multiplication overflow diagnostic: "
                  f"{overflow_messages}")
    tc.assertTrue(any("integer overflow in SUM" in message
                      for message in overflow_messages),
                  f"missing SUM overflow diagnostic: {overflow_messages}")
    tc.assertTrue(any("integer overflow in PROD" in message
                      for message in overflow_messages),
                  f"missing PROD overflow diagnostic: {overflow_messages}")
    tc.assertTrue(any("division by zero" in message
                      for message in overflow_messages),
                  f"missing division-by-zero diagnostic: "
                  f"{overflow_messages}")
    tc.assertTrue(any("modulo by zero" in message
                      for message in overflow_messages),
                  f"missing modulo-by-zero diagnostic: "
                  f"{overflow_messages}")
    tc.assertTrue(any("integer overflow in division" in message
                      for message in overflow_messages),
                  f"missing minimum/-1 division diagnostic: "
                  f"{overflow_messages}")

    # Bus sizes and parameter values are parsed ASTs: user
    # parentheses survive the print -> reparse round-trip, and the
    # evaluation honors them.  With N=4, M=2 the size (N+1)*M is 10,
    # while the left-associative misprint N+1*M would be 6.
    grouped = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 4;\n"
            "    M = 2;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a[(N+1)*M]; }\n"
            "  OUTPUTS { z; }\n"
            "  GUARANTEE { G(z -> a[9]); }\n"
            "}\n")

    tc.assertFalse(grouped.errors,
                   f"grouped bus size must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in grouped.errors]}")
    grouped_print = spot.ostringstream()
    spot.tlsf_print(grouped_print, grouped)
    tc.assertIn("a[(N + 1) * M];", grouped_print.str(),
                "printer must keep user parentheses in bus sizes; "
                f"got: {grouped_print.str()}")
    tc.assertIn("N = 4;", grouped_print.str())
    grouped_result = spot.tlsf_to_ltl(grouped)
    tc.assertTrue(bool(grouped_result.full_formula),
                  "grouped bus size must translate")
    tc.assertEqual(set(grouped_result.inputs),
                   {f"a_{i}" for i in range(10)},
                   f"(N+1)*M must expand to 10 APs; got: "
                   f"{list(grouped_result.inputs)}")
    # The canonical form re-parses and re-prints identically.
    grouped_rt = parse_tlsf(grouped_print.str())

    tc.assertFalse(grouped_rt.errors)
    grouped_rt_print = spot.ostringstream()
    spot.tlsf_print(grouped_rt_print, grouped_rt)
    tc.assertEqual(grouped_rt_print.str(), grouped_print.str(),
                   "grouped bus size round-trip must be stable")

    # Literals that do not fit in a signed 64-bit integer must be
    # diagnosed at parse time, not silently truncated to 0.
    too_big = parse_tlsf(
            "INFO {}\n"
            "MAIN {\n"
            "  INPUTS { a[2]; }\n"
            "  GUARANTEE {\n"
            "    a[999999999999999999999999999];\n"
            "  }\n"
            "}\n")

    too_big_messages = [e.second for e in too_big.errors]
    tc.assertTrue(any("integer literal is too large" in message
                      for message in too_big_messages),
                  f"missing too-large literal diagnostic: "
                  f"{too_big_messages}")

    # Test support for `@` and `'` in identifiers: `@` may lead an
    # identifier (`@event`); `'` may appear inside (`ack'0`).
    weird = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"weird ids\"\n"
            "  DESCRIPTION: \"fixture 15: @ and ' in idents\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 2;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            # Leading @ in an input AP name.
            "  INPUTS {\n"
            "    @event[N];\n"
            "  }\n"
            # Mixed @ and ' as letter characters.
            "  OUTPUTS {\n"
            "    ack'0;\n"
            "    ack'1;\n"
            "  }\n"
            "  GUARANTEE {\n"
            "    G(!@event[0] || F ack'0);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(weird.errors,
                   f"@ and ' identifiers must parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in weird.errors]}")
    tc.assertEqual(list(weird.inputs), ["@event"],
                   f"expected '@event' as INPUTS entry; got: "
                   f"{list(weird.inputs)}")
    tc.assertEqual(list(weird.outputs), ["ack'0", "ack'1"],
                   f"expected 'ack\\'0' and 'ack\\'1' as OUTPUTS; "
                   f"got: {list(weird.outputs)}")
    # Bus-flattening on @-led input: the deparser round-trip forms
    # one AP per index after parameter resolution.
    res_weird = spot.tlsf_to_ltl(weird)
    tc.assertTrue(bool(res_weird.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr_weird = str(res_weird.full_formula)
    tc.assertIn("@event_0", fstr_weird,
                f"bus-flattened @event[N] should produce '@event_0'; "
                f"got: {fstr_weird}")
    tc.assertIn("ack'0",  fstr_weird,
                f"output AP ack'0 should appear in formula; "
                f"got: {fstr_weird}")
    # Tests the `enum` keyword in GLOBAL { DEFINITIONS { ... } }.
    enum_test = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"with enum\"\n"
            "  DESCRIPTION: \"fixture 16: enum keyword pin\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 2; }\n"
            "  DEFINITIONS {\n"
            "    enum Color = RED: 00 GREEN: 01 BLUE: 10 BLACK: 11;\n"
            "    Gplus(x) = G x;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { request; }\n"
            "  OUTPUTS { grant; }\n"
            "  GUARANTEE { Gplus(request); }\n"
            "}\n")

    tc.assertFalse(enum_test.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in enum_test.errors]}")
    # The enum declaration is observable only through the canonical
    # print (the AST is opaque).  The canonical line below pins the
    # decl name, the 4 entries, their order, and their bit strings.
    # Don't-care bit `*` is also accepted; a lone `*` tag must be
    # the only tag of its enum (it overlaps every valuation).
    sigs = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Sigs = ANY: *;\n"
            "    enum Lev = LOW: 0* HIGH: 11;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G(p); }\n"
            "}\n")

    tc.assertFalse(sigs.errors,
                   f"don't-care bit must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in sigs.errors]}")
    # The `*` bit string is kept verbatim in the canonical print.
    sigs_canon = spot.ostringstream()
    spot.tlsf_print(sigs_canon, sigs)
    tc.assertIn("enum Sigs = ANY:*;",
                sigs_canon.str(),
                "don't-care bits must round-trip verbatim")
    # Round-trip: deparse, re-parse, idempotent.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, enum_test)
    can_enum = ostr.str()
    tc.assertIn("enum Color = ", can_enum,
                f"deparser should emit 'enum Color = '; got: "
                f"{can_enum}")
    tc.assertIn("RED:00", can_enum,
                f"deparser should emit 'RED:00'; got: {can_enum}")
    tc.assertIn("GREEN:01", can_enum,
                f"deparser should emit 'GREEN:01'; got: {can_enum}")
    tc.assertIn("BLUE:10", can_enum,
                f"deparser should emit 'BLUE:10'; got: {can_enum}")
    tc.assertIn("BLACK:11", can_enum,
                f"deparser should emit 'BLACK:11'; got: {can_enum}")
    tc.assertIn("enum Color = RED:00 GREEN:01 BLUE:10 BLACK:11;",
                can_enum,
                "enum name, entries, order, and bits must round-trip")
    enum_rt = parse_tlsf(can_enum)

    tc.assertFalse(enum_rt.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in enum_rt.errors]}")
    # Idempotence: deparse again, expect the same canonical form.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, enum_rt)
    can_enum2 = ostr.str()
    tc.assertEqual(can_enum2, can_enum,
                   f"enum deparse must be idempotent; "
                   f"first:\n{can_enum}\nsecond:\n{can_enum2}")
    # Negative test: a mis-spelled bit character (e.g. `X`) is a
    # syntax error: `0X` tokenises as the pattern `0` followed by a
    # new entry tag `X` whose mandatory `:` is missing.
    bad = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Bad = A: 0X;\n"
            "  }\n"
            "}\n"
            "MAIN {}\n")

    tc.assertTrue(bad.errors,
                  f"unknown bit character must yield a "
                  f"syntax error; got none")

    # Negative tests: all four strict-parity violations are
    # rejected: (a) the braced form -- no `{` after `=`;
    # (b) the empty enum -- at least one entry is mandatory;
    # (c) two DIFFERENT tags covering the same valuation;
    # (d) a pattern shorter/longer than the first one (the whole
    # list is parsed with a fixed width).
    # Overlapping patterns WITHIN one tag stay legal (the `U: 11*,
    # 1*1, *11` coverage union); tags may be named after a word the
    # scanner is able to shadow, because the scanner's enum state
    # recognizes no keywords.
    def enum_neg(body):
        res = parse_tlsf(
                "INFO {}\n"
                "GLOBAL {\n"
                "  DEFINITIONS {\n"
                "    " + body + "\n"
                "  }\n"
                "}\n"
                "MAIN {}\n")

        tc.assertTrue(res.errors,
                      f"expected diagnostics for: {body}; got none")
        return [(e.first, e.second) for e in res.errors]

    enum_neg("enum C = { A: 00, B: 01 };")
    enum_neg("enum C = ;")
    errs = enum_neg("enum C = A: 0* B: 01;")
    tc.assertTrue(any("share the same value: 01" in m for _, m in errs),
                  f"overlap diagnostic should name the shared value; "
                  f"got: {errs}")
    errs = enum_neg("enum C = A: 0 B: 01;")
    tc.assertTrue(any("width is fixed to 1" in m for _, m in errs),
                  f"width diagnostic should mention the fixed width; "
                  f"got: {errs}")

    # Positive: the specification's own multi-pattern tag example
    # (`UNDEF: 11*, 1*1, *11`) -- same-tag overlapping patterns are
    # a coverage union, and the tag `U` must not be mangled into an
    # LTL token.  Also legal: a duplicate tag with DISJOINT patterns
    # and a comma gluing extra patterns onto one tag.
    multi = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum B = U: 11*, 1*1, *11;\n"
            "    enum D = A: 00 A: 11;\n"
            "    enum E = V: 0*, 11;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G(p); }\n"
            "}\n")

    tc.assertFalse(multi.errors,
                   f"multi-pattern/keyword-tag enums must parse "
                   f"cleanly; got: "
                   f"{[(e.first, e.second) for e in multi.errors]}")
    m_canon = spot.ostringstream()
    spot.tlsf_print(m_canon, multi)
    tc.assertIn("enum B = U:11*,1*1,*11;", m_canon.str(),
                "multi-pattern tag must round-trip with commas")
    tc.assertIn("enum D = A:00 A:11;", m_canon.str(),
                "duplicate tags with disjoint patterns must survive")
    tc.assertIn("enum E = V:0*,11;", m_canon.str(),
                "comma-glued extra patterns must round-trip")

    # A word the file declares as the name or a tag of an `enum` is an
    # identifier, as in syfco: TLSF's word list is a scanner
    # convention, not a reservation.  The scanner keeps the declared
    # words and consults that set before returning a keyword, so a tag
    # named U reads as the tag while the other meaning of that same
    # word (`AND` below) still works.  The AST is opaque, so both
    # readings are observed through the canonical print and through
    # the LTL translation.
    def enum_kw(tag_a, tag_b, name="E"):
        return parse_tlsf(
                f"INFO {{}}\n"
                f"GLOBAL {{\n"
                f"  DEFINITIONS {{\n"
                f"    enum {name} = {tag_a}: 00 {tag_b}: 11;\n"
                f"  }}\n"
                f"}}\n"
                f"MAIN {{\n"
                f"  INPUTS  {{ {name} b; c; }}\n"
                f"  OUTPUTS {{ grant; }}\n"
                f"  GUARANTEE {{ G(((b == {tag_a}) AND (b != {tag_b}))"
                f" -> grant); }}\n"
                f"}}\n")

    kw = enum_kw("U", "V")

    tc.assertFalse(kw.errors,
                   f"tags named after words must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in kw.errors]}")
    k_canon = spot.ostringstream()
    spot.tlsf_print(k_canon, kw)
    tc.assertIn("enum E = U:00 V:11;", k_canon.str(),
                f"tags named after words must round-trip; got: "
                f"{k_canon.str()}")
    kw_rt = parse_tlsf(k_canon.str())
    tc.assertFalse(kw_rt.errors,
                   f"re-parsing the canonical print must stay clean; got: "
                   f"{[(e.first, e.second) for e in kw_rt.errors]}")
    # The word tags have to resolve to the values they are declared
    # with, so the specification must translate to the same formula as
    # the same one with neutral tag names.
    k_ltl = str(spot.tlsf_to_ltl(kw).full_formula)
    ref = enum_kw("Z", "W")
    tc.assertFalse(ref.errors,
                   f"the reference specification must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in ref.errors]}")
    tc.assertEqual(k_ltl, str(spot.tlsf_to_ltl(ref).full_formula),
                   f"a tag named after a word must read as the tag, not "
                   f"as a word; got: {k_ltl}")
    # The very same word, used where its own trigger is present, is
    # still the word: `AND` in the guarantee above is the conjunction,
    # and had it been read as a tag the two constraints would have been
    # nonsense rather than `b == U`.
    tc.assertIn("b_0 & !b_1", k_ltl,
                f"AND should still be the conjunction; got: {k_ltl}")
    # A word the scanner cannot tell from an identifier, because
    # nothing in the syntax follows it, stays reserved: `G` is usable
    # as the always word, and the tag may not be referred to.
    for w in ["G", "F", "X", "NOT", "SIZEOF", "true", "false"]:
        res = parse_tlsf(
                "INFO {}\n"
                "GLOBAL {\n"
                "  DEFINITIONS {\n"
                "    enum E = " + w + ": 0;\n"
                "  }\n"
                "}\n"
                "MAIN {\n"
                "  INPUTS  { E b; }\n"
                "  OUTPUTS { grant; }\n"
                "  GUARANTEE { G(b[0]) -> grant; }\n"
                "}\n")

        tc.assertFalse(res.errors,
                       f"a tag named {w} must leave that word alone; got: "
                       f"{[(e.first, e.second) for e in res.errors]}")
    # Referring to such a tag is a syntax error, though: the scanner
    # cannot tell that this occurrence is a value and not the word.
    res = parse_tlsf(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum E = G: 0;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { E b; }\n"
            "  OUTPUTS { grant; }\n"
            "  GUARANTEE { G(b[0] == G) -> grant; }\n"
            "}\n")

    tc.assertTrue(res.errors,
                  f"a word with no trigger must stay reserved; got none")
    # A word is not matched by prefix: `U2` is an identifier of its own.
    near = enum_kw("U2", "V")

    tc.assertFalse(near.errors,
                   f"a word is not a prefix; got: "
                   f"{[(e.first, e.second) for e in near.errors]}")

    # The enum grammar of TLSF v1.2 SS4.4 has no terminator, so the
    # `;` is optional when the enum is the last item of the
    # DEFINITIONS block: the `}` that closes the block ends the body.
    # This is the paper's own `Position` example, verbatim but without
    # the `;`.  The AST is opaque, so the `;`-less and the `;`-full
    # forms are compared through the canonical print.
    def enum_spec(body):
        return parse_tlsf(
                "INFO {\n"
                "  TITLE:       \"optional enum terminator\"\n"
                "  DESCRIPTION: \"fixture 21: `;`-less enum\"\n"
                "  SEMANTICS:   Mealy\n"
                "  TARGET:      Mealy\n"
                "}\n"
                "GLOBAL {\n"
                "  DEFINITIONS {\n" + body +
                "  }\n"
                "}\n"
                "MAIN {\n"
                "  INPUTS  { req; }\n"
                "  OUTPUTS { grant; }\n"
                "  GUARANTEE { G(grant <-> req); }\n"
                "}\n")

    def canon(spec):
        out = spot.ostringstream()
        spot.tlsf_print(out, spec)
        return out.str()

    position = "    enum Position =\n" \
               "      ZERO:    0000\n" \
               "      ONE:     0001\n" \
               "      TWO:     0010\n" \
               "      THREE:   0011\n" \
               "      INVALID: 1111\n"
    no_semi = enum_spec(position)
    tc.assertFalse(no_semi.errors,
                   f"a `;`-less last enum must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in no_semi.errors]}")
    # The `;` is optional on the last item of the block only, so for
    # each combination below the canonical form is the same whether or
    # not the final terminator is written.
    position_semi = position + "    ;\n"
    other = "    enum Other = X: 00;\n"
    last = "    enum Last = Y: 11;\n"
    for body, terminated in ((position, position_semi),
                             (position_semi + other,
                              position_semi + other.rstrip(";\n") + "\n"),
                             (position_semi + other + last,
                              position_semi + other
                              + last.rstrip(";\n") + "\n")):
        plain = enum_spec(body)
        tc.assertFalse(plain.errors,
                       f"must parse cleanly: {body!r}; got: "
                       f"{[(e.first, e.second) for e in plain.errors]}")
        tc.assertEqual(canon(plain), canon(enum_spec(terminated)),
                       f"the `;` must not change: {body!r}")
    # A `;`-less enum may NOT be followed by another item: the `;` is
    # mandatory between two def_list items, and syfco agrees -- its
    # enumVParserL consumes the following identifier before requiring
    # the `:` of a tag, so it cannot end the entry list there either.
    # Each of the three below is rejected with a single syntax error
    # reported where the next item starts.
    for following in ("    Gplus(x) = G x;\n",
                      "    hmm = 2;\n",
                      "    enum Other = X: 00\n"):
        errs = enum_neg(position + following)
        tc.assertEqual(len(errs), 1,
                       f"{following!r} after a `;`-less enum should give "
                       f"one diagnostic, got: {errs}")
        tc.assertTrue(any("syntax error" in m for _, m in errs),
                      f"the diagnostic should be a syntax error: {errs}")
    # The parameterless case above used to be reported as
    # "unexpected character '2'" instead: the `=` trailing context of
    # the enumdecl identifier rule took `hmm =` for the enumeration's
    # name and stranded the scanner in the enum body, where `2` is not
    # a pattern.  The name is now scanned in a state of its own, so
    # nothing but a syntax error is reported.
    # Restoring the `;` makes each of them parse, and the definition
    # that follows is a real item: the printed form shows the boundary.
    follows = enum_spec(position + "    ;\n" + "    Gplus(x) = G x;\n")
    tc.assertFalse(follows.errors,
                   f"a definition after a terminated enum must parse "
                   f"cleanly; "
                   f"got: {[(e.first, e.second) for e in follows.errors]}")
    lines = [x.strip() for x in canon(follows).splitlines()]
    tc.assertIn("Gplus(x) = G x;", lines,
                f"`Gplus` should be a definition line; got: {lines}")
    tc.assertEqual([x for x in lines if x.startswith("enum Position =")],
                   ["enum Position = ZERO:0000 ONE:0001 TWO:0010 "
                    "THREE:0011 INVALID:1111;"],
                   "the enum body should end at the last tag")
    # A parameterless definition after the `;` is fine too: the `=` of
    # a definition must not be mistaken for the enumeration's name.
    parmless = enum_spec(position + "    ;\n" + "    hmm = 2;\n")
    tc.assertFalse(parmless.errors,
                   f"got: {[(e.first, e.second) for e in parmless.errors]}")

    # A pattern is a single maximal run of `0`, `1` and `*` characters
    # (TLSF v1.2 SS4.4), so two juxtaposed runs are a misparse.  They
    # must not be merged into one longer pattern -- that would also
    # redefine the enum's width -- and the missing separator is
    # reported once, where the second run starts.  A comment between
    # the runs does not separate them either.
    errs = enum_neg("enum C = A: 10 01 B: 11;")
    tc.assertEqual(len(errs), 1,
                   f"one juxtaposed run should give one diagnostic, "
                   f"got: {errs}")
    tc.assertTrue(any("missing ',' between bit patterns" in m
                      for _, m in errs),
                  f"the diagnostic should name the missing separator; "
                  f"got: {errs}")
    errs = enum_neg("enum C = A: 10 /* c */ 01 B: 11;")
    tc.assertTrue(any("missing ',' between bit patterns" in m
                      for _, m in errs),
                  f"a comment does not separate two runs; got: {errs}")
    # The offending run is dropped, not merged: the canonical print of
    # the rejected declaration keeps the first run alone, so the enum
    # keeps the width 2 and no `1001` pattern ever exists.
    joined = enum_spec("    enum C = A: 10 01 B: 11;\n")
    tc.assertIn("enum C = A:10 B:11;", canon(joined),
                f"juxtaposed runs must not be merged: {canon(joined)}")
    tc.assertNotIn("1001", canon(joined),
                   f"the merged pattern must not be built: {canon(joined)}")
    # With the comma, the very same declaration is accepted: the two
    # runs are two patterns of tag A, and the width stays 2.
    comma = enum_spec("    enum C = A: 10, 01 B: 11;\n")
    tc.assertFalse(comma.errors,
                   f"comma-separated runs must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in comma.errors]}")
    tc.assertIn("enum C = A:10,01 B:11;", canon(comma),
                f"both patterns must survive: {canon(comma)}")

    # Regression: enum tag/bits (incl. don't-care `**`) survival
    # round-trip.  The enumerations are unreachable through
    # parsed_tlsf (the AST is opaque), so the exact canonical
    # `enum Color = {...}` line must survive parse -> deparse ->
    # reparse verbatim (catching tag/bits rewrites, dropped entries,
    # and `*`-to-`0`/`1` corruption) and deparse must be idempotent.
    parsed_enum = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"enum round-trip\"\n"
            "  DESCRIPTION: \"fixture 17: tag+bits+star survival\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Color = RED: 00 GREEN: 01 BLUE: 10 YELLOW: 11;\n"
            "    enum Any = ALL: **;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G(p); }\n"
            "}\n")

    tc.assertFalse(parsed_enum.errors,
                   f"source enum must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in parsed_enum.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_enum)
    canonical = ostr.str()
    enum_rt = parse_tlsf(canonical)

    tc.assertFalse(enum_rt.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in enum_rt.errors]}")
    # The tag/bits pairs (including the `**` don't-care pattern in
    # its own single-tag enum) survive parse -> deparse -> reparse.
    tc.assertIn("enum Color = RED:00 GREEN:01 BLUE:10 YELLOW:11;",
                canonical,
                "tag/bits pairs must survive round-trip")
    tc.assertIn("enum Any = ALL:**;",
                canonical,
                "the ** don't-care pattern must survive round-trip")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, enum_rt)
    tc.assertEqual(ostr.str(), canonical,
                   "enum deparse must be idempotent after round-trip")

    # Heavy-usage regression: 102 uses of `MultiUse(MyDef(a))`,
    # spread over all 6 MAIN subsections at 17 uses per section.
    # Each use triggers two levels of expansion (inner MyDef, outer
    # MultiUse with 5 nested MyDef leaves), for roughly 1500 AST
    # clone-and-replace operations.  Pins: every body slot carries
    # exactly 17 uses, translation succeeds, and the deparse ->
    # reparse -> deparse round-trip is byte-identical.

    USES_PER_SECTION = 17  # 17 * 6 sections = 102 use sites.
    # The 6 MAIN subsection keywords generated below; the per-section
    # counts are read back from the canonical print.
    SECS_18 = [
        'INITIALLY',
        'PRESET',
        'REQUIRE',
        'ASSERT',
        'GUARANTEE',
        'ASSUME',
    ]
    spec_lines = [
        'INFO {\n',
        '  TITLE:       "fixture 18: 102 nested MultiUse uses"\n',
        '  DESCRIPTION: "AST-clone-and-substitute regression '
        'pin"\n',
        '  SEMANTICS:   Mealy\n',
        '  TARGET:      Mealy\n',
        '}\n',
        'GLOBAL {\n',
        '  DEFINITIONS {\n',
        '    MyDef(x) = G x;\n',
        # MultiUse's body references MyDef FIVE times; each App
        # child is what substitution descends into on every use.
        '    MultiUse(x) = MyDef(x) || MyDef(x) || '
        'MyDef(x) || MyDef(x) || MyDef(x);\n',
        '  }\n',
        '}\n',
        'MAIN {\n',
        '  INPUTS { a; }\n',
    ]
    for kw in SECS_18:
        spec_lines.append(f'  {kw} {{\n')
        for _ in range(USES_PER_SECTION):
            spec_lines.append('    MultiUse(MyDef(a));\n')
        spec_lines.append('  }\n')
    spec_lines.append('}\n')
    contents_18 = ''.join(spec_lines)

    parsed_18 = parse_tlsf(contents_18)
    res_18 = spot.tlsf_to_ltl(parsed_18)

    # same shape `MultiUse(MyDef(a))` -- the parser must accept
    # all of them as App(MyUse, [App(MyDef, [Ident("a")])]).
    tc.assertFalse(
        list(parsed_18.errors),
        f"fixture 18: parse_tlsf must report 0 errors on the "
        f"102-use spec; got "
        f"{[(e.first, e.second) for e in parsed_18.errors]}")
    # No translate diagnostics: all defs are defined, all
    # actual arg counts match formal arities, no active_defs_
    # cycle (the def DAG is MyDef -> MyDef body, MultiUse ->
    # 5 MyDef calls).
    tc.assertFalse(
        list(parsed_18.errors),
        f"fixture 18: errors leaked from translate (arity, "
        f"unknown def, or active_defs_ cycle); got "
        f"{[(e.first, e.second) for e in parsed_18.errors]}")
    # A null formula would indicate a dead end in the expansion
    # path; the formula itself may simplify to true, so it is not
    # spelled out here.

    # Structural pin: every section carries EXACTLY 17 use sites
    # (6 * 17 = 102 total), read from the canonical print.
    count_18 = spot.ostringstream()
    spot.tlsf_print(count_18, parsed_18)
    can_counts_18 = count_18.str()
    for kw in SECS_18:
        n_use = len(formulas_in_section(can_counts_18, kw))
        tc.assertEqual(
            n_use, USES_PER_SECTION,
            f"fixture 18: section {kw} should hold exactly "
            f"{USES_PER_SECTION} MultiUse(MyDef(a)) uses; got "
            f"{n_use}")
    tc.assertEqual(can_counts_18.count('MultiUse(MyDef(a));'),
                   USES_PER_SECTION * len(SECS_18),
                   "fixture 18: 102 use sites must appear in the "
                   "canonical print")

    # Round-trip: the canonical form re-parses cleanly and
    # re-deparses byte-identically (deterministic iteration).
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_18)
    can_18 = ostr.str()
    parsed_18b = parse_tlsf(can_18)

    tc.assertFalse(
        list(parsed_18b.errors),
        f"fixture 18: round-trip (parse+deparse+reparse) must "
        f"stay clean; got "
        f"{[(e.first, e.second) for e in parsed_18b.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_18b)
    can_18b = ostr.str()
    tc.assertEqual(
        can_18b, can_18,
        f"fixture 18: deparse must be idempotent across "
        f"canon/parse/canon; first canonical \\n{can_18!r}\\n"
        f"second canonical \\n{can_18b!r}")

    # Guards and recursion in DEFINITIONS.  A definition body may be
    # a sequence of `guard : expr` clauses whose first true guard
    # wins (`otherwise` is the catch-all), and a guarded definition
    # may call itself with constant integer arguments that shrink
    # toward a guard-selected base case.  Four behaviors are pinned:
    #
    #   1. First-true-wins selection: `sel(3)` picks `x > 2 : b`.
    #   2. The deparser round-trips guard clauses.
    #   3. Terminating guarded recursion (the `one` exactly-one
    #      helper) unfolds to a formula equivalent to hand-written
    #      XORs -- pins constant-argument folding in expansion.
    #   4. Non-terminating recursion (unguarded self call, or a
    #      guard that never fires) is diagnosed exactly ONCE, with
    #      the diagnostic naming the definition that STARTED the
    #      expansion chain, not the leaf call that hit the depth
    #      budget.
    guarded = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"guards\"\n"
            "  DESCRIPTION: \"guard clauses\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    sel(x) =\n"
            "      x > 5 : a\n"
            "      x > 2 : b\n"
            "      otherwise : c;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a; b; c; }\n"
            "  GUARANTEE { sel(3); }\n"
            "}\n")

    tc.assertFalse(
        list(guarded.errors),
        f"fixture 19: guard clauses must parse cleanly; got "
        f"{[(e.first, e.second) for e in guarded.errors]}")
    res_guard = spot.tlsf_to_ltl(guarded)
    tc.assertTrue(bool(res_guard.full_formula),
                  "fixture 19: guarded definition must translate")
    tc.assertEqual(
        str(res_guard.full_formula), 'b',
        f"fixture 19: first-true-wins selection failed; "
        f"sel(3) should pick the `x > 2 : b` clause, got "
        f"{res_guard.full_formula}")
    # Round-trip: the deparser must print the guard clauses, and the
    # canonical form must reparse and translate identically.
    ostr_g = spot.ostringstream()
    spot.tlsf_print(ostr_g, guarded)
    can_g = ostr_g.str()
    tc.assertIn('x > 5 : a', can_g,
                f"fixture 19: guard clause lost in canonical print; "
                f"got:\n{can_g}")
    tc.assertIn('otherwise : c', can_g,
                f"fixture 19: otherwise clause lost in canonical "
                f"print; got:\n{can_g}")
    guarded_b = parse_tlsf(can_g)

    tc.assertFalse(
        list(guarded_b.errors),
        f"fixture 19: canonical print must reparse cleanly; got "
        f"{[(e.first, e.second) for e in guarded_b.errors]}")
    res_guard_b = spot.tlsf_to_ltl(guarded_b)
    tc.assertEqual(str(res_guard_b.full_formula), 'b',
                   "fixture 19: semantics must survive the "
                   "canonical round-trip")

    # Terminating guarded recursion: `one(bus,i,j)` holds iff exactly
    # one element of bus[i..j] is set; the recursion halves the range
    # toward a base case.  `one(g,0,2)` must be equivalent to the
    # hand-written XOR of the three flattened APs.
    recursive = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"one\"\n"
            "  DESCRIPTION: \"guarded recursion\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    none(bus,i,j) = &&[i <= t <= j] !bus[t];\n"
            "    one(bus,i,j) =\n"
            "      i > j : false\n"
            "      i == j : bus[i]\n"
            "      i < j : (none(bus, i, (i+j)/2) && "
            "one(bus, (i+j)/2 + 1, j)) ||\n"
            "              (one(bus, i, (i+j)/2) && "
            "none(bus, (i+j)/2 + 1, j));\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { g[3]; }\n"
            "  GUARANTEE { one(g, 0, 2); }\n"
            "}\n")

    tc.assertFalse(
        list(recursive.errors),
        f"fixture 19: recursive definition must parse cleanly; got "
        f"{[(e.first, e.second) for e in recursive.errors]}")
    rec_errors = spot.parse_aut_error_list()
    res_rec = spot.tlsf_to_ltl(
        recursive, spot.tlsf_translator_options(), rec_errors)
    tc.assertFalse(
        list(rec_errors),
        f"fixture 19: terminating recursion must not diagnose; got "
        f"{[(e.first, e.second) for e in rec_errors]}")
    tc.assertTrue(bool(res_rec.full_formula),
                  "fixture 19: guarded recursion must translate")
    tc.assertTrue(
        spot.are_equivalent(
            res_rec.full_formula,
            spot.formula('(g_0 & !g_1 & !g_2) | '
                         '(!g_0 & g_1 & !g_2) | '
                         '(!g_0 & !g_1 & g_2)')),
        f"fixture 19: one(g,0,2) must unfold to exactly-one; got "
        f"{res_rec.full_formula}")

    # Non-terminating recursion 1: an unguarded self call.  The
    # translator must diagnose it exactly once (not flood one
    # message per call site) and name the cyclic definition.
    loop1 = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"loop\"\n"
            "  DESCRIPTION: \"non-terminating recursion\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    f(x) = f(x);\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a; }\n"
            "  GUARANTEE { f(1); }\n"
            "}\n")

    tc.assertFalse(list(loop1.errors))
    loop1_errors = spot.parse_aut_error_list()
    res_loop1 = spot.tlsf_to_ltl(
        loop1, spot.tlsf_translator_options(), loop1_errors)
    tc.assertFalse(
        bool(res_loop1.full_formula),
        "fixture 19: non-terminating recursion must null the "
        "formula")
    loop1_msgs = [e.second for e in loop1_errors]
    tc.assertEqual(
        len(loop1_msgs), 1,
        f"fixture 19: exactly one expansion-limit diagnostic "
        f"expected; got {len(loop1_msgs)}")
    tc.assertIn("'f'", loop1_msgs[0],
                f"fixture 19: diagnostic must name the cyclic "
                f"definition; got: {loop1_msgs[0]}")
    tc.assertIn('cyclic', loop1_msgs[0],
                f"fixture 19: unexpected wording; got: "
                f"{loop1_msgs[0]}")

    # Non-terminating recursion 2: the guardless doubling variant.
    # Its argument tree doubles at every level, so it exercises the
    # total-work budget (the depth bound alone cannot stop an
    # exponential tree).  The diagnostic must name `mone`.
    loop2 = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"loop2\"\n"
            "  DESCRIPTION: \"non-terminating doubling\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    none(bus,i,j) = &&[i <= t <= j] !bus[t];\n"
            "    mone(bus,i,j) =\n"
            "      (none(bus, i, (i+j)/2) && "
            "mone(bus, (i+j)/2 + 1, j)) ||\n"
            "      (mone(bus, i, (i+j)/2) && "
            "none(bus, (i+j)/2 + 1, j));\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { g[2]; }\n"
            "  GUARANTEE { mone(g, 0, 1); }\n"
            "}\n")

    tc.assertFalse(list(loop2.errors))
    loop2_errors = spot.parse_aut_error_list()
    res_loop2 = spot.tlsf_to_ltl(
        loop2, spot.tlsf_translator_options(), loop2_errors)
    tc.assertFalse(
        bool(res_loop2.full_formula),
        "fixture 19: doubling non-termination must null the formula")
    loop2_msgs = [e.second for e in loop2_errors]
    tc.assertEqual(
        len(loop2_msgs), 1,
        f"fixture 19: exactly one expansion-limit diagnostic "
        f"expected; got {len(loop2_msgs)}")
    tc.assertIn("'mone'", loop2_msgs[0],
                f"fixture 19: diagnostic must name the cyclic "
                f"definition (not the none leaf); got: "
                f"{loop2_msgs[0]}")

    # Final `;` handling in DEFINITIONS and multi-line INFO strings.
    # `;` separates definitions so it is required between two of
    # them, but the LAST one may omit it.  INFO strings may span
    # several lines with `\"` as the single escape.  Pinned:
    #   1. a last definition without `;` parses and translates;
    #   2. two `;`-less definitions juxtaposed still fail -- the
    #      second one's head is munched into the first one's body
    #      (maximal munch), so the parse dies at the second `=`;
    #   3. a DESCRIPTION spanning lines keeps its embedded newlines,
    #      `\"` unescapes to a quote, `\\` unescapes to one backslash,
    #      any other `\x` is kept verbatim, and parse->print->parse is
    #      lossless (the deparser escapes quotes and backslashes back);
    #   4. an unterminated string is diagnosed instead of silently
    #      eating the rest of the file.
    m_style = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"M\"\n"
            "  DESCRIPTION: \"M\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    M(a, b) = b U (a && b)\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { b; }\n"
            "  OUTPUTS { a; }\n"
            "  ASSERT {\n"
            "    M(a, b);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(
        list(m_style.errors),
        f"fixture 20: a final definition without `;` must parse; "
        f"got {[(e.first, e.second) for e in m_style.errors]}")
    res_m = spot.tlsf_to_ltl(m_style)
    tc.assertTrue(bool(res_m.full_formula),
                  "fixture 20: M-style spec must translate")
    tc.assertEqual(str(res_m.full_formula), 'G(b U (a & b))',
                   f"fixture 20: unexpected formula: "
                   f"{res_m.full_formula}")
    # `;` between the two definitions, none after the last.
    two_defs = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"two\"\n"
            "  DESCRIPTION: \"two\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    P(a, b) = b U (a && b);\n"
            "    Q(c) = c\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { b; c; }\n"
            "  OUTPUTS { a; }\n"
            "  ASSERT {\n"
            "    P(a, b) && Q(c);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(
        list(two_defs.errors),
        f"fixture 20: `A; B` (B without trailing `;`) must parse; "
        f"got {[(e.first, e.second) for e in two_defs.errors]}")
    res_two = spot.tlsf_to_ltl(two_defs)
    tc.assertTrue(bool(res_two.full_formula),
                  "fixture 20: two-definition spec must translate")
    # Two `;`-less definitions juxtaposed: maximal munch merges the
    # second head into the first body, so the parse fails at the
    # second `=`.
    nosemi = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"nosi\"\n"
            "  DESCRIPTION: \"nosi\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    P(a, b) = b U (a && b)\n"
            "    Q(c) = c;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { b; c; }\n"
            "  OUTPUTS { a; }\n"
            "  ASSERT { P(a, b) && Q(c); }\n"
            "}\n")

    tc.assertTrue(
        list(nosemi.errors),
        "fixture 20: two juxtaposed `;`-less definitions must be "
        "rejected (second `=` is munched into the first body)")
    # Multi-line DESCRIPTION with an escaped quote, plus the lossless
    # parse->print->parse round trip.
    multiline = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"multi\"\n"
            "  DESCRIPTION: \"first line\n"
            "second line with a \\\"quote\\\", a \\\\ backslash, and "
            "\\ prose\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "MAIN {\n"
            "  GUARANTEE { true; }\n"
            "}\n")

    tc.assertFalse(
        list(multiline.errors),
        f"fixture 20: multi-line DESCRIPTION must parse; got "
        f"{[(e.first, e.second) for e in multiline.errors]}")
    tc.assertEqual(
        multiline.description,
        'first line\nsecond line with a "quote", a \\ backslash, and '
        '\\ prose',
        f"fixture 20: embedded newlines and the `\\\"` / `\\\\` escapes "
        f"must be preserved, and any other `\\x` kept verbatim; got: "
        f"{multiline.description!r}")
    ostr_20 = spot.ostringstream()
    spot.tlsf_print(ostr_20, multiline)
    multiline_b = parse_tlsf(ostr_20.str())

    tc.assertFalse(
        list(multiline_b.errors),
        f"fixture 20: canonical print of a multi-line description "
        f"must reparse; got "
        f"{[(e.first, e.second) for e in multiline_b.errors]}")
    tc.assertEqual(multiline_b.description, multiline.description,
                   "fixture 20: DESCRIPTION must survive the "
                   "canonical round trip losslessly")
    # Unterminated string: one clear diagnostic, not a cascade of
    # "unexpected character" errors chewing through the file.
    unclosed = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"oops\"\n"
            "  DESCRIPTION: \"never closed\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "MAIN { }\n")

    tc.assertTrue(
        any('unclosed string' in e.second for e in unclosed.errors),
        f"fixture 20: unterminated string must be diagnosed; got "
        f"{[e.second for e in unclosed.errors]}")

    # Quantifier under a unary operator.  Regression pin for a
    # printer oscillation: the UnaryOp deparse case wraps an
    # unparenthesized Quantifier child in parens, but the Quantifier
    # case ignored its own `parenthesized` flag, so
    #   round 1: `G (&&[..] p)`   (UnaryOp wraps its child)
    #   round 2: `G &&[..] p`     (flagged Quantifier reprinted bare)
    # never reached a fixed point.  The fix makes the Quantifier
    # case honor e.parenthesized; these assertions pin the result:
    # for each form below, print -> parse -> print must be
    # byte-identical (a fixed point from the FIRST print).
    quantunary = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"quantifier under unary operator\"\n"
            "  DESCRIPTION: \"round-trip regression for the printer "
            "oscillation\"\n"
            "  SEMANTICS:   Mealy,Finite\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    N = 2;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS {\n"
            "    req[N];\n"
            "  }\n"
            "  OUTPUTS {\n"
            "    ack[N];\n"
            "    idle;\n"
            "  }\n"
            "  ASSUME {\n"
            "    // unparenthesized quantifier under G "
            "(round_robin_arbiter)\n"
            "    G &&[0 <= i < N] (req[i] -> X req[i]);\n"
            "    // quantifier under X inside a binary op (load_balancer)\n"
            "    G (idle && X &&[0 <= i < N] ! ack[i] -> X idle);\n"
            "    // parenthesized quantifier under X (load_balancer)\n"
            "    ! idle -> X (&&[0 <= i < N] ! ack[i]);\n"
            "    // quantifier under X F inside a binary op "
            "(generalized_buffer)\n"
            "    &&[0 <= i < N] (req[i] -> X F ||[0 <= i < N] ack[i]);\n"
            "    // quantifier as the right operand of a binary op\n"
            "    G idle -> &&[0 <= i < N] ack[i];\n"
            "  }\n"
            "  GUARANTEE {\n"
            "    G (idle <-> &&[0 <= i < N] ! req[i]);\n"
            "  }\n"
            "}\n")

    tc.assertFalse(
        list(quantunary.errors),
        f"fixture 21: quantifier-under-unary fixture must parse "
        f"cleanly; got {[(e.first, e.second) for e in quantunary.errors]}")
    ostr_q = spot.ostringstream()
    spot.tlsf_print(ostr_q, quantunary)
    can_q = ostr_q.str()
    # The UnaryOp case wraps an unparenthesized quantifier child;
    # pin that form (it used to be the first half of the cycle).
    tc.assertIn('G (&&[0 <= i < N] (req[i] -> X req[i]));', can_q,
                f"fixture 21: unparenthesized quantifier child of G "
                f"must be wrapped by the deparser; got:\n{can_q}")
    tc.assertIn('G (idle && X (&&[0 <= i < N] ! ack[i]) -> X idle);',
                can_q,
                f"fixture 21: quantifier under X inside a binary op "
                f"must be wrapped; got:\n{can_q}")
    # A quantifier the user parenthesized in the source must keep its
    # parens in every print (this is the other half of the cycle).
    tc.assertIn('! idle -> X (&&[0 <= i < N] ! ack[i]);', can_q,
                f"fixture 21: source-parenthesized quantifier must "
                f"keep its parens; got:\n{can_q}")
    quantunary_b = parse_tlsf(can_q)

    tc.assertFalse(
        list(quantunary_b.errors),
        f"fixture 21: canonical print must reparse; got "
        f"{[(e.first, e.second) for e in quantunary_b.errors]}")
    ostr_q2 = spot.ostringstream()
    spot.tlsf_print(ostr_q2, quantunary_b)
    can_q2 = ostr_q2.str()
    tc.assertEqual(
        can_q2, can_q,
        f"fixture 21: print/parse/print must be a fixed point "
        f"(printer oscillation regression); first print:\n{can_q!r}\n\n"
        f"second print:\n{can_q2!r}")
    # One more cycle for good measure: the previously oscillating
    # forms alternate every round, so two stable rounds are the
    # minimal meaningful pin.
    quantunary_c = parse_tlsf(can_q2)

    tc.assertFalse(
        list(quantunary_c.errors),
        f"fixture 21: second round-trip must reparse; got "
        f"{[(e.first, e.second) for e in quantunary_c.errors]}")
    ostr_q3 = spot.ostringstream()
    spot.tlsf_print(ostr_q3, quantunary_c)
    tc.assertEqual(
        ostr_q3.str(), can_q,
        f"fixture 21: third print must equal the first (an "
        f"oscillation would flip between two forms)")

    # Typed enum buses and parameterless definitions.  Pins:
    #   1. `enumtype BUS;` declares a bus whose size is the enum's
    #      width, expanded to BUS_0..BUS_{w-1} APs;
    #   2. `BUS == tag` / `BUS != tag` fold to the tag's bit pattern
    #      (pattern bit k is AP BUS_k, `1` positive, `0` negated);
    #   3. valuations matched by no tag are excluded by an explicit
    #      constraint (the missing-valuation rule);
    #   4. a parameterless definition (`m = log2(n);`) evaluates in
    #      integer position (bus size) and LTL position, including a
    #      recursive definition like `log2`;
    #   5. the canonical print is a round-trip fixed point that
    #      keeps `enumtype BUS;` and the `m = ...;` form;
    #   6. an unknown enum type, an un-indexed typed-bus use, and an
    #      out-of-range index are diagnosed.
    spec_t = (
        "INFO {\n"
        "  TITLE:       \"typedbus\"\n"
        "  DESCRIPTION: \"typed enum buses and parameterless defs\"\n"
        "  SEMANTICS:   Mealy\n"
        "  TARGET:      Mealy\n"
        "}\n"
        "GLOBAL {\n"
        "  PARAMETERS {\n"
        "    n = 8;\n"
        "  }\n"
        "  DEFINITIONS {\n"
        "    enum hburst =\n"
        "      SINGLE: 01\n"
        "      INCR:   00\n"
        "      BURST4: 10;\n"
        "    m = log2(n);\n"
        "    log2(x) =\n"
        "      x <= 1     : 1\n"
        "      otherwise : 1 + log2(x / 2);\n"
        "    p = ack && X ack;\n"
        "  }\n"
        "}\n"
        "MAIN {\n"
        "  INPUTS {\n"
        "    hburst HBURST;\n"
        "  }\n"
        "  OUTPUTS {\n"
        "    grant[m];\n"
        "    ack;\n"
        "  }\n"
        "  GUARANTEE {\n"
        "    p;\n"
        "    G((HBURST == INCR) -> ack);\n"
        "    G((HBURST != SINGLE) || grant[3]);\n"
        "  }\n"
        "}\n")
    typed = parse_tlsf(spec_t)

    tc.assertFalse(
        list(typed.errors),
        f"fixture 22: typed-bus fixture must parse cleanly; got "
        f"{[(e.first, e.second) for e in typed.errors]}")
    t_errors = spot.parse_aut_error_list()
    res_t = spot.tlsf_to_ltl(
        typed, spot.tlsf_translator_options(), t_errors)
    tc.assertFalse(
        list(t_errors),
        f"fixture 22: typed-bus fixture must translate cleanly; got "
        f"{[(e.first, e.second) for e in t_errors]}")
    tc.assertTrue(bool(res_t.full_formula),
                  "fixture 22: typed-bus fixture must translate")
    f_t = str(res_t.full_formula)
    # (1) The typed bus expands to width-2 APs HBURST_0/HBURST_1.
    tc.assertIn('HBURST_0', f_t, f"fixture 22: got: {f_t}")
    tc.assertIn('HBURST_1', f_t, f"fixture 22: got: {f_t}")
    # (2) INCR is pattern 00; != SINGLE negates the SINGLE pattern 01.
    tc.assertIn('!HBURST_0 & !HBURST_1', f_t, f"fixture 22: got: {f_t}")
    tc.assertIn('!(!HBURST_0 & HBURST_1)', f_t, f"fixture 22: got: {f_t}")
    # (3) Valuation 11 matches no tag: excluded explicitly.
    tc.assertIn('G(!HBURST_0 | !HBURST_1)', f_t, f"fixture 22: got: {f_t}")
    # (4) The LTL-position zero-argument definition `p` is expanded,
    # and grant is sized by m = log2(8) = 4: grant[3] is in range
    # (it would be out of range if m were mis-evaluated as 3).
    tc.assertIn('ack & Xack', f_t, f"fixture 22: got: {f_t}")
    # (5) The canonical print keeps the typed declaration and the
    # bare `m = ...;` form, and is a round-trip fixed point.
    ostr_t = spot.ostringstream()
    spot.tlsf_print(ostr_t, typed)
    can_t = ostr_t.str()
    tc.assertIn('hburst HBURST;', can_t,
                f"fixture 22: typed declaration must survive the print; "
                f"got:\n{can_t}")
    tc.assertIn('m = log2(n);', can_t,
                f"fixture 22: parameterless definition must print "
                f"without empty parens; got:\n{can_t}")
    typed_b = parse_tlsf(can_t)

    tc.assertFalse(
        list(typed_b.errors),
        f"fixture 22: canonical print must reparse; got "
        f"{[(e.first, e.second) for e in typed_b.errors]}")
    ostr_t2 = spot.ostringstream()
    spot.tlsf_print(ostr_t2, typed_b)
    tc.assertEqual(
        ostr_t2.str(), can_t,
        f"fixture 22: print/parse/print must be a fixed point; "
        f"first print:\n{can_t!r}\n\nsecond print:\n"
        f"{ostr_t2.str()!r}")
    # (6a) Unknown enum type in the declaration.  The negative
    # variants are derived from the original source text (not from
    # can_t) so the replacements cannot be defeated by printer
    # spacing.
    bad1 = parse_tlsf(spec_t.replace('hburst HBURST;', 'noenum HBURST;'))

    b1_errors = spot.parse_aut_error_list()
    res_b1 = spot.tlsf_to_ltl(
        bad1, spot.tlsf_translator_options(), b1_errors)
    b1_msgs = ([e.second for e in b1_errors]
               + [e.second for e in bad1.errors])
    tc.assertTrue(
        any('not declared' in m for m in b1_msgs),
        f"fixture 22: unknown enum type must be diagnosed; got "
        f"{b1_msgs}")
    tc.assertFalse(
        bool(res_b1.full_formula),
        "fixture 22: unknown enum type must null the formula")
    # (6b) Un-indexed use of a typed bus.
    bad2 = parse_tlsf(spec_t.replace('G((HBURST == INCR) -> ack);',
                               'G(HBURST);'))

    b2_errors = spot.parse_aut_error_list()
    res_b2 = spot.tlsf_to_ltl(
        bad2, spot.tlsf_translator_options(), b2_errors)
    b2_msgs = ([e.second for e in b2_errors]
               + [e.second for e in bad2.errors])
    tc.assertTrue(
        any('without an index' in m for m in b2_msgs),
        f"fixture 22: un-indexed typed-bus use must be diagnosed; "
        f"got {b2_msgs}")
    tc.assertFalse(
        bool(res_b2.full_formula),
        "fixture 22: un-indexed typed-bus use must null the formula")
    # (6c) Index m = 4 on the 4-bit grant bus is out of range.
    bad3 = parse_tlsf(spec_t.replace('G((HBURST != SINGLE) || grant[3]);',
                               'G(grant[m]);'))

    b3_errors = spot.parse_aut_error_list()
    res_b3 = spot.tlsf_to_ltl(
        bad3, spot.tlsf_translator_options(), b3_errors)
    b3_msgs = ([e.second for e in b3_errors]
               + [e.second for e in bad3.errors])
    tc.assertTrue(
        any('outside bus' in m for m in b3_msgs),
        f"fixture 22: out-of-range index must be diagnosed; got "
        f"{b3_msgs}")
    tc.assertFalse(
        bool(res_b3.full_formula),
        "fixture 22: out-of-range index must null the formula")

    # Eager signal registration: declared signals appear in the
    # flattened lists even when the formula never mentions them,
    # and declaration errors (unknown enum type, bad size
    # expression) fire even on unreferenced buses.
    unused = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"unused\"\n"
            "  DESCRIPTION: \"eager signal registration\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    n = 2;\n"
            "  }\n"
            "  DEFINITIONS {\n"
            "    enum hburst =\n"
            "      SINGLE: 01\n"
            "      INCR:   00\n"
            "      BURST4: 10;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS {\n"
            "    b;\n"
            "    y[n];\n"
            "    hburst HB;\n"
            "  }\n"
            "  OUTPUTS {\n"
            "    w[2];\n"
            "    z;\n"
            "  }\n"
            "  GUARANTEE { G(b -> z); }\n"
            "}\n")

    tc.assertFalse(
        list(unused.errors),
        f"fixture 23: unused-declaration fixture must parse cleanly; "
        f"got {[(e.first, e.second) for e in unused.errors]}")
    # parsed_tlsf.inputs/outputs hold declaration names; the
    # flattened per-bit names appear on the translation result.
    tc.assertEqual(
        list(unused.inputs),
        ['b', 'y', 'HB'],
        f"fixture 23: declarations must be listed; got "
        f"{list(unused.inputs)}")
    unused_errors = spot.parse_aut_error_list()
    res_unused = spot.tlsf_to_ltl(
        unused, spot.tlsf_translator_options(), unused_errors)
    tc.assertFalse(
        list(unused_errors),
        f"fixture 23: unused-declaration fixture must translate "
        f"cleanly; got {[(e.first, e.second) for e in unused_errors]}")
    tc.assertEqual(
        list(res_unused.inputs),
        ['b', 'y_0', 'y_1', 'HB_0', 'HB_1'],
        f"fixture 23: declared-but-unused input signals must be "
        f"registered; got {list(res_unused.inputs)}")
    tc.assertEqual(
        list(res_unused.outputs),
        ['w_0', 'w_1', 'z'],
        f"fixture 23: declared-but-unused output signals must be "
        f"registered; got {list(res_unused.outputs)}")
    # Unknown enum type on an unreferenced bus: diagnosed, formula
    # nulled.
    unusedbad = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"unusedbad\"\n"
            "  DESCRIPTION: \"unknown enum on unreferenced bus\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS {\n"
            "    noenum HB;\n"
            "  }\n"
            "  OUTPUTS { ack; }\n"
            "  GUARANTEE { G(ack); }\n"
            "}\n")

    tc.assertFalse(
        list(unusedbad.errors),
        f"fixture 23: the enum check is a translation-time check; "
        f"got {[(e.first, e.second) for e in unusedbad.errors]}")
    ub_errors = spot.parse_aut_error_list()
    res_ub = spot.tlsf_to_ltl(
        unusedbad, spot.tlsf_translator_options(), ub_errors)
    ub_msgs = [e.second for e in ub_errors]
    tc.assertTrue(
        any('not declared' in m for m in ub_msgs),
        f"fixture 23: unknown enum on an unreferenced bus must be "
        f"diagnosed; got {ub_msgs}")
    tc.assertFalse(
        bool(res_ub.full_formula),
        "fixture 23: unknown enum on an unreferenced bus must null "
        "the formula")

    # Raise-the-tlsf-errors options: with raise_errors enabled, a
    # translation-time failure surfaces as a RuntimeError instead of
    # populating the error list.
    raisecyc = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"raisecyc\"\n"
            "  DESCRIPTION: \"cyclic params with raise_errors\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS {\n"
            "    A = B + 1;\n"
            "    B = A + 1;\n"
            "  }\n"
            "  DEFINITIONS {\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a; }\n"
            "  OUTPUTS { z; }\n"
            "  GUARANTEE { G(a); }\n"
            "}\n")

    tc.assertFalse(
        list(raisecyc.errors),
        "fixture 24: cyclic parameters are a translation-time "
        "diagnostic")
    opts = spot.tlsf_translator_options()
    opts.raise_errors = True
    tc.assertRaises(
        RuntimeError, lambda: spot.tlsf_to_ltl(raisecyc, opts))

    # The same raised-failure path applies when a section (not the
    # parameters) fails to translate -- e.g. an integer literal in LTL
    # position.
    raisebad = parse_tlsf(
            "INFO {\n"
            "  TITLE:       \"raisebadltl\"\n"
            "  DESCRIPTION: \"section failure with raise_errors\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS { a; }\n"
            "  OUTPUTS { z; }\n"
            "  GUARANTEE { G(5); }\n"
            "}\n")

    tc.assertFalse(
        list(raisebad.errors),
        "fixture 24: G(5) parses fine; the failure is in "
        "translation")
    tc.assertRaises(
        RuntimeError, lambda: spot.tlsf_to_ltl(raisebad, opts))

    # Lexer-level coverage gaps: CRLF line endings, C-style block
    # comments, a CRLF inside a TITLE string, a lone CR inside a
    # DESCRIPTION string, and comments inside an enum declaration.
    # Each is serviced by a dedicated scan rule ([\\r\\n]+, "/*"...*/",
    # <str>\\r\\n, <str>\\r, <enumdecl>"//", <enumdecl>"/*") that no
    # other fixture triggers (the rest of this file uses LF newlines,
    # `//` comments only, and CR-free strings).
    lexer_gaps = parse_tlsf(
            "INFO {\r\n"
            "  TITLE:       \"cr line\r\nbreak\"\r\n"
            "  DESCRIPTION: \"para\rpara2\"\r\n"
            "  SEMANTICS:   /* a */ Mealy\r\n"
            "  TARGET:      Mealy\r\n"
            "}\r\n"
            "GLOBAL {\r\n"
            "  PARAMETERS { /* empty */ }\r\n"
            "  DEFINITIONS {\r\n"
            "    /* before */ enum Mode = U: 11*, // in-enum\r\n"
            "      1*1, /* mid */ *11;\r\n"
            "  }\r\n"
            "}\r\n"
            "MAIN {\r\n"
            "  INPUTS { /* i */ x; }\r\n"
            "  GUARANTEE { G(x); }\r\n"
            "}\r\n")

    tc.assertFalse(
        list(lexer_gaps.errors),
        f"CRLF/comment spec must parse cleanly; got: "
        f"{[(e.first, e.second) for e in lexer_gaps.errors]}")
    lg_can = spot.ostringstream()
    spot.tlsf_print(lg_can, lexer_gaps)
    lg_canon = lg_can.str()
    # The deparser escapes the double quote and the backslash, so the
    # CRLF and the lone CR inside the INFO strings come back
    # byte-for-byte.
    tc.assertIn("\r\nbreak", lg_canon,
                "CRLF inside a TITLE string must round-trip")
    tc.assertIn("para\rpara2", lg_canon,
                "lone CR inside a DESCRIPTION must round-trip")
    # Comments and CRLF line endings are dropped by the deparser; the
    # enum body survives compacted (comma-separated patterns).
    tc.assertIn("enum Mode = U:11*,1*1,*11;", lg_canon,
                "in-enum comments must not corrupt the entries")
    lg_rt = parse_tlsf(lg_canon)
    tc.assertFalse(
        list(lg_rt.errors),
        f"canonical round-trip must stay clean; got: "
        f"{[(e.first, e.second) for e in lg_rt.errors]}")
    lg_can2 = spot.ostringstream()
    spot.tlsf_print(lg_can2, lg_rt)
    tc.assertEqual(lg_can2.str(), lg_canon,
                   "canonical deparse must be idempotent")

    # Enum coverage of wide buses.  The coverage constraint used to be
    # one disjunct per *uncovered* valuation, so a bus needed at least
    # 17 bits before the formula outgrew formula::nary's 65535
    # children; the exception was not caught on its way out of the
    # translator, and the process died with SIGABRT.  The translator
    # now emits the factored coverage formula (one term per tag, one
    # literal per bit the tag pins) and only falls back to the
    # per-valuation complement when that is smaller.  These checks pin
    # both the size (so a valuation-sized blow-up cannot come back) and
    # the semantics (the constraint must accept exactly the valuations
    # some tag covers).
    def enum_spec(entries, decl="b"):
        # The `;` terminates the enum as a whole, not each tag, and a
        # pattern list takes no trailing comma: `enum E = T0:00,01
        # T1:1*;` is the canonical (deparsed) shape, while
        # `T0:00;T1:11;` and `T0:00,\n T1:11;` are syntax errors.
        tags = " ".join("T%d:%s" % (i, ",".join(patterns))
                        for i, patterns in enumerate(entries))
        return ("INFO {\n"
                "  TITLE:       \"wide enum bus\"\n"
                "  DESCRIPTION: \"enum coverage constraint\"\n"
                "  SEMANTICS:   Mealy\n"
                "  TARGET:      Mealy\n"
                "}\n"
                "GLOBAL {\n"
                "  DEFINITIONS {\n"
                f"    enum E = {tags};\n"
                "  }\n"
                "}\n"
                "MAIN {\n"
                f"  INPUTS {{ E {decl}; }}\n"
                "  OUTPUTS { o; }\n"
                "  GUARANTEE { o; }\n"
                "}\n")

    def coverage(entries):
        p = parse_tlsf(enum_spec(entries))
        tc.assertFalse(
            list(p.errors),
            f"enum {entries} must parse cleanly; got: "
            f"{[(e.first, e.second) for e in p.errors]}")
        errs = spot.parse_aut_error_list()
        r = spot.tlsf_to_ltl(p, spot.tlsf_translator_options(), errs)
        tc.assertFalse(
            list(errs),
            f"enum {entries} must translate cleanly; got: "
            f"{[(e.first, e.second) for e in errs]}")
        return r.require

    def apname(f):
        return f.apname_from_apid(f.apid())

    def holds(f, bits):
        """Evaluate a (propositional) coverage constraint under `bits`,
        a dict mapping 'b_<i>' to a bool."""
        kind = f.kindstr()
        if kind in ('AP', 'ap'):
            return bits[apname(f)]
        if kind in ('true', 'True', 'tt', 'TT'):
            return True
        if kind in ('false', 'False', 'ff', 'FF'):
            return False
        if kind in ('not', 'Not'):
            return not holds(f[0], bits)
        if kind in ('and', 'And', '&&'):
            return all(holds(c, bits) for c in f)
        if kind in ('or', 'Or', '||'):
            return any(holds(c, bits) for c in f)
        raise AssertionError(f"unexpected operator {kind} in {f}")

    def nleaves(f):
        """Number of atomic propositions in a propositional formula.
        (`formula::size()` only counts the children of the top node,
        so it is 17 for a 17-bit factored term but 2 for a 32-bit
        enum with two tags.)"""
        kind = f.kindstr()
        if kind in ('AP', 'ap'):
            return 1
        if kind in ('true', 'True', 'tt', 'TT',
                    'false', 'False', 'ff', 'FF'):
            return 0
        if kind in ('not', 'Not'):
            return nleaves(f[0])
        return sum(nleaves(c) for c in f)

    def covers(entries, w, v):
        """True if some pattern of some tag matches valuation v."""
        for patterns in entries:
            for pat in patterns:
                if all(c == '*' or (c == '1') == bool((v >> k) & 1)
                       for k, c in enumerate(reversed(pat))):
                    return True
        return False

    def probes(entries, w, exhaustive_upto=12):
        """The valuations to compare the constraint against: everything
        for a narrow bus, and for a wide one the interesting corners
        plus valuations taken from, and adjacent to, the patterns."""
        if w <= exhaustive_upto:
            return range(1 << w)
        seen = set()
        out = [0, (1 << w) - 1]
        for k in range(w):
            out.append(1 << k)
            out.append((1 << w) - 1 - (1 << k))
        rng = random.Random(0)
        for patterns in entries:
            for pat in patterns:
                for bits in (0, (1 << w) - 1, rng.randrange(1 << w)):
                    v = 0
                    for k, c in enumerate(reversed(pat)):
                        if c == '1':
                            v |= 1 << k
                        elif bits >> k & 1:
                            v |= 1 << k
                    out.append(v)
                    # a valuation that differs in one pinned bit must
                    # not be covered
                    for k, c in enumerate(reversed(pat)):
                        if c != '*':
                            out.append(v ^ (1 << k))
                            break
        out += [rng.randrange(1 << w) for _ in range(64)]
        return [v for v in out if not (v in seen or seen.add(v))]

    def check_coverage(entries, w):
        """The constraint must accept exactly the covered valuations."""
        f = coverage(entries)
        for v in probes(entries, w):
            bits = {f'b_{k}': bool((v >> k) & 1) for k in range(w)}
            tc.assertEqual(
                holds(f, bits), covers(entries, w, v),
                f"coverage of {entries} at valuation {v}: got {f}")
        return f

    # A 17-bit bus with one concrete tag: one term of 17 literals.
    # This is the case that used to abort the process.
    wide = check_coverage([['0' * 17]], 17)
    tc.assertEqual(nleaves(wide), 17,
                   f"a 17-bit enum needs one literal per bit: got {wide}")
    # A 32-bit bus with two tags: two terms, still linear in the width.
    wide2 = check_coverage([['0' * 32], ['1' * 32]], 32)
    tc.assertEqual(nleaves(wide2), 64,
                   f"two 32-bit tags need 64 literals: got {wide2}")
    # A 20-bit all-wildcard tag covers every valuation, so no
    # constraint is emitted at all.
    tc.assertTrue(coverage([['*' * 20]]).is_tt(),
                  "an all-wildcard tag must not constrain the bus")
    # Wildcards are still honoured inside a tag, and the leftmost
    # character of a pattern is the most significant bit: `1*` is a
    # 2-bit pattern pinning bit 1, so the constraint is a single
    # literal rather than 4 valuation-sized terms.
    star = check_coverage([['1*']], 2)
    tc.assertEqual(str(star), 'b_1',
                   f"a half-cover wildcard needs one literal: got {star}")
    # ... and the complement is still preferred when it is smaller, as
    # for the width-2 hburst of fixture 22: 3 tags cover 3 of the 4
    # valuations, so the missing one gets a 2-literal disjunct.
    small = check_coverage([['01'], ['00'], ['10']], 2)
    tc.assertEqual(str(small), '!b_0 | !b_1',
                   f"narrow enums keep the complement form: got {small}")
    # Several patterns in one tag are alternatives, not a conjunction:
    # `00,11` on 2 bits is the "bits are equal" condition, so it must
    # come out as a disjunction (an And would be unsatisfiable, and a
    # per-valuation expansion would have cost 4 disjuncts).
    multi = check_coverage([['00', '11']], 2)
    tc.assertEqual(str(multi), '(!b_0 & !b_1) | (b_0 & b_1)',
                   f"alternatives of a tag must be unioned: got {multi}")
    # A wildcard next to a pinned bit pins only the latter: `1*0` on
    # 3 bits.
    pins = check_coverage([['1*0']], 3)
    tc.assertEqual(str(pins), '!b_0 & b_2',
                   f"a wildcard must add no literal: got {pins}")
    # Tags that together cover everything constrain nothing.
    tc.assertTrue(coverage([['0*'], ['1*']]).is_tt(),
                  "a total enumeration must not constrain the bus")
    # A 12-bit enum with a single tag: exhaustive over all 4096
    # valuations, and the factored form is used.
    mid = check_coverage([['1' * 11 + '0']], 12)
    tc.assertEqual(nleaves(mid), 12,
                   f"a 12-bit enum needs one literal per bit: got {mid}")

    # Comparisons between two integer expressions in LTL position.
    # TLSF v1.2 SS4.3 defines an LTL expression as a boolean
    # expression -- which includes eN <eN> -- plus signals and temporal
    # operators, so `(SIZEOF b) == 4`, `N >= 4`, or `m(2) == 2` are
    # valid even though the comparison operators have no LTL
    # counterpart.  Both operands are known at translation time, so
    # the comparison is a constant: the translator folds it, like the
    # `IN` membership it has always accepted.  `lte` is a
    # Boolean-valued definition, so `lte(1, 2)` reaches the same fold
    # through the expansion of a body that is a comparison.
    def intcmp(expr):
        """Translate `expr` as the sole GUARANTEE of a small spec, and
        return (translation result, [diagnostic messages])."""
        p = parse_tlsf(
                "INFO {}\n"
                "GLOBAL {\n"
                "  PARAMETERS { N = 4; }\n"
                "  DEFINITIONS {\n"
                "    m(x) = x;\n"
                "    lte(x, y) = x <= y;\n"
                "  }\n"
                "}\n"
                "MAIN {\n"
                "  INPUTS { a; b; s; bus[N]; }\n"
                "  OUTPUTS { o; }\n"
                "  GUARANTEE { %s }\n"
                "}\n" % expr)
        tc.assertFalse(
            list(p.errors),
            f"fixture 25: {expr} must parse cleanly; got: "
            f"{[(e.first, e.second) for e in p.errors]}")
        errs = spot.parse_aut_error_list()
        r = spot.tlsf_to_ltl(p, spot.tlsf_translator_options(), errs)
        return r, [e.second for e in errs]

    for expr in ('G((SIZEOF bus) == 4)',  # SIZEOF of a declared bus
                 'G(N >= 4)',             # a parameter
                 'G(m(2) == 2)',          # an integer-valued definition
                 'G(lte(1, 2))',          # a Boolean-valued body
                 'G(1 < 2 && 2 <= 2 && 3 > 2 && 3 >= 3)'):
        r, errs = intcmp(expr)
        tc.assertFalse(errs, f"fixture 25: {expr} must not diagnose; got: "
                             f"{errs}")
        tc.assertTrue(r.guarantee.is_tt(),
                      f"fixture 25: {expr} is a true constant; got "
                      f"{r.guarantee}")

    for expr in ('G((SIZEOF bus) == 5)',  # SIZEOF of a declared bus
                 'G(N < 4)',              # a parameter
                 'G(m(2) != 2)',          # an integer-valued definition
                 'G(2 != 2)'):            # literals
        r, errs = intcmp(expr)
        tc.assertFalse(errs, f"fixture 25: {expr} must not diagnose; got: "
                             f"{errs}")
        tc.assertTrue(r.guarantee.is_ff(),
                      f"fixture 25: {expr} is a false constant; got "
                      f"{r.guarantee}")

    # A folded false is a false subterm, not a rejected one: the
    # comparison disappears from the disjunction it guards.
    r, errs = intcmp('G((SIZEOF bus) == 5 || a)')
    tc.assertFalse(errs, f"fixture 25: must not diagnose; got: {errs}")
    tc.assertTrue(spot.are_equivalent(r.guarantee, spot.formula('G a')),
                  f"fixture 25: the false comparison must fold away; got "
                  f"{r.guarantee}")

    # A comparison that involves a signal has no constant value and is
    # still rejected.  A signal on both sides is a plain rejection
    # (`a == b`), while a mistake inside an operand is reported first
    # and only then is the enclosing comparison rejected.
    for expr, expected in (('G(a == b)',
                            ["arithmetic/comparison op '==' is not "
                             "supported in LTL position"]),
                           ('G(lte(a, b))',
                            ["arithmetic/comparison op '<=' is not "
                             "supported in LTL position"]),
                           ('G(SIZEOF(s) == 1)',
                            ["SIZEOF of scalar AP 's'",
                             "arithmetic/comparison op '==' is not "
                             "supported in LTL position"]),
                           ('G(NOPE(1) == 1)',
                            ["function call 'NOPE' is not supported in "
                             "integer position",
                             "arithmetic/comparison op '==' is not "
                             "supported in LTL position"])):
        r, errs = intcmp(expr)
        tc.assertFalse(bool(r.full_formula),
                       f"fixture 25: {expr} must yield a null formula; got "
                       f"{r.full_formula}")
        tc.assertEqual(errs, expected,
                       f"fixture 25: diagnostics for {expr}")
    # ----------------------------------------------------------------
    # TLSF v1.2 SS1.2/SS1.3/SS1.4: the cross-section validations.

    def diags(errors):
        """[(line, column, message)] of a list of parse diagnostics."""
        return [(e.first.begin.line, e.first.begin.column, e.second)
                for e in errors]

    # One symbol, one definition: a name declared twice is a
    # collision whichever declaration spaces the two declarations come
    # from, and both of them are reported.
    full_info = ('INFO {\n'
                 '  TITLE:       "clash"\n'
                 '  DESCRIPTION: "one symbol, one definition"\n'
                 '  SEMANTICS:   Mealy\n'
                 '  TARGET:      Mealy\n'
                 '}\n')
    # Each pair of declarations is reported on both sides.
    p = parse_tlsf(full_info
                   + 'GLOBAL {\n'
                   '  PARAMETERS { p = 1; }\n'
                   '  DEFINITIONS { p = 2; }\n'
                   '}\n'
                   'MAIN {\n'
                   '  INPUTS  { q; }\n'
                   '  OUTPUTS { o; }\n'
                   '  GUARANTEE { G(q); }\n'
                   '}\n')
    tc.assertEqual(diags(p.errors),
                   [(8, 16, "'p' is shadowed by a later declaration as "
                     "a definition"),
                    (9, 17, "'p' is already declared as a parameter")],
                   "a parameter redefined by a definition must be "
                   "reported on both declarations")

    p = parse_tlsf(full_info
                   + 'GLOBAL {\n'
                   '  PARAMETERS { p = 1; }\n'
                   '  DEFINITIONS {\n'
                   '    enum e = E: 0*;\n'
                   '    e = 2;\n'
                   '  }\n'
                   '}\n'
                   'MAIN {\n'
                   '  INPUTS  { q; }\n'
                   '  OUTPUTS { o; }\n'
                   '  GUARANTEE { G(q); }\n'
                   '}\n')
    tc.assertEqual([e[2] for e in diags(p.errors)],
                   ["'e' is shadowed by a later declaration as a "
                    "definition",
                    "'e' is already declared as an enumeration"],
                   "an enumeration and a definition of the same name "
                   "collide too")

    p = parse_tlsf(full_info
                   + 'GLOBAL {\n'
                   '}\n'
                   'MAIN {\n'
                   '  INPUTS  { sig; }\n'
                   '  OUTPUTS { sig; }\n'
                   '  GUARANTEE { G(sig); }\n'
                   '}\n')
    tc.assertEqual([e[2] for e in diags(p.errors)],
                   ["'sig' is shadowed by a later declaration as an "
                    "output signal",
                    "'sig' is already declared as an input signal"],
                   "a signal listed in both INPUTS and OUTPUTS must be "
                   "reported on both declarations")

    # The four mandatory INFO items are required by default, and
    # reported at the INFO section (or at the start of the file when
    # there is no INFO section at all).
    p = spot.parse_tlsf('INFO {}\nGLOBAL {}\nMAIN {}\n')
    tc.assertEqual([e[2] for e in diags(p.errors)],
                   ["missing mandatory INFO item 'TITLE:'",
                    "missing mandatory INFO item 'DESCRIPTION:'",
                    "missing mandatory INFO item 'SEMANTICS:'",
                    "missing mandatory INFO item 'TARGET:'"],
                   "an empty INFO section lacks all four mandatory items")
    tc.assertEqual([(e[0], e[1]) for e in diags(p.errors)],
                   [(1, 1)] * 4,
                   "a missing item is reported at the INFO section")

    p = spot.parse_tlsf('GLOBAL {}\nMAIN {}\n')
    tc.assertEqual([e[2] for e in diags(p.errors)],
                   ["missing mandatory INFO item 'TITLE:'",
                    "missing mandatory INFO item 'DESCRIPTION:'",
                    "missing mandatory INFO item 'SEMANTICS:'",
                    "missing mandatory INFO item 'TARGET:'"],
                   "a file without an INFO section lacks them all")
    tc.assertEqual([(e[0], e[1]) for e in diags(p.errors)],
                   [(1, 1)] * 4,
                   "a missing INFO section is reported at the file start")

    # A partial INFO section names only what is missing.
    p = spot.parse_tlsf('INFO {\n'
                        '  TITLE:       "partial"\n'
                        '  SEMANTICS:   Mealy\n'
                        '}\n'
                        'GLOBAL {}\n'
                        'MAIN {}\n')
    tc.assertEqual([e[2] for e in diags(p.errors)],
                   ["missing mandatory INFO item 'DESCRIPTION:'",
                    "missing mandatory INFO item 'TARGET:'"],
                   "only the absent items are reported")

    # check_info = False turns the requirement off, and nothing else.
    o = spot.tlsf_parser_options()
    o.check_info = False
    p = spot.parse_tlsf('INFO {}\nGLOBAL {}\nMAIN {}\n', o)
    tc.assertFalse(list(p.errors),
                   f"check_info = False must accept a bare INFO; got "
                   f"{diags(p.errors)}")

    # A duplicated INFO item is a grammar-level mistake, and is
    # reported whatever check_info says.  The first value wins, so the
    # specification still translates.
    for opts in (None, o):
        p = spot.parse_tlsf('INFO {\n'
                            '  TITLE:       "first"\n'
                            '  TITLE:       "second"\n'
                            '  TAGS:        t1\n'
                            '  TAGS:        t2\n'
                            '  DESCRIPTION: "d"\n'
                            '  SEMANTICS:   Mealy\n'
                            '  TARGET:      Mealy\n'
                            '}\n'
                            'MAIN { INPUTS { a; } OUTPUTS { b; }\n'
                            '  GUARANTEE { G(a -> b); } }\n', opts)
        tc.assertEqual(diags(p.errors),
                       [(3, 3, "duplicate INFO item 'TITLE:'"),
                        (5, 3, "duplicate INFO item 'TAGS:'")],
                       f"duplicate INFO items (check_info = "
                       f"{None if opts is None else opts.check_info})")
        tc.assertEqual(p.title, 'first',
                       "the first value of a duplicated item wins")
        tc.assertEqual(list(p.tags), ['t1'],
                       "the first TAGS list wins")

    # SEMANTICS and TARGET are parsed by a sub-production of their
    # INFO item, so their value used to be assigned before the
    # duplicate could be rejected.  The first value must win there too.
    p = spot.parse_tlsf('INFO {\n'
                        '  TITLE:       "dup model"\n'
                        '  DESCRIPTION: "d"\n'
                        '  SEMANTICS:   Mealy,Finite\n'
                        '  SEMANTICS:   Moore\n'
                        '  TARGET:      Mealy\n'
                        '  TARGET:      Moore\n'
                        '}\n'
                        'MAIN { INPUTS { a; } OUTPUTS { b; }\n'
                        '  GUARANTEE { G(a -> b); } }\n')
    tc.assertEqual(diags(p.errors),
                   [(5, 3, "duplicate INFO item 'SEMANTICS:'"),
                    (7, 3, "duplicate INFO item 'TARGET:'")],
                   "duplicate SEMANTICS / TARGET items")
    tc.assertEqual(p.semantics, spot.tlsf_semantics_MealyFinite,
                   "the first SEMANTICS wins")
    tc.assertEqual(p.target, spot.tlsf_target_Mealy,
                   "the first TARGET wins")

    # SEMANTICS and TARGET must agree on the system model.
    for semantics, target, model in (('Moore', 'Mealy', 'Moore'),
                                     ('Mealy,Finite', 'Moore', 'Mealy'),
                                     ('Moore,Strict', 'Mealy', 'Moore')):
        p = spot.parse_tlsf('INFO {\n'
                            '  TITLE:       "mismatch"\n'
                            '  DESCRIPTION: "SEMANTICS vs TARGET"\n'
                            f'  SEMANTICS:   {semantics}\n'
                            f'  TARGET:      {target}\n'
                            '}\n'
                            'MAIN { INPUTS { a; } OUTPUTS { b; }\n'
                            '  GUARANTEE { G(a -> b); } }\n')
        tc.assertFalse(list(p.errors),
                       f"{semantics} vs {target}: an ambiguous "
                       f"specification still parses; got "
                       f"{diags(p.errors)}")
        tc.assertEqual(diags(p.warnings),
                       [(4, 3, f"SEMANTICS declares a {model} system "
                         f"model, but TARGET declares {target}; the "
                         f"specification is ambiguous, the {model} "
                         f"composition is used")],
                       f"{semantics} vs {target}: warning at SEMANTICS")

    # A specification that agrees with itself says nothing, and a
    # specification that only spells out one of the two cannot be
    # compared, so neither of them warns.
    for info in ('  SEMANTICS:   Moore\n  TARGET:      Moore\n',
                 '  SEMANTICS:   Moore\n',
                 '  TARGET:      Moore\n',
                 ''):
        p = parse_tlsf('INFO {\n'
                       '  TITLE:       "t"\n'
                       '  DESCRIPTION: "d"\n'
                       f'{info}'
                       '}\n'
                       'MAIN { INPUTS { a; } OUTPUTS { b; }\n'
                       '  GUARANTEE { G(a -> b); } }\n')
        tc.assertFalse(list(p.errors),
                       f"the INFO items {info!r} must be accepted; got "
                       f"{diags(p.errors)}")
        tc.assertFalse(list(p.warnings),
                       f"the INFO items {info!r} must not warn; got "
                       f"{diags(p.warnings)}")

    # A name that clashes is rejected, and so is a specification that
    # is both ambiguous and clashing, while the ambiguous-only one
    # translates.  The validations do not hide each other.
    p = spot.parse_tlsf('INFO {\n'
                        '  TITLE:       "both"\n'
                        '  DESCRIPTION: "clash and mismatch"\n'
                        '  SEMANTICS:   Moore\n'
                        '  TARGET:      Mealy\n'
                        '}\n'
                        'MAIN { INPUTS { sig; } OUTPUTS { sig; }\n'
                        '  GUARANTEE { G(sig); } }\n')
    tc.assertEqual(len(list(p.errors)), 2,
                   f"the clash and the missing items are all reported; "
                   f"got {diags(p.errors)}")
    tc.assertEqual(len(list(p.warnings)), 1,
                   "the ambiguity is reported even when the file also "
                   "has errors")

    # A big operator takes a comma-separated binder list, which is
    # shorthand for nested single-binder quantifiers.  A run of nested
    # quantifiers sharing a tag prints back as one binder list, in
    # nesting order.
    def canon_guarantee(body):
        """Canonical text of the single GUARANTEE formula `body`."""
        spec = parse_tlsf('INFO {}\n'
                          'GLOBAL { PARAMETERS { N = 2; M = 2; } }\n'
                          'MAIN { INPUTS { a; }\n'
                          f'  GUARANTEE {{ {body}; }} }}\n')
        tc.assertFalse(spec.errors,
                       f"{body!r} must parse cleanly; got "
                       f"{diags(spec.errors)}")
        ostr = spot.ostringstream()
        spot.tlsf_print(ostr, spec)
        formulas = formulas_in_section(ostr.str(), 'GUARANTEE')
        tc.assertEqual(len(formulas), 1, f"expected one formula for {body!r}")
        return formulas[0][:-1]  # drop the terminating ';'

    for body, expected in [
        ('&&[i IN {0, 1}, j IN {0, 1}] a', '&&[i IN {0, 1}, j IN {0, 1}] a'),
        # Nested quantifiers print back as one binder list, outermost
        # binder first, so the two spellings converge.
        ('&&[i IN {0, 1}] &&[j IN {0, 1}] a',
         '&&[i IN {0, 1}, j IN {0, 1}] a'),
        ('&&[j IN {0, 1}] &&[i IN {0, 1}] a',
         '&&[j IN {0, 1}, i IN {0, 1}] a'),
        ('||[j IN {0, 1}] ||[i IN {0, 1}] a',
         '||[j IN {0, 1}, i IN {0, 1}] a'),
        ('&&[0 <= i < 2, 0 <= j < 2] a',
         '&&[0 <= i < 2, 0 <= j < 2] a'),
        # AND/FORALL share the And tag and OR/EXISTS share the Or tag,
        # so each pair canonicalizes to the same spelling.
        ('FORALL[i IN {0, 1}, j IN {0, 1}] a',
         '&&[i IN {0, 1}, j IN {0, 1}] a'),
        ('EXISTS[i IN {0, 1}, j IN {0, 1}] a',
         '||[i IN {0, 1}, j IN {0, 1}] a'),
        # A parenthesized head keeps its parentheses.
        ('G (&&[i IN {0, 1}, j IN {0, 1}] a)',
         'G (&&[i IN {0, 1}, j IN {0, 1}] a)'),
        # `X[n] phi` is a next-stack length, not a binder, so a run of
        # nexts keeps one head each.
        ('X[N] X[M] a', 'X[N] X[M] a'),
        ('X[N] X[M] X[N] a', 'X[N] X[M] X[N] a'),
        # `X[!n] phi` keeps its marker inside the brackets.
        ('X[!N] a', 'X[N!] a'),
    ]:
        got = canon_guarantee(body)
        tc.assertEqual(got, expected,
                       f"{body!r} must canonicalize to {expected!r}")

    # A binder list may not be empty and may not end with a comma, and
    # the brackets of `X[n]` and `F[lo:hi]` take no list at all.
    for body, fragment in [
        ('&&[i IN {0, 1},] a', 'unexpected ]'),
        ('X[N, N] a', 'unexpected ","'),
        ('F[1:2, 3:4] a', 'unexpected ","'),
    ]:
        spec = parse_tlsf('INFO {}\n'
                          'GLOBAL { PARAMETERS { N = 2; } }\n'
                          'MAIN { INPUTS { a; }\n'
                          f'  GUARANTEE {{ {body}; }} }}\n')
        tc.assertTrue(spec.errors,
                      f"{body!r} must be rejected as a malformed "
                      f"binder list")

    # SIZE is an alias for the set cardinality `|eSX|` and prints back
    # in that canonical form.  The prefix extrema print with the
    # parentheses their operator word requires in comparison context.
    tc.assertEqual(canon_guarantee('SIZE {1, 2, 3} == 3'), '|{1, 2, 3}| == 3')
    tc.assertEqual(canon_guarantee('|{1, 2, 3}| == 3'), '|{1, 2, 3}| == 3')
    tc.assertEqual(canon_guarantee('MIN {1, 2, 3} == 1'),
                   '(MIN {1, 2, 3}) == 1')
    tc.assertEqual(canon_guarantee('MAX {1, 2, 3} == 3'),
                   '(MAX {1, 2, 3}) == 3')

    # A big operator is a head, a binder list, and a body.  It prints
    # back as one head carrying the whole list, with no parentheses
    # around it: `SUM[` and `PROD[` are the tightest tier of Table 1,
    # and `CUP[`, `CAP[`, and `SETMINUS[` the unary-set tier, which
    # binds tighter than a comparison.  Each alias canonicalizes to the
    # spelling the AST tag names.
    for body, expected in [
        ('SUM[i IN {0, 1}] i == 3', 'SUM[i IN {0, 1}] i == 3'),
        ('+[i IN {0, 1}] i == 3', 'SUM[i IN {0, 1}] i == 3'),
        ('PROD[i IN {0, 1}] (i + 1) == 2', 'PROD[i IN {0, 1}] (i + 1) == 2'),
        ('*[i IN {0, 1}] (i + 1) == 2', 'PROD[i IN {0, 1}] (i + 1) == 2'),
        ('|CUP[i IN {0, 1}] {i}| == 2', '|CUP[i IN {0, 1}] {i}| == 2'),
        ('|(+)[i IN {0, 1}] {i}| == 2', '|CUP[i IN {0, 1}] {i}| == 2'),
        ('|CAP[i IN {0, 1}] {i}| == 1', '|CAP[i IN {0, 1}] {i}| == 1'),
        ('|(*)[i IN {0, 1}] {i}| == 1', '|CAP[i IN {0, 1}] {i}| == 1'),
        ('|SETMINUS[i IN {0, 1}] {i}| == 1',
         '|SETMINUS[i IN {0, 1}] {i}| == 1'),
        ('|(-)[i IN {0, 1}] {i}| == 1',
         '|SETMINUS[i IN {0, 1}] {i}| == 1'),
        # The list survives the round-trip, outermost binder first, just
        # as for the Boolean heads.
        ('SUM[i IN {0, 1}, j IN {0, 1}] i == 4',
         'SUM[i IN {0, 1}, j IN {0, 1}] i == 4'),
        # A body that is itself a comparison stays unparenthesized,
        # because the head binds tighter than `==`.
        ('SUM[i IN {0, 1}] i * 2 == 4', 'SUM[i IN {0, 1}] i * 2 == 4'),
    ]:
        got = canon_guarantee(body)
        tc.assertEqual(got, expected,
                       f"{body!r} must canonicalize to {expected!r}")

    # An explicitly parenthesized head keeps its parentheses, as the
    # other unary operators do.
    tc.assertEqual(canon_guarantee('G (SUM[i IN {0, 1}] i)'),
                   'G (SUM[i IN {0, 1}] i)')
finally:
    os.unlink(filename)
