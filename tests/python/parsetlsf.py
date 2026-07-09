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
import spot
from unittest import TestCase
tc = TestCase()


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

# chomp.tlsf, a real-world benchmark, is embedded here so that the
# round-trip and translation fixtures below do not depend on a copy
# of the file living at the top level of the source tree.
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

filename = 'parsetlsf.tlsf'
with open(filename, 'w') as f:
    f.write(contents)

try:
    parsed = spot.parse_tlsf(filename)
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
    # canonical printed form instead.  INITIALLY/PRESET/REQUIRE/ASSERT
    # are empty and GUARANTEE holds 2 formulas.
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

    with open(filename, 'w') as f:
        f.write(canonical)
    parsed2 = spot.parse_tlsf(filename)
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
    # whose inputs list mirrors those names in first-use order.
    res = spot.tlsf_to_ltl(parsed)
    tc.assertTrue(bool(res.full_formula),
                  "tlsf_to_ltl returned a null formula")
    fstr = str(res.full_formula)
    tc.assertIn('request_0', fstr)
    tc.assertIn('grant_0',  fstr)
    tc.assertIn('request_1', fstr)
    tc.assertIn('grant_1',  fstr)
    tc.assertEqual(list(res.inputs),
                   ['request_0', 'grant_0', 'request_1', 'grant_1'])
    tc.assertEqual(list(res.outputs), [])
    # Errors are surfaced on the parsed AST, not on the result.
    tc.assertFalse(parsed.errors,
                   f"errors: {[(e.first, e.second) for e in parsed.errors]}")
    # tlsf_translation_result carries one LTL formula per MAIN
    # section plus the composed full_formula.  Only GUARANTEE is
    # non-empty here: every other section folds to true, and the
    # composed formula is (semantically) just that guarantee.
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
    with open(filename, 'w') as f:
        f.write("INFO {} GLOBAL {} MAIN {}\n")
    empty = spot.parse_tlsf(filename)
    tc.assertFalse(empty.errors)
    tc.assertEqual(empty.title, "")
    tc.assertEqual(list(empty.inputs), [])
    tc.assertEqual(list(empty.outputs), [])
    empty_canon = spot.ostringstream()
    spot.tlsf_print(empty_canon, empty)
    tc.assertEqual(formulas_in_section(empty_canon.str(), 'GUARANTEE'),
                   [])

    # Bogus file.
    bogus = spot.parse_tlsf("/nonexistent/path.tlsf")
    tc.assertTrue(bogus.errors)

    # Malformed file.
    with open(filename, 'w') as f:
        f.write("INFO { TITLE: \"oops\"\n")
    broken = spot.parse_tlsf(filename)
    tc.assertTrue(broken.errors)

    # TRANSITIONS is not a TLSF section and must not be accepted as
    # a Spot-specific extension.
    with open(filename, 'w') as f:
        f.write("INFO {} GLOBAL {} MAIN { TRANSITIONS { a; } }\\n")
    transitions = spot.parse_tlsf(filename)
    tc.assertTrue(
        transitions.errors,
        "TRANSITIONS must be rejected as a non-TLSF extension")
    # Second spec exercising bool/mixed-binary + quantifier bodies.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a[2]; }\n"
            "  OUTPUTS { b[2]; }\n"
            "  REQUIRE {\n"
            "    G((!a[0]) || (b[0] -> F a[1]));\n"
            "    &&[N - 1] (b[i] || !b[i + 1]);\n"
            "  }\n"
            "}\n")
    val = spot.parse_tlsf(filename)
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
    tc.assertIn("&&[N - 1]", can2)
    # Round-trip: re-parse the canonical and verify the second
    # deparse matches the first (idempotence).
    with open(filename, 'w') as f:
        f.write(can2)
    val2 = spot.parse_tlsf(filename)
    tc.assertFalse(val2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, val2)
    can3 = ostr.str()
    tc.assertEqual(can3, can2)

    # Third spec exercising the associativity-aware BinaryOp wrap
    # (right-assoc LHS, right-assoc RHS interplay, cross-precedence,
    # and quantifier under BinaryOp).  Each line is deparsed and
    # re-parsed; deparse-on-deparse must be idempotent.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a; b; c; p; q; }\n"
            "  ASSERT {\n"
            # Right-assoc -> : re-derives same shape.
            "    a -> b -> c;\n"
            # Tighter LHS (&& inside -> LHS) needs no wrap.
            "    a && b -> c;\n"
            # Tighter RHS (&& inside -> RHS) needs no wrap.
            "    a -> b && c;\n"
            # Quantifier body extends with -> (bison `%prec "<->>"`).
            "    &&[N - 1] p -> q;\n"
            # Force-source paren preserved through round-trip.
            "    (a -> b) -> c;\n"
            # Left-assoc parent with looser-precedence RHS: emitted as
            # `(b -> c)` via the BinaryOp parenthesized branch.
            "    a && (b -> c);\n"
            "  }\n"
            "}\n")
    assoc = spot.parse_tlsf(filename)
    tc.assertFalse(assoc.errors,
                   f"errors: {[(e.first, e.second) for e in assoc.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, assoc)
    can_ass = ostr.str()
    with open(filename, 'w') as f:
        f.write(can_ass)
    assoc2 = spot.parse_tlsf(filename)
    tc.assertFalse(assoc2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, assoc2)
    can_ass2 = ostr.str()
    tc.assertEqual(can_ass2, can_ass)

    # Precedence follows Table 1 of TLSF v1.2.  In particular, U and W
    # are separate right-associative tiers, R is a lower left-associative
    # tier, division/modulo are right-associative and weaker than MUL,
    # and quantified Boolean operators share the unary-LTL tier.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS { a; b; c; d; e; f; g; h; i; j; }\n"
            "  ASSERT {\n"
            "    a U b W c;\n"
            "    a R b U c;\n"
            "    a / b / c;\n"
            "    &&[N - 1] p -> q;\n"
            "    a -> b <-> c;\n"
            "    a || b && c;\n"
            "  }\n"
            "}\n")
    precedence = spot.parse_tlsf(filename)
    tc.assertFalse(precedence.errors,
                   f"precedence fixture must parse cleanly; "
                   f"errors: {[(e.first, e.second) for e in precedence.errors]}"
                   )
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, precedence)
    can_prec = ostr.str()
    # These spellings are unambiguous under TLSF v1.2's precedence
    # and associativity rules and must remain stable through a
    # print/parse/print round-trip.
    tc.assertIn("a U b W c;", can_prec)
    tc.assertIn("a R b U c;", can_prec)
    tc.assertIn("a / b / c;", can_prec)
    tc.assertIn("&&[N - 1] p -> q;", can_prec)
    tc.assertIn("a -> b <-> c;", can_prec)
    tc.assertIn("a || b && c;", can_prec)
    with open(filename, 'w') as f:
        f.write(can_prec)
    precedence2 = spot.parse_tlsf(filename)
    tc.assertFalse(precedence2.errors)
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, precedence2)
    tc.assertEqual(ostr.str(), can_prec)

    # Fourth spec: Finite semantics + bus inputs/outputs in
    # MAIN, with `X[!] ack[0]` in GUARANTEE.  The TLSF lexer
    # accepts `X[!]` (only) as the LTLf-style "strong" next
    # operator (spot/parsetlsf/scantlsf.ll: token rule
    # `"X[!]"  return token::LTL_STRONG_NEXT`).  The bare
    # `X!` is NOT a token: it parses as the sequence `X !`
    # (next + bang), and Spot's formula printer renders the
    # resulting `X(NOT p)` as `X!p` -- a textual coincidence
    # with the old token spelling.  This fixture exercises
    # the dispatch-by-semantics Finite branch (X strong
    # accepted, emitted as strong_X) along with bus
    # flattening on both sides: `event[N]` -> `event_0/1`,
    # `ack[N]` -> `ack_0/1`.
    with open(filename, 'w') as f:
        f.write(
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
    finite = spot.parse_tlsf(filename)
    tc.assertFalse(finite.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in finite.errors]}")
    tc.assertEqual(finite.semantics, spot.tlsf_semantics_MealyFinite)
    tc.assertEqual(finite.target, spot.tlsf_target_Mealy)
    tc.assertEqual(list(finite.inputs), ["event"])
    tc.assertEqual(list(finite.outputs), ["ack"])
    # The GUARANTEE section carries the single X[!]-formula; visible
    # through the canonical print since parsed_tlsf keeps its AST
    # opaque.
    finite_canon = spot.ostringstream()
    spot.tlsf_print(finite_canon, finite)
    tc.assertEqual(len(formulas_in_section(finite_canon.str(),
                                           'GUARANTEE')), 1)

    # Translate.  Finite semantics accepts X strong next
    # and emits spot::formula::strong_X.  Spot's default
    # `repr` and the 'spot' printer both render strong_X
    # as `X[!]`, distinguishable from the weak `X` of
    # plain LTL; assert both renderings agree.
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

    # Bus-flattened inputs/outputs (orthogonal to semantics):
    # the body's four BusRef occurrences (ack[0], ack[1],
    # event[0], event[1]) flatten the buses into indexed APs,
    # recorded in first-use order on res_fin.inputs/outputs.
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
        with open(filename, 'w') as f:
            f.write("INFO { SEMANTICS: " + semantics_text + " }\n"
                    "GLOBAL {} MAIN { OUTPUTS { done; } }\n")
        ordered = spot.parse_tlsf(filename)
        tc.assertFalse(ordered.errors,
                       f"{semantics_text} should parse cleanly; got: "
                       f"{[(e.first, e.second) for e in ordered.errors]}")
        tc.assertEqual(ordered.semantics, expected_semantics)

    # Non-finite semantics must reject strong next, while finite
    # semantics preserves it as Spot's strong_X operator.
    with open(filename, 'w') as f:
        f.write("INFO { SEMANTICS: Mealy }\n"
                "GLOBAL {} MAIN { OUTPUTS { done; }\n"
                "  GUARANTEE { X[!] done; } }\n")
    nonfinite = spot.parse_tlsf(filename)
    tc.assertFalse(nonfinite.errors)
    nonfinite_errors = spot.parse_aut_error_list()
    nonfinite_result = spot.tlsf_to_ltl(
        nonfinite, spot.tlsf_translator_options(), nonfinite_errors)
    tc.assertFalse(bool(nonfinite_result.full_formula))
    tc.assertTrue(any("requires finite semantics" in e.second
                      for e in nonfinite_errors),
                  f"expected finite-semantics diagnostic; got: "
                  f"{[e.second for e in nonfinite_errors]}")

    # Fifth spec: regression pin for the dropped `X!` token.
    # Source `X!done` falls through to `X` (next) + `!` (not)
    # + `done` (AP) and translates to `X(!done)`, NOT strong-next.
    # Spot's default printer renders this as `X!done` -- the
    # textual match is coincidental but a useful confirmation
    # that the operator kind is unchanged from a plain weak-X
    # wrap of NOT.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  OUTPUTS { done; }\n"
            "  GUARANTEE { X! done; }\n"
            "}\n")
    weak = spot.parse_tlsf(filename)
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

    # Sixth spec: PARAMETERS end-to-end.
    # PARAMETERS { N = 2; } is resolved at translate time.  The
    # body uses `event[N - 1]` so the resolved value of N
    # participates directly in the bus index -- a body that only
    # referenced event[0] / event[1] would not exercise PARAMETERS
    # resolution.  Translating once with no override (declared
    # N=2 -> event_1) and once with a translate-time override
    # (N=4 -> event_3) pins the layering code in translate.cc:
    # declared defaults first, then opts.overrides on top.
    with open(filename, 'w') as f:
        f.write(
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
    param = spot.parse_tlsf(filename)
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
    tc.assertEqual(list(res_decl.inputs), ["event_1"])
    tc.assertEqual(list(res_decl.outputs), [])

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
                   f"override N=4 must NOT produce 'event_2'; "
                   f"got: {fstr_ovr}")
    tc.assertEqual(list(res_ovr.inputs), ["event_3"])
    tc.assertEqual(list(res_ovr.outputs), [])

    # Seventh spec: parser-time overrides are mirrored onto
    # parsed_tlsf::overrides, per public.hh's "mirrored here for
    # documentation and round-trip printing" contract.  This pins
    # the bug-fix in public.cc::populate_parsed which previously
    # did NOT copy opts.overrides onto out.overrides.  The spec
    # body itself is intentionally simple (no PARAMETERS block,
    # no buses) so the only thing under test is the override
    # mirror into the public.hh struct.
    with open(filename, 'w') as f:
        f.write(
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
            "}\n")
    p_opts = spot.tlsf_parser_options()
    p_opts.overrides["N"] = 7
    parsed7 = spot.parse_tlsf(filename, p_opts)
    tc.assertFalse(parsed7.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in parsed7.errors]}")
    # Pin the bug-fix: parser-time override is now mirrored.
    # Use subscript (not .get()) because SWIG's std::map<string,int>
    # proxy exposes __getitem__ and __iter__ but not the .get method.
    tc.assertEqual(parsed7.overrides["N"], 7,
                   f"expected N=7 in parsed.overrides; got: "
                   f"{parsed7.overrides['N']}")
    # Defense-in-depth: keys should be exactly what the parser
    # caller passed in (no prior fixture data leaks through).
    keys = list(parsed7.overrides)
    tc.assertEqual(keys, ["N"],
                   f"expected keys=['N']; got: {keys}")

    # Eighth spec: comparison-chain and nested quantifier ranges.
    # The outer range binds i and the inner range binds j.  Both
    # variables are used in the bus index, so a single implicit loop
    # binding would either leave j unresolved or repeatedly use i.
    with open(filename, 'w') as f:
        f.write(
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
    ranges = spot.parse_tlsf(filename)
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
                   {"a_1", "a_2", "a_3", "a_4"})

    # Ninth spec: arithmetic parameter expressions.  B refers to A,
    # and B is used both as a bus size and as a quantifier upper bound.
    # This exercises expression parsing, recursive parameter lookup,
    # and the same evaluator in both integer contexts.
    with open(filename, 'w') as f:
        f.write(
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
    arithmetic = spot.parse_tlsf(filename)
    tc.assertFalse(arithmetic.errors,
                   f"arithmetic parameters must parse cleanly; "
                   f"errors: {[(e.first, e.second) for e in arithmetic.errors]}"
                   )
    arithmetic_result = spot.tlsf_to_ltl(arithmetic)
    tc.assertTrue(bool(arithmetic_result.full_formula),
                  "arithmetic parameters must translate")
    tc.assertEqual(set(arithmetic_result.inputs),
                   {"b_0", "b_1", "b_2", "b_3", "b_4", "b_5"})

    # Tenth spec: parser-time overrides flow into translation.  The
    # translation-time value remains the more specific override.
    parser_options = spot.tlsf_parser_options()
    parser_options.overrides["N"] = 4
    # Reuse the arithmetic fixture's A/B names to make sure the
    # parser override is not accidentally treated as a declaration.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN { INPUTS { a[8]; }\n"
            "  GUARANTEE { &&[0 <= i < N] a[i]; } }\n")
    parsed_override = spot.parse_tlsf(filename, parser_options)
    tc.assertFalse(parsed_override.errors)
    parser_result = spot.tlsf_to_ltl(parsed_override)
    tc.assertEqual(set(parser_result.inputs),
                   {"a_0", "a_1", "a_2", "a_3"})
    translator_options = spot.tlsf_translator_options()
    translator_options.overrides["N"] = 2
    translator_result = spot.tlsf_to_ltl(parsed_override, translator_options)
    tc.assertEqual(set(translator_result.inputs), {"a_0", "a_1"})

    # Eleventh spec: DEFINITIONS expansion.
    # Defines Gplus(x) = G x and verifies that user-defined function
    # calls are expanded: the body is a parsed tlsf_expr_ptr AST node
    # (no text / STRING fallback — TLSF v1.2 forbids STRING RHS for
    # definition bodies; syfco's
    # spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs
    # `reminderParser` parses only `many1 exprParser`).  Expansion
    # uses translator::subst_arg -- a structural clone-and-replace
    # -- so the formal argument x is replaced with the actual
    # argument expression, and the resulting formula is composed into
    # the surrounding context.  Gplus(a) and Gplus(b) translate to
    # G(a) and G(b), so the rendered formula must contain both APs and
    # the G operator.
    with open(filename, 'w') as f:
        f.write(
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
    deftest = spot.parse_tlsf(filename)
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

    # Ninth spec: same-name definitions of different arity.  Two
    # definitions share the name `Both` -- one unary, one
    # binary.  TLSF v1.2 (and syfco's tArgs map keyed by symbol
    # name in spot/parsetlsf/refs/syfco/src/lib/Reader/Bindings.hs)
    # enforces "one symbol = one definition", so the Bison
    # `definition:` action (spot/parsetlsf/parsetlsf.yy) detects
    # the duplicate via `def_first_loc` and emits BOTH
    # diagnostics -- the full strings are
    # "definition '<name>' is shadowed by a later re-definition"
    # (anchored at the FIRST definition's location) and
    # "definition '<name>' is already defined" (anchored at
    # the SECOND location).  The substring asserts in this
    # spec's `tc.assertTrue(any(...))` calls key on the
    # unique substrings "shadowed" and "already defined"
    # (verbatim quoted here so a future diagnostic-wording
    # change cannot drift past the pin silently), and the
    # second body is dropped.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            # NOTE: TLSF distinguishes two comma/space conventions:
            #   - `arg_list` (definition formal params, parsetlsf.yy)
            #     is `arg_list: arg_list IDENTIFIER` -- SPACE-
            #     separated, no commas.  Mirror the convention used
            #     elsewhere in this file (`Pos(grid i j)` at the
            #     top fixture).
            #   - `arg_expr_list` (function-call actuals) IS
            #     comma-separated (`MIN(a, b, c)`-style).  See the
            #     call site `Both(b, c)` below for the comma form.
            # The comma-separated form on the binary def: the new
            # `arg_list` grammar (parsetlsf.yy) requires COMMAs in
            # definition formal-arg lists, mirroring syfco's
            # `commaSep tokenparser` parser in
            # spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs.
            # The previous "Both(x y)" would now hit a Bison
            # syntax error rather than a definition duplicate.
            '    Both(x) = G x;\n'
            '    Both(x, y) = G x && y;\n'
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; b; c; }\n"
            "  OUTPUTS { ok; }\n"
            "  GUARANTEE { G a; }\n"
            "}\n")
    # Negative test: TLSF enforces "one symbol = one definition"
    # (arXiv 1604.02284 §6.2, syfco's tArgs map keyed by symbol
    # name in spot/parsetlsf/refs/syfco/src/lib/Reader/Bindings.hs);
    # the new Bison semantic action for `definition:` mirrors that
    # by emitting BOTH diagnostics on a duplicate-name pair -- one
    # at the FIRST definition's location ("shadowed") and one at
    # the SECOND definition's location ("already defined") --
    # and the second body is dropped.
    arity = spot.parse_tlsf(filename)
    tc.assertTrue(arity.errors,
                  f"parse_tlsf should reject same-name "
                  f"DEFINITIONS with a diagnostic; got none")
    err_strs = [e.second for e in arity.errors]
    tc.assertTrue(any("already defined" in s for s in err_strs),
                  f"expected an 'already defined' diagnostic at "
                  f"the second definition's location; got: {err_strs}")
    tc.assertTrue(any("shadowed" in s for s in err_strs),
                  f"expected a 'shadowed' diagnostic at the first "
                  f"definition's location; got: {err_strs}")
    # Exactly two diagnostics are expected -- one per occurrence --
    # but we deliberately do not pin the count here, since the
    # grammar's `error SEMICOLON` recovery rules could emit extra
    # "syntax error" entries on future grammar regressions, and the
    # pin matters less than the presence of the two key substrings.

    # Tenth spec: translator-side arity-mismatch diagnostic.
    # This pins the explicit `def.args.size() != e.children.size()`
    # branch in translate.cc's App case (spot/parsetlsf/translate.cc)
    # which, under the new "one symbol = one definition" rule, can
    # no longer be triggered by a duplicate-name def (that path is
    # caught at parse time, exercise by fixture 9 above); instead,
    # the mismatch comes from a call site that supplies the wrong
    # number of actual arguments.  `Bar(x)` is unique, so the parser
    # accepts the spec; the translator then sets failed_ on the
    # arity-mismatch diagnostic and emits a null formula.
    with open(filename, 'w') as f:
        f.write(
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
    mismatch = spot.parse_tlsf(filename)
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
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { a[0] && a[0] && a[N - 1]; }\n"
            "}\n")
    valid_bus = spot.parse_tlsf(filename)
    tc.assertFalse(valid_bus.errors)
    valid_bus_errors = spot.parse_aut_error_list()
    valid_bus_result = spot.tlsf_to_ltl(
        valid_bus, spot.tlsf_translator_options(), valid_bus_errors)
    tc.assertTrue(bool(valid_bus_result.full_formula))
    tc.assertEqual(list(valid_bus_result.inputs), ["a_0", "a_1"])
    tc.assertFalse(valid_bus_errors)

    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { a[N]; }\n"
            "}\n")
    invalid_index = spot.parse_tlsf(filename)
    tc.assertFalse(invalid_index.errors)
    invalid_index_errors = spot.parse_aut_error_list()
    invalid_index_result = spot.tlsf_to_ltl(
        invalid_index, spot.tlsf_translator_options(), invalid_index_errors)
    tc.assertFalse(bool(invalid_index_result.full_formula))
    tc.assertTrue(any("outside bus 'a'" in e.second
                      for e in invalid_index_errors),
                  f"expected out-of-range diagnostic; got: "
                  f"{[e.second for e in invalid_index_errors]}")

    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; scalar; }\n"
            "  GUARANTEE { scalar[0]; }\n"
            "}\n")
    scalar_index = spot.parse_tlsf(filename)
    tc.assertFalse(scalar_index.errors)
    scalar_index_errors = spot.parse_aut_error_list()
    scalar_index_result = spot.tlsf_to_ltl(
        scalar_index, spot.tlsf_translator_options(), scalar_index_errors)
    tc.assertFalse(bool(scalar_index_result.full_formula))
    tc.assertTrue(any("scalar AP 'scalar'" in e.second
                      for e in scalar_index_errors),
                  f"expected scalar-index diagnostic; got: "
                  f"{[e.second for e in scalar_index_errors]}")

    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL { PARAMETERS { N = 2; } }\n"
            "MAIN {\n"
            "  INPUTS { a[N]; }\n"
            "  GUARANTEE { a[N - 3]; }\n"
            "}\n")
    negative_index = spot.parse_tlsf(filename)
    tc.assertFalse(negative_index.errors)
    negative_index_errors = spot.parse_aut_error_list()
    negative_index_result = spot.tlsf_to_ltl(
        negative_index, spot.tlsf_translator_options(), negative_index_errors)
    tc.assertFalse(bool(negative_index_result.full_formula))
    tc.assertTrue(any("outside bus 'a'" in e.second
                      for e in negative_index_errors),
                  f"expected negative-index diagnostic; got: "
                  f"{[e.second for e in negative_index_errors]}")

    # Eleventh fixture: round-trip regression for chomp.tlsf, whose
    # content is embedded above in chomp_contents and written to the
    # local `filename`.  Pins the clean-parse baseline: chomp.tlsf
    # parses with zero errors, the canonical form deparses via
    # tlsf_print, the canonical re-parses to the same AST shape, and
    # deparse-on-deparse is idempotent.  A future regression that
    # introduces any parse error in chomp.tlsf -- whether from
    # a grammar change, a deparser divergence, or a token-
    # stream change -- surfaces as a `len(errs) != 0` failure
    # here.  The fixture additionally checks that round-tripping
    # the canonical form does not introduce new diagnostics
    # (catches a deparser producing an unparseable form).
    #
    # chomp.tlsf omits trailing `;` on its INFO items, which is
    # the canonical form: Spot matches syfco exactly, so `;`
    # after any INFO item is a SYNTAX ERROR.  Verified
    # empirically against `syfco 1.2.1.2` (the canonical TLSF
    # reference parser) on variants of the embedded fixture --
    # the no-`;` canonical exits 0, and every variant that adds
    # `;` to TITLE, DESCRIPTION, SEMANTICS, or TARGET exits 1
    # with `unexpected ";" expecting TITLE/DESCRIPTION/SEMANTICS/
    # TARGET/TAGS or "}"`.  See spot/parsetlsf/parsetlsf.yy for
    # the grammar rationale (cites syfco's `infoContentParser`
    # in spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Info.hs).
    with open(filename, 'w') as f:
        f.write(chomp_contents)
    parsed_chomp = spot.parse_tlsf(filename)
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

    # Round-trip: tlsf_print deparse, re-parse, then idempotence.
    # The canonical form must re-parse to zero errors, the
    # deparser must be deterministic (std::vector iteration
    # only -- no unordered_map/set), and the canonical form
    # must be byte-identical to a re-deparse of the round-
    # tripped form.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_chomp)
    canonical = ostr.str()
    # Structural pins: section skeletons always appear in the
    # canonical form even though comments and blank lines are
    # not preserved.
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
    with open(filename, 'w') as f:
        f.write(canonical)
    parsed_rt = spot.parse_tlsf(filename)
    errs_rt = list(parsed_rt.errors)
    tc.assertFalse(
        errs_rt,
        f'chomp.tlsf round-trip (parse+deparse+reparse) should '
        f'produce 0 errors; got {len(errs_rt)}: '
        f'{[(e.first, e.second) for e in errs_rt]!r}.  A '
        f'non-zero error count means the deparser emitted a '
        f'form the parser cannot ingest -- a deparser/'
        f'grammar divergence this fixture must catch.')
    # Idempotence: tlsf_print walks std::vector containers in
    # source order (no unordered_map/set iteration), so a
    # second deparse must produce the same canonical form.
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
    # chomp.tlsf is the embedded copy written to `filename`;
    # tictactoe.tlsf and scutella1.tlsf are exercised when present
    # at the top level of the source tree.
    with open(filename, 'w') as f:
        f.write(chomp_contents)
    benchmark_files = [('chomp.tlsf', filename)]
    for benchmark_name in ('tictactoe.tlsf', 'scutella1.tlsf'):
        benchmark_path = os.path.join(os.path.dirname(__file__),
                                      '..', '..', benchmark_name)
        if os.path.exists(benchmark_path):
            benchmark_files.append((benchmark_name, benchmark_path))
    for benchmark_name, benchmark_path in benchmark_files:
        benchmark = spot.parse_tlsf(benchmark_path)
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

    # Twelfth spec: INFO TAGS.  Tests the new Tier-1 TAGS keyword
    # (syfco 1.2.1.2 reference parser, refs/.../Reader/Parser/Info.hs).
    # TAGS takes a comma-separated IDENTIFIER list.  Round-trips
    # through tlsf_print -> parse_tlsf without diagnostic drift.
    with open(filename, 'w') as f:
        f.write(
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
    tagged = spot.parse_tlsf(filename)
    tc.assertFalse(tagged.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in tagged.errors]}")
    tc.assertEqual(list(tagged.tags), ["arbiter", "synth"],
                   f"expected tags ['arbiter','synth']; got: "
                   f"{list(tagged.tags)}")
    # Note: `parsed.ast` is not exposed at all (the AST is an opaque
    # private member of parsed_tlsf); the tags are mirrored onto
    # `parsed.tags` by `spot::populate_parsed` (public.cc) where
    # `out.tags = res.spec->tags;` -- the Python-side test pins
    # `parsed.tags` directly, which matches the tags stored in the
    # private AST.
    # Round-trip: deparse + reparse yields the same tags (and no
    # new diagnostics, which would indicate a parser/deparser
    # grammar divergence on the comma-separated list).
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, tagged)
    can_tags = ostr.str()
    tc.assertIn("TAGS:", can_tags,
                f"deparser should emit TAGS: line; got: {can_tags}")
    with open(filename, 'w') as f:
        f.write(can_tags)
    tagged2 = spot.parse_tlsf(filename)
    tc.assertFalse(tagged2.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in tagged2.errors]}")
    tc.assertEqual(list(tagged2.tags), list(tagged.tags),
                   f"round-tripped tags should match source; "
                   f"got: {list(tagged2.tags)}")
    # TAGS is OPTIONAL: a spec with no TAGS line yields the empty
    # vector (not an error).  Pins the option-C alignment with
    # syfco, which allows TAGS to be entirely omitted.
    with open(filename, 'w') as f:
        f.write(
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
    untagged = spot.parse_tlsf(filename)
    tc.assertFalse(untagged.errors,
                   f"TAGS omission must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in untagged.errors]}")
    tc.assertEqual(list(untagged.tags), [])

    # Thirteenth spec: plural MAIN keywords.  Tests the new
    # MAIN/Require/Assert/Guarantee/Assume plural-alias Tier-1
    # acceptance -- REQUIREMENTS, INVARIANTS, GUARANTEES, ASSUME,
    # ASSUMPTIONS all point to the canonical body fields.  Each
    # plural form produces the same require_body/assert_body/
    # guarantee_body/assumptions_body shape as its singular
    # counterpart; this fixture verifies that every plural form
    # parses without diagnostics and that the formulas reach the
    # right body vector.  (syfco reference:
    # refs/.../Reader/Parser/Component.hs componentContentParser,
    # which dispatches REQUIRE/REQUIREMENTS to the same
    # `requirements` field, etc.)
    with open(filename, 'w') as f:
        f.write(
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
            # ASSUME + ASSUMPTIONS, both populating
            # assumptions_body (newly added field).
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
    plurals = spot.parse_tlsf(filename)
    tc.assertFalse(plurals.errors,
                   f"plural MAIN keywords must parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in plurals.errors]}")
    # The plural aliases must funnel into the same MAIN section as
    # their singular counterparts.  parsed_tlsf no longer mirrors the
    # bodies, so the per-section shapes are read back from the
    # canonical print (which is generated from the private AST):
    # ASSUME + ASSUMPTIONS -> 2 formulas under ASSUME;
    # REQUIREMENTS -> 1 under REQUIRE; INVARIANTS -> 1 under ASSERT;
    # GUARANTEES -> 1 under GUARANTEE.
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
    # Cross-check that mixed singular + plural for the SAME body
    # type both funnel into the same vector.  This is what
    # doesn't work without the `assert_body <- ASSERT |
    # INVARIANTS` rule grouping on a shared `res.current_body`
    # field.
    with open(filename, 'w') as f:
        f.write(
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
    mixed = spot.parse_tlsf(filename)
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

    # Fourteenth spec: quantifier range `l..hi` form.  Tests the
    # new Tier-2 productions `&& [ lo DOTDOT hi ] body` /
    # `|| [ lo DOTDOT hi ] body` (reuses the existing DOTDOT
    # token; the bound is a synthesised SetRange AST node so the
    # deparser prints `&& [{lo..hi}] body`).  Pin the deparse
    # shape explicitly: the synthesised {..} braces are part of
    # the round-trip contract.
    with open(filename, 'w') as f:
        f.write(
            "INFO {\n"
            "  TITLE:       \"quant range\"\n"
            "  DESCRIPTION: \"fixture 14: &&[lo..hi]\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 4; }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { a; }\n"
            "  OUTPUTS { ok; }\n"
            # Both spells parse to the same quantifier AST kind
            # (SetRange bound).  The un-braced source `&& [1..5] p`
            # is normalised by the deparser to `&&[{1..5}] p`,
            # which round-trips as the same shape (idempotent).
            "  GUARANTEE {\n"
            "    &&[1..5] a;\n"
            "    ||[0..3] a;\n"
            "  }\n"
            "}\n")
    qrange = spot.parse_tlsf(filename)
    tc.assertFalse(qrange.errors,
                   f"quantifier range MUST parse cleanly; "
                   f"errors: "
                   f"{[(e.first, e.second) for e in qrange.errors]}")
    # Round-trip emits SetRange with braces: spot's deparser
    # unifies `&&[1..5]` (un-braced source) and `&&[{1..5}]`
    # (already-braced source) to the same AST shape; assert
    # both source forms lead to the same canonical string.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, qrange)
    can_qr = ostr.str()
    tc.assertEqual(len(formulas_in_section(can_qr, 'GUARANTEE')), 2,
                   "expected 2 quantifier formulas in GUARANTEE")
    tc.assertIn("&&[{1..5}] a", can_qr,
                f"expected '&&[{{1..5}}] a' canonical form; "
                f"got: {can_qr}")
    tc.assertIn("||[{0..3}] a", can_qr,
                f"expected '||[{{0..3}}] a' canonical form; "
                f"got: {can_qr}")
    # Idempotence: reparse the canonical and re-deparse.
    with open(filename, 'w') as f:
        f.write(can_qr)
    qrange2 = spot.parse_tlsf(filename)
    tc.assertFalse(qrange2.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in qrange2.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, qrange2)
    can_qr2 = ostr.str()
    tc.assertEqual(can_qr2, can_qr,
                   f"round-trip must be idempotent; "
                   f"first:\n{can_qr}\nsecond:\n{can_qr2}")
    # Negative cross-check: the SET-EXPLICIT form already
    # accepted by Spot, `&& [{1,2,3}] body`, still parses.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {}\n"
            "MAIN {\n"
            "  INPUTS  { a; }\n"
            "  GUARANTEE { && [{1, 2, 3}] a; }\n"
            "}\n")
    set_explicit = spot.parse_tlsf(filename)
    tc.assertFalse(set_explicit.errors,
                   f"set-explicit form (regression pin) must stay "
                   f"clean; got: "
                   f"{[(e.first, e.second) for e in set_explicit.errors]}")

    # Fifteenth spec: TLSF v1.2 quantifier bounds must introduce an
    # explicit iteration variable, either via a comparison chain
    # (`&&[0 <= i < N]`) or via membership (`&&[i IN {0, 2, 4}]`).
    # Set-valued and count-valued bounds that omit the variable -- set
    # literals, ranges, CUP/CAP/SETMINUS combinations, and bare counts
    # -- parse (for round-trip printing) but are diagnosed at
    # translation as invalid TLSF, instead of silently iterating over
    # an implicit `i`.
    set_cases = [
        "&&[{0, 2, 4}] a[i];",
        "&&[{1..3}] a[i];",
        "&&[CUP[{0}, {2, 4}]] a[i];",
        "&&[CAP[{0, 2}, {2, 4}]] a[i];",
        "&&[SETMINUS[{0, 2, 4}, {2}]] a[i];",
    ]
    set_operator_case = None
    for set_body in set_cases:
        with open(filename, 'w') as f:
            f.write("INFO {}\n"
                    "GLOBAL {}\n"
                    "MAIN { INPUTS { a[5]; }\n"
                    "  GUARANTEE { " + set_body + " } }\n")
        set_case = spot.parse_tlsf(filename)
        tc.assertFalse(set_case.errors,
                       f"set domain must parse cleanly; got: "
                       f"{[(e.first, e.second) for e in set_case.errors]}")
        set_errors = spot.parse_aut_error_list()
        set_result = spot.tlsf_to_ltl(
            set_case, spot.tlsf_translator_options(), set_errors)
        tc.assertFalse(bool(set_result.full_formula),
                       f"variable-less set bound must be diagnosed: "
                       f"{set_body}")
        set_messages = [e.second for e in set_errors]
        tc.assertTrue(any("iteration variable" in message
                          for message in set_messages),
                      f"missing iteration-variable diagnostic for "
                      f"{set_body}; got: {set_messages}")
        if set_body.startswith("&&[CUP["):
            set_operator_case = set_case

    # Empty sets as quantifier bounds are likewise variable-less and
    # must be diagnosed, not folded to the empty-domain algebra
    # identities.  They still parse as a real SetExplicit node.
    with open(filename, 'w') as f:
        f.write("INFO {}\nGLOBAL {}\nMAIN { INPUTS { a; }\n"
                "  GUARANTEE { &&[{}] a; ||[{}] a; } }\n")
    empty_set = spot.parse_tlsf(filename)
    tc.assertFalse(empty_set.errors,
                   f"empty set must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in empty_set.errors]}")
    empty_set_errors = spot.parse_aut_error_list()
    empty_set_result = spot.tlsf_to_ltl(
        empty_set, spot.tlsf_translator_options(), empty_set_errors)
    tc.assertFalse(bool(empty_set_result.full_formula),
                   "variable-less empty-set quantifiers must be diagnosed")
    tc.assertTrue(any("iteration variable" in e.second
                      for e in empty_set_errors),
                  f"missing iteration-variable diagnostic for empty sets; "
                  f"got: {[e.second for e in empty_set_errors]}")

    # Membership bounds DO carry an explicit variable and must
    # translate.  The set on the right may be a literal, a range, or a
    # set-algebra combination; the body is expanded over its elements
    # in set order.
    with open(filename, 'w') as f:
        f.write("INFO {}\nGLOBAL {}\nMAIN {\n"
                "  INPUTS { a[5]; b[3]; }\n"
                "  GUARANTEE {\n"
                "    &&[i IN {0, 2, 4}] a[i];\n"
                "    ||[j IN {1..2}] b[j];\n"
                "    &&[k IN CUP[{0}, {3}]] a[k];\n"
                "  }\n}\n")
    membership = spot.parse_tlsf(filename)
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
    tc.assertEqual(set(membership_result.inputs),
                   {"a_0", "a_2", "a_3", "a_4", "b_1", "b_2"})
    # A membership bound must round-trip through the deparser.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, membership)
    membership_canonical = ostr.str()
    tc.assertIn("&&[i IN {0, 2, 4}] a[i]", membership_canonical,
                f"membership bound must stay printable; got: "
                f"{membership_canonical}")
    with open(filename, 'w') as f:
        f.write(membership_canonical)
    membership_rt = spot.parse_tlsf(filename)
    tc.assertFalse(membership_rt.errors,
                   f"membership canonical form must reparse cleanly; got: "
                   f"{[(e.first, e.second) for e in membership_rt.errors]}")

    # Count bounds (`&&[3]`) are the other variable-less legacy form
    # and must be diagnosed, even when the body mentions `i`.
    with open(filename, 'w') as f:
        f.write("INFO {}\nGLOBAL {}\nMAIN {\n"
                "  GUARANTEE {\n"
                "    &&[3] (i IN {0, 2});\n"
                "    ||[3] (i IN {0, 2});\n"
                "  }\n}\n")
    membership = spot.parse_tlsf(filename)
    tc.assertFalse(membership.errors,
                   f"membership must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in membership.errors]}")
    membership_errors = spot.parse_aut_error_list()
    membership_result = spot.tlsf_to_ltl(
        membership, spot.tlsf_translator_options(), membership_errors)
    tc.assertFalse(bool(membership_result.full_formula),
                   "count-bound quantifier must be diagnosed")
    tc.assertTrue(any("iteration variable" in e.second
                      for e in membership_errors),
                  f"missing iteration-variable diagnostic; got: "
                  f"{[e.second for e in membership_errors]}")

    # Printer round-trip for the new prefix set-operator syntax.
    # Prefix CUP[...] is normalized to the canonical binary spelling
    # because the AST stores set algebra as BinaryOp nodes.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, set_operator_case)
    set_canonical = ostr.str()
    tc.assertIn(" CUP ", set_canonical,
                f"set algebra must remain printable; got: {set_canonical}")
    with open(filename, 'w') as f:
        f.write(set_canonical)
    set_roundtrip = spot.parse_tlsf(filename)
    tc.assertFalse(set_roundtrip.errors,
                   f"set canonical form must reparse cleanly; got: "
                   f"{[(e.first, e.second) for e in set_roundtrip.errors]}")

    # Seventeenth spec: textual SyFCo operator aliases.  These
    # aliases must lower to the same AST operators as punctuation and
    # must remain usable in integer, comparison, and quantifier
    # contexts.  Quantifier bounds must be comparison chains (TLSF v1.2
    # requires an explicit iteration variable), so the textual
    # comparison/quantifier aliases are exercised inside chains.
    with open(filename, 'w') as f:
        f.write(
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
    aliases = spot.parse_tlsf(filename)
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
    # Eighteenth spec: integer evaluator overflow and invalid
    # arithmetic.  Every case must diagnose instead of relying on
    # signed-overflow behavior from the C++ implementation.
    with open(filename, 'w') as f:
        f.write(
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
    overflow = spot.parse_tlsf(filename)
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

    # Literals that do not fit in a signed 64-bit integer must be
    # diagnosed at parse time, not silently truncated to 0.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "MAIN {\n"
            "  INPUTS { a[2]; }\n"
            "  GUARANTEE {\n"
            "    a[999999999999999999999999999];\n"
            "  }\n"
            "}\n")
    too_big = spot.parse_tlsf(filename)
    too_big_messages = [e.second for e in too_big.errors]
    tc.assertTrue(any("integer literal is too large" in message
                      for message in too_big_messages),
                  f"missing too-large literal diagnostic: "
                  f"{too_big_messages}")

    # Nineteenth spec: identifier letters `@` and `'`.  Tests
    # the new Tier-2 lexer extension
    # `[a-zA-Z_@][a-zA-Z0-9_@']*` matching syfco's
    # Reader/Parser/Data.hs `identStart` /
    # `identLetter` definitions.  `@` may lead an identifier
    # (`@foo`); `'` may appear inside (`o'biter`).
    with open(filename, 'w') as f:
        f.write(
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
    weird = spot.parse_tlsf(filename)
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
    # Sixteenth spec: enum declarations.  Tests the new
    # Tier-1#2 `enum` keyword in GLOBAL { DEFINITIONS { ... } }.
    # Format per syfco
    # (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs
    # enumParser): `enum Name = { Tag0:bits0, Tag1:bits1, ... };`
    # -- a comma-separated list of `Tag:bits` pairs.  The bits
    # width is the length of the first entry's bits string.
    # Pin: 1 enum, 1 regular def in DEFINITIONS, source order
    # of entries preserved, round-trip idempotent.
    with open(filename, 'w') as f:
        f.write(
            "INFO {\n"
            "  TITLE:       \"with enum\"\n"
            "  DESCRIPTION: \"fixture 16: enum keyword pin\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  PARAMETERS { N = 2; }\n"
            "  DEFINITIONS {\n"
            "    enum Color = {RED:00, GREEN:01, BLUE:10, BLACK:11};\n"
            "    Gplus(x) = G x;\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { request; }\n"
            "  OUTPUTS { grant; }\n"
            "  GUARANTEE { Gplus(request); }\n"
            "}\n")
    enum_test = spot.parse_tlsf(filename)
    tc.assertFalse(enum_test.errors,
                   f"parse_tlsf reported errors: "
                   f"{[(e.first, e.second) for e in enum_test.errors]}")
    # The enum declaration is only observable through the canonical
    # print (parsed_tlsf keeps its AST -- and the enumerations --
    # opaque).  The exact canonical line below pins the decl name,
    # the 4 entries, their order, and their bit strings.
    # Don't-care bit `*` is also accepted: re-declare an enum
    # whose first value uses `*` to verify the STAR branch.
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Sigs = {NONE:*, LOW:0, HIGH:1};\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G(p); }\n"
            "}\n")
    sigs = spot.parse_tlsf(filename)
    tc.assertFalse(sigs.errors,
                   f"don't-care bit must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in sigs.errors]}")
    # The `*` bit string is kept verbatim; observable through the
    # canonical print of the opaque AST.
    sigs_canon = spot.ostringstream()
    spot.tlsf_print(sigs_canon, sigs)
    tc.assertIn("enum Sigs = {NONE:*, LOW:0, HIGH:1};",
                sigs_canon.str(),
                "don't-care bits must round-trip verbatim")
    # Round-trip: deparse, re-parse, idempotent.
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, enum_test)
    can_enum = ostr.str()
    tc.assertIn("enum Color = {", can_enum,
                f"deparser should emit 'enum Color = {{'; got: "
                f"{can_enum}")
    tc.assertIn("RED:00", can_enum,
                f"deparser should emit 'RED:00'; got: {can_enum}")
    tc.assertIn("GREEN:01", can_enum,
                f"deparser should emit 'GREEN:01'; got: {can_enum}")
    tc.assertIn("BLUE:10", can_enum,
                f"deparser should emit 'BLUE:10'; got: {can_enum}")
    tc.assertIn("BLACK:11", can_enum,
                f"deparser should emit 'BLACK:11'; got: {can_enum}")
    tc.assertIn("enum Color = {RED:00, GREEN:01, BLUE:10, BLACK:11};",
                can_enum,
                "enum name, entries, order, and bits must round-trip")
    with open(filename, 'w') as f:
        f.write(can_enum)
    enum_rt = spot.parse_tlsf(filename)
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
    # Negative test: a mis-spelled bit character (e.g. `X`) inside
    # the bits non-terminal is a syntax error (no token matches
    # it: NUMBER rejects `X`, STAR rejects `X`).
    with open(filename, 'w') as f:
        f.write(
            "INFO {}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Bad = {X:0, Y:1};\n"
            "  }\n"
            "}\n"
            "MAIN {}\n")
    bad = spot.parse_tlsf(filename)
    tc.assertTrue(bad.errors,
                  f"unknown bit character must yield a "
                  f"syntax error; got none")

    # Seventeenth spec: enum-entry tag/bits (incl. don't-care-bit `**`)
    # survival round-trip regression.  The enumerations are no longer
    # reachable through parsed_tlsf (the AST is opaque), so the
    # regression is pinned on the canonical text instead: the exact
    # `enum Color = {...}` line must survive parse -> deparse ->
    # reparse verbatim (catching tag/bits rewrites, dropped entries,
    # and `*`-to-`0`/`1` corruption) and deparse must be idempotent.
    with open(filename, 'w') as f:
        f.write(
            "INFO {\n"
            "  TITLE:       \"enum round-trip\"\n"
            "  DESCRIPTION: \"fixture 17: tag+bits+star survival\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "GLOBAL {\n"
            "  DEFINITIONS {\n"
            "    enum Color = {RED:00, GREEN:01, BLUE:10, YELLOW:**};\n"
            "  }\n"
            "}\n"
            "MAIN {\n"
            "  INPUTS  { p; }\n"
            "  GUARANTEE { G(p); }\n"
            "}\n")
    parsed_enum = spot.parse_tlsf(filename)
    tc.assertFalse(parsed_enum.errors,
                   f"source enum must parse cleanly; got: "
                   f"{[(e.first, e.second) for e in parsed_enum.errors]}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_enum)
    canonical = ostr.str()
    with open(filename, 'w') as f:
        f.write(canonical)
    enum_rt = spot.parse_tlsf(filename)
    tc.assertFalse(enum_rt.errors,
                   f"round-trip must stay clean; got: "
                   f"{[(e.first, e.second) for e in enum_rt.errors]}")
    # The tag/bits pairs (including the `**` don't-care pattern)
    # survive parse -> deparse -> reparse.  Pin the exact canonical
    # line and the deparse idempotence; the enumerations are not
    # reachable through parsed_tlsf anymore.
    tc.assertIn("enum Color = {RED:00, GREEN:01, BLUE:10, YELLOW:**};",
                canonical,
                "tag/bits pairs (with **) must survive round-trip")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, enum_rt)
    tc.assertEqual(ostr.str(), canonical,
                   "enum deparse must be idempotent after round-trip")

    # Eighteenth spec: AST-clone-and-substitute-with-eager-
    # expansion architecture regression test.
    #
    # The deliberate heavy-usage shape: 102 uses of
    # `MultiUse(MyDef(a))`, distributed across all 6 MAIN
    # subsections (INITIALLY / PRESET / REQUIRE /
    # ASSERT / GUARANTEE / ASSUME) at 17 uses per section.
    # Each use triggers TWO levels of expansion:
    #   - expand_ast flattens the inner `MyDef(a)` App call to
    #     `G a` (an UnaryOp AST) before subst_arg runs, so the
    #     outer splice lands with no nested App in the actual;
    #     then
    #   - expand_ast then flattens the 5 nested `MyDef(x)`
    #     leaves inside MultiUse.body against that already-flat
    #     `G a` AST.
    # 102 use sites × (1 eager-expand on actual + 1 recursive
    # expand on the cloned body + 5 subst_arg walks on the
    # leaf App calls re-firing at translate time) ≈ 1500 AST
    # clone-and-replace operations.
    #
    # Pin mechanism (the suite fails loudly under a regression):
    # every body slot carries exactly 17 MultiUse uses (6*17 =
    # 102 total); `tlsf_to_ltl` returns a non-null formula;
    # round-trip (deparse -> reparse -> deparse) is byte-
    # identical (idempotence).

    USES_PER_SECTION = 17  # 17 * 6 sections = 102 use sites.
    # The 6 MAIN subsection keywords generated below.  Each keyword
    # parses into its own private-AST body vector (plural aliases are
    # exercised by fixture 13); the per-section counts are read back
    # from the canonical print since parsed_tlsf keeps its AST opaque.
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
        # MultiUse's body references MyDef FIVE times; each
        # App(MyDef, ...) child is what the App-case `subst_arg`
        # walk descends into on every MultiUse use.
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
    with open(filename, 'w') as f:
        f.write(contents_18)

    parsed_18 = spot.parse_tlsf(filename)
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
    # The translator returned a non-null formula -- pins
    # that all 510 MyDef expansions (102 × 5) produced valid
    # G a sub-formulas.
    tc.assertTrue(
        bool(res_18.full_formula),
        f"fixture 18: tlsf_to_ltl returned a null formula; "
        f"expected a non-null result after 102 MultiUse uses")
    # The formula may simplify completely to true because every
    # section contains the same implication, so do not rely on an
    # unsimplified formula spelling to prove expansion happened.

    # Structural pin: every section carries EXACTLY 17 use
    # sites.  Total 6 * 17 = 102.  A regression where the body
    # route shortcuts (e.g., a def that drops one of its 5
    # children during cloning) would change this count; the
    # arithmetic pin catches it here.  The counts are read from the
    # canonical print of the private AST (one ';'-terminated line
    # per use site).
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

    # Idempotence: the cached AST bodies produce a canonical
    # form that re-parses cleanly and re-deparses byte-
    # identically.  This is the deparser's deterministic-
    # iteration contract (std::vector only -- no
    # unordered_map/set, no implicit clone paths).
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, parsed_18)
    can_18 = ostr.str()
    with open(filename, 'w') as f:
        f.write(can_18)
    parsed_18b = spot.parse_tlsf(filename)
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

    # Nineteenth spec: guard clauses and recursion in DEFINITIONS.
    # TLSF v1.2 §4.6 lets a definition body be a sequence of clauses
    # `ec ≡ e | eB : e | eP : e` whose first true guard wins, and a
    # guarded definition may call itself while its constant integer
    # arguments shrink toward a guard-selected base case (the
    # `mone` mutual-exclusion helper of full_arbiter.tlsf is the
    # canonical example).  This fixture pins four behaviors:
    #
    #   1. Guard selection: the first clause whose guard holds is
    #      translated; `otherwise` is the catch-all.  `sel(3)` must
    #      pick the `x > 2 : b` clause (not `x > 5 : a`), so the
    #      translated GUARANTEE is exactly `b`.
    #   2. The deparser round-trips guard clauses (canonical print
    #      -> reparse -> translate stays byte-clean and semantic).
    #   3. Terminating guarded recursion: `one(g,0,2)` (exactly-one
    #      over a 3-wide bus, halving the index range at each level
    #      exactly like full_arbiter's mone) must unfold to a
    #      formula equivalent to the hand-written XOR conjunction.
    #      This is the regression pin for the constant-argument
    #      folding in the translate_expr App case: without it each
    #      recursion level wraps its argument in another layer of
    #      arithmetic, and the substituted trees grow linearly deep
    #      with the recursion instead of staying constant-sized.
    #   4. Non-terminating recursion (an unguarded self call, or a
    #      guard that never fires) is diagnosed exactly ONCE, with
    #      the diagnostic naming the definition that STARTED the
    #      expansion chain (not the leaf call that happened to trip
    #      the depth budget), instead of hanging or flooding one
    #      message per call site.
    with open(filename, 'w') as f:
        f.write(
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
    guarded = spot.parse_tlsf(filename)
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
    with open(filename, 'w') as f:
        f.write(can_g)
    guarded_b = spot.parse_tlsf(filename)
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
    # like full_arbiter's mone.  `one(g,0,2)` must be equivalent to
    # the hand-written XOR of the three flattened APs.
    with open(filename, 'w') as f:
        f.write(
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
    recursive = spot.parse_tlsf(filename)
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
    with open(filename, 'w') as f:
        f.write(
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
    loop1 = spot.parse_tlsf(filename)
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

    # Non-terminating recursion 2: the guardless doubling variant of
    # full_arbiter's mone.  Its argument tree doubles at every level,
    # so it exercises the total-work budget (the depth bound alone
    # cannot stop an exponential tree).  The diagnostic must name
    # `mone`, not the `none` leaf that happens to trip the limit.
    with open(filename, 'w') as f:
        f.write(
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
    loop2 = spot.parse_tlsf(filename)
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

    # Twentieth spec: the two corpus conformance gaps of the
    # DEFINITIONS/INFO syntax.  TLSF v1.2 and the canonical syfco
    # parser treat `;` as a SEPARATOR between DEFINITIONS entries
    # (`sepBy assignmentParser (rOp ";")` in
    # spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs): it
    # is required between two definitions, but the LAST one may omit
    # it (project-root M.tlsf relies on this).  And syfco's
    # stringParser accepts STRINGs spanning several lines with `\"`
    # as the single escape (spot/parsetlsf/refs/syfco/src/lib/Reader/
    # Parser/Utils.hs) -- tictactoe_1.tlsf carries a whole prose
    # DESCRIPTION paragraph this way.  This fixture pins:
    #   1. a last definition without `;` parses and translates
    #      (and `;` between two definitions plus none after the last
    #      works too);
    #   2. two `;`-less definitions juxtaposed still fail -- the
    #      second one's head is munched into the first one's body
    #      (maximal munch, like syfco), so the parse dies at the
    #      second `=`;
    #   3. a DESCRIPTION spanning lines keeps its embedded newlines
    #      and `\"` unescapes to a quote, and parse->print->parse is
    #      lossless (the deparser escapes quotes, see
    #      escape_info_string in spot/parsetlsf/public.cc);
    #   4. an unterminated string is diagnosed instead of silently
    #      eating the rest of the file.
    with open(filename, 'w') as f:
        f.write(
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
    m_style = spot.parse_tlsf(filename)
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
    with open(filename, 'w') as f:
        f.write(
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
    two_defs = spot.parse_tlsf(filename)
    tc.assertFalse(
        list(two_defs.errors),
        f"fixture 20: `A; B` (B without trailing `;`) must parse; "
        f"got {[(e.first, e.second) for e in two_defs.errors]}")
    res_two = spot.tlsf_to_ltl(two_defs)
    tc.assertTrue(bool(res_two.full_formula),
                  "fixture 20: two-definition spec must translate")
    # Two `;`-less definitions juxtaposed: maximal munch merges the
    # second head into the first body, so the parse fails at the
    # second `=` -- exactly where syfco fails (verified against the
    # reference parser).
    with open(filename, 'w') as f:
        f.write(
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
    nosemi = spot.parse_tlsf(filename)
    tc.assertTrue(
        list(nosemi.errors),
        "fixture 20: two juxtaposed `;`-less definitions must be "
        "rejected (second `=` is munched into the first body)")
    # Multi-line DESCRIPTION with an escaped quote, plus the lossless
    # parse->print->parse round trip.
    with open(filename, 'w') as f:
        f.write(
            "INFO {\n"
            "  TITLE:       \"multi\"\n"
            "  DESCRIPTION: \"first line\n"
            "second line with a \\\"quote\\\" and \\ prose\"\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "MAIN {\n"
            "  GUARANTEE { true; }\n"
            "}\n")
    multiline = spot.parse_tlsf(filename)
    tc.assertFalse(
        list(multiline.errors),
        f"fixture 20: multi-line DESCRIPTION must parse; got "
        f"{[(e.first, e.second) for e in multiline.errors]}")
    tc.assertEqual(
        multiline.description,
        'first line\nsecond line with a "quote" and \\ prose',
        f"fixture 20: embedded newlines and the `\\\"` escape must "
        f"be preserved; got: {multiline.description!r}")
    ostr_20 = spot.ostringstream()
    spot.tlsf_print(ostr_20, multiline)
    with open(filename, 'w') as f:
        f.write(ostr_20.str())
    multiline_b = spot.parse_tlsf(filename)
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
    with open(filename, 'w') as f:
        f.write(
            "INFO {\n"
            "  TITLE:       \"oops\"\n"
            "  DESCRIPTION: \"never closed\n"
            "  SEMANTICS:   Mealy\n"
            "  TARGET:      Mealy\n"
            "}\n"
            "MAIN { }\n")
    unclosed = spot.parse_tlsf(filename)
    tc.assertTrue(
        any('unclosed string' in e.second for e in unclosed.errors),
        f"fixture 20: unterminated string must be diagnosed; got "
        f"{[e.second for e in unclosed.errors]}")
finally:
    os.unlink(filename)
