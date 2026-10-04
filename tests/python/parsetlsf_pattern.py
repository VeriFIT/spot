# -*- mode: python; coding: utf-8 -*-
# Copyright (C) by the Spot authors, see the AUTHORS file for details.
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

"""Pattern matching (TLSF v1.2 SS4.6), exercised through the bindings.

These live in a file of their own rather than in parsetlsf.py so that
they stay independent of the rest of that file's fixtures: the AST
surface they poke at -- tlsf_op.PatternMatch and the shared pattern
predicates of spot/parsetlsf/ast.hh -- is reachable from Python, and
the printer and the parser's canonical output are checked here too.
"""

import spot
from unittest import TestCase
tc = TestCase()

# ---------------------------------------------------------------------
# Fixtures.

INFO = ('INFO {\n'
        '  TITLE:       "pattern matching"\n'
        '  DESCRIPTION: "TLSF v1.2 SS4.6"\n'
        '  SEMANTICS:   Mealy\n'
        '  TARGET:      Mealy\n'
        '}\n')


def parse_tlsf(source):
    """spot.parse_tlsf() with the mandatory-INFO check disabled."""
    opts = spot.tlsf_parser_options()
    opts.check_info = False
    return spot.parse_tlsf(source, opts)


def diags(errors):
    """[(line, column, message)] of a list of parse diagnostics."""
    return [(e.first.begin.line, e.first.begin.column, e.second)
            for e in errors]


def messages(errors):
    """The messages of a list of parse diagnostics, in order."""
    return [e.second for e in errors]


def spec(definitions, guarantee, decls='INPUTS { a; b; }',
         params='', extra=''):
    """A complete specification around `definitions` and `guarantee`."""
    return (INFO
            + 'GLOBAL {\n'
            + ('  PARAMETERS { %s }\n' % params if params else '')
            + '  DEFINITIONS {\n'
            + definitions
            + '  }\n'
            + extra
            + '}\n'
            + 'MAIN {\n'
            + '  ' + decls + '\n'
            + '  OUTPUTS { o; }\n'
            + '  GUARANTEE { ' + guarantee + ' }\n'
            + '}\n')


def translate(source):
    """(translation result, [diagnostic messages]) for `source`."""
    p = parse_tlsf(source)
    errs = spot.parse_aut_error_list()
    r = spot.tlsf_to_ltl(p, spot.tlsf_translator_options(), errs)
    return r, [e.second for e in errs]


def guarantee_of(source):
    """The translated GUARANTEE, or None if the file was rejected."""
    p = parse_tlsf(source)
    tc.assertFalse(list(p.errors),
                   f"must parse cleanly; got {diags(p.errors)}")
    errs = spot.parse_aut_error_list()
    r = spot.tlsf_to_ltl(p, spot.tlsf_translator_options(), errs)
    tc.assertFalse([e.second for e in errs],
                   f"must translate cleanly; got "
                   f"{[e.second for e in errs]}")
    return r.guarantee


def translate_ok(definitions, guarantee, **kw):
    """Assert a fixture is accepted, and return its GUARANTEE."""
    p = parse_tlsf(spec(definitions, guarantee, **kw))
    tc.assertFalse(list(p.errors),
                   f"{definitions!r} must parse cleanly; got "
                   f"{diags(p.errors)}")
    return guarantee_of(spec(definitions, guarantee, **kw))


def yields(definitions, guarantee, expected, why, **kw):
    """Assert a fixture translates to the formula `expected`.

    Equivalence rather than textual equality: the canonical printer
    picks its own operand order, and what a pattern clause selects is a
    property of the formula, not of how it was spelled.
    """
    got = translate_ok(definitions, guarantee, **kw)
    tc.assertTrue(spot.are_equivalent(got, spot.formula(expected)),
                  f"{why}: expected {expected}, got {got}")


# ---------------------------------------------------------------------
# The subject of a pattern is matched structurally against it, and each
# identifier of the pattern binds to the subexpression it matched.

yields('    fun(f) = f ~ (q U _) : q\n'
       '             otherwise : X f;\n',
       'G(o <-> fun(a U b));', 'G(a <-> o)',
       "an until subject binds the pattern's left operand")

yields('    fun(f) = f ~ (q U _) : q\n'
       '             otherwise : X f;\n',
       'G(o <-> fun(G a));', 'G(o <-> XGa)',
       "a non-until subject falls through to `otherwise`")

# The wildcard matches anything and binds nothing: the value cannot
# mention it, so a clause whose value is only the wildcard yields the
# constant `true` rather than a free identifier.
yields('    any(x) = x ~ _ : true;\n', 'G(o <-> any(a));', 'Go',
       "the wildcard binds nothing, so a `true` value stays true")

# Every metavariable of the pattern is visible in the value, and only
# there.  Two metavariables in one pattern bind independently.
yields('    two(x) = x ~ (p U q) : p && q\n'
       '                otherwise : false;\n',
       'G(o <-> two(a U b));', 'G(o <-> (a & b))',
       "both operands of the matched `U` are bound")

# `true` and `false` are literals in a pattern, not metavariables: each
# matches only itself.
yields('    ptrue(x) = x ~ true : b\n'
       '                 otherwise : c;\n',
       'G(o <-> (ptrue(true) && ptrue(F a)));', 'G(o <-> (b & c))',
       "`true` matches the literal `true` and nothing else")

yields('    pfalse(x) = x ~ false : b\n'
       '                  otherwise : c;\n',
       'G(o <-> (pfalse(false) && pfalse(G a)));', 'G(o <-> (b & c))',
       "`false` matches the literal `false` and nothing else")

# A subject of a different shape falls through, whatever the
# connective: only structural equivalence counts.
for definition, subject in (
        # a different unary connective
        ('    w(x) = x ~ G p : b otherwise : c;\n', 'F a'),
        # a binary connective under a unary one
        ('    w(x) = x ~ G p : b otherwise : c;\n', 'X G a'),
        # a bare signal is not a temporal operator
        ('    w(x) = x ~ G p : b otherwise : c;\n', 'a'),
        # the two unary G and F are not interchangeable
        ('    w(x) = x ~ F p : b otherwise : c;\n', 'G a'),
        # X and X[!] are not interchangeable
        ('    w(x) = x ~ X p : b otherwise : c;\n', 'X[!] a'),
        # ! applies to a subterm, so it is not the top connective
        ('    w(x) = x ~ !p : b otherwise : c;\n', 'G a'),
        # the two operands are not interchangeable
        ('    w(x) = x ~ (p && q) : b otherwise : c;\n', 'a || b'),

):
    yields(definition, f'G(o <-> w({subject}));', 'G(o <-> c)',
           f"{subject!r} must not match")

# ...and the same subjects do match the patterns that describe them.
for definition, subject in (
        ('    w(x) = x ~ G p : b otherwise : c;\n', 'G a'),
        ('    w(x) = x ~ F p : b otherwise : c;\n', 'F a'),
        ('    w(x) = x ~ X[!] p : b otherwise : c;\n', 'X[!] a'),
        ('    w(x) = x ~ !p : b otherwise : c;\n', '!a'),
        ('    w(x) = x ~ (p && q) : b otherwise : c;\n', 'a && b'),
):
    yields(definition, f'G(o <-> w({subject}));', 'G(o <-> b)',
           f"{subject!r} must match")

# A pattern with a concrete operand matches only the grouping that puts
# the concrete part where it was written: `G p && q` matches
# `G a && b` but not `(a && b) && G c`, even though both are conjunctions
# of a G with something.  This is where the AST is strictly binary --
# `a && b && G c` is `(a && b) && G c` -- so no associativity question
# arises; see SPEC.md SS4.6 for the divergence from syfco, whose
# checkPattern asserts on an n-ary conjunction.
yields('    w(x) = x ~ (G p && q) : b otherwise : c;\n',
    'G(o <-> (w(G a && b) && w(a && b && G c)));',
    'G(o <-> (b & c))',
    "only the grouping the pattern names matches",
    decls='INPUTS { a; b; c; }')

# ---------------------------------------------------------------------
# The first matching clause wins, and a pattern that does not match is
# not an error: the scan simply moves on.

yields('    first(x) = x ~ m : a\n'
       '                x ~ m : b\n'
       '                otherwise : c;\n',
       'G(o <-> first(a));', 'G(a <-> o)',
       "the first of two matching clauses is selected")

# A bare metavariable is a catch-all: it matches any subject at all.
yields('    any(x) = x ~ m : b otherwise : c;\n',
       'G(o <-> (any(a) && any(G (a U b))));', 'G(b <-> o)',
       "a bare metavariable matches every subject")

# A metavariable name may repeat across clauses: each clause is scanned
# on its own, so the binding of one clause does not leak into the next.
# The first clause is the specific one, so the two subjects below take
# different clauses and yield different results.
yields('    perclause(x) = x ~ G m : a\n'
       '                    x ~ m : b\n'
       '                    otherwise : c;\n',
       'G(o <-> (perclause(G a) && perclause(a)));', 'G(o <-> (a & b))',
       "the same metavariable name may be reused by another clause")

# ---------------------------------------------------------------------
# Bounded and stacked forms.  Their bounds are integer expressions and
# are compared as numbers; only the body is a pattern.

yields('    w(x) = x ~ F[1:2] p : b otherwise : c;\n',
       'G(o <-> (w(F[1:2] a) && w(F[2:2] a)));', 'G(o <-> (b & c))',
       "equal bounds match and unequal ones do not")

yields('    w(x) = x ~ G[!1:2] p : b otherwise : c;\n',
       'G(o <-> (w(G[!1:2] a) && w(G[1:2] a)));', 'G(o <-> (b & c))',
       "the strong flavour of a bound is part of the match")

yields('    w(x) = x ~ X[2] p : b otherwise : c;\n',
       'G(o <-> (w(X[2] a) && w(X[3] a)));', 'G(o <-> (b & c))',
       "a next-stack length is compared as a number")

yields('    w(x) = x ~ X[!2] p : b otherwise : c;\n',
       'G(o <-> (w(X[!2] a) && w(X[2] a)));', 'G(o <-> (b & c))',
       "the strong flavour of a next stack is part of the match")

# A bound over a parameter compares by value, so the two spellings of
# the same bound match one another.
yields('    w(x) = x ~ F[n:2] p : b otherwise : c;\n',
       'G(o <-> (w(F[n:2] a) && w(F[1:2] a)));',
       'G(o <-> (b & c))',
       "a bound over a parameter compares by value",
       params='n = 2;')

# A bounded form still matches on its body.  The pattern body is a
# concrete connective here, so the second subject -- whose body is a
# bare signal -- does not match it, while the bounds still agree.
yields('    w(x) = x ~ F[1:2] G p : b otherwise : c;\n',
       'G(o <-> (w(F[1:2] G a) && w(F[1:2] a)));', 'G(o <-> (b & c))',
       "a bounded form matches on its body as well as its bounds")

# A quantifier head in a pattern: the binder is not a pattern, so only
# the body is compared.
yields('    w(x) = x ~ &&[0 <= i < 2] G p : b otherwise : c;\n',
       'G(o <-> (w(&&[0 <= i < 2] G a)'
       ' && w(&&[0 <= i < 2] a)));', 'G(o <-> (b & c))',
       "a quantified body is matched as a pattern")

# Two binders desugar into nested quantifiers, and a pattern matches
# that whole run.
yields('    w(x) = x ~ (&&[i IN {0, 1}, j IN {0, 1}] G p) : b'
       ' otherwise : c;\n',
       'G(o <-> (w(&&[i IN {0, 1}, j IN {0, 1}] G a)'
       ' && w(&&[i IN {0, 1}, j IN {0, 1}] a)));', 'G(o <-> (b & c))',
       "a run of binders is matched as one nested pattern")

# ---------------------------------------------------------------------
# The subject is the substituted and expanded expression.

# A plain macro is flattened before the match, so a call to one does not
# hide the shape of the formula it stands for.
yields('    Mac(x) = G x;\n'
       '    w(x) = x ~ G p : b otherwise : c;\n',
       'G(o <-> w(Mac(a)));', 'G(o <-> b)',
       "a plain macro is flattened, so the match sees through it")

# The call to a guarded definition is NOT flattened (its clauses are
# selected at translate time), so the subject is still an App node and
# does not match a formula-shaped pattern.
yields('    Guarded(x) = (x == 0) : a\n'
       '                   x == 1 : b;\n'
       '    w(x) = x ~ G p : b otherwise : c;\n',
       'G(o <-> w(Guarded(0)));', 'G(c <-> o)',
       "the call to a guarded definition stays an App and does not match")

# The subject may be any expression: the `~` is one tier tighter than
# the guard `:` but looser than every operator of the subject, so the
# subject keeps its natural grouping without parentheses.
yields('    w(x) = x ~ G p : b otherwise : c;\n',
       'G(o <-> w(G a && b));', 'G(o <-> c)',
       "an unparenthesized subject groups as an expression would")

# ---------------------------------------------------------------------
# Diagnostics.

# A `~` that survives expansion has no meaning outside a definition
# body, exactly like a `:`.
r, errs = translate(spec('', 'G(a ~ b);'))
tc.assertFalse(bool(r.full_formula),
               f"a `~` in LTL position must yield a null formula; got "
               f"{r.full_formula}")
tc.assertEqual(errs, ["pattern match '~' is only meaningful inside a "
                      "definition body"],
               f"diagnostic for a `~` in LTL position; got {errs}")

# A pattern clause carries a value: SS4.6 gives `ec ::= e | eB : e |
# eP : e`, so the `:` is not optional the way an unguarded clause is.
r, errs = translate(spec('    w(x) = x ~ m;\n', 'G(o <-> w(a));'))
tc.assertEqual(errs, ["a pattern match clause needs a `: value' on its "
                      "right; a bare `~' has no value to select"],
               f"a pattern clause with no value must say so; got {errs}")

# A pattern nested under a temporal operator is not a clause guard:
# `~` must be the whole guard for the clause to be a pattern clause.
# syfco agrees, reporting the same situation (its own guard is not
# statically decidable).
r, errs = translate(spec('    w(x) = G(x ~ q) : b;\n', 'G(o <-> w(a));'))
tc.assertTrue(any('not statically decidable' in e for e in errs),
              f"a `~` under a temporal operator is not a clause guard; got "
              f"{errs}")

# The SHAPE of a pattern is checked while parsing, so it is reported
# even for a definition that is never called.  Every one of these is a
# connective SS4.6 does not list, plus the two structural mistakes.
for body, expected in (
        ('x ~ (p < 2)', "invalid pattern: `<' cannot appear in a "
         "pattern"),
        ('x ~ (p + 1)', "invalid pattern: `+' cannot appear in a "
         "pattern"),
        ('x ~ (p == 0)', "invalid pattern: `==' cannot appear in a "
         "pattern"),
        ('x ~ (p IN {0, 1})', "invalid pattern: `IN' cannot appear in a "
         "pattern"),
        ('x ~ 3', "invalid pattern: an integer literal cannot appear in "
         "a pattern"),
        ('x ~ {0, 1}', "invalid pattern: a set literal cannot appear in "
         "a pattern"),
        ('x ~ (a ~ p)', "invalid pattern: a pattern cannot itself contain "
         "`~`"),
        ('x ~ (p && p)', "pattern variable 'p' is bound more than once"),
):
    p = parse_tlsf(spec('    bad(x) = %s : b;\n' % body, 'G(o <-> a);'))
    tc.assertEqual(messages(p.errors), [expected],
                   f"{body!r} must be rejected; got {diags(p.errors)}")

# A bus reference is not a pattern either.  It is spelled separately
# because the scanner builds it from an identifier and a bracketed
# index, so it reaches the check as a distinct node kind.
p = parse_tlsf(spec('    bad(x) = x ~ (p[0]) : b;\n',
                    'G(o <-> a);',
                    decls='INPUTS { a; b[2]; }'))
tc.assertEqual(messages(p.errors),
               ["invalid pattern: a bus reference cannot appear in a "
                "pattern"],
               f"a bus reference must be rejected; got {diags(p.errors)}")

# A metavariable must be fresh.  This is checked at translate time,
# because it depends on what the definition body knows, and it is a
# documented divergence: syfco binds such a name silently.
for definitions, decls, params, extra, expected in (
        ('    w(x) = x ~ G x : x;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'x' is already bound as a formal argument of "
         "the definition"),
        ('    w(x) = x ~ G n : n;\n', 'INPUTS { a; b; }', 'n = 2;', '',
         "pattern variable 'n' is already bound as a parameter"),
        ('    w(x) = x ~ G w : w;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'w' is already bound as a definition"),
        ('    w(x) = x ~ G a : a;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'a' is already bound as an input or output"),
        ('    w(x) = x ~ G o : o;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'o' is already bound as an input or output"),
        ('    enum E = T0:0 T1:1;\n'
         '    w(x) = x ~ G E : E;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'E' is already bound as an enum"),
        ('    enum E = T0:0 T1:1;\n'
         '    w(x) = x ~ G T0 : T0;\n', 'INPUTS { a; b; }', '', '',
         "pattern variable 'T0' is already bound as an enum tag"),
):
    r, errs = translate(spec(definitions, 'G(o <-> w(a));',
                             decls=decls, params=params, extra=extra))
    tc.assertEqual(errs, [expected],
                   f"{definitions!r} must be rejected; got {errs}")

# ---------------------------------------------------------------------
# The printer.

def canonical(source):
    """The tlsf_print canonical form of `source`."""
    p = parse_tlsf(source)
    tc.assertFalse(list(p.errors),
                   f"must parse cleanly; got {diags(p.errors)}")
    ostr = spot.ostringstream()
    spot.tlsf_print(ostr, p)
    return ostr.str()


# A clause prints as `subject ~ pattern : value`, and `~` binds tighter
# than `:` so no parentheses appear around the match.
tc.assertIn('w(x) = x ~ G p : b;',
            canonical(spec('    w(x) = x ~ G p : b;\n', 'G(o <-> a);')),
            "a pattern clause prints with `~` and no extra parentheses")

# The wildcard prints as the single character `_`.
tc.assertIn('w(x) = x ~ (q U _) : q;',
            canonical(spec('    w(x) = x ~ (q U _) : q;\n',
                           'G(o <-> a);')),
            "the wildcard prints as `_`")

# Every connective of Table 1's connective set prints back unchanged,
# and the printed form reparses to the same canonical text: the `~`
# tier is what keeps the grouping of both operands.
for body in ('x ~ _',
             'x ~ true',
             'x ~ !p',
             'x ~ X p',
             'x ~ X[!] p',
             'x ~ F p',
             'x ~ G p',
             'x ~ (p && q)',
             'x ~ (p || q)',
             'x ~ (p -> q)',
             'x ~ (p <-> q)',
             'x ~ (p U q)',
             'x ~ (p W q)',
             'x ~ (p R q)',
             'x ~ F[1:2] p',
             'x ~ G[!1:2] p',
             'x ~ X[2] p',
             'x ~ X[!2] p',
             'x ~ &&[0 <= i < 2] p',
             'x ~ (G p && X q)',
             'x ~ (G p || F q)'):
    source = spec('    w(x) = %s : b;\n' % body, 'G(o <-> a);')
    once = canonical(source)
    tc.assertIn('~', once,
                f"{body!r} must survive the print; got {once}")
    twice = canonical(once)
    tc.assertEqual(twice, once,
                   f"{body!r} must be stable under print/parse/print")

# A subject that is itself a comparison needs no parentheses, because
# `~` is looser than every comparison operator of Table 1.
tc.assertIn('w(x) = (x + 1) ~ G p : b;',
            canonical(spec('    w(x) = (x + 1) ~ G p : b;\n',
                           'G(o <-> a);')),
            "an arithmetic subject keeps only its own parentheses")

# The AST surface itself -- tlsf_op.PatternMatch and the shared pattern
# predicates of spot/parsetlsf/ast.hh -- is not reachable from the
# bindings: SWIG exports only tlsf_semantics_* and tlsf_target_*, not
# the tlsf_op enum or the inline helpers.  It is covered from the C++
# side instead: tests/core/parsetlsf.test pins the operator through the
# printer and through the signals a metavariable does and does not
# register, and the 1141-file reference corpus pins that no other
# operator changed shape.
