// -*- coding: utf-8 -*-
// Copyright (C) by the Spot authors, see the AUTHORS file for details.
//
// This file is part of Spot, a model checking library.
//
// Spot is free software; you can redistribute it and/or modify it
// under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 3 of the License, or
// (at your option) any later version.
//
// Spot is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
// or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
// License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "config.h"
#include <spot/misc/common.hh>
#include <spot/parsetlsf/public.hh>
#include "ast.hh"  // private header; the real spot::tlsf_ast definition.
#include "parsedecl.hh"  // private header; tlsfyyopen/close/reset decls.
#include "translate.hh"  // private header; spot::tlsf::translator.
#include <spot/parsetlsf/parsetlsf.hh>  // Bison; declares tlsf_result.
#include <spot/tl/formula.hh>
#include <algorithm>
#include <ostream>
#include <sstream>
#include <utility>
#include <vector>

namespace spot
{
  parsed_tlsf::parsed_tlsf(std::string filename)
    : filename(std::move(filename))
  {
  }

  parsed_tlsf::~parsed_tlsf() = default;

  /// True iff \a op is right-associative in the TLSF grammar.
  ///
  /// The deparser needs this to decide when to wrap an LHS BinaryOp
  /// child: a right-assoc parent declared at the same precedence would
  /// otherwise steal the LHS (e.g., `a -> b -> c` re-parses as
  /// `a -> (b -> c)`, not `(a -> b) -> c`).
  static bool op_is_right_associative(tlsf_op op)
  {
    return op == tlsf_op::Implies || op == tlsf_op::Equiv
      || op == tlsf_op::W || op == tlsf_op::U
      || op == tlsf_op::SetDifference
      || op == tlsf_op::Div || op == tlsf_op::Mod;
  }

  /// Lower number = looser binding.  Used by tlsf_print_expr to decide
  /// when a child needs its own parenthesisation.
  /// The precedence values follow the order of Table 1 in TLSF v1.2,
  /// inverted so that larger values bind more tightly.  This is also the
  /// convention used by the deparser below.
  static int op_precedence(tlsf_op op)
  {
    switch (op)
      {
      case tlsf_op::None:
        return 0;
      case tlsf_op::Guard:
        return 0;
      case tlsf_op::R:
        return 1;
      case tlsf_op::U:
        return 2;
      case tlsf_op::W:
        return 3;
      case tlsf_op::Implies:
        return 4;
      case tlsf_op::Equiv:
        return 4;
      case tlsf_op::Or:
        return 5;
      case tlsf_op::And:
        return 6;
      case tlsf_op::Not:
        return 7;
      case tlsf_op::F:
        return 7;
      case tlsf_op::G:
        return 7;
      case tlsf_op::X:
        return 7;
      case tlsf_op::StrongNext:
        return 7;
      case tlsf_op::XStack:
      case tlsf_op::StrongXStack:
        return 7;
      case tlsf_op::FBounded:
      case tlsf_op::GBounded:
      case tlsf_op::StrongFBounded:
      case tlsf_op::StrongGBounded:
        return 7;
      case tlsf_op::In:
        return 8;
      case tlsf_op::Eq:
        return 9;
      case tlsf_op::Neq:
        return 9;
      case tlsf_op::Lt:
        return 9;
      case tlsf_op::Le:
        return 9;
      case tlsf_op::Gt:
        return 9;
      case tlsf_op::Ge:
        return 9;
      case tlsf_op::SetUnion:
        return 11;
      case tlsf_op::SetIntersection:
        return 12;
      case tlsf_op::SetDifference:
        return 13;
      case tlsf_op::Add:
        return 14;
      case tlsf_op::Sub:
        return 14;
      case tlsf_op::Div:
        return 15;
      case tlsf_op::Mod:
        return 15;
      case tlsf_op::Mul:
        return 16;
      // The remaining tags name unary operators, which
      // expr_precedence() answers for directly without consulting
      // op_precedence(); list them so the switch stays exhaustive.
      case tlsf_op::BigSum:
      case tlsf_op::BigProd:
        return 17;
      case tlsf_op::BigUnion:
      case tlsf_op::BigInter:
      case tlsf_op::BigDiff:
        return 10;
      case tlsf_op::SetSize:
      case tlsf_op::SetMin:
      case tlsf_op::SetMax:
        return 7;
      }
    return 0;
  }

  /// Return the effective precedence of an expression node.  Quantifiers
  /// and unary operators both occupy Table 1's precedence-11 tier, even
  /// though a quantifier's operator tag is also used for its Boolean fold.
  static int expr_precedence(const tlsf_expr& e)
  {
    // `|eSX|` is self-delimiting: the bars are both the operator and its
    // delimiters, so it never needs parentheses around it and never
    // needs one inside.  Treat it as atomic rather than as a unary
    // operator, or every comparison would print as `(|{1, 2}|) == 3`.
    if (e.op == tlsf_op::SetSize && e.type == tlsf_expr_type::UnaryOp)
      return 100;
    // The big operators are prefix heads too, but they are not in that
    // tier: Table 1 puts the numeric two in the tightest row and the set
    // three in the unary-set row, which binds tighter than a comparison
    // yet looser than `+`/`-`.  Wrapping a head as if it were a `G` would
    // print `(SUM[i] i) == 3` where the source said `SUM[i] i == 3`.
    if (e.type == tlsf_expr_type::UnaryOp)
      switch (e.op)
        {
        case tlsf_op::BigSum:
        case tlsf_op::BigProd:
        case tlsf_op::BigUnion:
        case tlsf_op::BigInter:
        case tlsf_op::BigDiff:
          return op_precedence(e.op);
        default:
          break;
        }
    if (e.type == tlsf_expr_type::Quantifier
        || e.type == tlsf_expr_type::UnaryOp)
      return 7;
    if (e.type == tlsf_expr_type::BinaryOp)
      return op_precedence(e.op);
    return 100;
  }

  static void tlsf_print_expr(std::ostream& os, const tlsf_expr& e);

  /// \brief Print the binder list of the quantifier run starting at \a e.
  ///
  /// A big operator's argument is a comma-separated binder list, which
  /// tlsf_make_binders() desugars into nested single-binder quantifiers:
  /// `&&[i, j] p` becomes `&&[i] &&[j] p`.  The outermost binder is the
  /// head's child and the innermost quantifier's child is the body, so
  /// walking that run prints the list back out.  Returns the body, i.e.
  /// the node that is not a quantifier of \a e's tag.
  ///
  /// \a e must be a quantifier whose tag is neither XStack nor
  /// StrongXStack: those brackets hold a next-stack length rather than
  /// binders, so they are never a list.
  static const tlsf_expr*
  print_binder_list(std::ostream& os, const tlsf_expr& e)
  {
    const tlsf_expr* q = &e;
    bool first = true;
    while (q->type == tlsf_expr_type::Quantifier && q->op == e.op
           && q->children.size() >= 2 && q->children[0]
           && q->children[1])
      {
        if (!first)
          os << ", ";
        first = false;
        tlsf_print_expr(os, *q->children[0]);
        q = q->children[1].get();
      }
    return q;
  }

  /// \brief Deparse \a e to canonical TLSF surface syntax on \a os.
  ///
  /// Parentheses explicitly present in the source (recorded by the
  /// \c parenthesized flags) are re-emitted verbatim, and additional
  /// parentheses are inserted around children whose effective
  /// precedence requires it, so that print/parse round-trips yield
  /// the same AST.
  static void tlsf_print_expr(std::ostream& os, const tlsf_expr& e)
  {
    switch (e.type)
      {
      case tlsf_expr_type::LiteralInt:
        os << e.val;
        return;
      case tlsf_expr_type::Identifier:
        os << e.name;
        return;
      case tlsf_expr_type::BusRef:
        os << e.name;
        if (!e.children.empty())
          {
            os << '[';
            tlsf_print_expr(os, *e.children[0]);
            os << ']';
          }
        return;
      case tlsf_expr_type::App:
        os << e.name << '(';
        for (size_t i = 0; i < e.children.size(); ++i)
          {
            if (i)
              os << ", ";
            tlsf_print_expr(os, *e.children[i]);
          }
        os << ')';
        return;
      case tlsf_expr_type::UnaryOp:
        // Set cardinality `|eSX|` has no operator word: the bars are
        // the operator and its two delimiters at once, so it does not
        // fit the `OP e` shape the rest of this case prints.
        if (e.op == tlsf_op::SetSize)
          {
            if (e.parenthesized)
              os << '(';
            os << '|';
            if (!e.children.empty() && e.children[0])
              tlsf_print_expr(os, *e.children[0]);
            os << '|';
            if (e.parenthesized)
              os << ')';
            return;
          }
        // A big operator is a head, a binder list, and a body: its
        // child is the nested run of quantifiers the list desugars to.
        // print_binder_list() writes the list and hands back the body,
        // which goes after the closing bracket.  This is checked
        // before the parenthesized shortcut below because the bracket
        // is part of the head's spelling, not of a body the generic
        // `OP e` shape can hold.
        switch (e.op)
          {
          case tlsf_op::BigSum:
          case tlsf_op::BigProd:
          case tlsf_op::BigUnion:
          case tlsf_op::BigInter:
          case tlsf_op::BigDiff:
            {
              if (e.parenthesized)
                os << '(';
              os << tlsf_format_op(e.op);
              if (e.children.empty() || !e.children[0])
                {
                  // A child lost to error recovery.
                  os << "] ";
                  if (e.parenthesized)
                    os << ')';
                  return;
                }
              {
                const tlsf_expr* body =
                  print_binder_list(os, *e.children[0]);
                os << "] ";
                tlsf_print_expr(os, *body);
              }
              if (e.parenthesized)
                os << ')';
              return;
            }
          default:
            break;
          }
        if (e.parenthesized)
          {
            os << '(' << tlsf_format_op(e.op);
            if (!e.children.empty())
              {
                os << ' ';
                tlsf_print_expr(os, *e.children[0]);
              }
            os << ')';
            return;
          }
        // Unary ops (BANG, G, F, X, X[!]) bind tightest in this grammar;
        // an unwrapped BinaryOp child would re-parse as
        // ``(BANG LHS) OP RHS`` rather than ``BANG (LHS OP RHS)``, so
        // emit parens to preserve the AST grouping through round-trip.
        // The same applies to Quantifier children: writing
        // ``! &&[:i]p`` instead of ``! (&&[:i]p)`` is ambiguous when
        // combined with trailing operators.
        if (!e.children.empty() && e.children[0]
            && !e.children[0]->parenthesized
            && (e.children[0]->type == tlsf_expr_type::BinaryOp
                || e.children[0]->type == tlsf_expr_type::Quantifier))
          {
            os << tlsf_format_op(e.op) << " (";
            tlsf_print_expr(os, *e.children[0]);
            os << ')';
            return;
          }
        os << tlsf_format_op(e.op);
        if (!e.children.empty() && e.children[0])
          {
            os << ' ';
            tlsf_print_expr(os, *e.children[0]);
          }
        return;
      case tlsf_expr_type::BinaryOp:
        if (e.parenthesized)
          {
            os << '(';
            tlsf_print_expr(os, *e.children[0]);
            os << ' ' << tlsf_format_op(e.op) << ' ';
            tlsf_print_expr(os, *e.children[1]);
            os << ')';
            return;
          }
        // Wrap child operands according to the effective precedence of
        // every expression node.  This mirrors Table 1 and preserves the
        // AST grouping through a print/parse round-trip.
        {
          bool par_is_right_ass =
            op_is_right_associative(e.op);
          int par_prec = op_precedence(e.op);
          // LHS
          if (e.children.size() >= 1 && e.children[0])
            {
              const auto& lhs = *e.children[0];
              bool wrap = false;
              if (!lhs.parenthesized)
                {
                  if (lhs.type == tlsf_expr_type::BinaryOp
                      || lhs.type == tlsf_expr_type::UnaryOp
                      || lhs.type == tlsf_expr_type::Quantifier)
                    {
                      int lhs_prec = expr_precedence(lhs);
                      wrap = par_is_right_ass
                        ? lhs_prec <= par_prec
                        : lhs_prec < par_prec;
                    }
                }
              if (wrap)
                {
                  os << '(';
                  tlsf_print_expr(os, lhs);
                  os << ')';
                }
              else
                {
                  tlsf_print_expr(os, lhs);
                }
            }
          os << ' ' << tlsf_format_op(e.op) << ' ';
          // RHS
          if (e.children.size() >= 2 && e.children[1])
            {
              const auto& rhs = *e.children[1];
              bool wrap = false;
              if (!rhs.parenthesized
                  && (rhs.type == tlsf_expr_type::BinaryOp
                      || rhs.type == tlsf_expr_type::UnaryOp
                      || rhs.type == tlsf_expr_type::Quantifier))
                {
                  int rhs_prec = expr_precedence(rhs);
                  wrap = par_is_right_ass
                    ? rhs_prec < par_prec
                    : rhs_prec <= par_prec;
                }
              if (wrap)
                {
                  os << '(';
                  tlsf_print_expr(os, rhs);
                  os << ')';
                }
              else
                {
                  tlsf_print_expr(os, rhs);
                }
            }
        }
        return;
      case tlsf_expr_type::Quantifier:
        // An explicitly parenthesized quantifier must reprint its
        // own parentheses: the UnaryOp case above skips wrapping
        // children that carry the flag, expecting them to print
        // their own parens.  Without this, `G (&&[..] p)` (emitted
        // by the UnaryOp case for an unparenthesized child) reparses
        // as a parenthesized quantifier, is re-emitted bare as
        // `G &&[..] p`, and print/parse/print oscillates forever.
        if (e.parenthesized)
          os << '(';
        // Bounded temporal operators carry two integer bounds and the
        // body: `F[lo:hi] body` / `G[lo:hi] body`.  The strong (LTLf)
        // flavour carries a `!` marker, which we always print next to
        // the closing bracket: TLSF v1.2 SS4.8 accepts it on either
        // side of the bounds, and printing one canonical spelling keeps
        // print/parse/print stable for either input spelling.
        if (e.op == tlsf_op::FBounded || e.op == tlsf_op::GBounded
            || e.op == tlsf_op::StrongFBounded
            || e.op == tlsf_op::StrongGBounded)
          {
            const bool strong = e.op == tlsf_op::StrongFBounded
                                || e.op == tlsf_op::StrongGBounded;
            os << tlsf_format_op(e.op) << '[';
            if (e.children.size() >= 1 && e.children[0])
              tlsf_print_expr(os, *e.children[0]);
            os << ':';
            if (e.children.size() >= 2 && e.children[1])
              tlsf_print_expr(os, *e.children[1]);
            if (strong)
              os << '!';
            os << "] ";
            if (e.children.size() >= 3 && e.children[2])
              tlsf_print_expr(os, *e.children[2]);
            if (e.parenthesized)
              os << ')';
            return;
          }
        os << tlsf_format_op(e.op) << '[';
        if (e.op == tlsf_op::StrongXStack)
          {
            // The strong next-stack carries its marker inside the
            // brackets rather than after them.
            if (e.children.size() >= 1 && e.children[0])
              tlsf_print_expr(os, *e.children[0]);
            os << '!';
          }
        else if (e.op != tlsf_op::XStack)
          {
            // A run of quantifiers sharing this node's tag is one head
            // with several binders, so it prints back as a single
            // comma-separated binder list, outermost binder first.
            // `X[n] p` is deliberately left out: its bracket holds the
            // length of a next-stack rather than a binder, so
            // `X[n] X[m] p` must keep its two separate heads.  A node
            // that lost a child to error recovery matches no binder at
            // all and falls back to the single-binder shape below.
            if (e.children.size() >= 2 && e.children[0]
                && e.children[1])
              {
                const tlsf_expr* body = print_binder_list(os, e);
                os << "] ";
                tlsf_print_expr(os, *body);
                if (e.parenthesized)
                  os << ')';
                return;
              }
            if (e.children.size() >= 1 && e.children[0])
              tlsf_print_expr(os, *e.children[0]);
          }
        else if (e.children.size() >= 1 && e.children[0])
          tlsf_print_expr(os, *e.children[0]);
        os << "] ";
        if (e.children.size() >= 2 && e.children[1])
          tlsf_print_expr(os, *e.children[1]);
        if (e.parenthesized)
          os << ')';
        return;
      case tlsf_expr_type::SetExplicit:
        os << '{';
        for (size_t i = 0; i < e.children.size(); ++i)
          {
            if (i)
              os << ", ";
            tlsf_print_expr(os, *e.children[i]);
          }
        os << '}';
        return;
      case tlsf_expr_type::SetRange:
        os << '{';
        if (e.children.size() >= 1 && e.children[0])
          tlsf_print_expr(os, *e.children[0]);
        os << "..";
        if (e.children.size() >= 2 && e.children[1])
          tlsf_print_expr(os, *e.children[1]);
        os << '}';
        return;
      }
  }

  namespace
  {
    /// Escape a string for re-emission inside a double-quoted INFO
    /// string, using the two escapes the scanner understands (see
    /// the str start condition in scantlsf.ll): `\"` unescapes to a
    /// quote and `\\` to a backslash.  Both have to be escaped here,
    /// or a literal backslash would be read back as the first half
    /// of an escape.  A backslash followed by any OTHER character is
    /// kept verbatim by the scanner, so a hand-written `\n` survives
    /// a print -> parse round trip unchanged.
    std::string
    escape_info_string(const std::string& in)
    {
      std::string out;
      out.reserve(in.size());
      for (char c : in)
        {
          if (c == '"' || c == '\\')
            out += '\\';
          out += c;
        }
      return out;
    }

    std::string format_semantics(tlsf_semantics s)
    {
      switch (s)
        {
        case tlsf_semantics::Mealy:
          return "Mealy";
        case tlsf_semantics::MealyStrict:
          return "Mealy,Strict";
        case tlsf_semantics::MealyFinite:
          return "Mealy,Finite";
        case tlsf_semantics::Moore:
          return "Moore";
        case tlsf_semantics::MooreStrict:
          return "Moore,Strict";
        case tlsf_semantics::MooreFinite:
          return "Moore,Finite";
        }
      SPOT_UNREACHABLE();
    }

    std::string format_target(tlsf_target t)
    {
      return t == tlsf_target::Moore ? "Moore" : "Mealy";
    }

    // Print one ap_decl line.
    void print_ap(std::ostream& os, const tlsf_ap_decl& d)
    {
      os << "    ";
      // A typed bus is spelled `enumType name;`: the width is
      // carried by the named enum, not by an explicit size.
      if (!d.enum_type.empty())
        os << d.enum_type << ' ';
      os << d.name;
      // The size is a parsed expression AST: deparse it like any
      // other expression, honoring its .parenthesized flags so the
      // user's grouping round-trips.
      if (d.size)
        {
          os << '[';
          tlsf_print_expr(os, *d.size);
          os << ']';
        }
      os << ";\n";
    }

    // Print a body that may be empty.  An empty body is rendered as
    // `KEY { }`, a non-empty body as `KEY { expr1;\n expr2;\n ... }`.
    // Each formula is deparsed from its AST node via tlsf_print_expr;
    // the deparser honors the .parenthesized flag and inserts
    // precedence-driven parens so the round-trip is stable.
    void print_body(std::ostream& os, const char* keyword,
                    const std::vector<tlsf_expr_ptr>& body)
    {
      if (body.empty())
        {
          os << "  " << keyword << " { }\n";
          return;
        }
      os << "  " << keyword << " {\n";
      for (const auto& e : body)
        {
          tlsf_print_expr(os, *e);
          os << ";\n";
        }
      os << "  }\n";
    }
  }

  // Print a TLSF dump of the parsed spec.  Comments, blank lines, and
  // the original indentation or section order are NOT preserved; the
  // goal is human inspection, not byte-for-byte round-tripping.
  // The output is itself is meant to be a valid TLSF spec equivalent to
  // the original one.
  void
  tlsf_print(std::ostream& os, const parsed_tlsf& parsed)
  {
    const auto& ast = parsed.ast;
    if (!ast)
      return;

    os << "INFO {\n";
      os << "  TITLE:       \""
         << escape_info_string(ast->title) << "\"\n";
      os << "  DESCRIPTION: \""
         << escape_info_string(ast->description) << "\"\n";
      os << "  SEMANTICS:   " << format_semantics(ast->semantics) << '\n';
      os << "  TARGET:      " << format_target(ast->target) << '\n';
      if (!ast->tags.empty())
        {
          os << "  TAGS:        ";
          for (size_t i = 0; i < ast->tags.size(); ++i)
            {
              if (i)
                os << ", ";
              os << ast->tags[i];
            }
          os << '\n';
        }
    os << "}\n\n";

    os << "GLOBAL {\n";
    if (ast->parameters.empty())
      os << "  PARAMETERS { }\n";
    else
      {
        os << "  PARAMETERS {\n";
        for (const auto& p : ast->parameters)
          {
            os << "    " << p.name << " = ";
            if (p.value)
              tlsf_print_expr(os, *p.value);
            os << ";\n";
          }
        os << "  }\n";
      }      if (ast->definitions.empty() && ast->enumerations.empty())
        os << "  DEFINITIONS { }\n";
      else
        {
          os << "  DEFINITIONS {\n";
          // Enums first: their position relative to regular
          // definitions is not preserved (parsetlsf.yy keeps
          // them in separate vectors).  Round-trip is byte-stable
          // iff the source ordering is "enums first, then
          // definitions"; re-parsing the canonical form yields
          // the same AST shape.
          for (const auto& e : ast->enumerations)
            {
              // Brace-less canonical form (Sec. 4.4 of the
              // TLSF specification): entries are whitespace-
              // separated, and each tag's patterns are comma-
              // separated.  The commas are MANDATORY here: two
              // juxtaposed bit runs are a diagnosed misparse (a
              // pattern is a single run of `0`, `1` and `*`), so
              // `A: 00 01` would not round-trip.
              os << "    enum " << e.name << " = ";
              for (size_t i = 0; i < e.entries.size(); ++i)
                {
                  if (i)
                    os << ' ';
                  const auto& v = e.entries[i];
                  os << v.tag << ':';
                  for (size_t j = 0; j < v.patterns.size(); ++j)
                    {
                      if (j)
                        os << ',';
                      os << v.patterns[j];
                    }
                }
              os << ";\n";
            }
          for (const auto& d : ast->definitions)
            {
              // Bodies are lists of clause AST nodes (no text
              // fallback), so we deparse directly via
              // tlsf_print_expr.  Argument names are COMMA-separated;
              // this must match parsetlsf.yy's `arg_list` rule.  The
              // deparser honors each node's .parenthesized flag and
              // inserts parens for loose-precedence BinaryOp /
              // Quantifier children, so the canonical form
              // round-trips through a fresh parse_tlsf without
              // losing grouping.
              os << "    " << d.name;
              // A parameterless definition (`m = log2(n);`) is
              // spelled without parentheses -- emitting `m() =`
              // would still parse, but the canonical form should
              // mirror the TLSF source style.
              if (!d.args.empty())
                {
                  os << '(';
                  for (size_t i = 0; i < d.args.size(); ++i)
                    {
                      if (i)
                        os << ", ";
                      os << d.args[i];
                    }
                  os << ')';
                }
              // Grammar invariant; mirrors translate.cc's assert().
              assert(!d.body.empty());
              if (d.body.size() == 1)
                {
                  // Single-clause bodies (the common macro case)
                  // keep the one-line spelling.
                  os << " = ";
                  assert(d.body[0]);
                  tlsf_print_expr(os, *d.body[0]);
                  os << ";\n";
                }
              else
                {
                  // Multi-clause (guarded) bodies print one clause
                  // per line; the clauses are juxtaposed maximal
                  // expressions, so the layout re-parses to the
                  // same clause list regardless of line breaks.
                  os << " =\n";
                  for (size_t i = 0; i < d.body.size(); ++i)
                    {
                      assert(d.body[i]);
                      os << "      ";
                      tlsf_print_expr(os, *d.body[i]);
                      os << (i + 1 == d.body.size() ? ";\n" : "\n");
                    }
                }
            }
          os << "  }\n";
        }
    os << "}\n\n";

    os << "MAIN {\n";
    if (ast->inputs.empty())
      os << "  INPUTS { }\n";
    else
      {
        os << "  INPUTS {\n";
        for (const auto& d : ast->inputs)
          print_ap(os, d);
        os << "  }\n";
      }
    if (ast->outputs.empty())
      os << "  OUTPUTS { }\n";
    else
      {
        os << "  OUTPUTS {\n";
        for (const auto& d : ast->outputs)
          print_ap(os, d);
        os << "  }\n";
      }
    print_body(os, "INITIALLY", ast->initially_body);
    print_body(os, "PRESET", ast->preset_body);
    // ASSUME/ASSUMPTIONS plural-aliases share `assumptions_body`;
    // emit it under the canonical singular keyword.
    print_body(os, "ASSUME", ast->assumptions_body);
    // REQUIRE/REQUIREMENTS share `require_body`; emit the
    // canonical singular.
    print_body(os, "REQUIRE", ast->require_body);
    // ASSERT/INVARIANTS share `assert_body`; emit canonical.
    print_body(os, "ASSERT", ast->assert_body);
    // GUARANTEE/GUARANTEES share `guarantee_body`; emit canonical.
    print_body(os, "GUARANTEE", ast->guarantee_body);
    os << "}\n";
  }

  // Copy the source metadata held in the AST built by the Bison
  // grammar actions onto the public parsed_tlsf so callers can
  // inspect it.  The AST itself (holding parameters, definitions,
  // enumerations, and the parsed MAIN bodies) is attached to out.ast
  // by the parse_tlsf entry points, which are friends of parsed_tlsf.
  // Bus expansion and parameter resolution remain for later phases.
  //
  // The caller-supplied parser-time overrides are mirrored onto
  // out.overrides so parsed_tlsf::overrides reflects the
  // documentation/round-trip contract promised by public.hh
  // (\"mirrored here for documentation and round-trip printing\").
  //
  // Note: the diagnostic list (`res.errors`) is moved out of \a res
  // by the caller (parse_tlsf) BEFORE this function runs, so we
  // only handle the AST-derived fields here.
  static void copy_tlsf_metadata(parsed_tlsf& out,
                                 const tlsf_result& res,
                                 const tlsf_parser_options& opts)
  {
    out.overrides = opts.overrides;
    if (!res.spec)
      return;
    out.title = res.spec->title;
    out.description = res.spec->description;
    out.semantics = res.spec->semantics;
    out.target = res.spec->target;
    out.tags = res.spec->tags;
    out.inputs.reserve(res.spec->inputs.size());
    for (const auto& d : res.spec->inputs)
      out.inputs.push_back(d.name);
    out.outputs.reserve(res.spec->outputs.size());
    for (const auto& d : res.spec->outputs)
      out.outputs.push_back(d.name);
  }

  namespace
  {
    /// The declaration space a name was declared in, for diagnostics.
    enum class decl_kind
    {
      parameter,
      definition,
      enumeration,
      input,
      output,
    };

    const char*
    kind_article(decl_kind k)
    {
      switch (k)
        {
        case decl_kind::parameter:
          return "a parameter";
        case decl_kind::definition:
          return "a definition";
        case decl_kind::enumeration:
          return "an enumeration";
        case decl_kind::input:
          return "an input signal";
        case decl_kind::output:
          return "an output signal";
        }
      SPOT_UNREACHABLE();
    }

    /// The system model of a SEMANTICS declaration.  The Strict and
    /// Finite modifiers do not change the model, only the
    /// composition built from it (see translate.cc).
    bool semantics_is_moore(tlsf_semantics s)
    {
      return s == tlsf_semantics::Moore
        || s == tlsf_semantics::MooreStrict
        || s == tlsf_semantics::MooreFinite;
    }

    /// The location to anchor a diagnostic about the INFO item at
    /// \a loc.  A location the parser never set is still at line 0;
    /// point at the start of the file in that case, so that a missing
    /// item (or a whole missing INFO section) is reported at 1.1
    /// rather than at 0.0.
    const location&
    info_anchor(const tlsf_ast& spec, const location& loc)
    {
      return loc.begin.line ? loc : spec.loc;
    }

    /// Run the cross-section validations of TLSF v1.2 on \a spec.
    ///
    /// These are the checks that need the whole file, and therefore
    /// cannot live in the grammar's per-construction actions.  They
    /// run once per successful parse, on the AST the parser built:
    ///
    ///  * every declared name is used once in the whole symbol space
    ///    (parameters, definitions, enumerations, inputs, outputs).
    ///    This covers SS1.3's `I \cap O = \emptyset` -- a signal
    ///    declared in both INPUTS and OUTPUTS, which the translator
    ///    would otherwise silently treat as an output -- and the
    ///    "one symbol = one definition" principle of SS1.2, whose
    ///    only enforcement so far was the parser's check of a
    ///    re-defined DEFINITION.  Two diagnostics are emitted per
    ///    collision, one at each declaration, as that check does.
    ///
    ///  * the mandatory INFO items (TITLE, DESCRIPTION, SEMANTICS,
    ///    TARGET) are all present, but only when \a check_info is
    ///    true.  An absent SEMANTICS is the most damaging omission
    ///    of the four, because the translator would compose the
    ///    formula as if the file had declared `Mealy`.
    ///
    ///  * the system model of SEMANTICS matches the TARGET player.
    ///    SS1.4 only defines the composition when the two agree, so a
    ///    mismatch is genuinely ambiguous rather than always wrong:
    ///    it is appended to \a warnings, never to \a errors, and the
    ///    declared SEMANTICS is used.  The check is skipped unless
    ///    both items were spelled out, so that a file that omits
    ///    them gets the "missing item" diagnostic alone.
    ///
    /// Appends to both lists; returns true iff \a errors was left
    /// empty, i.e. iff \a spec passes every fatal check.
    static bool
    validate_spec(const tlsf_ast& spec,
                  bool check_info,
                  parse_tlsf_error_list& errors,
                  parse_tlsf_error_list& warnings)
    {
      const size_t before = errors.size();

      // One symbol, one definition (SS1.2): a name that is declared
      // twice is a collision whichever of the declaration spaces the
      // two declarations come from, because all of them are looked up
      // in the same namespace by the translator.
      //
      // The declarations of the five spaces are collected into a single
      // list and sorted by source position, so that "the later
      // declaration" of a diagnostic really is the one written last,
      // whatever space each declaration belongs to (a DEFINITIONS block
      // may well come after the MAIN block that uses one of its names).
      //
      // Note that a re-defined DEFINITION does not reach this pass: the
      // parser drops the second one, so the AST holds a single
      // declaration and the parser's own pair of diagnostics is not
      // duplicated here.
      struct declaration
      {
        const std::string* name;
        decl_kind kind;
        location loc;
      };
      std::vector<declaration> declarations;
      auto declare = [&](const std::string& name, decl_kind kind,
                         const location& loc)
        {
          declarations.push_back({&name, kind, loc});
        };
      for (const auto& p: spec.parameters)
        declare(p.name, decl_kind::parameter, p.loc);
      for (const auto& d: spec.definitions)
        declare(d.name, decl_kind::definition, d.loc);
      for (const auto& e: spec.enumerations)
        declare(e.name, decl_kind::enumeration, e.loc);
      for (const auto& d: spec.inputs)
        declare(d.name, decl_kind::input, d.loc);
      for (const auto& d: spec.outputs)
        declare(d.name, decl_kind::output, d.loc);
      std::sort(declarations.begin(), declarations.end(),
                [](const declaration& a, const declaration& b)
                {
                  if (a.loc.begin.line != b.loc.begin.line)
                    return a.loc.begin.line < b.loc.begin.line;
                  return a.loc.begin.column < b.loc.begin.column;
                });

      // Report both declarations, as the parser's re-definition check
      // does: the first one is what the user has to delete or rename,
      // the second one is where they wrote the colliding name.
      for (size_t i = 1; i < declarations.size(); ++i)
        for (size_t j = 0; j < i; ++j)
          if (*declarations[i].name == *declarations[j].name)
            {
              const std::string& name = *declarations[i].name;
              errors.emplace_back(declarations[j].loc,
                                  "'" + name + "' is shadowed by a later "
                                  "declaration as "
                                  + kind_article(declarations[i].kind));
              errors.emplace_back(declarations[i].loc,
                                  "'" + name + "' is already declared as "
                                  + kind_article(declarations[j].kind));
              break;
            }

      // The four mandatory INFO items (SS1.2).  TAGS is optional and
      // is only checked for duplicates, which the grammar reports.
      if (check_info)
        {
          static const struct
          {
            unsigned bit;
            const char* name;
          } mandatory[] = {
            { TLSF_INFO_TITLE, "TITLE:" },
            { TLSF_INFO_DESCRIPTION, "DESCRIPTION:" },
            { TLSF_INFO_SEMANTICS, "SEMANTICS:" },
            { TLSF_INFO_TARGET, "TARGET:" },
          };
          const location& at = info_anchor(spec, spec.info_loc);
          for (const auto& item : mandatory)
            if (!(spec.info_seen & item.bit))
              errors.emplace_back(at, "missing mandatory INFO item '"
                                  + std::string(item.name) + "'");
        }

      // SEMANTICS and TARGET must agree on the system model (SS1.4).
      // Only when both are spelled out: an absent one would make the
      // comparison below a statement about the defaults rather than
      // about the file.
      if ((spec.info_seen & TLSF_INFO_SEMANTICS)
          && (spec.info_seen & TLSF_INFO_TARGET))
        {
          const char* semantics = semantics_is_moore(spec.semantics)
            ? "Moore" : "Mealy";
          const char* target = spec.target == tlsf_target::Moore
            ? "Moore" : "Mealy";
          if (std::string(semantics) != target)
            warnings.emplace_back(
              info_anchor(spec, spec.semantics_loc),
              std::string("SEMANTICS declares a ") + semantics
              + " system model, but TARGET declares " + target
              + "; the specification is ambiguous, the " + semantics
              + " composition is used");
        }

      return errors.size() == before;
    }
  }

  // Shared tail of the three parse_tlsf() overloads: check the
  // declarations of the AST the parser built, hand the diagnostics
  // and the AST over to the parsed_tlsf being returned, and honor
  // opts.raise_errors.
  void
  parsed_tlsf::finish_parse(tlsf_result& res,
                            const tlsf_parser_options& opts)
  {
    // The cross-section checks only run on a file the parser
    // understood: after a syntax error the AST is partial, and every
    // declaration the error swallowed would be reported as missing on
    // top of the syntax error itself.
    if (res.errors.empty() && res.spec)
      validate_spec(*res.spec, opts.check_info, res.errors, res.warnings);
    // Promote parser diagnostics before testing raise_errors.  The
    // scanner and Bison parser write into res.errors, not into the
    // public result directly.
    errors = std::move(res.errors);
    warnings = std::move(res.warnings);
    ast = res.spec;
    copy_tlsf_metadata(*this, res, opts);
    if (opts.raise_errors && !errors.empty())
      {
        std::ostringstream out;
        format_errors(out);
        throw std::runtime_error(out.str());
      }
  }

  // Open the scanner, wire the tlsf_result via yylex_init_extra
  // (registering it in tlsfyyopen), run yyparse(), then hand the
  // result over to finish_parse() above.
  parsed_tlsf_ptr
  parse_tlsf(const std::string& filename,
             const tlsf_parser_options& opts)
  {
    auto parsed = std::make_shared<parsed_tlsf>(filename);
    tlsf_result res;
    res.spec = std::make_shared<tlsf_ast>();

    void* scanner = nullptr;
    if (tlsfyyopen(filename, &scanner, res))
      {
        parsed->errors.emplace_back(
          location(),
          "cannot open file: " + filename);
        if (opts.raise_errors)
          {
            std::ostringstream out;
            parsed->format_errors(out);
            throw std::runtime_error(out.str());
          }
        return parsed;
      }

    {
      tlsfyy::parser parser(scanner, res);
      static bool env_debug = !!getenv("SPOT_DEBUG_PARSER");
      parser.set_debug_level(opts.debug || env_debug);
      parser.parse();
    }
    tlsfyyclose(scanner);
    parsed->finish_parse(res, opts);
    return parsed;
  }

  parsed_tlsf_ptr
  parse_tlsf(int fd,
             const std::string& filename,
             const tlsf_parser_options& opts)
  {
    auto parsed = std::make_shared<parsed_tlsf>(filename);
    tlsf_result res;
    res.spec = std::make_shared<tlsf_ast>();

    void* scanner = nullptr;
    if (tlsfyyopen(fd, &scanner, res))
      {
        parsed->errors.emplace_back(
          location(),
          "cannot open descriptor for TLSF parsing");
        if (opts.raise_errors)
          {
            std::ostringstream out;
            parsed->format_errors(out);
            throw std::runtime_error(out.str());
          }
        return parsed;
      }

    {
      tlsfyy::parser parser(scanner, res);
      parser.set_debug_level(opts.debug);
      parser.parse();
    }
    tlsfyyclose(scanner);
    parsed->finish_parse(res, opts);
    return parsed;
  }

  parsed_tlsf_ptr
  parse_tlsf(const std::string& contents,
             const std::string& name,
             const tlsf_parser_options& opts)
  {
    auto parsed = std::make_shared<parsed_tlsf>(name);
    tlsf_result res;
    res.spec = std::make_shared<tlsf_ast>();

    void* scanner = nullptr;
    if (tlsfyystring(contents.c_str(), &scanner, res))
      {
        // Only a failure of yylex_init_extra gets here (the memory
        // allocation of the scanner state).  scanner is still null,
        // so the parser must not be constructed on top of it.
        parsed->errors.emplace_back(
          location(),
          "cannot initialize the TLSF scanner");
        if (opts.raise_errors)
          {
            std::ostringstream out;
            parsed->format_errors(out);
            throw std::runtime_error(out.str());
          }
        return parsed;
      }

    {
      tlsfyy::parser parser(scanner, res);
      parser.set_debug_level(opts.debug);
      parser.parse();
    }
    tlsfyyclose(scanner);
    parsed->finish_parse(res, opts);
    return parsed;
  }

  // Walk the AST, evaluate integer contexts, expand buses and ranges,
  // and compose the provisional synthesis formula.  Unsupported
  // language constructs surface as diagnostics (see translate.hh).
  tlsf_translation_result
  tlsf_to_ltl(const parsed_tlsf& tlsf,
              const tlsf_translator_options& opts,
              parse_tlsf_error_list* errors_out)
  {
    if (!tlsf.ast)
      {
        if (errors_out)
          errors_out->emplace_back(location(),
                                   "tlsf_to_ltl: empty AST");
        return tlsf_translation_result{};
      }
    // Parser-time overrides are the defaults for conversion.  A
    // translation-time override has higher precedence and therefore
    // replaces the corresponding parser-time value.
    tlsf_translator_options effective = opts;
    for (const auto& kv : tlsf.overrides)
      if (!effective.overrides.count(kv.first))
        effective.overrides[kv.first] = kv.second;
    // Composing the output formula can trip an assertion-free limit
    // deep inside spot's formula layer: fnode::nary refuses more
    // children than the configured maximum and throws
    // std::runtime_error (see spot/tl/formula.cc).  A specification
    // pathological enough to hit that must not take a whole tool
    // down, so turn the exception into a diagnostic.  With
    // raise_errors the caller still gets the exception, re-thrown
    // below so its usual contract is unchanged.
    try
      {
        tlsf::translator tr(*tlsf.ast, effective, errors_out);
        return tr.run();
      }
    catch (const std::runtime_error& e)
      {
        if (errors_out)
          errors_out->emplace_back(location(),
                                   std::string("tlsf_to_ltl: ")
                                   + e.what());
        if (effective.raise_errors)
          throw;
        tlsf_translation_result partial;
        return partial;
      }
  }
}
