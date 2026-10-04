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

// This private header (NOT installed) holds the whole TLSF AST:
// the expression node type `tlsf_expr` (tagged struct), the enum
// declarations, the helper predicates, the
// input/output/parameter/definition declaration records, and the root
// `tlsf_ast` struct.  Only the
// forward declaration of `tlsf_ast` (and of `tlsf_expr` where it
// appears in public signatures) escapes through
// spot/parsetlsf/public.hh; the field layouts live here so they can
// evolve without breaking ABI.  The deparser that renders an
// expression node is private to spot/parsetlsf/public.cc.

#pragma once

#include <spot/misc/common.hh>
#include <spot/misc/location.hh>
#include <spot/parsetlsf/public.hh>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

namespace spot
{
  /// \brief Kind of an expression node.
  ///
  /// Tagged-struct approach: a single \c tlsf_expr carries a type tag
  /// in `.type`; meaningful fields are `.op`, `.name`, `.val`, and
  /// `.children` depending on the tag.
  enum class tlsf_expr_type : std::uint8_t
  {
    LiteralInt,         //!< integer literal: `.val`
    Identifier,         //!< bare identifier: `.name`
    BusRef,             //!< `name [ .children[0] ]`
    App,                //!< `.name(.children[0..n])`
    UnaryOp,            //!< `.op .children[0]`
    BinaryOp,           //!< `.children[0] .op .children[1]`
    Quantifier,         //!< `op [ .children[0] ] .children[1]`
    SetExplicit,        //!< `{ .children[0..n] }`
    SetRange,           //!< `{ .children[0] .. .children[1] }`
  };

  /// \brief Operator tag for UnaryOp / BinaryOp / Quantifier.
  enum class tlsf_op : std::uint8_t
  {
    None,

    // Boolean unary
    Not,

    // LTL unary
    G,
    F,
    X,
    StrongNext,        //!< LTLf `X[!]`
    // Stacked next `X[n] phi`: n nested next operators.  Stored as a
    // Quantifier node whose bound is the integer expression `n`; the
    // printer emits the `X[n] phi` surface syntax and the translator
    // expands it at LTL-conversion time.
    XStack,
    // `StrongXStack` is the LTLf flavour `X[!n] phi` / `X[n!] phi`,
    // lowered with strong next instead of weak next.
    StrongXStack,
    // Bounded temporal operators `F[a:b] phi` / `G[a:b] phi`
    // Stored as a Quantifier node with three children
    // [lower bound, upper bound, body]; the bounds are integer
    // expressions while the body is an LTL expression.  The printer
    // emits the `F[a:b] phi` surface syntax and the translator
    // lowers them to plain LTL.
    FBounded,
    GBounded,
    // `StrongFBounded` and `StrongGBounded` are the LTLf flavours
    // `F[!a:b] phi` / `F[a:b!] phi` and `G[!a:b] phi` /
    // `G[a:b!] phi`; the printer carries the `!` marker and the
    // translator lowers them with strong next.
    StrongFBounded,
    StrongGBounded,

    // Boolean binary
    And,
    Or,
    Implies,
    Equiv,

    // Guard selection `guard : body`, used by the (possibly
    // several) clauses of a DEFINITION body.  TLSF v1.2 Table 1
    // lists the guard operator at the loosest precedence (row 19);
    // at translation time the first clause whose guard is true is
    // selected and its body expanded.
    Guard,

    // Pattern match `subject ~ pattern`, the second form a clause
    // guard may take (Table 1 row 18, one tier tighter than `:`).
    // `children[0]` is the LTL expression the pattern is matched
    // against and `children[1]` the pattern itself, whose
    // identifiers are metavariables bound to the subexpressions
    // they match (see tlsf_pattern_vars below and
    // translator::match_pattern).
    PatternMatch,

    // LTL binary
    U,
    R,
    W,

    // Comparison
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    In,                //!< set membership
    SetUnion,
    SetIntersection,
    SetDifference,

    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Set folding.  These six tags carry a big operator with an
    // already-desugared binder list: `tlsf_make_bigop` turns
    // `OP[b0, b1] body` into nested tlsf_op::And / tlsf_op::Or
    // quantifiers, one per binder, and the remaining tag only records
    // which operation the head denoted.
    BigSum,              //!< `+[` (alias `SUM[`)
    BigProd,             //!< `*[` (alias `PROD[`)
    BigUnion,            //!< `(+)[` (alias `CUP[`)
    BigInter,            //!< `(*)[` (alias `CAP[`)
    BigDiff,             //!< `(-)[` (alias `SETMINUS[`)

    // Set cardinality `|eSX|` and its `SIZE` alias.
    SetSize,
    // Cardinality-folded extrema `MIN eSX` / `MAX eSX`, which build a
    // cardinality guard `(v == |eSX|)` rather than a quantifier.
    SetMin,
    SetMax,
  };

  /// \brief A single TLSF expression node (tagged struct).
  ///
  /// Carries a \c spot::location for diagnostics. The `.parenthesized`
  /// flag records whether the source explicitly parenthesised this
  /// sub-expression; tlsf_print re-emits those parens verbatim so the
  /// round-trip is stable.
  struct SPOT_API tlsf_expr
  {
    /// Source location of the node, for diagnostics.
    location loc;

    // The three small fields below occupy one byte each thanks to the
    // enums' std::uint8_t underlying type -- a plain member of such an
    // enum is exactly one byte, so no bit-field width is needed.  They
    // are kept adjacent so the tag group takes 3 bytes instead of 9
    // (two 4-byte enums + a padded bool).

    /// Tag selecting which fields are meaningful.
    tlsf_expr_type type;

    /// Operator (only meaningful for UnaryOp / BinaryOp / Quantifier).
    tlsf_op op;

    /// True iff the source explicitly parenthesised this
    /// sub-expression. Round-trip printing re-emits those parens.
    bool parenthesized;

    /// True if this expression or any of its subexpressions is an App.
    bool has_app = false;

    /// True if this expression or any subexpression can name a
    /// definition formal, i.e. is an Identifier, a BusRef, or a
    /// Quantifier (whose loop variable can capture an outer formal).
    /// LiteralInt subtrees carry no name, so `single(a + 1)` has
    /// this false and the substitution pass hands it back untouched.
    bool has_binding_target = false;

    /// Identifier name (Identifier / BusRef base / App callee).
    std::string name;

    /// Integer literal value (LiteralInt only).
    long long val = 0;

    /// Children:
    ///   UnaryOp / BinaryOp: operands
    ///   BusRef: index expression
    ///   App: arguments in order
    ///   Quantifier: [0] bound expression, [1] body.  The bound keeps
    ///     its original source tree verbatim (e.g. `(0 <= i) < N` or
    ///     `i IN {0, 1}`); the two TLSF bound shapes are distinguished
    ///     during translation to LTL rather than at parse time, so no
    ///     derived metadata is stored on the node.
    ///   SetExplicit: elements
    ///   SetRange: [lo] [hi]
    std::vector<std::shared_ptr<tlsf_expr>> children;

    /// Initialize the small fields so a default-constructed node
    /// carries a harmless (Identifier, None, unparenthesized) tag
    /// group.
    tlsf_expr()
      : type(tlsf_expr_type::Identifier),
        op(tlsf_op::None),
        parenthesized(false),
        has_app(false),
        has_binding_target(false)
    {
    }
  };

  /// \brief Shared-pointer alias used throughout the AST.
  typedef std::shared_ptr<tlsf_expr> tlsf_expr_ptr;

  // --- helpers: classes and predicates ---------------------------------

  /// Render an operator tag back to canonical TLSF punctuation.
  inline std::string tlsf_format_op(tlsf_op op)
  {
    switch (op)
      {
      case tlsf_op::Not:
        return "!";
      case tlsf_op::Guard:
        return ":";
      case tlsf_op::PatternMatch:
        return "~";
      case tlsf_op::G:
        return "G";
      case tlsf_op::XStack:
        return "X";
      case tlsf_op::FBounded:
      case tlsf_op::StrongFBounded:
        return "F";
      case tlsf_op::GBounded:
      case tlsf_op::StrongGBounded:
        return "G";
      case tlsf_op::F:
        return "F";
      case tlsf_op::X:
      case tlsf_op::StrongXStack:
        return "X";
      case tlsf_op::StrongNext:
        return "X[!]";
      case tlsf_op::And:
        return "&&";
      case tlsf_op::Or:
        return "||";
      case tlsf_op::Implies:
        return "->";
      case tlsf_op::Equiv:
        return "<->";
      case tlsf_op::U:
        return "U";
      case tlsf_op::R:
        return "R";
      case tlsf_op::W:
        return "W";
      case tlsf_op::Eq:
        return "==";
      case tlsf_op::Neq:
        return "!=";
      case tlsf_op::Lt:
        return "<";
      case tlsf_op::Le:
        return "<=";
      case tlsf_op::Gt:
        return ">";
      case tlsf_op::Ge:
        return ">=";
      case tlsf_op::In:
        return "IN";
      case tlsf_op::SetUnion:
        return "CUP";
      case tlsf_op::SetIntersection:
        return "CAP";
      case tlsf_op::SetDifference:
        return "SETMINUS";
      case tlsf_op::Add:
        return "+";
      case tlsf_op::Sub:
        return "-";
      case tlsf_op::Mul:
        return "*";
      case tlsf_op::Div:
        return "/";
      case tlsf_op::Mod:
        return "%";
      case tlsf_op::BigSum:
        return "SUM[";
      case tlsf_op::BigProd:
        return "PROD[";
      case tlsf_op::BigUnion:
        return "CUP[";
      case tlsf_op::BigInter:
        return "CAP[";
      case tlsf_op::BigDiff:
        return "SETMINUS[";
      case tlsf_op::SetSize:
        return "|";
      case tlsf_op::SetMin:
        return "MIN";
      case tlsf_op::SetMax:
        return "MAX";
      case tlsf_op::None:
        return "";
      }
    return "";
  }

  // --- constructor helpers used by parsetlsf.yy -----------------------

  /// \brief Recompute the summary flags of \a e from its children.
  ///
  /// Both flags are monotone over the subtree, so a single pass over
  /// the direct children is enough once the children already carry
  /// their own flags.  Every tlsf_make_* helper calls this as its
  /// last step; deriving the flags here rather than inline at each
  /// call site keeps them correct even when a helper moves a child
  /// pointer into `children` before reading it.
  inline void tlsf_update_flags(const tlsf_expr_ptr& e)
  {
    if (!e)
      return;
    e->has_app = e->type == tlsf_expr_type::App;
    e->has_binding_target =
      e->type == tlsf_expr_type::Identifier
      || e->type == tlsf_expr_type::BusRef
      || e->type == tlsf_expr_type::Quantifier;
    for (const auto& ch : e->children)
      {
        if (!ch)
          continue;
        if (ch->has_app)
          e->has_app = true;
        if (ch->has_binding_target)
          e->has_binding_target = true;
      }
  }

  /// \brief Build a LiteralInt node for integer literal \a v at \a loc.
  inline tlsf_expr_ptr tlsf_make_int(location loc, long long v)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::LiteralInt;
    e->val = v;
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build an Identifier node named \a name at \a loc.
  inline tlsf_expr_ptr tlsf_make_ident(location loc, std::string name)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::Identifier;
    e->name = std::move(name);
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a BusRef node \a name at \a loc, with optional index
  /// expression \a index (a scalar reference when it is null).
  inline tlsf_expr_ptr tlsf_make_busref(location loc,
                                        std::string name,
                                        tlsf_expr_ptr index)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::BusRef;
    e->name = std::move(name);
    if (index)
      e->children.push_back(std::move(index));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build an App node calling \a name on \a args at \a loc.
  ///
  /// This covers both built-in functions (MIN/MAX/SUM/PROD/SIZEOF)
  /// and calls to user-defined DEFINITIONS entries.
  inline tlsf_expr_ptr tlsf_make_app(location loc,
                                     std::string name,
                                     std::vector<tlsf_expr_ptr> args)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::App;
    e->name = std::move(name);
    e->children = std::move(args);
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a UnaryOp node applying \a op to \a child at \a loc.
  ///
  /// A null \a child is tolerated by the parser while it recovers
  /// from an error; the node is then built without children.
  inline tlsf_expr_ptr tlsf_make_unop(tlsf_op op, location loc,
                                      tlsf_expr_ptr child)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::UnaryOp;
    e->op = op;
    if (child)
      e->children.push_back(std::move(child));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a BinaryOp node \a lhs \a op \a rhs at \a loc.
  ///
  /// A null \a lhs or \a rhs is tolerated by the parser while it
  /// recovers from an error; the node is then built with fewer
  /// children.
  inline tlsf_expr_ptr tlsf_make_binop(tlsf_op op, location loc,
                                       tlsf_expr_ptr lhs, tlsf_expr_ptr rhs)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::BinaryOp;
    e->op = op;
    if (lhs)
      e->children.push_back(std::move(lhs));
    if (rhs)
      e->children.push_back(std::move(rhs));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a Quantifier node \a op[\a bound] \a body at \a loc.
  ///
  /// \a op is Forall or Exists; a null \a bound or \a body is
  /// tolerated by the parser while it recovers from an error.
  inline tlsf_expr_ptr tlsf_make_quantifier(tlsf_op op, location loc,
                                            tlsf_expr_ptr bound,
                                            tlsf_expr_ptr body)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::Quantifier;
    e->op = op;
    if (bound)
      e->children.push_back(std::move(bound));
    if (body)
      e->children.push_back(std::move(body));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Which connective a big operator expands into.
  ///
  /// Every TLSF big operator binds one identifier per binder and folds
  /// the body with one of the two Boolean connectives: `AND[`, `&&[`,
  /// `SUM[`, `PROD[`, `MIN[`, `MAX[` use \c And (conjunction), while
  /// `OR[`, `||[`, `CUP[`, `CAP[`, `SETMINUS[` use \c Or (disjunction).
  /// This is the same expansion syfco performs, where `&&[X] e` is
  /// literally `forall X. e`.
  enum class tlsf_bigop_fold
  {
    And,
    Or,
  };

  /// \brief The connective a big operator expands into, as a tlsf_op.
  inline tlsf_op tlsf_fold_op(tlsf_bigop_fold fold)
  {
    return fold == tlsf_bigop_fold::And ? tlsf_op::And : tlsf_op::Or;
  }

  /// \brief The iteration variable a quantifier bound introduces.
  ///
  /// TLSF v1.2 SS4.7 gives a binder exactly two shapes: the membership
  /// `id IN eSX`, and the range `n .o.1 id .o.2 m` whose two relational
  /// operators are both drawn from `<` and `<=` (SS4.8).  In the AST the
  /// range arrives as the nested comparison `((n .o.1 id) .o.2 m)`, so
  /// the identifier sits on the right of the inner comparison, and the
  /// inclusivity of each end of the range is the spelling of its own
  /// operator.
  ///
  /// Returns null when \a bound has neither shape.  That covers the
  /// variable-less bounds Spot used to accept (`&&[{0, 1}]`, `&&[3]`)
  /// as well as a range spelled with `>`, `>=`, `==`, or `!=`.
  /// syfco rejects the same set in a pass of its own that runs before
  /// type inference (Bindings.conditional, reported as a syntax
  /// error), and the parser calls this on every binder so that such a
  /// bound never reaches the translator.
  inline const std::string* tlsf_binder_variable(const tlsf_expr& bound)
  {
    // The variable is never a position in the comparison: it is the LHS
    // of `IN`, or the RHS of the inner comparison of a range.
    auto is_identifier = [](const tlsf_expr_ptr& e)
      {
        return e && e->type == tlsf_expr_type::Identifier;
      };
    if (bound.type == tlsf_expr_type::BinaryOp
        && bound.children.size() >= 2
        && (bound.op == tlsf_op::Lt || bound.op == tlsf_op::Le)
        && bound.children[0]
        && bound.children[0]->type == tlsf_expr_type::BinaryOp
        && (bound.children[0]->op == tlsf_op::Lt
            || bound.children[0]->op == tlsf_op::Le)
        && bound.children[0]->children.size() >= 2
        && is_identifier(bound.children[0]->children[1]))
      return &bound.children[0]->children[1]->name;
    if (bound.type == tlsf_expr_type::BinaryOp
        && bound.children.size() >= 2
        && bound.op == tlsf_op::In
        && is_identifier(bound.children[0]))
      return &bound.children[0]->name;
    return nullptr;
  }

  /// \brief The name the pattern wildcard `_` is stored under.
  ///
  /// The scanner returns `_` as a token of its own (it is a reserved
  /// word, as it is in syfco), and the grammar builds it as an ordinary
  /// Identifier, so a wildcard costs no new \c tlsf_expr_type and needs
  /// no new arm in the many exhaustive switches over \c
  /// tlsf_expr_type.  Every predicate that walks a pattern therefore has
  /// to recognise this one name, which is why it is named here rather
  /// than spelled out at each of them.
  inline constexpr const char* tlsf_pattern_wildcard = "_";

  /// \brief True iff \a e is the `_` wildcard.
  inline bool tlsf_is_wildcard(const tlsf_expr& e)
  {
    return e.type == tlsf_expr_type::Identifier
      && e.name == tlsf_pattern_wildcard;
  }

  /// \brief True iff \a e is one of the two Boolean literals.
  ///
  /// `true` and `false` are Identifiers in the AST (see the `BOOL_TRUE`
  /// and `BOOL_FALSE` productions of spot/parsetlsf/parsetlsf.yy), so a
  /// pattern that names one of them is a leaf rather than a
  /// metavariable.
  inline bool tlsf_is_bool_literal(const tlsf_expr& e)
  {
    return e.type == tlsf_expr_type::Identifier
      && (e.name == "true" || e.name == "false");
  }

  /// \brief The children of \a e that a pattern may descend into.
  ///
  /// Every node of a legal pattern except a Quantifier contributes
  /// all of its children.  A Quantifier is different: its trailing
  /// child is the formula the operator scopes over, and that is the
  /// only part that is a pattern.  The leading children are bounds
  /// (`X[n]`'s stack length, `F[lo:hi]`'s two bounds, a binder run's)
  /// and they are integer expressions (or a binder), not LTL, so
  /// SS4.6 gives them no pattern reading and they are compared as
  /// numbers by the matcher instead.
  ///
  /// syfco's getPatternIds (Abstraction.hs:441-473) makes exactly this
  /// cut: it recurses into the body of `LtlRGlobally _ x` and into
  /// both operands of `LtlUntil x y`, and never into a bound.
  inline void
  tlsf_pattern_children(const tlsf_expr& e,
                        std::vector<const tlsf_expr*>& out)
  {
    if (e.type != tlsf_expr_type::Quantifier)
      {
        for (const auto& ch : e.children)
          if (ch)
            out.push_back(ch.get());
        return;
      }
    if (!e.children.empty() && e.children.back())
      out.push_back(e.children.back().get());
  }

  /// \brief True iff \a e is a metavariable of a pattern.
  ///
  /// TLSF v1.2 SS4.6: "every identifier expression that appears in
  /// \c phi' is bound to the equivalent sub-expression in \c phi".  So
  /// every identifier of a pattern is a metavariable, and only the two
  /// exceptions are leaves: the wildcard and the Boolean literals.
  inline bool tlsf_is_pattern_var(const tlsf_expr& e)
  {
    return e.type == tlsf_expr_type::Identifier
      && e.name != tlsf_pattern_wildcard && e.name != "true"
      && e.name != "false";
  }

  /// \brief True iff the operator of \a e may head a pattern.
  ///
  /// This is the single authority on which connectives a pattern may
  /// use: the parser validates a pattern with \ref tlsf_pattern_valid
  /// (which calls this), and translator::match_pattern dispatches on
  /// exactly these tags.  Keeping the list here is what keeps the two
  /// from drifting apart -- a connective this admits is one the
  /// matcher can compare, and one it rejects never reaches it.
  ///
  /// The admitted set mirrors syfco's `getPatternIds`
  /// (refs/syfco/src/lib/Reader/Abstraction.hs:441-473), which walks
  /// the same Boolean and temporal constructors and reports anything
  /// else through `errPattern`: the Boolean connectives, the unary and
  /// binary temporal operators, the bounded and stacked spellings of
  /// the latter, and the quantifier run a big operator desugars into.
  /// Integer arithmetic, comparisons, membership, set expressions and
  /// bus references are excluded, as they are in syfco.
  inline bool tlsf_pattern_op_is_legal(tlsf_op op, tlsf_expr_type type)
  {
    switch (type)
      {
      case tlsf_expr_type::UnaryOp:
        switch (op)
          {
          case tlsf_op::Not:
          case tlsf_op::X:
          case tlsf_op::StrongNext:
          case tlsf_op::G:
          case tlsf_op::F:
            return true;
          default:
            return false;
          }
      case tlsf_expr_type::BinaryOp:
        switch (op)
          {
          case tlsf_op::And:
          case tlsf_op::Or:
          case tlsf_op::Implies:
          case tlsf_op::Equiv:
          case tlsf_op::U:
          case tlsf_op::W:
          case tlsf_op::R:
            return true;
          default:
            return false;
          }
      case tlsf_expr_type::Quantifier:
        // A quantifier node carries either a binder run -- which is
        // what `&&[b] e`, `||[b] e` and the four big-operator heads
        // desugar into, and which the AST no longer distinguishes from
        // a plain `And`/`Or` node -- or one of the bounded and stacked
        // temporal spellings of SS4.8.
        switch (op)
          {
          case tlsf_op::And:
          case tlsf_op::Or:
          case tlsf_op::XStack:
          case tlsf_op::StrongXStack:
          case tlsf_op::FBounded:
          case tlsf_op::GBounded:
          case tlsf_op::StrongFBounded:
          case tlsf_op::StrongGBounded:
            return true;
          default:
            return false;
          }
      default:
        return false;
      }
  }

  /// \brief The first subexpression of \a pat that may not appear in a
  /// pattern, or null if \a pat is well-formed.
  ///
  /// Returning the offending node rather than a bool is what lets a
  /// caller point the diagnostic at it and name what it is: a pattern
  /// can be wrong deep inside, and the interesting part of the message
  /// is which construct was rejected.
  inline const tlsf_expr* tlsf_pattern_invalid(const tlsf_expr& pat)
  {
    if (tlsf_is_wildcard(pat) || tlsf_is_bool_literal(pat)
        || tlsf_is_pattern_var(pat))
      return nullptr;
    if (!tlsf_pattern_op_is_legal(pat.op, pat.type))
      return &pat;
    std::vector<const tlsf_expr*> children;
    tlsf_pattern_children(pat, children);
    for (const tlsf_expr* ch : children)
      if (const tlsf_expr* bad = tlsf_pattern_invalid(*ch))
        return bad;
    return nullptr;
  }

  /// \brief True iff \a pat is a well-formed pattern.
  ///
  /// A pattern is built by the grammar from a general expression, so
  /// this is what rejects the shapes SS4.6 does not give one -- an
  /// integer literal, an arithmetic or comparison subexpression, a bus
  /// reference, a set literal, a nested pattern -- as well as a
  /// connective \ref tlsf_pattern_op_is_legal excludes.  The parser
  /// calls it on the right-hand side of every `~` (see check_pattern in
  /// spot/parsetlsf/parsetlsf.yy), so a bad pattern is reported even
  /// in a definition that is never called, exactly as a malformed
  /// binder is.
  inline bool tlsf_pattern_valid(const tlsf_expr& pat)
  {
    return tlsf_pattern_invalid(pat) == nullptr;
  }

  /// \brief Explain, in a fragment of a sentence, why \a e is not
  /// allowed in a pattern.
  ///
  /// \a e is expected to be a node \ref tlsf_pattern_invalid returned;
  /// the caller prefixes and suffixes it.
  inline std::string tlsf_pattern_invalid_reason(const tlsf_expr& e)
  {
    switch (e.type)
      {
      case tlsf_expr_type::LiteralInt:
        return "an integer literal cannot appear in a pattern";
      case tlsf_expr_type::BinaryOp:
        if (e.op == tlsf_op::PatternMatch)
          return "a pattern cannot itself contain `~`";
        return "`" + tlsf_format_op(e.op)
          + "' cannot appear in a pattern";
      case tlsf_expr_type::UnaryOp:
        return "`" + tlsf_format_op(e.op)
          + "' cannot appear in a pattern";
      case tlsf_expr_type::Quantifier:
        return "the `" + tlsf_format_op(e.op)
          + "' quantifier cannot appear in a pattern";
      case tlsf_expr_type::App:
        return "a function call cannot appear in a pattern";
      case tlsf_expr_type::BusRef:
        return "a bus reference cannot appear in a pattern";
      case tlsf_expr_type::SetExplicit:
      case tlsf_expr_type::SetRange:
        return "a set literal cannot appear in a pattern";
      default:
        return "this expression cannot appear in a pattern";
      }
  }

  /// \brief Collect the metavariables of \a pat, outermost first.
  ///
  /// \a out receives the Identifier nodes of \a pat that \ref
  /// tlsf_is_pattern_var admits, in source order, so a caller can
  /// report the name and the location of every binding a pattern
  /// introduces.  Duplicates are NOT filtered: binding the same name
  /// twice is a diagnostic the caller reports, not something this
  /// silently drops.
  inline void tlsf_pattern_vars(const tlsf_expr& pat,
                                std::vector<const tlsf_expr*>& out)
  {
    if (tlsf_is_pattern_var(pat))
      {
        out.push_back(&pat);
        return;
      }
    if (tlsf_is_wildcard(pat) || tlsf_is_bool_literal(pat))
      return;
    if (!tlsf_pattern_op_is_legal(pat.op, pat.type))
      return;
    std::vector<const tlsf_expr*> children;
    tlsf_pattern_children(pat, children);
    for (const tlsf_expr* ch : children)
      tlsf_pattern_vars(*ch, out);
  }

  /// \brief Nest \a binders into quantifiers around \a body at \a loc.
  ///
  /// The binders are folded right-to-left, so `q[b0, b1, b2] body`
  /// becomes `q[b0] q[b1] q[b2] body` with the first binder outermost;
  /// this matches syfco, where `q[b0,b1] e` is accepted as a shorthand
  /// for `q[b0] q[b1] e`.  \a qop is the quantifier tag the fold uses.
  ///
  /// A null bound is tolerated while the parser recovers from an error:
  /// it simply contributes no quantifier at that position.
  inline tlsf_expr_ptr tlsf_make_binders(tlsf_op qop, location loc,
                                         const std::vector<tlsf_expr_ptr>&
                                           binders,
                                         tlsf_expr_ptr body)
  {
    tlsf_expr_ptr res = body;
    for (auto it = binders.rbegin(); it != binders.rend(); ++it)
      if (*it)
        res = tlsf_make_quantifier(qop, loc, *it, res);
    return res;
  }

  /// \brief Build the big operator `OP[\a binders] \a body` at \a loc.
  ///
  /// \a op selects the fold (see \ref tlsf_op::BigSum and friends) and \a
  /// fold the quantifier it expands into.  The body is the nested run of
  /// binders built by \ref tlsf_make_binders, kept as the single child
  /// of a node tagged \a op so the deparser can tell which head
  /// introduced it.
  inline tlsf_expr_ptr tlsf_make_bigop(tlsf_op op, tlsf_bigop_fold fold,
                                       location loc,
                                       const std::vector<tlsf_expr_ptr>&
                                         binders,
                                       tlsf_expr_ptr body)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::UnaryOp;
    e->op = op;
    tlsf_expr_ptr nested = tlsf_make_binders(tlsf_fold_op(fold), loc,
                                             binders, std::move(body));
    if (nested)
      e->children.push_back(std::move(nested));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a bounded-temporal Quantifier node `op[lo:hi] body`.
  ///
  /// \a op is FBounded, GBounded, StrongFBounded or StrongGBounded --
  /// the two Strong tags being the LTLf flavour, whose printer output
  /// carries the `!` marker.  Unlike \ref tlsf_make_quantifier,
  /// the node carries three children: the lower bound, the upper bound
  /// (both integer expressions), and the body.  A null bound or body is
  /// tolerated while the parser recovers from an error.
  inline tlsf_expr_ptr tlsf_make_bounded(tlsf_op op, location loc,
                                         tlsf_expr_ptr lo,
                                         tlsf_expr_ptr hi,
                                         tlsf_expr_ptr body)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::Quantifier;
    e->op = op;
    if (lo)
      e->children.push_back(std::move(lo));
    if (hi)
      e->children.push_back(std::move(hi));
    if (body)
      e->children.push_back(std::move(body));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a SetExplicit node listing \a elements at \a loc.
  inline tlsf_expr_ptr tlsf_make_set_explicit(
      location loc,
      std::vector<tlsf_expr_ptr> elements)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::SetExplicit;
    e->children = std::move(elements);
    tlsf_update_flags(e);
    return e;
  }

  /// \brief Build a SetRange node {\a lo .. \a hi} at \a loc.
  inline tlsf_expr_ptr tlsf_make_set_range(location loc,
                                            tlsf_expr_ptr lo,
                                            tlsf_expr_ptr hi)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::SetRange;
    if (lo)
      e->children.push_back(std::move(lo));
    if (hi)
      e->children.push_back(std::move(hi));
    tlsf_update_flags(e);
    return e;
  }

  /// \brief A single value (Tag : patterns) entry of an enum decl.
  ///
  /// A tag is followed by one or more comma-separated bit patterns,
  /// e.g.  `UNDEF: 11*, 1*1, *11`.  Each pattern is kept as raw text:
  /// a sequence of `0`, `1`, and (don't-care) `*` characters.  The
  /// enum's bit width is the length of the first pattern; the parser
  /// rejects entries whose patterns do not all have that width.
  struct SPOT_API tlsf_enum_value
  {
    /// Source location of the entry (tag through its last pattern).
    location loc;
    /// Symbolic tag name.
    std::string tag;
    /// Bit patterns bound to this tag (usually exactly one),
    /// each a raw string such as "00", "01", or "1*0".
    std::vector<std::string> patterns;
  };

  /// \brief An `enum` declaration from GLOBAL/DEFINITIONS.
  ///
  /// Spot stores only the name and entries; coverage and duplicate
  /// detection is deferred to the translator.
  struct SPOT_API tlsf_enum_decl
  {
    /// Source location of the decl (covers `enum` through `;`).
    location loc;
    /// Enum name.
    std::string name;
    /// Entries in source order.
    std::vector<tlsf_enum_value> entries;
  };

  /// \brief An input or output declaration from the MAIN block.
  ///
  /// A declaration is either a simple variable (`oti;`), a bus of
  /// size given by either a numeric literal (`os[8];`) or a parameter
  /// name (`ix[N];`), or a typed bus whose width comes from a
  /// declared enumeration (`hburst HBURST;`).  In all cases the
  /// translator resolves the width once parameter overrides are known
  /// (typed buses get the enum's bit width).
  struct tlsf_ap_decl
  {
    /// Source location of the declaration.
    location loc;
    /// Variable or bus name.
    std::string name;
    /// Parsed bus-size expression (arithmetic over literals,
    /// parameters, and definitions, as in `os[N*M];`); null means
    /// a single (scalar) AP or a typed bus (see enum_type).  The
    /// translator evaluates it to an integer width with eval_int
    /// once parameter overrides are known.
    tlsf_expr_ptr size;
    /// Enum type name for a typed-bus declaration
    /// (`enumType SIGNAL;`); empty for scalars and size buses.
    /// The signal's width is the bit width of the named enum.
    std::string enum_type;
  };

  /// \brief A PARAMETERS block entry from GLOBAL.
  struct tlsf_parameter_decl
  {
    /// Source location of the entry.
    location loc;
    /// Parameter name.
    std::string name;
    /// Parsed value expression, as written in the file.  The
    /// translator evaluates it to an integer when overrides are
    /// applied.
    tlsf_expr_ptr value;
  };

  /// \brief A DEFINITIONS block entry from GLOBAL.
  ///
  /// The body is a list of clause expressions (LTL ops, boolean ops,
  /// bus references, integer arithmetic), not text.  Expansion uses
  /// the AST directly: spot::tlsf_expr substitution clones the
  /// clauses and replaces each formal-argument Identifier with the
  /// call-site actual.  No reparse is needed -- the body is parsed
  /// exactly once, at the source level, by parse_tlsf.
  ///
  /// TLSF v1.2 SS4.6 lets a definition body be one or more guarded
  /// clauses `(ec)+` with `ec ≡ e | eB : e | eP : e`; the function
  /// binds to the first clause whose guard holds.  Each element of
  /// `body` is one clause: either a plain expression (implicit guard
  /// `true`) or a BinaryOp with tlsf_op::Guard whose children are
  /// [guard, value].  The clauses are juxtaposed maximal
  /// expressions, parsed as a `body: expr | body expr` rule.
  struct tlsf_definition
  {
    /// Source location of the entry (covers the LHS up through '=').
    location loc;
    /// Definition name.
    std::string name;
    /// Argument names (empty if no parameter list).
    std::vector<std::string> args;
    /// Parsed clauses of the body, in source order.  Never empty
    /// for a definition accepted by the parser.  Each clause is
    /// reused across every call site via structural
    /// clone-and-substitute (see translator::subst_arg).
    std::vector<tlsf_expr_ptr> body;
  };

  /// \brief The INFO items a parsed file may carry.
  ///
  /// TLSF v1.2 SS1.2 makes TITLE, DESCRIPTION, SEMANTICS and TARGET
  /// mandatory and allows TAGS at most once.  Their values alone
  /// cannot answer whether an item was written: the default of a
  /// missing TITLE is the empty string, and the default of a missing
  /// SEMANTICS (Mealy) is a value a file may well spell out.  The
  /// `info_item` action of spot/parsetlsf/parsetlsf.yy therefore
  /// records the items it saw in tlsf_ast::info_seen, which both the
  /// duplicate check and the cross-section validator
  /// (spot/parsetlsf/public.cc) rely on.
  enum tlsf_info_item : unsigned
  {
    TLSF_INFO_TITLE       = 1u << 0,
    TLSF_INFO_DESCRIPTION = 1u << 1,
    TLSF_INFO_SEMANTICS   = 1u << 2,
    TLSF_INFO_TARGET      = 1u << 3,
    TLSF_INFO_TAGS        = 1u << 4,
  };

  /// \brief Root of a parsed TLSF specification.
  struct tlsf_ast
  {
    /// Source location of the AST (typically the start of the file).
    location loc;

    //--- INFO section (metadata) ----------------------------------

    /// Location of the `INFO` keyword, or -- when the file has no
    /// INFO section at all -- the default-constructed location
    /// (line 0), which is how the validator tells the two apart and
    /// picks the start of the file as the anchor of a diagnostic
    /// about a whole missing section.
    location info_loc;
    /// Union of the tlsf_info_item flags of the items that the file
    /// spelled out.  TAGS is not mandatory, but like the other items
    /// it may appear at most once.
    unsigned info_seen = 0;
    /// Location of the first `SEMANTICS:` item (of the mandatory
    /// item's own span, i.e. the keyword and its colon).  Used to
    /// anchor the SEMANTICS / TARGET mismatch warning; stays at line
    /// 0 when the item is absent.
    location semantics_loc;
    /// Location of the first `TARGET:` item, same convention.
    location target_loc;
    /// Title from the INFO section (empty if missing).
    std::string title;
    /// Description from the INFO section (empty if missing).
    std::string description;
    /// Semantics declared in the file (carries Finite / Strict).
    tlsf_semantics semantics = tlsf_semantics::Mealy;
    /// Target declared in the file.
    tlsf_target target = tlsf_target::Mealy;
    /// Tags declared in INFO { TAGS: foo, bar; }.  Empty when the
    /// INFO section omits TAGS.  Order matches source order.
    std::vector<std::string> tags;

    //--- GLOBAL section -------------------------------------------

    /// Parameters declared in GLOBAL { PARAMETERS { ... } }.
    std::vector<tlsf_parameter_decl> parameters;

    /// Definitions from GLOBAL { DEFINITIONS { ... } }.
    std::vector<tlsf_definition> definitions;

    /// Enumerations declared inside GLOBAL { DEFINITIONS { ... } }
    /// via `enum X = T0:patterns0 T1:patterns1 ...;`.  Consumed by
    /// the translator to (a) resolve typed-bus declarations (`hburst
    /// HBURST;` in INPUTS / OUTPUTS: the signal is expanded to
    /// `name_0..name_{w-1}` where w is the enum's bit width) and (b)
    /// fold enum comparisons (`HBURST == INCR`) into Boolean formulas
    /// over the expanded bits.
    std::vector<tlsf_enum_decl> enumerations;

    //--- MAIN section ---------------------------------------------

    /// Atomic propositions declared in MAIN { INPUTS { ... } }.
    std::vector<tlsf_ap_decl> inputs;
    /// Atomic propositions declared in MAIN { OUTPUTS { ... } }.
    std::vector<tlsf_ap_decl> outputs;

    /// Parsed formulas for each subsection of MAIN: MAIN { INITIALLY
    /// { formula1; formula2; ... } }, etc.  Each formula is a fully-
    /// structured AST node tree (LTL ops, boolean ops, bus
    /// references, integer arithmetic); the printer deparses these
    /// back to TLSF for round-trip.  Empty when the subsection was
    /// absent.
    std::vector<tlsf_expr_ptr> initially_body;
    /// Parsed formulas of MAIN { PRESET { ... } }.
    std::vector<tlsf_expr_ptr> preset_body;
    /// Parsed formulas of MAIN { REQUIRE / REQUIREMENTS { ... } }.
    std::vector<tlsf_expr_ptr> require_body;
    /// Parsed formulas of MAIN { ASSERT / INVARIANTS { ... } }.
    std::vector<tlsf_expr_ptr> assert_body;
    /// Parsed formulas of MAIN { GUARANTEE / GUARANTEES { ... } }.
    std::vector<tlsf_expr_ptr> guarantee_body;
    /// Parsed formulas of MAIN { ASSUME / ASSUMPTIONS { ... } }.
    std::vector<tlsf_expr_ptr> assumptions_body;
  };

  /// \brief Check if expression has any App node in subtree.
  inline bool tlsf_subtree_has_app(const tlsf_expr& e)
  {
    // Deliberately recompute from the node kinds instead of trusting
    // e.has_app: this is the independent check the translator's
    // assert() uses to catch a flag that was never propagated.
    if (e.type == tlsf_expr_type::App)
      return true;
    for (const auto& ch : e.children)
      if (ch && tlsf_subtree_has_app(*ch))
        return true;
    return false;
  }

  /// \brief Independent recomputation of \c tlsf_expr::has_binding_target.
  ///
  /// Mirrors tlsf_subtree_has_app: walks the tree instead of reading
  /// the cached flag, so an assert() on it can catch a missing
  /// propagation in a clone.
  inline bool tlsf_subtree_has_binding_target(const tlsf_expr& e)
  {
    if (e.type == tlsf_expr_type::Identifier
        || e.type == tlsf_expr_type::BusRef
        || e.type == tlsf_expr_type::Quantifier)
      return true;
    for (const auto& ch : e.children)
      if (ch && tlsf_subtree_has_binding_target(*ch))
        return true;
    return false;
  }
}
