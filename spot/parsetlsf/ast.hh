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
        parenthesized(false)
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

  /// \brief Build a LiteralInt node for integer literal \a v at \a loc.
  inline tlsf_expr_ptr tlsf_make_int(location loc, long long v)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::LiteralInt;
    e->val = v;
    return e;
  }

  /// \brief Build an Identifier node named \a name at \a loc.
  inline tlsf_expr_ptr tlsf_make_ident(location loc, std::string name)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::Identifier;
    e->name = std::move(name);
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
}
