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
// declarations, the helper predicates and deparser that operate on
// expression nodes, the input/output/parameter/definition
// declaration records, and the root `tlsf_ast` struct.  Only the
// forward declaration of `tlsf_ast` (and of `tlsf_expr` where it
// appears in public signatures) escapes through
// spot/parsetlsf/public.hh; the field layouts live here so they can
// evolve without breaking ABI.

#pragma once

#include <spot/misc/common.hh>
#include <spot/misc/location.hh>
#include <spot/parsetlsf/public.hh>
#include <cstdint>
#include <memory>
#include <ostream>
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
    // Stacked next `X[n] phi` (TLSF v1.2 SS4.8): n nested next
    // operators.  Stored as a Quantifier node whose bound is the
    // integer expression `n`; the printer emits the `X[n] phi`
    // surface syntax and the translator expands it at LTL-conversion
    // time.
    XStack,

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
  };

  /// \brief A single TLSF expression node (tagged struct).
  ///
  /// Carries a \c spot::location for diagnostics. The `.parenthesized`
  /// flag records whether the source explicitly parenthesised this
  /// sub-expression; tlsf_print re-emits those parens verbatim so the
  /// round-trip is stable.
  struct SPOT_API tlsf_expr
  {
    spot::location loc;

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

  inline bool tlsf_op_is_ltl_unary(tlsf_op op)
  {
    return op == tlsf_op::G || op == tlsf_op::F || op == tlsf_op::X
      || op == tlsf_op::StrongNext;
  }

  inline bool tlsf_op_is_ltl_binary(tlsf_op op)
  {
    return op == tlsf_op::U || op == tlsf_op::R || op == tlsf_op::W;
  }

  inline bool tlsf_op_is_boolean(tlsf_op op)
  {
    return op == tlsf_op::Not || op == tlsf_op::And || op == tlsf_op::Or
      || op == tlsf_op::Implies || op == tlsf_op::Equiv;
  }

  /// True iff \a op is right-associative in the TLSF grammar.
  ///
  /// The deparser needs this to decide when to wrap an LHS BinaryOp
  /// child: a right-assoc parent declared at the same precedence would
  /// otherwise steal the LHS (e.g., `a -> b -> c` re-parses as
  /// `a -> (b -> c)`, not `(a -> b) -> c`).
  inline bool tlsf_op_is_right_associative(tlsf_op op)
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
  inline int tlsf_op_precedence(tlsf_op op)
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
        return 10;
      case tlsf_op::SetIntersection:
        return 11;
      case tlsf_op::SetDifference:
        return 12;
      case tlsf_op::Add:
        return 13;
      case tlsf_op::Sub:
        return 13;
      case tlsf_op::Div:
        return 14;
      case tlsf_op::Mod:
        return 14;
      case tlsf_op::Mul:
        return 15;
      }
    return 0;
  }

  /// Return the effective precedence of an expression node.  Quantifiers
  /// and unary operators both occupy Table 1's precedence-11 tier, even
  /// though a quantifier's operator tag is also used for its Boolean fold.
  inline int tlsf_expr_precedence(const tlsf_expr& e)
  {
    if (e.type == tlsf_expr_type::Quantifier
        || e.type == tlsf_expr_type::UnaryOp)
      return 7;
    if (e.type == tlsf_expr_type::BinaryOp)
      return tlsf_op_precedence(e.op);
    return 100;
  }

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
      case tlsf_op::F:
        return "F";
      case tlsf_op::X:
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
      case tlsf_op::None:
        return "";
      }
    return "";
  }

  // --- constructor helpers used by parsetlsf.yy -----------------------

  inline tlsf_expr_ptr tlsf_make_int(spot::location loc, long long v)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::LiteralInt;
    e->val = v;
    return e;
  }

  inline tlsf_expr_ptr tlsf_make_ident(spot::location loc, std::string name)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::Identifier;
    e->name = std::move(name);
    return e;
  }

  inline tlsf_expr_ptr tlsf_make_busref(spot::location loc,
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

  inline tlsf_expr_ptr tlsf_make_app(spot::location loc,
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

  inline tlsf_expr_ptr tlsf_make_unop(tlsf_op op, spot::location loc,
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

  inline tlsf_expr_ptr tlsf_make_binop(tlsf_op op, spot::location loc,
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

  inline bool tlsf_is_comparison(tlsf_op op)
  {
    return op == tlsf_op::Eq || op == tlsf_op::Neq
      || op == tlsf_op::Lt || op == tlsf_op::Le
      || op == tlsf_op::Gt || op == tlsf_op::Ge;
  }

  inline tlsf_expr_ptr tlsf_make_quantifier(tlsf_op op, spot::location loc,
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

  inline tlsf_expr_ptr tlsf_make_set_explicit(
      spot::location loc,
      std::vector<tlsf_expr_ptr> elements)
  {
    auto e = std::make_shared<tlsf_expr>();
    e->loc = loc;
    e->type = tlsf_expr_type::SetExplicit;
    e->children = std::move(elements);
    return e;
  }

  inline tlsf_expr_ptr tlsf_make_set_range(spot::location loc,
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

  /// Build a left-associated set operation from a bracketed list such
  /// as `CUP[{0}, {1, 2}]`.  The reference TLSF syntax permits one or
  /// more operands for these operators; an empty list is represented by
  /// the empty set so the algebra keeps its usual identity behavior.
  inline tlsf_expr_ptr tlsf_make_nary_setop(
      tlsf_op op, spot::location loc,
      std::vector<tlsf_expr_ptr> operands)
  {
    if (operands.empty())
      return tlsf_make_set_explicit(loc, {});
    auto result = std::move(operands.front());
    for (size_t i = 1; i < operands.size(); ++i)
      result = tlsf_make_binop(op, loc, std::move(result),
                               std::move(operands[i]));
    return result;
  }

  /// \brief A single value (Tag : bits) entry of an enum decl.
  ///
  /// The bits string is kept as raw text: a sequence of `0`,
  /// `1`, and (syfco's don't-care) `*` characters.  Length
  /// determines the enum's bit width; syfco enforces uniform
  /// length across entries (refs/.../Reader/Parser/Global.hs
  /// enumVParserL n), but Spot does not (yet) enforce
  /// uniformity -- the translator (translate.cc) is the right
  /// place for that check, since the bits width participates in
  /// bus-sizing for typed AP declarations.
  struct SPOT_API tlsf_enum_value
  {
    /// Source location of the entry (covers the LHS through `:`).
    spot::location loc;
    /// Symbolic tag name.
    std::string tag;
    /// Raw bits string (e.g. "00", "01", "1*0").
    std::string bits;
  };

  /// \brief An `enum` declaration from GLOBAL/DEFINITIONS.
  ///
  /// Mirrors syfco's `EnumDefinition` (Data.Enum) record
  /// (spot/parsetlsf/refs/syfco/src/lib/Data/Enum.hs).  Spot
  /// stores only the source-derived name + entries; the
  /// `analyze` step (syfco's coverage / duplicate detection) is
  /// deferred to the translator.
  struct SPOT_API tlsf_enum_decl
  {
    /// Source location of the decl (covers `enum` through `;`).
    spot::location loc;
    /// Enum name.
    std::string name;
    /// Entries in source order.
    std::vector<tlsf_enum_value> entries;
  };

  /// \brief An input or output declaration from the MAIN block.
  ///
  /// A declaration is either a simple variable (`oti;`) or a bus of
  /// size given by either a numeric literal (`os[8];`) or a
  /// parameter name (`ix[N];`).  In all three cases, the AST
  /// remembers the raw size expression as a string so the
  /// translator can resolve it once parameter overrides are known.
  struct tlsf_ap_decl
  {
    /// Source location of the declaration.
    spot::location loc;
    /// Variable or bus name.
    std::string name;
    /// Raw size expression; empty string means a single (scalar) AP.
    std::string size;
  };

  /// \brief A PARAMETERS block entry from GLOBAL.
  struct tlsf_parameter_decl
  {
    /// Source location of the entry.
    spot::location loc;
    /// Parameter name.
    std::string name;
    /// Raw value expression, as written in the file.  The translator
    /// parses it as an integer when overrides are applied.
    std::string value;
  };

  /// \brief A DEFINITIONS block entry from GLOBAL.
  ///
  /// Mirror of syfco's `BindExpr` (Data/Binding.hs): the body is a
  /// list of clause expressions (LTL ops, boolean ops, bus
  /// references, integer arithmetic), not text.  Expansion uses the
  /// AST directly: spot::tlsf_expr substitution clones the clauses
  /// and replaces each formal-argument Identifier with the call-site
  /// actual.  No reparse is needed -- the body is parsed exactly
  /// once, at the source level, by parse_tlsf.
  ///
  /// TLSF v1.2 SS4.6 lets a definition body be one or more guarded
  /// clauses `(ec)+` with `ec ≡ e | eB : e | eP : e`; the function
  /// binds to the first clause whose guard holds.  Each element of
  /// `body` is one clause: either a plain expression (implicit guard
  /// `true`) or a BinaryOp with tlsf_op::Guard whose children are
  /// [guard, value].  The TLSF reference grammar (syfco's
  /// `Reader/Parser/Global.hs` `reminderParser`) parses the body
  /// with `many1 exprParser`, i.e. the clauses are juxtaposed
  /// maximal expressions; this parser mirrors that with a
  /// `body: expr | body expr` rule.  Quoted STRING literals are
  /// only legal in the INFO section (TITLE: / DESCRIPTION:).
  struct tlsf_definition
  {
    /// Source location of the entry (covers the LHS up through '=').
    spot::location loc;
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

  /// Root of a parsed TLSF specification.
  ///
  /// Phase 2 fills every field of the AST with structured expression
  /// nodes (no longer raw text).  Each MAIN subsection stores a list
  /// of stand-alone formulas, separated by `;` in the source.  An
  /// empty subsection yields an empty vector.
  ///
  /// The type is forward-declared in spot/parsetlsf/public.hh; this
  /// private header (NOT installed) holds the real definition, so
  /// the field layout can evolve without breaking ABI.
  struct tlsf_ast
  {
    /// Source location of the AST (typically the start of the file).
    spot::location loc;

    //--- INFO section (metadata) ----------------------------------

    /// Title from the INFO section (empty if missing).
    std::string title;
    /// Description from the INFO section (empty if missing).
    std::string description;
    /// Semantics declared in the file (carries Finite / Strict).
    tlsf_semantics semantics = tlsf_semantics::Mealy;
    /// Target declared in the file.
    tlsf_target target = tlsf_target::Mealy;
    /// Tags declared in INFO { TAGS: foo, bar; }.  Empty when the
    /// INFO section omits TAGS.  Order matches source order.  See
    /// syfco's `tagsParser` (refs/.../Reader/Parser/Info.hs).
    std::vector<std::string> tags;

    //--- GLOBAL section -------------------------------------------

    /// Parameters declared in GLOBAL { PARAMETERS { ... } }.
    std::vector<tlsf_parameter_decl> parameters;

    /// Definitions from GLOBAL { DEFINITIONS { ... } }.
    std::vector<tlsf_definition> definitions;

    /// Enumerations declared inside GLOBAL { DEFINITIONS { ... } }
    /// via `enum X = { V0:00, V1:01, ... };`.  Mirrors syfco's
    /// `enumerations` field (Reader/Parser/Data.hs Specification
    /// record).  Empty when no enums are declared; the
    /// `tlsf_to_ltl` translator will eventually consume them to
    /// resolve typed-bus declarations (`ap E;` where E names
    /// an enum); that wiring is a follow-up.  The current scope
    /// is the parser accepting the source shape.
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
    std::vector<tlsf_expr_ptr> preset_body;
    std::vector<tlsf_expr_ptr> require_body;
    std::vector<tlsf_expr_ptr> assert_body;
    std::vector<tlsf_expr_ptr> guarantee_body;
    /// Parsed formulas of MAIN { ASSUME / ASSUMPTIONS { ... } }.
    /// New section added alongside REQUIREMENTS / INVARIANTS /
    /// GUARANTEES; mirrors syfco's four separate `requirements` /
    /// `assumptions` / `invariants` / `guarantees` fields
    /// (refs/.../Reader/Parser/Component.hs).
    std::vector<tlsf_expr_ptr> assumptions_body;
  };

  // --- deparser --------------------------------------------------------
  //
  // tlsf_print_expr() recurses through the AST and emits the canonical
  // surface syntax. The parenthesized flag is preserved verbatim: every
  // round-tripped source paren reappears in the output. For an
  // operator child whose precedence is strictly lower than its parent's
  // we wrap it in parens to keep grouping stable across deparse.

  inline void tlsf_print_expr(std::ostream& os, const tlsf_expr& e)
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
            tlsf_op_is_right_associative(e.op);
          int par_prec = tlsf_op_precedence(e.op);
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
                      int lhs_prec = tlsf_expr_precedence(lhs);
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
                  int rhs_prec = tlsf_expr_precedence(rhs);
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
        os << tlsf_format_op(e.op) << '[';
        if (e.children.size() >= 1 && e.children[0])
          tlsf_print_expr(os, *e.children[0]);
        os << "] ";
        if (e.children.size() >= 2 && e.children[1])
          tlsf_print_expr(os, *e.children[1]);
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
}
