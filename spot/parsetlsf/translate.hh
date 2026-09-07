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

#pragma once

#include <spot/misc/common.hh>
#include <spot/misc/location.hh>
#include <spot/tl/formula.hh>
#include <spot/parsetlsf/ast.hh>
#include <spot/parsetlsf/public.hh>

#include <map>
#include <set>
#include <vector>

namespace spot
{
  /// \addtogroup tlsf_io
  /// @{
  namespace tlsf
  {
    /// \brief One-shot TLSF→LTL translator.
    ///
    /// Walks a tlsf_ast (built by parse_tlsf) and produces a
    /// `tlsf_translation_result` carrying the produced `spot::formula`
    /// plus the bus-flattened input/output AP lists.
    ///
    /// The translator is single-use: instantiate, call \c run(), read
    /// the result. It is private to spot/parsetlsf/ — callers should
    /// go through the public `tlsf_to_ltl()` entry point in
    /// spot/parsetlsf/public.hh.
    ///
    /// Bus expansion (`name_i`), parameter resolution from
    /// `tlsf_translator_options::overrides` layered over AST-declared
    /// parameters, boolean / LTL / quantifier expressions,
    /// comparisons in integer contexts, and pieces that use only the
    /// boolean & LTL ops of spot::formula are all supported.
    ///
    /// The following are deferred and emit a diagnostic; the
    /// corresponding subterm collapses to `ff()` (false) so a partial
    /// result still flows through:
    ///
    /// * malformed or unsupported quantifier bounds, including
    ///   non-integer set members or ranges that are too large. The
    ///   quantifier collapses to `ff()` (or `tt()` for conjunction).
    /// * Comparison operators (Eq/Lt/etc.) at the top of an LTL
    ///   position.  Spot has no Boolean comparison operators, so a
    ///   comparison outside an integer context collapses to `ff()`
    ///   with a diagnostic.
    /// * malformed strict-semantics combinations are rejected by the
    ///   parser; valid strict semantics uses the TLSF strict-implication
    ///   composition in addition to the standard composition.
    ///
    /// On any of the above the diagnostic is appended to the
    /// caller-supplied error list; if `opts.raise_errors` is set, the
    /// first such error throws `std::runtime_error`.
    class SPOT_API translator
    {
    public:
      /// \brief Bind translator to \a ast and its \a opts.
      ///
      /// \a errors may be nullptr if the caller does not care about
      /// diagnostics (it only matters when `opts.raise_errors` is
      /// false, which is the default).
      translator(const tlsf_ast& ast,
                 const tlsf_translator_options& opts,
                 parse_tlsf_error_list* errors);
      ~translator();

      translator(const translator&) = delete;
      translator(translator&&) = delete;
      translator& operator=(const translator&) = delete;
      translator& operator=(translator&&) = delete;

      /// \brief Walk the AST and produce the translation result.
      ///
      /// Returns a result whose `full_formula` is null on failure.
      /// The per-section formulas (initially, preset, require,
      /// assertion, assume, guarantee) and the inputs/outputs that
      /// were already collected up to the failure point are still
      /// returned so callers can inspect partial progress.
      tlsf_translation_result run();

    private:
      // \brief Recursively translate \a e into a spot::formula.
      formula translate_expr(const tlsf_expr& e);

      // \brief Evaluate \a e as an integer; false on type/unknown
      // error.
      bool eval_int(const tlsf_expr& e, long long& out);

      // \brief Apply a user-defined definition in integer position.
      //
      // Called from eval_int's Identifier case (zero-argument defs
      // used as bare identifiers, e.g. amba's `HMASTER[m]` with
      // `m = log2(n);`) and from eval_int's App case (arity-matching
      // calls like `bit(v,i)`).  \a actuals must already be folded
      // to LiteralInt nodes with size == def.args.size().  Selects
      // the first clause whose guard holds (select_def_clause) and
      // evaluates it via eval_int, under the shared
      // def_app_budget limits (max_def_depth /
      // max_def_expansions_total in translate.cc); int_def_depth_
      // bounds the integer-position recursion, and expansion_depth_
      // is kept in sync so a body that falls back to LTL-position
      // expansion nests correctly under the same chain.
      bool eval_def_int(const tlsf_definition& def,
                        const std::vector<tlsf_expr_ptr>& actuals,
                        const tlsf_expr& call,
                        long long& out);

      // \brief Shared budget check for one definition application
      // (see def_app_budget in translate.cc).  \a depth is the
      // caller's current recursion depth (expansion_depth_ on the
      // LTL path, int_def_depth_ on the integer path); on true the
      // caller must pop expansion_depth_ when its expansion is
      // done.  Returns false once either limit trips, with exactly
      // one diagnostic emitted (expansion_exhausted_ is sticky).
      bool def_app_budget(const std::string& name,
                          const tlsf_expr& call, unsigned depth);

      // \brief Evaluate an integer set, preserving source order.
      bool eval_set(const tlsf_expr& e, std::vector<long long>& out);

      void diag(const location& loc, const std::string& msg);
      void diag(const tlsf_expr& e, const std::string& msg);

      // \brief Check that the file's SEMANTICS admits strong next.
      //
      // The LTLf flavour of the temporal operators -- `X[!]`, and the
      // `!`-marked stacked next and bounded forms `X[!n]`/`X[n!]`,
      // `F[!a:b]`/`F[a:b!]`, `G[!a:b]`/`G[a:b!]` -- is only defined
      // for a finite run, and syfco rejects it otherwise.  Returns
      // true when the semantics are finite, false after emitting one
      // diagnostic naming the offending expression.
      bool require_finite_semantics(const tlsf_expr& e);

      // \brief Evaluate \a e as a compile-time Boolean: returns 0
      // or 1 when the value is decidable with the current
      // parameter/loop-variable bindings, -1 otherwise.  Emits no
      // diagnostics either way (the caller reports undecidability
      // with its own message).
      int eval_guard_bool(const tlsf_expr& g);

      // Quiet variants of eval_int / eval_set used while probing
      // guard truth: they suppress every diagnostic that eval_int /
      // eval_set would otherwise emit, so a guard that merely
      // happens to reference something unevaluable is not reported
      // twice (once by the probe, once by the caller).
      bool eval_int_quiet(const tlsf_expr& e, long long& out);
      bool eval_set_quiet(const tlsf_expr& e,
                          std::vector<long long>& out);

      // \brief Pick the body of the first clause of \a def whose
      // guard is true for the given \a actuals.
      //
      // The \a actuals must already be AST-expanded (via
      // expand_ast) before substitution.  Guards are evaluated with
      // the translator's current parameter and loop-variable
      // bindings; a guard that is not statically decidable, and a
      // definition whose every guard is false, are reported via
      // diag() and yield nullptr.  Recursive calls (guarded clauses
      // whose value re-enters \a def with smaller arguments) are
      // allowed here -- termination is bounded by the translator's
      // expansion counter instead of by a cycle test.
      tlsf_expr_ptr select_def_clause(
        const tlsf_definition& def,
        const std::vector<tlsf_expr_ptr>& actuals,
        const tlsf_expr& call);

      // \brief True iff \a name matches a declared output base.
      bool base_is_output(const std::string& name) const;

      // \brief Find a declared input/output AP by base name.
      const tlsf_ap_decl* find_decl(const std::string& name) const;

      // \brief Find a DEFINITION by name (nullptr if none).
      //
      // TLSF's "one symbol = one definition" rule (enforced by the
      // parser's duplicate diagnostics) makes the name lookup
      // unambiguous.
      const tlsf_definition* find_def(const std::string& name) const;

      // \brief Find an ENUM declaration by name (nullptr if none).
      const tlsf_enum_decl* find_enum(const std::string& name) const;

      // \brief Resolve the width of an input/output declaration.
      //
      // Returns true and sets \a out on success.  A scalar has
      // width 1; a size bus evaluates its parsed size expression
      // (AST); a typed bus takes the bit width of its named enum
      // (diag on unknown enum).  The declaration is an error case
      // only via diag(); a false return always corresponds to a
      // diagnostic (or a failed size evaluation) already emitted.
      bool eval_ap_width(const tlsf_ap_decl& d, long long& out);

      // \brief Lower an enum comparison to a Boolean formula.
      //
      // `BUS == const` folds to the OR of the constant's bit
      // patterns, each pattern a conjunction over the expanded
      // `bus_0..bus_{w-1}` APs (bit k of the pattern constrains
      // `bus_k`: '1' positive, '0' negated, '*' omitted).
      // `BUS != const` is the negation of the `==` fold.  A width
      // mismatch between the two sides is a diagnostic, and the
      // expanded APs are registered as inputs/outputs per the bus
      // declaration.
      formula translate_enum_cmp(const tlsf_expr& e,
                                 const tlsf_ap_decl& bus,
                                 bool equal);

      // (cache_key helpers removed in favour of using def.name
      // directly: TLSF's parse-time duplicate-detection enforces
      // "one symbol = one definition" (see the `definition:`
      // semantic action in spot/parsetlsf/parsetlsf.yy), so the
      // cached body for a given definition is keyed by the bare
      // symbol name with no further qualification.)

      const tlsf_ast& ast_;
      const tlsf_translator_options& opts_;
      parse_tlsf_error_list* errors_;
      bool failed_ = false;

      // When true, diag() drops its message and does not mark the
      // translation as failed.  Used by eval_int_quiet /
      // eval_set_quiet while probing guard truth.
      bool diags_quiet_ = false;

      // Parameter values: AST-declared defaults are loaded first,
      // then opts.overrides are applied on top.  param_exprs_ holds
      // the unevaluated value expression of each declared parameter
      // (a parsed AST, shared with the main AST), used when one
      // parameter references another.
      std::map<std::string, long long> params_;
      std::map<std::string, tlsf_expr_ptr> param_exprs_;
      std::set<std::string> active_params_;

      // Loop-variable bindings during quantifier expansion. Bindings
      // are saved and restored when nested quantifiers are entered.
      std::map<std::string, long long> loop_vars_;

      // Accumulated flattened AP names; the order matches first-use.
      std::vector<std::string> inputs_;
      std::vector<std::string> outputs_;
      std::set<std::string> seen_inputs_;
      std::set<std::string> seen_outputs_;

      // Names currently being flattened by expand_ast.  expand_ast
      // is a purely structural pass (used on call actuals and on
      // single-clause unguarded bodies); a def whose body calls
      // itself would make it recurse forever, so it records the
      // names it is flattening and leaves a recursive App untouched
      // for translate_expr to process.  Guarded / recursive
      // definitions are expanded by translate_expr itself (see
      // select_def_clause and the expansion budgets) and never
      // reach
      // expand_ast with an active name.
      std::set<std::string> active_defs_;

      // Depth of the current user-definition expansion stack.  The
      // translate_expr App case increments it around each definition
      // application and diagnoses a body whose application depth
      // exceeds max_def_depth (see translate.cc): guarded recursive
      // definitions (e.g. the `mone` mutual-exclusion helper of
      // full_arbiter.tlsf) legitimately re-enter the same symbol
      // while their integer arguments shrink toward a
      // guard-selected base case, so recursion is not rejected
      // outright; this counter diagnoses genuine non-termination
      // (an unguarded self call, or a guard that never becomes
      // false) instead.
      unsigned expansion_depth_ = 0;

      // Total number of definition applications performed in this
      // translation run (never decremented).  Catches
      // non-terminating recursion whose substituted tree grows
      // exponentially, which would blow up in size before the depth
      // bound alone could fire (see max_def_expansions_total in
      // translate.cc).
      unsigned expansion_total_ = 0;

      // Set once either expansion bound trips (see the App case of
      // translate_expr).  From then on every definition application
      // returns ff() silently so the diagnostics stay limited to the
      // first overflow instead of flooding one message per call site.
      bool expansion_exhausted_ = false;

      // Depth of the current integer-position definition expansion
      // (eval_int's Identifier/App cases via eval_def_int).
      // Definitions are usable wherever an integer is expected --
      // bus sizes (`HMASTER[m]` with amba's parameterless
      // `m = log2(n);`) and guard expressions -- including guarded
      // recursive ones (`log2(x) =
      // x <= 1 : 1; otherwise : 1 + log2(x / 2);`).  The LTL path
      // budgets recursion with expansion_depth_; this counter is the
      // analogous safety valve for integer evaluation, where a body
      // like `k = 1 + k;` would otherwise recurse until the C++
      // stack overflows.  Both counters feed the same def_app_budget
      // check (max_def_depth / max_def_expansions_total in
      // translate.cc), so the limits are shared across paths.
      unsigned int_def_depth_ = 0;

      // Name of the definition that started the currently-active
      // expansion chain (the first App seen at expansion_depth_ 0).
      // Reported by the expansion-limit diagnostic, which would
      // otherwise blame a leaf call inside the cyclic def's own
      // clause.
      std::string expansion_root_name_;

      // Return a deep clone of \a body with every free Identifier
      // matching \a arg_name replaced by \a replacement.  Identifiers
      // in \a shadowed are left untouched.  Used for argument
      // substitution during definition expansion.
      tlsf_expr_ptr subst_arg(const tlsf_expr_ptr& body,
                              const std::string& arg_name,
                              const tlsf_expr_ptr& replacement,
                              const std::set<std::string>& shadowed);

      // Recursively flatten user-defined-def App calls in \a
      // expr.  For each App(call) where `call` is a known
      // user-defined def with matching arity, returns the
      // def's body with formals replaced by recursively-
      // expanded actuals (the substituted body is itself
      // recursively flattened).  Built-in helpers (MIN/MAX/
      // SUM/PROD/SIZEOF), unknown names, BusRefs, and
      // Quantifier bounds pass through unchanged --
      // integers, AP bases, and range bounds are evaluated at
      // translate time via \c eval_int, not at AST-shape time.
      //
      // The translator's \c active_defs_ set bounds any
      // expansion so truly cyclic def bodies (a def whose
      // body, directly or transitively, calls itself) come
      // back unchanged; the \c translate_expr App case then
      // surfaces the diagnostic.  This eager flattening
      // removes the false-positive cycle trip on
      // compositional patterns like `MultiUse(MyDef(a))`
      // where the substituted actual contains a def call
      // that the lazy-substitution path would re-fire.
      tlsf_expr_ptr expand_ast(const tlsf_expr_ptr& expr);
    };
  }
  /// @}
}
