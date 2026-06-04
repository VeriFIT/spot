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

#include <spot/tl/formula.hh>
#include <spot/twa/twagraph.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/simplify.hh>
#include <spot/twaalgos/powerset.hh>

namespace spot
{
  /// \ingroup twa_ltl
  /// \brief Build a spot::twa_graph_ptr from an LTL or PSL formula.
  ///
  /// This originally derived from an algorithm by Couvreur
  /// \cite couvreur.99.fm , but it has been improved in many
  /// ways \cite duret.14.ijccbs .
  ///
  /// \param f The formula to translate into an automaton.
  ///
  /// \param dict The spot::bdd_dict the constructed automaton should use.
  ///
  /// \param exprop When set, the algorithm will consider all properties
  /// combinations possible on each state, in an attempt to reduce
  /// the non-determinism.  The automaton will have the same size as
  /// without this option, but because the transitions will be more
  /// deterministic, the product automaton will be smaller (or, at worst,
  /// equal).
  ///
  /// \param symb_merge When false, states with the same symbolic
  /// representation (these are equivalent formulas) will not be
  /// merged.
  ///
  /// \param branching_postponement When set, several transitions leaving
  /// from the same state with the same label (i.e., condition + acceptance
  /// conditions) will be merged.  \cite sebastiani.03.charme
  ///
  /// \param fair_loop_approx When set, a really simple characterization of
  /// unstable state is used to suppress all acceptance conditions from
  /// incoming transitions.
  ///
  /// \param unobs When non-zero, the atomic propositions in the LTL formula
  /// are interpreted as events that exclude each other.  The events in the
  /// formula are observable events, and \c unobs can be filled with
  /// additional unobservable events.
  ///
  /// \param simplifier If this parameter is set, the LTL formulas
  /// representing each state of the automaton will be simplified
  /// before computing the successor.  \a simpl should be configured
  /// for the type of reduction you want, see spot::tl_simplifier.
  /// This idea is taken from \cite thirioux.02.fmics .
  ///
  /// \param unambiguous When true, unambiguous TGBA will be produced
  /// using the trick described in \cite benedikt.13.tacas .
  ///
  /// \param aborter When given, aborts the construction whenever the
  /// constructed automaton would become larger than specified by the
  /// output_aborter.
  ///
  /// \param label_with_ltl keep one LTL formula equivalent to the
  /// language recognized by each state, and use that to name each
  /// state.
  ///
  /// \param force_obligation when true, force the result to satisfy
  /// the obligation property, as if the formula is already an obligation.
  ///
  /// \return A spot::twa_graph that recognizes the language of \a f.
  SPOT_API twa_graph_ptr
  ltl_to_tgba_fm(formula f, const bdd_dict_ptr& dict,
                 bool exprop = false, bool symb_merge = true,
                 bool branching_postponement = false,
                 bool fair_loop_approx = false,
                 const atomic_prop_set* unobs = nullptr,
                 tl_simplifier* simplifier = nullptr,
                 bool unambiguous = false,
                 const output_aborter* aborter = nullptr,
                 bool label_with_ltl = false,
                 bool force_obligation = false);

  /// \ingroup twa_ltl
  /// \brief A single successor edge from a formula-state.
  struct SPOT_API fm_edge
  {
    bdd cond;              ///< Condition on atomic propositions.
    formula dst;           ///< Destination formula-state.
    acc_cond::mark_t acc;  ///< Acceptance marks, using negated-Inf semantics;
                           ///< see \ref acc_semantics for details.
  };

  /// \ingroup twa_ltl
  /// \brief A simplified successor edge without condition.
  ///
  /// This is a lighter variant of fm_edge that omits the BDD condition
  /// on atomic propositions.  It is useful for on-the-fly emptiness
  /// checks where the condition is known to be bddtrue (e.g., after
  /// realizability simplification has removed all atomic propositions).
  struct SPOT_API fm_simple_edge
  {
    acc_cond::mark_t acc;  ///< Acceptance marks, using negated-Inf semantics.
    formula dst;           ///< Destination formula-state.

    bool operator<(const fm_simple_edge& o) const noexcept
    {
      if (dst.id() < o.dst.id())
        return true;
      if (o.dst.id() < dst.id())
        return false;
      return acc < o.acc;
    }
  };

  /// \ingroup twa_ltl
  /// \brief On-the-fly LTL→TGBA explorer.
  ///
  /// Encapsulates the data structures from ltl_to_tgba_fm() so that
  /// successors of a formula-state can be computed without building
  /// the full automaton.  Two views are provided:
  ///
  ///   - succ_as_bdd(): a symbolic BDD view (cached, no exprop)
  ///   - succ_as_edges(): an explicit edge list (exprop, simplification,
  ///     canonicalization, and branching postponement applied here)
  ///
  /// The class also exposes accessors so that a client can decompose
  /// the BDD returned by succ_as_bdd() on its own if needed.
  ///
  /// \section acc_semantics Acceptance condition semantics
  ///
  /// This class does not own a twa_graph; it receives one from the
  /// caller (\a aut) and uses it only to call register_ap() as new
  /// atomic propositions are discovered, and to update its acceptance
  /// condition as new colors are allocated.  The acceptance condition
  /// of \a aut is therefore mutated during the lifetime of the
  /// explorer.
  ///
  /// The Couvreur translation internally encodes promises P(…) using
  /// negated Inf sets: the acceptance condition of \a aut effectively
  /// represents Inf(!0)&Inf(!1)&…&Inf(!(N-1)), a form Spot does not
  /// directly support.  The acceptance marks returned in
  /// fm_edge::acc therefore correspond to this negated semantics.
  ///
  /// Because the number of acceptance sets N grows during exploration
  /// (each new promise allocates a fresh color), the marks cannot be
  /// complemented on-the-fly; complementation must wait until
  /// exploration is complete and the final N is known.  At that point,
  /// build a proper TGBA by complementing each edge's mark with
  /// respect to N and setting the acceptance condition to
  /// generalized-Büchi:
  /// \code
  ///   auto& acc = aut->acc();
  ///   for (auto& e: aut->edges())
  ///     e.acc = acc.comp(e.acc);
  ///   acc.set_generalized_buchi();
  /// \endcode
  /// This is exactly what ltl_to_tgba_fm() does before returning the
  /// completed automaton.
  class SPOT_API ltl_to_tgba_fm_otf final
  {
  public:
    /// \brief Bundle the boolean options for translation.
    struct options
    {
      /// Use all property combinations to reduce nondeterminism.
      bool exprop = false;
      /// Merge states with the same symbolic representation.
      bool symb_merge = true;
      /// Merge transitions with the same label leaving the same state.
      bool branching_postponement = false;
      /// Suppress acceptance conditions from incoming transitions of
      /// unstable states.
      bool fair_loop_approx = false;
      /// Restrict to unambiguous transitions.
      bool unambiguous = false;
      /// Force the result to satisfy the obligation property.
      bool force_obligation = false;
      options() {}
    };

    /// \brief Constructor.
    ///
    /// Normalizes the formula, initializes the BDD variable mappings,
    /// and prepares all internal data structures.
    ///
    /// \param f          the LTL/PSL formula
    /// \param aut        the automaton being built, used only to call
    ///                   register_ap(); the explorer never adds states
    ///                   or edges itself
    /// \param opts       translation options
    /// \param simplifier optional LTL simplifier (owned by caller)
    /// \param unobs      optional set of unobservable events
    ltl_to_tgba_fm_otf(formula f, twa_graph_ptr aut,
                options opts = options(),
                tl_simplifier* simplifier = nullptr,
                const atomic_prop_set* unobs = nullptr);

    ~ltl_to_tgba_fm_otf();

    // Non-copyable, non-movable.
    ltl_to_tgba_fm_otf(const ltl_to_tgba_fm_otf&) = delete;
    ltl_to_tgba_fm_otf& operator=(const ltl_to_tgba_fm_otf&) = delete;

    // ---- State interface ----

    /// The initial formula-state (canonicalized if symb_merge is on).
    formula init_state() const;

    /// The original formula after normalization and quantifier extraction,
    /// but before canonicalization.  Useful for property checks on the
    /// resulting automaton.
    formula orig_formula() const;

    // ---- Symbolic successor view ----

    /// Translate \a s into a single BDD representing all its successors.
    ///
    /// This calls the internal formula_canonicalizer and caches the
    /// result.  The returned BDD uses three variable families:
    ///
    ///   - var_set():  atomic propositions (edge conditions)
    ///   - next_set(): destination encoding (one variable per formula)
    ///   - a_set():    acceptance promises (one variable per promise)
    ///
    /// \note exprop and branching_postponement are NOT applied here;
    ///       they only affect succ_as_edges().
    bdd succ_as_bdd(formula s);

    // ---- Explicit successor view ----

    /// Decompose the successors of \a s into individual edges.
    ///
    /// Internally calls succ_as_bdd(), then extracts edges via
    /// minato_isop (with minterm iteration when exprop is enabled).
    /// Applies simplification, canonicalization (symb_merge), and
    /// branching postponement.  Promises are converted to mark_t.
    ///
    /// The acceptance marks returned in fm_edge::acc use negated
    /// Inf semantics; see the class-level documentation for how to
    /// convert them to proper generalized-Büchi marks.
    ///
    /// Results are NOT cached.
    std::vector<fm_edge> succ_as_edges(formula s);

    /// \brief Decompose the successors of \a s into edges without conditions.
    ///
    /// This is a lighter variant of succ_as_edges() that omits the BDD
    /// condition on atomic propositions.  It is useful for on-the-fly
    /// emptiness checks where the condition is known to be bddtrue (e.g.,
    /// after realizability simplification has removed all atomic
    /// propositions).  Skipping the condition computation avoids
    /// unnecessary BDD work.
    ///
    /// Internally calls succ_as_bdd(), existentially quantifies all
    /// atomic propositions away (so the BDD only contains Next and
    /// acceptance variables), then extracts (acc, dst) pairs via
    /// minato_isop.  Applies simplification and canonicalization
    /// (symb_merge), but skips branching postponement and all
    /// condition-related post-processing.  The \c exprop option is
    /// ignored: since no conditions are extracted, there is no need to
    /// iterate over all combinations of atomic propositions.
    ///
    /// Results are NOT cached.
    std::vector<fm_simple_edge> succ_as_acc_and_dest(formula s);

    // ---- Accessors for interpreting succ_as_bdd() results ----

    /// Variable set: atomic propositions.
    const bdd& var_set() const;

    /// Variable set: Next variables (destination encoding).
    const bdd& next_set() const;

    /// Variable set: acceptance promises.
    const bdd& a_set() const;

    /// Convert a cube over next_set() into a formula.
    formula conj_bdd_to_formula(bdd cube) const;

    /// Convert a cube over a_set() into acceptance marks.
    acc_cond::mark_t bdd_to_mark(bdd a) const;

    /// Register a new Next variable for \a f and return its BDD
    /// variable index.
    int register_next_variable(formula f);

    /// The BDD dictionary.
    const bdd_dict_ptr& get_dict() const;

  private:
    struct impl;
    std::unique_ptr<impl> impl_;
  };

}
