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
  /// \param simplifier Deprecated.  This argument used to simplify the
  /// LTL formula representing each state of the automaton before
  /// computing its successors, an idea taken from
  /// \cite thirioux.02.fmics .  This is unsound: a simplifier may
  /// rewrite a destination in a way that moves a promise under a
  /// temporal operator (e.g., Xd & FG!d is rewritten as X(d & FG!d)),
  /// while the acceptance marks attached to a transition are collected
  /// from the unsimplified destination, so the resulting automaton can
  /// accept too much.  The argument is now only used to simplify \a f
  /// itself before the translation starts, and it will be removed in a
  /// future release: call spot::tl_simplifier::simplify() on \a f
  /// before calling this function instead.
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
  };

  /// \ingroup twa_ltl
  /// \brief Bundle the boolean options of ltl_to_tgba_fm_otf() and
  /// ltl_to_ba_otf().
  struct SPOT_API ltl_to_tgba_fm_otf_options
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
    ltl_to_tgba_fm_otf_options() {}
  };

  /// \ingroup twa_ltl
  /// \brief On-the-fly LTL→TGBA explorer.
  ///
  /// Encapsulates the data structures from ltl_to_tgba_fm() so that
  /// successors of a formula-state can be computed without building
  /// the full automaton.  Two views are provided:
  ///
  ///   - succ_as_bdd(): a symbolic BDD view (cached, no exprop)
  ///   - succ_as_edges(): an explicit edge list (exprop,
  ///     canonicalization, and branching postponement applied here)
  ///
  /// The class also exposes accessors so that a client can decompose
  /// the BDD returned by succ_as_bdd() on its own if needed.
  ///
  /// \section acc_semantics Acceptance condition semantics
  ///
  /// This class does not own an automaton, and does not build one: it
  /// only needs a bdd_dict (to register atomic propositions, Next
  /// variables, and promise variables), and it allocates its own
  /// acceptance colors with dense indices starting at 0.  The marks
  /// returned on the edges therefore never depend on any acceptance
  /// set that could pre-exist in a caller's automaton.
  ///
  /// The Couvreur translation internally encodes promises P(…) using
  /// negated Inf sets: the acceptance condition it assumes effectively
  /// represents Inf(!0)&Inf(!1)&…&Inf(!(N-1)), a form Spot does not
  /// directly support.  The acceptance marks returned in
  /// fm_edge::acc therefore correspond to this negated semantics.
  ///
  /// Because the number of colors N grows during exploration (each
  /// new promise allocates a fresh color), the marks cannot be
  /// complemented on-the-fly; complementation must wait until
  /// exploration is complete and the final N is known.  At that
  /// point, build a proper TGBA by setting the acceptance condition
  /// of the target automaton to generalized-Büchi over the N sets
  /// allocated by the exploration (num_colors()), and complementing
  /// each edge's mark with respect to these N sets:
  /// \code
  ///   aut->set_generalized_buchi(expl.num_colors());
  ///   auto& acc = aut->acc();
  ///   for (auto& e: aut->edges())
  ///     e.acc = acc.comp(e.acc);
  /// \endcode
  /// This is exactly what ltl_to_tgba_fm() does before returning the
  /// completed automaton.
  class SPOT_API ltl_to_tgba_fm_otf final
  {
  public:
    /// \brief Bundle the boolean options for translation.
    /// \see ltl_to_tgba_fm_otf_options
    using options = ltl_to_tgba_fm_otf_options;

    /// \brief Constructor.
    ///
    /// Normalizes the formula, initializes the BDD variable mappings,
    /// and prepares all internal data structures.  The explorer
    /// neither builds nor owns an automaton: the caller drives the
    /// exploration with init_state() and succ_as_edges()/
    /// succ_as_bdd().
    ///
    /// \param f          the LTL/PSL formula
    /// \param dict       the bdd_dict in which all BDD variables used
    ///                   by the exploration (atomic propositions, Next
    ///                   variables, and acceptance promises) are
    ///                   registered; the BDD conditions returned by
    ///                   succ_as_edges() and succ_as_bdd() are
    ///                   expressed in this dict
    /// \param opts       translation options
    /// \param simplifier deprecated optional LTL simplifier (owned by
    ///                   the caller); it is now only applied to \a f
    ///                   itself, see ltl_to_tgba_fm()
    /// \param unobs      optional set of unobservable events
    /// \param owner      an optional identity under which the
    ///                   acceptance and Next variables are
    ///                   registered.  By default (null), the explorer
    ///                   uses its own identity, and unregisters these
    ///                   variables when it is destroyed.  Passing
    ///                   another identity (e.g., the address of the
    ///                   automaton being built, aut.get()) makes them
    ///                   survive the destruction of the explorer.
    ///                   In all cases, a caller that builds an
    ///                   automaton should declare the atomic
    ///                   propositions listed by ap(), in that order,
    ///                   using twa::register_ap(), while the explorer
    ///                   is still alive: the explorer unregisters them
    ///                   when it is destroyed.
    ltl_to_tgba_fm_otf(formula f, bdd_dict_ptr dict,
                       ltl_to_tgba_fm_otf_options opts =
                         ltl_to_tgba_fm_otf_options(),
                       tl_simplifier* simplifier = nullptr,
                       const atomic_prop_set* unobs = nullptr,
                       void* owner = nullptr);

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
    /// Applies canonicalization (symb_merge) and branching
    /// postponement.  Promises are converted to mark_t.
    ///
    /// The acceptance marks returned in fm_edge::acc use negated
    /// Inf semantics; see the class-level documentation for how to
    /// convert them to proper generalized-Büchi marks.
    ///
    /// Results are NOT cached.
    std::vector<fm_edge> succ_as_edges(formula s);

    /// \brief Decompose the raw symbolic successors of \a s into edges.
    ///
    /// Internally calls succ_as_bdd(), then extracts edges via
    /// minato_isop.  Applies simplification and canonicalization
    /// (symb_merge), but, contrary to succ_as_edges(), it does not
    /// apply the \c exprop option (conditions are the prime implicants
    /// of the symbolic BDD) nor branching postponement.  The result
    /// therefore matches succ_as_bdd() transition by transition.
    ///
    /// The acceptance marks returned in fm_edge::acc use negated
    /// Inf semantics; see the class-level documentation for how to
    /// convert them to proper generalized-Büchi marks.
    ///
    /// Results are NOT cached.
    std::vector<fm_edge> succ_as_raw_edges(formula s);

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
    /// minato_isop.  Applies canonicalization (symb_merge), but skips
    /// branching postponement and all
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

    /// \brief The number of colors (acceptance sets) allocated so far.
    ///
    /// Each promise registered by the translation allocates one color,
    /// with a dense index starting at 0.  A caller that turns the
    /// exploration into a TGBA can use this to size the acceptance
    /// condition of the result (see \ref acc_semantics).
    unsigned num_colors() const;

    /// \brief The atomic propositions encountered so far, in the order
    /// they were discovered.
    ///
    /// An automaton built from this exploration should register those
    /// propositions with twa::register_ap() in this order, so that its
    /// twa::ap() list is consistent with the order in which the
    /// exploration discovered them (this is what ltl_to_tgba_fm() does).
    const std::vector<formula>& ap() const;

    /// \brief Print the explored automaton in GraphViz dot format,
    /// MTBDD-style.
    ///
    /// This is to succ_as_bdd() what mtdswa::print_dot() is to the
    /// \c mtdswa data structure: every reachable state (a formula) is
    /// displayed as a root, and the successors of each state are
    /// represented by the BDD of succ_as_bdd().  Nodes of this BDD are
    /// labeled either by atomic propositions, by acceptance promises
    /// \c P(f), or by next-state variables, which are shown as the
    /// destination formula.  Note that this ignores the \c exprop and
    /// \c branching_postponement options, like succ_as_bdd().
    ///
    /// When \a alternating is set, a conjunction of Next variables
    /// along an edge denotes a conjunction of several successor
    /// states, not a single state labeled by that conjunction: the
    /// states displayed are then simply the initial state and every
    /// Next-variable formula reachable from it, without any
    /// conjunction being formed.
    ///
    /// The true state \c 1 is never displayed as a state, in either
    /// mode.
    ///
    /// Calling this explores the automaton, registering the Next
    /// variables needed by the states it displays: the destinations
    /// returned by succ_as_raw_edges() in the default mode, or the
    /// individual Next variables of succ_as_bdd() when \a alternating
    /// is set.
    std::ostream& print_dot(std::ostream& os, bool alternating = false);

    /// The BDD dictionary.
    const bdd_dict_ptr& get_dict() const;

  private:
    struct impl;
    std::unique_ptr<impl> impl_;
  };
// ---------------------------------------------------------------------------
// class ltl_to_ba_otf — on-the-fly LTL→Büchi automaton explorer
// ---------------------------------------------------------------------------
/// \ingroup twa_ltl
/// \brief On-the-fly LTL→Büchi automaton explorer.
///
/// Degeneralizes the on-the-fly LTL→TGBA explorer ltl_to_tgba_fm_otf
/// into an NBA with *state-based* Büchi acceptance, using
/// minimum-unfulfilled-promise tracking.
///
/// A state is a pair (formula, m), where m is the smallest promise not
/// yet discharged in the current round, or -1 once the round has been
/// completed.  States with m == -1 are the accepting states.
///
/// Two successor views are provided:
///   - succ_as_ba_edges(): an explicit edge list;
///   - succ_as_bdd(): a symbolic BDD over atomic propositions and
///     anonymous next-state variables (one per pair (f, m)); this BDD
///     contains no promise variable.
///
/// To build a state-based Büchi automaton from the result, expand the
/// (formula, m) pairs as states, and after exploration mark every state
/// with m == -1 as accepting (i.e., tag all its outgoing transitions
/// with acceptance set 0), then call set_buchi() and prop_state_acc(true)
/// on the output automaton.
class SPOT_API ltl_to_ba_otf final
{
public:
  /// \brief Bundle the boolean options for translation.
  ///
  /// The options are those of ltl_to_tgba_fm_otf.  Note that \c exprop
  /// and \c branching_postponement only affect succ_as_ba_edges();
  /// succ_as_bdd() ignores them.
  using options = ltl_to_tgba_fm_otf_options;

  /// \brief Constructor.
  ///
  /// Like ltl_to_tgba_fm_otf, this is an on-the-fly explorer that
  /// neither builds nor owns an automaton: the caller drives the
  /// exploration with init_state() and succ_as_ba_edges()/
  /// succ_as_bdd(), and may pass an automaton as \a owner when it
  /// wants to build one from the exploration.  This class uses no
  /// acceptance variable itself: states with \c m == -1 are
  /// accepting, and the caller is expected to implement the Büchi
  /// condition (set 0 on the successors of accepting states) in the
  /// automaton it builds, as described in the class documentation
  /// above.
  ///
  /// \param f          the LTL/PSL formula to convert to a Büchi
  ///                   automaton
  /// \param dict       the bdd_dict in which the atomic propositions
  ///                   and the next-state variables decoded by
  ///                   state_from_var() are registered
  /// \param opts       translation options
  /// \param simplifier deprecated optional LTL simplifier (owned by
  ///                   the caller); it is now only applied to \a f
  ///                   itself, see ltl_to_tgba_fm()
  /// \param unobs      optional set of unobservable events
  /// \param owner      identity used to register the variables in \a
  ///                   dict; see ltl_to_tgba_fm_otf
  ltl_to_ba_otf(formula f, bdd_dict_ptr dict,
                ltl_to_tgba_fm_otf_options opts =
                  ltl_to_tgba_fm_otf_options(),
                tl_simplifier* simplifier = nullptr,
                const atomic_prop_set* unobs = nullptr,
                void* owner = nullptr);

  ~ltl_to_ba_otf();

  // Non-copyable, non-movable.
  ltl_to_ba_otf(const ltl_to_ba_otf&) = delete;
  ltl_to_ba_otf& operator=(const ltl_to_ba_otf&) = delete;

  // ---- State interface ----

  /// \brief Büchi automaton state: formula-state plus tracker.
  struct ba_state
  {
    formula f;            ///< formula-state
    int m;                ///< minimum unfulfilled promise, -1 = accepting

    /// \brief Equality of states: same formula-state and same tracker.
    bool operator==(const ba_state& other) const noexcept
    {
      return f == other.f && m == other.m;
    }
  };

  /// \brief Hash function for \ref ba_state.
  struct ba_state_hash
  {
    /// \brief Hash a state from its formula's identifier and tracker.
    size_t operator()(const ba_state& s) const noexcept
    {
      return s.f.id() ^ static_cast<size_t>(s.m + 1);
    }
  };

  /// \brief An explicit transition of the Büchi automaton.
  struct ba_edge
  {
    bdd cond;      ///< condition on atomic propositions
    ba_state dst;  ///< destination state; accepting iff dst.m == -1
  };

  /// The initial formula-state paired with the minimum unfulfilled
  /// promise 0.
  ba_state init_state() const;

  /// The original formula after normalization and quantifier extraction,
  /// but before canonicalization.  Useful for property checks on the
  /// resulting automaton.
  formula orig_formula() const;

  // ---- Explicit successor view ----

  /// \brief Decompose the successors of \a s into explicit edges.
  ///
  /// Applies the option-dependent machinery of
  /// ltl_to_tgba_fm_otf::succ_as_edges() (exprop, branching
  /// postponement, canonicalization) and pairs each
  /// transition with its new minimum unfulfilled promise.
  ///
  /// Results are cached.
  std::vector<ba_edge> succ_as_ba_edges(ba_state s);

  // ---- Symbolic successor view ----

  /// \brief Translate \a s into a single BDD representing its successors.
  ///
  /// The BDD uses two variable families:
  ///
  ///   - var_set():  atomic propositions (edge conditions), shared with
  ///     ltl_to_tgba_fm_otf;
  ///   - next_set(): anonymous variables, one per destination (f, m).
  ///
  /// Contrary to ltl_to_tgba_fm_otf::succ_as_bdd(), the \c exprop and
  /// \c branching_postponement options are ignored.  There is no promise
  /// variable: a transition is accepting iff the m component of its
  /// destination is -1.
  ///
  /// Each cube of the result contains exactly one next_set() variable.
  /// Because next_set() is the conjunction of *all* registered
  /// next-state variables, extract it with
  /// \code
  ///   int v = bdd_var(bdd_exist(cube, var_set()));
  ///   ba_state dst = state_from_var(v);
  /// \endcode
  /// (do not use <code>cube &amp; next_set()</code>, as this would
  /// reintroduce the other next-state variables).
  ///
  /// Results are cached.
  bdd succ_as_bdd(ba_state s);

  // ---- Accessors for interpreting succ_as_bdd() results ----

  /// Variable set: atomic propositions (same as in ltl_to_tgba_fm_otf).
  const bdd& var_set() const;

  /// Variable set: anonymous next-state variables.
  const bdd& next_set() const;

  /// \brief Decode a next-state variable of next_set() into a state.
  ba_state state_from_var(int v) const;

  /// \brief Whether \a s is accepting (m == -1).
  bool is_accepting(ba_state s) const;

  /// \brief Return the next-state variable associated to \a s,
  /// registering it if needed.
  int register_next_state(ba_state s);

  /// \brief The number of colors allocated by the translation.
  ///
  /// Delegates to the inner ltl_to_tgba_fm_otf explorer.
  /// See \ref acc_semantics.
  unsigned num_colors() const;

  /// \brief The atomic propositions encountered so far, in the order
  /// they were discovered.
  ///
  /// Delegates to the inner ltl_to_tgba_fm_otf explorer; see
  /// ltl_to_tgba_fm_otf::ap().
  const std::vector<formula>& ap() const;

  /// \brief Print the explored automaton in GraphViz dot format,
  /// MTBDD-style.
  ///
  /// This is to succ_as_bdd() what mtdswa::print_dot() is to the
  /// \c mtdswa data structure: every reachable state \c (f, m) is
  /// displayed as a root, and the successors of each state are
  /// represented by the BDD of succ_as_bdd().  Nodes of this BDD are
  /// labeled either by atomic propositions, or by next-state
  /// variables, which are shown as pairs \c (f, m); nodes of the form
  /// \c (f, -1) (accepting states) use a doubled border.
  ///
  /// Calling this explores the automaton, registering next-state
  /// variables as needed.
  std::ostream& print_dot(std::ostream& os);

  /// The BDD dictionary.
  const bdd_dict_ptr& get_dict() const;

private:
  struct impl;
  std::unique_ptr<impl> impl_;
};
}
