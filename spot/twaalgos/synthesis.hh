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

#include <memory>
#include <string>
#include <vector>

#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/relabel.hh>
#include <bddx.h>

namespace spot
{

  /// \ingroup synthesis
  /// \brief Benchmarking data and options for synthesis
  struct SPOT_API synthesis_info
  {
    /// \brief Algorithm selection for synthesis.
    enum class algo
    {
      DET_SPLIT = 0,
      SPLIT_DET,
      DPA_SPLIT,
      LAR,
      LAR_OLD,
      ACD,
    };

    /// \brief Splitting strategy for 2-step games.
    enum class splittype
    {
      AUTO = 0,  // Uses a heuristic to choose
      EXPL,  // Explicit enumerations of inputs
      SEMISYM,  // Works on one bdd per env state
      FULLYSYM  // Works on a fully symbolic version of the automaton
    };

    /// \brief When to apply realizability-preserving simplifications.
    enum class simplification_stage
    {
      never,                          ///< Never simplify.
      before_decomposition,           ///< Simplify only before decomposition.
      before_and_after_decomposition  ///< Also simplify each sub-specification.
    };

    /// \brief Benchmarking variables tracking timing and counts for
    /// each step of synthesis.
    ///
    /// The sum_* and max_* variables make more sense when the
    /// specification is split into multiple sub-specifications.  In
    /// this case, sum_*/max_* variables are sums/max over all
    /// sub-specifications.
    struct bench_var
    {
      /// \brief Number of sub-specifications, after decomposition.
      unsigned sub_specs = 0;
      /// \brief Total synthesis time.
      double total_time = 0.0;
      /// \brief Total LTL-to-automaton translation time.
      double sum_trans_time = 0.0;
      /// \brief Total automaton splitting time.
      double sum_split_time = 0.0;
      /// \brief Total paritization time.
      double sum_paritize_time = 0.0;
      /// \brief Total game solving time.
      double sum_solve_time = 0.0;
      /// \brief Total strategy-to-automaton conversion time.
      double sum_strat2aut_time = 0.0;
      /// \brief Total strategy simplification time.
      double sum_simplify_strat_time = 0.0;
      /// \brief Total AIG encoding time.
      double aig_time = 0.0;
      /// \brief Max translated automaton states.
      unsigned max_trans_states = 0;
      /// \brief Max translated automaton edges.
      unsigned max_trans_edges = 0;
      /// \brief Max translated automaton colors.
      unsigned max_trans_colors = 0;
      /// \brief Max translated automaton APs.
      unsigned max_trans_ap = 0;
      /// \brief Max game states.
      unsigned max_game_states = 0;
      /// \brief Max game colors.
      unsigned max_game_colors = 0;
      /// \brief Max strategy states.
      unsigned max_strat_states = 0;
      /// \brief Max strategy edges.
      unsigned max_strat_edges = 0;
      /// \brief Total strategy states.
      unsigned sum_strat_states = 0;
      /// \brief Total strategy edges.
      unsigned sum_strat_edges = 0;
      /// \brief Max simplified strategy states.
      unsigned max_simpl_strat_states = 0;
      /// \brief Max simplified strategy edges.
      unsigned max_simpl_strat_edges = 0;
      /// \brief Total simplified strategy states.
      unsigned sum_simpl_strat_states = 0;
      /// \brief Total simplified strategy edges.
      unsigned sum_simpl_strat_edges = 0;
      /// \brief Number of AIG latches.
      unsigned aig_latches = 0;
      /// \brief Number of AIG gates.
      unsigned aig_gates = 0;
      /// \brief Whether the specification is realizable.
      bool realizable = false;
    };

    synthesis_info()
        : force_sbacc{false},
          s{algo::LAR},
          minimize_lvl{2},
          sp{splittype::AUTO},
          bv{},
          verbose_stream{nullptr},
          moore{false},
          dict(make_bdd_dict())
    {
    }

    bool force_sbacc; ///< Force state-based acceptance.
    algo s; ///< Selected algorithm.
    int minimize_lvl; ///< Minimization level.
    splittype sp; ///< Splitting strategy.
    std::optional<bench_var> bv; ///< Benchmarking data.
    std::ostream* verbose_stream; ///< Verbose output stream.
    option_map opt; ///< Additional options.
    bool moore; ///< Use Moore (output-first) semantics instead of Mealy.
    bdd_dict_ptr dict; ///< BDD dictionary.
    /// \brief Whether to decompose the specification into independent
    /// sub-specifications.
    bool decompose = true;
    /// \brief Whether to try the direct-strategy bypass before building
    /// a game.
    bool use_bypass = true;
    /// \brief Whether to use on-the-fly MTBDD-based synthesis for
    /// syntactic obligations.
    bool obligation_synthesis = true;
    /// \brief When to remove atomic propositions with a single polarity.
    simplification_stage polarity =
      simplification_stage::before_and_after_decomposition;
    /// \brief When to remove atomic propositions that are always
    /// equivalent to another one.
    simplification_stage global_equiv =
      simplification_stage::before_and_after_decomposition;
    /// \brief Restrict global-equivalence simplifications to
    /// output/output equivalences.
    ///
    /// This is required when the game is going to be printed: moves
    /// are separated in a game, so equivalences between an input and
    /// an output cannot be recovered by patch_game().
    bool game_output_only = false;
  };

  /// \addtogroup synthesis Reactive Synthesis
  /// \ingroup twa_algorithms

  /// \ingroup synthesis
  /// \brief make each transition a 2-step transition, transforming
  ///        the graph into an alternating arena
  ///
  /// This function is used to transform an automaton into a turn-based game in
  /// the context of LTL reactive synthesis.
  ///
  /// Given a set of atomic propositions I, split each transition
  ///     p -- cond --> q                cond in 2^2^(I∪O)
  /// into a set of transitions whose form depend on the synthesis semantics
  /// used.   For Mealy semantics we want transitions of the form:
  ///     p -- i₁ --> (p,i₁) -- o₁ --> q
  ///     p -- i₂ --> (p,i₂) -- o₂ --> q
  ///     ...
  /// where iᵢ∈2^2^I, oᵢ∈2^2^O, and cond = Or(iᵢ∧oᵢ, i=1..n).
  /// For Moore semantics, we want
  ///     p -- o₁ --> (p,o₁) -- i₁ --> q
  ///     p -- o₂ --> (p,o₂) -- i₂ --> q
  ///     ...
  ///
  /// \param aut          automaton to be transformed
  /// \param output_bdd   conjunction of all output AP, all APs not present
  ///                     are treated as inputs
  /// \param complete_env Whether the automaton should be complete for the
  ///                     environment, i.e. the player of inputs
  /// \param sp           Defines which splitting algo to use
  /// \param moore        If true, use Moore (output-first) semantics:
  ///                     the controller plays first
  /// \note This function also computes the state players
  /// \note If the automaton is to be completed, sink states will
  ///       be added for both env and player if necessary
  SPOT_API twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env = true,
              synthesis_info::splittype sp
                = synthesis_info::splittype::AUTO,
              bool moore = false);

  /// \ingroup synthesis
  /// \brief Like split_2step but relying on the named property
  /// 'synthesis-outputs'
  SPOT_API twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut, bool complete_env = true,
              synthesis_info::splittype sp
                            = synthesis_info::splittype::AUTO,
              bool moore = false);

  /// \ingroup synthesis
  /// \brief Like split_2step but allows to fine-tune the splitting
  /// via the options set in \a gi, always completes the
  /// environment states and relies on the named property to
  /// extract the output proposition
  SPOT_API twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              synthesis_info& gi);


  /// \ingroup synthesis
  /// \brief the inverse of split_2step
  ///
  /// \pre aut is an alternating arena
  /// \post All edge conditions in the returned automaton are of the form
  ///       ins&outs, with ins/outs being a condition over the input/output
  ///       propositions
  /// \note This function relies on the named property "state-player"
  SPOT_API twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut);

  /// \ingroup synthesis
  /// \brief Stream algo
  SPOT_API std::ostream&
  operator<<(std::ostream& os, synthesis_info::algo s);

  /// \ingroup synthesis
  /// \brief Stream benchmarks and options
  SPOT_API std::ostream &
  operator<<(std::ostream &os, const synthesis_info &gi);


  /// \ingroup synthesis
  /// \brief Creates a game from a specification and a set of
  /// output propositions
  ///
  /// \param f The specification given as an LTL/PSL formula
  /// \param all_outs The names of all output propositions
  /// \param gi synthesis_info structure
  /// \param unobs When non-null, a list of additional unobservable propositions
  ///        not included in \a all_outs.
  /// \note All propositions in the formula that do not appear in all_outs
  /// are treated as input variables.
  SPOT_API twa_graph_ptr
  ltl_to_game(formula f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi,
              const std::vector<std::string>* unobs = nullptr);

  /// \ingroup synthesis
  /// \brief Creates a game from a specification and a set of
  /// output propositions
  ///
  /// \param f The specification given as an LTL/PSL formula
  /// \param all_outs The names of all output propositions
  /// \param unobs When non-null, a list of additional unobservable propositions
  ///        not included in \a all_outs.
  /// \note All propositions in the formula that do not appear in all_outs
  /// are treated as input variables.
  SPOT_API twa_graph_ptr
  ltl_to_game(formula f,
              const std::vector<std::string>& all_outs,
              const std::vector<std::string>* unobs = nullptr);

  /// \ingroup synthesis
  /// \brief creates a mealy machine from a solved game \a arena
  /// taking into account the options given in \a gi.
  /// This concerns in particular whether or not the machine is to be reduced
  /// and how.
  /// solved_game_to_mealy can return any type of mealy machine. In fact it
  /// will return the type that necessitates no additional operations
  /// @{
  SPOT_API twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena, synthesis_info& gi);
  SPOT_API twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena);
  SPOT_API twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena, synthesis_info& gi);
  SPOT_API twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena);
  SPOT_API twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena, synthesis_info& gi);
  SPOT_API twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena);
  /// @}

  /// \ingroup synthesis
  /// \brief A struct that represents different types of mealy like
  ///        objects
  struct SPOT_API mealy_like
  {
    /// \brief Realizability result codes.
    enum class realizability_code
    {
      UNREALIZABLE,
      UNKNOWN,
      REALIZABLE_REGULAR,
      // strat is DTGBA and a glob_cond
      REALIZABLE_DTGBA
    };

    realizability_code success; ///< Realizability result.
    twa_graph_ptr mealy_like;
    bdd glob_cond; ///< Global condition for DTGBA strategies.
  };

  /// \ingroup synthesis
  /// \brief Seeks to decompose a formula into independently synthetizable
  /// sub-parts. The conjunction of all sub-parts then
  /// satisfies the specification
  ///
  /// The algorithm is based on work by Finkbeiner et al.
  /// \cite finkbeiner.21.nfm, \cite finkbeiner.21.arxiv.
  ///
  /// \param f the formula to split
  /// \param outs vector with the names of all output propositions
  /// \return A vector of pairs holding a subformula and the used output
  ///  propositions each.
  /// @{
  SPOT_API std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(formula f, const std::vector<std::string>& outs);

  SPOT_API std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(const std::string& f,
                             const std::vector<std::string>& outs);
  /// @}

  /// \ingroup synthesis
  /// \brief Return the negation of the assumptions of \a f.
  ///
  /// If \a f is an implication `A → G`, return `¬A`.  If \a f is a
  /// conjunction, collect the antecedents of all its top-level
  /// implications and return their negated conjunction.  This is the
  /// `getNegAss()` pre-check of the compositional-synthesis algorithm
  /// of Finkbeiner et al.  Input-only conjuncts of \a f are ignored
  /// (they cannot be assumptions of an implication), but they are
  /// still part of the specification checked by the caller.
  ///
  /// Returns a null formula when \a f has no top-level implication.
  SPOT_API formula get_negated_assumptions(formula f);

  /// \ingroup synthesis
  /// \brief Creates a strategy for the formula given by calling all
  ///        intermediate steps
  ///
  /// For certain formulas, we can ''bypass'' the traditional way
  /// and find directly a strategy or some other representation of a
  /// winning condition without translating the formula as such.
  /// If no such simplifications can be made, it executes the usual way.
  ///
  /// \param f The formula to synthesize a strategy for
  /// \param output_aps A vector with the name of all output properties.
  ///                   All APs not named in this vector are treated as inputs
  /// \param gi synthesis_info structure controlling the synthesis algorithm.
  /// \param want_strategy Set to false if we don't want to construct the
  /// strategy but only test realizability.
  SPOT_API mealy_like
  try_create_direct_strategy(formula f,
                             const std::vector<std::string>& output_aps,
                             synthesis_info& gi, bool want_strategy = false);

  /// \ingroup synthesis
  /// \brief Solve a game, and update synthesis_info
  ///
  /// This is just a wrapper around the solve_game() function with a
  /// single argument.  This one measure the runtime and update \a gi.
  SPOT_API bool
  solve_game(twa_graph_ptr arena, synthesis_info& gi);

  /// \brief Pair of relabeling maps for environment and player edges in a
  /// synthesis game.
  struct SPOT_API game_relabeling_map
  {
    relabeling_map env_map; ///< Map for environment edges.
    relabeling_map player_map; ///< Map for player edges.
  };

  /// \ingroup synthesis
  /// \brief Tries to relabel a SPLIT game \a arena using fresh propositions.
  /// Can be applied to env or player depending on \a relabel_env
  /// and \a relabel_play. The arguments \a split_env and \a split_play
  /// determine whether or not env and player edges are to
  /// be split into several transitions labelled by letters not conditions.
  ///
  /// \return pair of relabeling_map, first is for env, second is for player.
  /// The maps are empty if no relabeling was performed
  /// \note Can also be applied to split mealy machine.
  /// \note partitioned_relabel_here can not be used directly if there are
  /// T (true conditions)
  SPOT_API game_relabeling_map
  partitioned_game_relabel_here(twa_graph_ptr& arena,
                                bool relabel_env,
                                bool relabel_play,
                                bool split_env = false,
                                bool split_play = false,
                                unsigned max_letter = -1u,
                                unsigned max_letter_mult = -1u);

  /// \ingroup synthesis
  /// \brief Undoes a relabeling done by partitioned_game_relabel_here.
  /// A dedicated function is necessary in order to remove the
  /// variables tagging env and player conditions
  SPOT_API void
  relabel_game_here(twa_graph_ptr& arena,
                    game_relabeling_map& rel_maps);


  /// \ingroup synthesis
  /// \brief One reactive-synthesis problem.
  ///
  /// This object stores a specification, the partition of its atomic
  /// propositions into inputs and outputs (plus optional unobservable
  /// inputs), and a #spot::synthesis_info structure controlling the
  /// synthesis pipeline.
  ///
  /// The expensive stages (simplification, decomposition, solving,
  /// strategy extraction, and AIG encoding) are performed lazily and
  /// memoized.  However each entry point tunes the pipeline for the
  /// artefact it returns: is_realizable() may avoid building any
  /// strategy, while strategy() and aig() enable the optimizations
  /// that make that artefact smaller.  Asking for one artefact and
  /// then for another can therefore solve the problem twice, so call
  /// directly for what you need: a null strategy() or aig() already
  /// answers the realizability question.
  ///
  /// This class is not thread-safe.
  class SPOT_API synthesis_problem
  {
  public:
    /// \brief Build a reactive-synthesis problem.
    ///
    /// The three lists classify the atomic propositions of \a f, using
    /// the same rules as the --ins, --outs, and --unobservable-ins
    /// options of ltlsynt.  An element of a list is either the name of
    /// a proposition, or a regular expression enclosed in slashes that
    /// is matched (with std::regex_search) against those names.  A
    /// proposition may be an output, an input, or an unobservable
    /// input, but it cannot be both an output and an input: the latter
    /// case is an error.
    ///
    /// A proposition matched by none of the lists is inferred: it is
    /// an output when only \a input_aps (and possibly \a
    /// unobservable_aps) is given, an input when only \a output_aps is
    /// given, and an error when both sides are given.  When none of
    /// the three lists is given, propositions are classified by their
    /// first letter ('i' for inputs, 'o' for outputs, 'u' for
    /// unobservable inputs), and an ambiguous proposition is an error.
    ///
    /// The three lists are passed by pointer so that a list that is
    /// not specified (a null pointer) can be distinguished from a list
    /// that specifies nothing (a pointer to an empty vector): the
    /// former triggers the inference above, exactly like omitting the
    /// --ins, --outs, or --unobservable-ins option of ltlsynt, while
    /// the latter is taken literally, like passing --ins= with an
    /// empty argument.  In Python, pass None for an unspecified list
    /// and [] for an empty one.
    ///
    /// std::invalid_argument is thrown when the lists are inconsistent
    /// or leave a proposition unclassified, and when a regular
    /// expression is invalid.
    ///
    /// \param f The specification.
    /// \param input_aps Patterns selecting the input propositions, or
    ///        nullptr when the inputs are not specified.
    /// \param output_aps Patterns selecting the output propositions,
    ///        or nullptr when the outputs are not specified.
    /// \param unobservable_aps Patterns selecting additional
    ///        unobservable input propositions, or nullptr when they are
    ///        not specified.
    /// \param si Synthesis options and statistics.
    synthesis_problem(formula f,
                      const std::vector<std::string>* input_aps = nullptr,
                      const std::vector<std::string>* output_aps = nullptr,
                      const std::vector<std::string>* unobservable_aps
                      = nullptr,
                      synthesis_info si = {});

    ~synthesis_problem();

    synthesis_problem(const synthesis_problem&) = delete;
    synthesis_problem& operator=(const synthesis_problem&) = delete;

    // --- Solving services -----------------------------------------

    /// \brief Check realizability.
    ///
    /// This avoids building the strategy when the selected algorithms
    /// can decide realizability without it.  Use it only when no
    /// controller is wanted: strategy() and aig() decide realizability
    /// as well, with the optimizations suited to the artefact they
    /// return.
    bool is_realizable();

    /// \brief Return a controller as a Mealy machine.
    ///
    /// Returns nullptr when the specification is unrealizable, so this
    /// also answers the realizability question.
    twa_graph_ptr strategy();

    /// \brief Return one controller per sub-specification.
    ///
    /// The returned vector has size one when no decomposition was
    /// used, and is empty when the specification is unrealizable.
    const std::vector<twa_graph_ptr>& sub_strategies();

    /// \brief Encode the strategy (or sub-strategies) as an AIG.
    ///
    /// \param mode Encoding mode, as documented by
    ///        spot::mealy_machine_to_aig().
    /// Returns nullptr when the specification is unrealizable, so this
    /// also answers the realizability question.
    aig_ptr aig(const char* mode = "ite");

    // --- Games and decomposition ----------------------------------

    /// \brief Return the games corresponding to the syntactic
    /// decomposition.
    ///
    /// This does not solve anything and does not perform the
    /// negated-assumption pre-check.  The returned vector has size one
    /// when no decomposition was used.
    const std::vector<twa_graph_ptr>& games();

    /// \brief Return the sub-specifications used by the solver.
    ///
    /// This is empty when the negated-assumption pre-check produced
    /// the solution, because no sub-specification was solved then.
    const std::vector<formula>& sub_specifications();

    /// \brief Return the output propositions of each sub-specification.
    const std::vector<std::vector<std::string>>& sub_outputs();

    /// \brief Whether the returned strategy violates the assumptions.
    ///
    /// This is true when the strategy has no behaviour satisfying the
    /// assumptions: it then solves the negation of the assumptions
    /// instead of enforcing the guarantees (item 1 of the report in
    /// issue #665).
    ///
    /// The negated-assumption pre-check establishes this directly.
    /// When the specification is not split into independent conjuncts
    /// that pre-check is not used, so the strategy is compared with
    /// the assumptions instead.  That comparison requires the
    /// strategy: calling this function may therefore have to solve the
    /// problem.
    ///
    /// The assumptions are the left-hand side of the top-level
    /// implication, or of each top-level implication of a conjunction.
    /// A formula without such an implication has no assumptions to
    /// violate, so the flag is false for it.
    bool assumptions_violated() const;

    // --- Configuration and statistics -----------------------------

    /// \brief Return the options used by this problem.
    const synthesis_info& options() const;

    /// \brief Return benchmarking data collected while solving.
    const synthesis_info::bench_var& statistics() const;

    // --- Verification ---------------------------------------------

    /// \brief Verify strategy() against the original specification.
    ///
    /// Throws std::runtime_error if the strategy is invalid or does
    /// not satisfy the specification.
    void verify_strategy();

    /// \brief Verify an AIG against the original specification.
    ///
    /// Throws std::runtime_error if the circuit is invalid or does not
    /// satisfy the specification.
    void verify_aig(const const_aig_ptr& circuit);

  private:
    struct data;
    std::unique_ptr<data> data_;
  };
}
