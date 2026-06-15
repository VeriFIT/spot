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

#include <spot/twa/twagraph.hh>
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

}
