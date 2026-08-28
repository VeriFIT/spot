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

#include <algorithm>
#include <memory>
#include <ostream>
#include <unordered_map>
#include <vector>
#include <optional>

#include <bddx.h>
#include <spot/misc/optionmap.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/parity.hh>

namespace spot
{
  /// \addtogroup games Functions related to game solving
  /// \ingroup twa_algorithms

  /// \ingroup games
  /// \brief Transform an automaton into a parity game by propagating
  /// players
  ///
  /// This propagates state players, assuming the initial state belongs
  /// to \a first_player, and alternating players on each transition.
  /// If an odd cycle is detected, a runtime_exception is raised.
  ///
  /// If \a complete0 is set, ensure that states of player 0 are
  /// complete.
  SPOT_API
  void alternate_players(spot::twa_graph_ptr& arena,
                         bool first_player = false,
                         bool complete0 = true);


  // false -> env, true -> player
  /// \ingroup games
  /// \brief Winning region: false = player 0 (env), true = player 1.
  typedef std::vector<bool> region_t;
  // state idx -> global edge number
  /// \ingroup games
  /// \brief Strategy: maps each state index to the chosen global edge number.
  typedef std::vector<unsigned> strategy_t;


  /// \ingroup games
  /// \brief Solve a parity game.
  ///
  /// The arena must have a transition-based parity acceptance and a
  /// "state-player" property.  The solver accepts all four parity
  /// variants (`max`/`min`, `odd`/`even`) and normalizes them
  /// internally.  Choices are made by the owner of each state;
  /// determinism of transition labels is not required by the solver,
  /// but callers such as synthesis may require mutually exclusive
  /// labels.  States without successors are not supported by parity
  /// games and should be removed or completed by the caller.
  ///
  /// Player 1 tries to satisfy the acceptance condition, while player
  /// 0 tries to prevent that.
  ///
  /// This computes a winning region (stored in the "state-winner"
  /// property) and a positional winning strategy (stored in the
  /// "strategy" property).  The strategy is meaningful only for
  /// states whose owner is the winner; its entry is a global edge
  /// number leading to a state with the same winner.  Other entries
  /// are unspecified and currently represented by 0; zero can
  /// nevertheless be a valid global edge number, so callers must
  /// check the owner and winner before using an entry.
  ///
  /// By default only a 'local' strategy is computed: only the part of
  /// the arena reachable from the initial state is considered.
  /// Unreachable states consequently have no solved winner or
  /// strategy guarantee.  If you want winners and strategies for all
  /// states, set \a solve_globally to true.  In either mode, solving
  /// is done from scratch, and named properties from an earlier solve
  /// are replaced.
  ///
  /// The implementation currently uses Zielonka's recursive
  /// algorithm, with optimizations inspired by Oink.  These
  /// implementation details are not part of the strategy-selection
  /// contract.
  /// \cite zielonka.98.tcs
  /// \cite vandijk.18.tacas
  ///
  /// Returns the player winning in the initial state, and sets
  /// the "state-winner" and "strategy" named properties.
  SPOT_API
  bool solve_parity_game(const twa_graph_ptr& arena,
                         bool solve_globally = false);

  /// \ingroup games
  /// \brief Solve a safety game.
  ///
  /// The arena should be represented by an automaton with true
  /// acceptance.
  ///
  /// Player 1 tries to satisfy the acceptance condition, while player
  /// 0 tries to prevent that.   The only way for player 0 to win is
  /// to find a way to move the play toward a state without successors.
  /// If there is no state without successors, then the game is necessarily
  /// winning for player 1.
  ///
  /// Returns the player winning in the initial state, and sets
  /// the "state-winner" and "strategy" named properties.
  SPOT_API
  bool solve_safety_game(const twa_graph_ptr& game);

  /// \ingroup games
  /// \brief Generic interface for game solving
  ///
  /// Dispatch to solve_safety_game() if the acceptance condition is
  /// t, or to solve_parity_game() if it is a parity acceptance.  Note that
  /// parity acceptance include Büchi, co-Büchi, Rabin 1, and Streett 1.
  ///
  /// Currently unable to solve a game with other acceptance conditions
  /// that are not parity.
  ///
  /// Return the winning player for the initial state, and sets
  /// the state-winner and strategy named properties.
  SPOT_API bool
  solve_game(const twa_graph_ptr& arena);


  /// \ingroup games
  /// \brief Print a parity game using PG-solver syntax
  ///
  /// The input automaton should have parity acceptance and should
  /// define state owner.  Since the PG solver format want player 1 to
  /// solve a max odd condition, the acceptance condition will be
  /// adapted to max odd if necessary.
  ///
  /// The output will list the initial state as first state (because
  /// that is the convention of our parser), and list only reachable
  /// states.
  ///
  /// If states are named, the names will be output as well.
  /// @{
  SPOT_API
  std::ostream& print_pg(std::ostream& os, const const_twa_graph_ptr& arena);

  SPOT_DEPRECATED("use print_pg() instead")
  SPOT_API
  void pg_print(std::ostream& os, const const_twa_graph_ptr& arena);
  /// @}

  /// \ingroup games
  /// \brief Highlight the edges of a strategy on an automaton.
  ///
  /// Pass a negative color to not display the corresponding strategy.
  SPOT_API
  twa_graph_ptr highlight_strategy(twa_graph_ptr& arena,
                                   int player0_color = 5,
                                   int player1_color = 4);

  /// \ingroup games
  /// \brief Set the owner for all the states.
  /// @{
  SPOT_API
  void set_state_players(twa_graph_ptr& arena, const region_t& owners);
  SPOT_API
  void set_state_players(twa_graph_ptr& arena, region_t&& owners);
  /// @}

  /// \ingroup games
  /// \brief Set the owner of a state.
  SPOT_API
  void set_state_player(twa_graph_ptr& arena, unsigned state, bool owner);

  /// \ingroup games
  /// \brief Get the owner of a state.
  SPOT_API
  bool get_state_player(const const_twa_graph_ptr& arena, unsigned state);

  /// \ingroup games
  /// \brief Get the owner of all states
  ///@{
  SPOT_API
  const region_t& get_state_players(const const_twa_graph_ptr& arena);
  SPOT_API
  const region_t& get_state_players(twa_graph_ptr& arena);
  ///@}

  /// \ingroup games
  /// \brief Get or set the strategy
  /// @{
  SPOT_API
  const strategy_t& get_strategy(const const_twa_graph_ptr& arena);
  SPOT_API
  void set_strategy(twa_graph_ptr& arena, const strategy_t& strat);
  SPOT_API
  void set_strategy(twa_graph_ptr& arena, strategy_t&& strat);
  /// @}

  /// \ingroup games
  /// \brief Set all synthesis outputs as a conjunction
  SPOT_API
  void set_synthesis_outputs(const twa_graph_ptr& arena, const bdd& outs);

  /// \ingroup games
  /// \brief Get all synthesis outputs as a conjunction
  SPOT_API
  bdd get_synthesis_outputs(const const_twa_graph_ptr& arena);

  /// \brief Get the vector with the names of the output propositions
  SPOT_API
  std::vector<std::string>
  get_synthesis_output_aps(const const_twa_graph_ptr& arena);

  /// \ingroup games
  /// \brief Set the winner for all the states.
  /// @{
  SPOT_API
  void set_state_winners(twa_graph_ptr& arena, const region_t& winners);
  SPOT_API
  void set_state_winners(twa_graph_ptr& arena, region_t&& winners);
  /// @}

  /// \ingroup games
  /// \brief Set the winner of a state.
  SPOT_API
  void set_state_winner(twa_graph_ptr& arena, unsigned state, bool winner);

  /// \ingroup games
  /// \brief Get the winner of a state.
  SPOT_API
  bool get_state_winner(const const_twa_graph_ptr& arena, unsigned state);

  /// \ingroup games
  /// \brief Get the winner of all states
  /// @{
  SPOT_API
  const region_t& get_state_winners(const const_twa_graph_ptr& arena);
#ifndef SWIG
  SPOT_API
  const region_t& get_state_winners(twa_graph_ptr& arena);
#endif
  /// @}
}
