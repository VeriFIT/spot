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

#include <iosfwd>
#include <unordered_map>
#include <spot/misc/common.hh>
#include <spot/misc/trival.hh>
#include <spot/graph/adjlist.hh>

namespace spot
{

  /// \ingroup games
  /// \brief Graph used for backward propagation of winning conditions in parity
  /// games.
  class SPOT_API backprop_graph final
  {
    static constexpr unsigned target = (1U << (sizeof(unsigned)*8 - 4)) - 1;

      struct backprop_state
    {
      int counter;            // number of unknown successors
      bool owner:1;
      bool frozen:1;
      bool determined:1;
      bool winner:1;            // meaningful only if determined is true
      unsigned choice: sizeof(unsigned)*8 - 4;

      backprop_state(bool owner)
        : counter(0),
          owner(owner),
          frozen(false),
          determined(false),
          winner(false),
          choice(0)
      {
      }
    };
  public:
    /// \brief Construct the backpropagation graph.
    backprop_graph(bool stop_asap = true)
      : stop_asap_(stop_asap)
    {
    }

    /// \brief Add a new state; \a owner is true if owned by Player 1.
    int new_state(bool owner)
    {
      return reverse_.new_state(owner);
    }

    /// \brief Set the name of the given state.
    void set_name(unsigned state, const std::string& s)
    {
      names_.emplace(state, s);
    }

    /// \brief Add an edge from \a src to \a dst.
    bool new_edge(unsigned src, unsigned dst);

    /// \brief Mark a state as frozen (no more incoming edges).
    ///
    /// Once a state is frozen, no more incoming edges can be added.
    /// If all successors are won by the other player, then a frozen
    /// state can be marked as won by the other player too.
    bool freeze_state(unsigned state);

    /// \brief Check if a state is frozen.
    ///
    /// Once a state is frozen, no more incoming edges can be added.
    /// If all successors are won by the other player, then a frozen
    /// state can be marked as won by the other player too.
    bool is_frozen(unsigned state) const
    {
      return (*this)[state].frozen;
    }

    /// \brief Check if the winner of a state has been determined.
    bool is_determined(unsigned state) const
    {
      return (*this)[state].determined;
    }

    /// \brief Return the winner of a state (true = Player 0).
    bool winner(unsigned state) const
    {
      return (*this)[state].winner;
    }

    /// \brief Return the chosen successor for a state.
    unsigned choice(unsigned state) const
    {
      return (*this)[state].choice;
    }

    /// \brief Set the winner of a state.
    bool set_winner(unsigned state, bool winner)
    {
      return set_winner(state, winner, target);
    }

    /// \brief Print the graph in dot format.
    std::ostream& print_dot(std::ostream& os) const;

    /// \brief Return the number of edges.
    unsigned num_edges() const
    {
      return reverse_.num_edges();
    }

  private:
    bool set_winner(unsigned state, bool winner, unsigned choice_state);

    adjlist<backprop_state> reverse_;
    bool stop_asap_;
    std::unordered_map<unsigned, std::string> names_;

    const backprop_state& operator[](unsigned state) const
    {
      return reverse_.state_data(state);
    }

    backprop_state& operator[](unsigned state)
    {
      return reverse_.state_data(state);
    }
  };


}
