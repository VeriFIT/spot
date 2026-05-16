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

#include <unordered_map>
#include <vector>
#include <spot/graph/graph.hh>

namespace spot
{
  /// \brief A graph wrapper associating named states to graph state indices.
  template <typename Graph,
            typename State_Name,
            typename Name_Hash = std::hash<State_Name>,
            typename Name_Equal = std::equal_to<State_Name>>
  class SPOT_API named_graph
  {
  protected:
    Graph& g_; ///< The underlying graph.
  public:

    typedef typename Graph::state state; ///< State type.
    typedef typename Graph::edge edge;   ///< Edge type.
    typedef State_Name name;             ///< Name type.

    /// Map from name to state number type.
    typedef std::unordered_map<name, state,
                               Name_Hash, Name_Equal> name_to_state_t;
    name_to_state_t name_to_state; ///< Map from name to state number.
    /// Map from state number to name type.
    typedef std::vector<name> state_to_name_t;
    state_to_name_t state_to_name; ///< Map from state number to name.

    /// Construct wrapping graph g.
    named_graph(Graph& g)
      : g_(g)
    {
    }

    /// Return the underlying graph.
    Graph& graph()
    {
      return g_;
    }

    /// Return the underlying graph.
    Graph& graph() const
    {
      return g_;
    }

    /// Create a new state with the given name.
    template <typename... Args>
    state new_state(name n, Args&&... args)
    {
      auto p = name_to_state.emplace(n, 0U);
      if (p.second)
        {
          unsigned s = g_.new_state(std::forward<Args>(args)...);
          p.first->second = s;
          if (state_to_name.size() < s + 1)
            state_to_name.resize(s + 1);
          state_to_name[s] = n;
          return s;
        }
      return p.first->second;
    }

    /// \ingroup graph_data_structures
    /// \brief Give an alternate name to a state.
    /// \return true iff the newname state already existed
    /// (in this case the existing newname state will be merged
    /// with state s: the newname will be unreachable and without
    /// successors.)
    bool alias_state(state s, name newname)
    {
      auto p = name_to_state.emplace(newname, s);
      if (!p.second)
        {
          // The state already exists.  Change its number.
          auto old = p.first->second;
          p.first->second = s;
          // Add the successor of OLD to those of S.
          auto& trans = g_.edge_vector();
          auto& states = g_.states();
          trans[states[s].succ_tail].next_succ = states[old].succ;
          states[s].succ_tail = states[old].succ_tail;
          states[old].succ = 0;
          states[old].succ_tail = 0;
          // Remove all references to old in edges:
          unsigned tend = trans.size();
          for (unsigned t = 1; t < tend; ++t)
            {
              if (trans[t].src == old)
                trans[t].src = s;
              if (trans[t].dst == old)
                trans[t].dst = s;
            }
        }
      return !p.second;
    }

    /// Return the state number for the given name.
    state get_state(name n) const
    {
      return name_to_state.at(n);
    }

    /// Return the name for the given state number.
    name get_name(state s) const
    {
      return state_to_name.at(s);
    }

    /// Return true iff a state with the given name exists.
    bool has_state(name n) const
    {
      return name_to_state.find(n) != name_to_state.end();
    }

    /// Return all state names.
    const state_to_name_t& names() const
    {
      return state_to_name;
    }

    /// Add a new edge.
    template <typename... Args>
    edge
    new_edge(name src, name dst, Args&&... args)
    {
      return g_.new_edge(get_state(src), get_state(dst),
                         std::forward<Args>(args)...);
    }

    /// Add a new universal edge.
    template <typename I, typename... Args>
    edge
    new_univ_edge(name src, I dst_begin, I dst_end, Args&&... args)
    {
      std::vector<unsigned> d;
      d.reserve(std::distance(dst_begin, dst_end));
      while (dst_begin != dst_end)
        d.emplace_back(get_state(*dst_begin++));
      return g_.new_univ_edge(get_state(src), d.begin(), d.end(),
                              std::forward<Args>(args)...);
    }

    /// Add a new universal edge.
    template <typename... Args>
    edge
    new_univ_edge(name src,
                  const std::initializer_list<State_Name>& dsts, Args&&... args)
    {
      return new_univ_edge(src, dsts.begin(), dsts.end(),
                           std::forward<Args>(args)...);
    }
  };
}
