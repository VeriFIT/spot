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

#include "config.h"

#include <spot/twaalgos/dependent.hh>
#include <spot/twa/twagraph.hh>

#include <bddx.h>
#include <algorithm>
#include <cstddef>
#include <deque>
#include <unordered_set>
#include <stdexcept>
#include <utility>

namespace spot
{
  namespace
  {
    using state_pair = std::pair<unsigned, unsigned>;

    static size_t
    pair_key(unsigned s1, unsigned s2)
    {
      constexpr unsigned half_bits = sizeof(size_t) * 4;
      return (static_cast<size_t>(s1) << half_bits)
             ^ static_cast<size_t>(s2);
    }

    struct state_pair_hash
    {
      size_t operator()(const state_pair& p) const noexcept
      {
        return pair_key(p.first, p.second);
      }
    };

    static std::vector<state_pair>
    compute_compatible_pairs(const const_twa_graph_ptr& aut)
    {
      std::vector<state_pair> pairs;
      pairs.reserve(aut->num_states());

      std::unordered_set<state_pair, state_pair_hash> seen;
      seen.reserve(aut->num_states());

      std::deque<state_pair> todo;
      unsigned init = aut->get_init_state_number();
      todo.emplace_back(init, init);
      seen.insert({init, init});

      while (!todo.empty())
        {
          auto [s1, s2] = todo.front();
          todo.pop_front();
          pairs.emplace_back(s1, s2);

          for (const auto& e1: aut->out(s1))
            for (const auto& e2: aut->out(s2))
              if (bdd_have_common_assignment(e1.cond, e2.cond))
                {
                  unsigned d1 = e1.dst;
                  unsigned d2 = e2.dst;
                  if (d1 > d2)
                    std::swap(d1, d2);
                  if (seen.insert({d1, d2}).second)
                    todo.emplace_back(d1, d2);
                }
        }

      return pairs;
    }

    static bool
    is_dependent_var(const const_twa_graph_ptr& orig,
                     const std::vector<state_pair>& compatible_pairs,
                     int var,
                     bdd ignored_vars)
    {
      const_twa_graph_ptr aut = orig;
      if (ignored_vars != bddtrue)
        {
          // If we have some variable to ignore, make a copy of the
          // automaton and existentially quantify the label of the
          // edges leaving all states.
          twa_graph_ptr copy = make_twa_graph(orig, twa::prop_set::all());
          unsigned ns = orig->num_states();
          for (unsigned s = 0; s < ns; ++s)
            for (auto& e: copy->out(s))
              e.cond = bdd_exist(e.cond, ignored_vars);
          aut = copy;
        }

      for (auto [s1, s2]: compatible_pairs)
        for (const auto& e1: aut->out(s1))
          for (const auto& e2: aut->out(s2))
            if (!bdd_have_dependent_var(e1.cond, e2.cond, var))
              return false;
      return true;
    }
  }

  std::vector<int>
  analyze_dependent_output(const const_twa_graph_ptr& aut,
                           const std::vector<int>& outputs)
  {
    if (SPOT_UNLIKELY(!aut->is_existential()))
      throw std::runtime_error
        ("analyze_dependent_output() does not support alternating automata");

    std::vector<int> dependent_outputs;
    auto compatible_pairs = compute_compatible_pairs(aut);

    bdd ignored_vars = bddtrue;
    for (int o: outputs)
      if (is_dependent_var(aut, compatible_pairs, o, ignored_vars))
        {
          dependent_outputs.emplace_back(o);
          ignored_vars &= bdd_ithvar(o);
        }

    return dependent_outputs;
  }
}
