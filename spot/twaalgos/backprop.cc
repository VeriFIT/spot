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
#include <deque>
#include <bddx.h>
#include <spot/twaalgos/backprop.hh>

namespace spot
{

  bool backprop_graph::new_edge(int src, int dst)
  {
    backprop_state& ss = (*this)[src];
    if (SPOT_UNLIKELY(ss.frozen))
      throw std::runtime_error
        ("backprop_graph: cannot add successor to frozen state");
    if (!ss.status.is_maybe())
      return false;
    backprop_state& ds = (*this)[dst];
    if (ds.status.is_maybe())
      {
        // declare an edge for backward propagation
        reverse_.new_edge(dst, src);
        ss.counter += 1;
      }
    else if (ss.owner && ds.status.is_true())
      {
        return set_status(src, true);
      }
    else if (!ss.owner && ds.status.is_false())
      {
        return set_status(src, false);
      }
    // ignore other edges
    return false;
  }

  bool backprop_graph::freeze_state(int state)
  {
    backprop_state& ss = (*this)[state];
    ss.frozen = true;
    if (ss.status.is_maybe() && ss.counter == 0)
      return set_status(state, !ss.owner);
    return false;
  }

  bool backprop_graph::set_status(int state, bool new_status)
  {
    if (SPOT_UNLIKELY(!(*this)[state].status.is_maybe()))
      throw std::runtime_error
        ("backprop_graph: cannot change status of determined state");
    (*this)[state].status = new_status;
    std::deque<int> todo;
    todo.push_back(state);
    bool result = false;
    do
      {
        int s = todo.front();
        todo.pop_front();

        backprop_state& bs = (*this)[state];
        assert(!bs.status.is_maybe());
        bool bs_status = bs.status.is_true();
        for (unsigned p: reverse_.out(s))
          {
            backprop_state& prev = (*this)[p];
            if (!prev.status.is_maybe())
              continue;
            if ((prev.owner == bs_status)
                || (--prev.counter == 0 && prev.frozen))
              {
                prev.status = bs_status;
                if (SPOT_UNLIKELY(p == 0))
                  {
                    if (stop_asap_)
                      return true;
                    else
                      result = true;
                  }
                todo.push_back(p);
              }
          }
      }
    while (!todo.empty());
    return result;
  }

  std::ostream& backprop_graph::print_dot(std::ostream& os) const
  {
    os << "digraph mtdfa {\n  rankdir=TB;\n";
    unsigned num_states = reverse_.num_states();
    for (unsigned state = 0; state < num_states; ++state)
      {
        const backprop_state& bs = (*this)[state];
        os << "  " << state << " [shape="
           << (bs.owner ? "diamond" : "box")
           << ", style=\"filled";
        if (!bs.owner)
          os << ",rounded";
        if (!bs.frozen)
          os << ",dashed";
        os << "\" fillcolor="
           << (bs.status.is_true() ? "\"#33A02C\""
               : bs.status.is_false() ? "\"#E31A1C\"" : "white")
           << ", label=\"" << state << "\"];\n";
      }
    for (unsigned state = 0; state < num_states; ++state)
      for (unsigned p: reverse_.out(state))
        os << "  " << p << " -> " << state << ";\n";
    return os << "}\n";
  }

}
