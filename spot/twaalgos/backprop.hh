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

  struct SPOT_API backprop_state
  {
    int counter;                // number of unknown successors
    bool owner;
    bool frozen;
    trival status;             // satisfiable, unstatisfiable, unknown

    backprop_state(bool owner)
      : counter(0),
        owner(owner),
        frozen(false)
    {
    }
  };

  struct SPOT_API backprop_graph final
  {
    backprop_graph(bool stop_asap = true)
      : stop_asap_(stop_asap)
    {
    }

    int new_state(bool owner)
    {
      return reverse_.new_state(owner);
    }

    void set_name(unsigned state, const std::string& s)
    {
      names_.emplace(state, s);
    }

    const backprop_state& operator[](unsigned state) const
    {
      return reverse_.state_data(state);
    }

    // return true if the status of src is now known
    bool new_edge(unsigned src, unsigned dst);

    // call once the successors of a state have all been declared to
    // see if the status of that state can be determined already
    bool freeze_state(unsigned state);

    trival status_of(unsigned state) const
    {
      return (*this)[state].status;
    }

    bool set_status(unsigned state, bool status);

    std::ostream& print_dot(std::ostream& os) const;

    unsigned num_edges() const
    {
      return reverse_.num_edges();
    }

  private:
    adjlist<backprop_state> reverse_;
    bool stop_asap_;
    std::unordered_map<unsigned, std::string> names_;

    backprop_state& operator[](unsigned state)
    {
      return reverse_.state_data(state);
    }
  };


}
