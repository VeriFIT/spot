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
#include <spot/misc/bddlt.hh>
#include <unordered_map>

namespace spot
{
  typedef std::pair<acc_cond::mark_t, unsigned> terminal_data_t;
  typedef std::vector<terminal_data_t> terminal_data_map_t;

  struct SPOT_API mtdtwa: public std::enable_shared_from_this<mtdtwa>
  {
  public:
    mtdtwa(const bdd_dict_ptr& dict) noexcept
      : dict_(dict)
     {
     }

    ~mtdtwa()
    {
      dict_->unregister_all_my_variables(this);
    }

    std::vector<bdd> states;
    acc_cond acc;
    bdd_dict_ptr dict_;
    terminal_data_map_t terminal_data_map;

    unsigned num_roots() const
    {
      return states.size();
    }

    // Print the MTBDD.
    std::ostream& print_dot(std::ostream& os) const;

    // convert to twa
    twa_graph_ptr as_twa(bool state_based = false, bool labels = true) const;
  };


  typedef std::shared_ptr<mtdtwa> mtdtwa_ptr;
  typedef std::shared_ptr<const mtdtwa> const_mtdtwa_ptr;

  SPOT_API mtdtwa_ptr dtwa_to_mtdtwa(const twa_graph_ptr& aut);
}
