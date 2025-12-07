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
#include <spot/tl/sat.hh>
#include <spot/tl/apcollect.hh>
#include <spot/twaalgos/translate.hh>

namespace spot
{
  bool ltl_satisfiable(formula f)
  {
    // Remove atomic propositions that always have
    // the same polarity in the formula.   For instance
    // if P always appears positively, then f is satisfiable
    // iff f[P<-true] is satisfiable.
    {
      std::vector<std::string> no_inputs;
      realizability_simplifier rs(f, no_inputs);
      f = rs.simplified_formula();
    }

    if (f.is_tt())
      return true;
    if (f.is_ff())
      return false;

    spot::translator trans;
    trans.set_level(spot::postprocessor::Low);
    trans.set_type(spot::postprocessor::GeneralizedBuchi);
    trans.set_pref(spot::postprocessor::Any);
    twa_graph_ptr a = trans.run(f);
    return !a->is_empty();
  }


}
