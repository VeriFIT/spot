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
#include <spot/tl/distribute.hh>

namespace spot
{
  namespace
  {
    // Distribute chains of X and X[!] operators over Boolean
    // operators.  For example:
    //
    //   X(a | X(b | X[!](c & Xd)))  ->  X(a) | XX(b) | (XXX[!](c) &
    //                                                        XXX[!]X(d))
    //
    // The strong_x vector tracks the strong vs weak status of each
    // level of X/X[!] encountered on the path from the root to the
    // current subformula.  A true entry means X[!] (strong), false
    // means plain X.
    //
    // The vector is modified in-place as we recurse: each level
    // pushes the operators it peels, processes its children (which
    // push/pop their own), and pops its own entries before returning.
    // This avoids copying the vector for each recursive call.
    static formula distribute_next_impl(formula f,
                                        std::vector<bool>& strong_x)
    {
      size_t saved = strong_x.size();

      // Peel all leading X and X[!] operators, recording their
      // strong/weak status into the vector.
      while (f.is(op::X, op::strong_X))
        {
          strong_x.push_back(f.is(op::strong_X));
          f = f[0];
        }

      switch (op o = f.kind())
        {
        case op::Or:
        case op::And:
          {
            std::vector<formula> new_subs;
            bool changed = false;
            for (const formula& g: f)
              {
                // Each child gets the same strong_x state; it will
                // push/pop its own operators, restoring the state.
                formula s = distribute_next_impl(g, strong_x);
                if (s != g)
                  changed = true;
                new_subs.push_back(s);
              }
            strong_x.resize(saved);
            if (!changed)
              return f;
            return formula::multop(o, new_subs);
          }
        default:
          {
            // No Boolean operator to distribute into: build the chain
            // of X/X[!] from the recorded flags, in reverse order
            // (innermost first).
            for (auto it = strong_x.rbegin();
                 it != strong_x.rend(); ++it)
              {
                if (*it)
                  f = formula::strong_X(std::move(f));
                else
                  f = formula::X(std::move(f));
              }
            strong_x.resize(saved);
            return f;
          }
        }
    }
  }

  formula distribute_next(formula f)
  {
    std::vector<bool> strong_x;
    return distribute_next_impl(f, strong_x);
  }
}
