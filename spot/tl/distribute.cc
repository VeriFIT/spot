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
  // Convert a formula like X(a | X(b | X(c & Xd)))
  // into X(a) | XX(b) | (XXX(c) & XXXXd)
  formula distribute_next(formula f, int level)
  {
    if (!f.is(op::X, op::strong_X))
      return formula::X(level, f);
    formula sub = f[0];
    ++level;
    while (sub.is(op::X, op::strong_X))
      {
        sub = sub[0];
        ++level;
      }
    switch (op o = sub.kind())
      {
      case op::Or:
      case op::And:
        {
          std::vector<formula> new_subs;
          bool changed = false;
          for (const formula& g: sub)
            {
              formula s = distribute_next(g, level);
              if (s != g)
                changed = true;
              new_subs.push_back(s);
            }
          if (!changed)
            return f;
          return formula::multop(o, new_subs);
        }
      default:
        return distribute_next(sub, level);
      }
  }
}
