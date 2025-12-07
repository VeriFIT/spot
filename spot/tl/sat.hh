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

#include <spot/tl/formula.hh>

namespace spot
{
  /// \addtogroup tl_misc
  /// @{

  /// \brief Decide if an LTL formula is satisfiable.
  ///
  /// This is not a very smart implementation currently: the formula
  /// is first simplified by removing atomic propositions that always
  /// have the same polarity, then the result is translated into a
  /// TGBA that is checked for emptiness.  Note that building an
  /// entire automaton is overkill when the formula is satisfiable, so
  /// eventually this could be done on-the-fly or using other
  /// techniques.
  SPOT_API bool ltl_satisfiable(formula f);

  /// @}
}
