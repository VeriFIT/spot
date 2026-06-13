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

#include <spot/misc/common.hh>
#include <spot/tl/formula.hh>

namespace spot
{
  /// \ingroup tl_rewriting
  /// \brief Simplify a formula via one-pass unit propagation.
  ///
  /// This function traverses the formula tree top-down, collecting
  /// facts (subformulas known to be true or false in context) and
  /// using them to simplify sibling subformulas.  Facts are gathered
  /// without constructing new formulas: only existing subformulas can
  /// become facts.
  ///
  /// Examples:
  ///   - G(a) & (a | b)   → G(a) & b
  ///   - !a & (a | b)     → !a & b
  ///   - (a | b) -> b     → a -> b
  ///   - G(a & b & F(c)) propagates a, b, F(c) globally
  SPOT_API formula unit_propagate(formula f);
}
