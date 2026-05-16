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
#include <vector>

namespace spot
{
  /// \ingroup tl_rewriting
  /// \brief Types of mutations supported by mutate().
  enum mut_opts
    {
      /// Convert atomic propositions to constants.
      Mut_Ap2Const = 1U << 0,
      /// \brief Simplify bounds of bounded operators.
      ///
      /// If a bound is not formula::unbounded(), it can
      /// be reduced by one, or set to formula::unbounded().
      Mut_Simplify_Bounds = 1U << 1,
      /// Remove operands from n-ary operators.
      Mut_Remove_Multop_Operands = 1U << 2,
      /// \brief Remove operators.
      ///
      /// Unary operators can be replaced by their operand.
      /// Binary operators can be replaced by one of their operands.
      Mut_Remove_Ops = 1U << 3,
      /// \brief Split syntactic sugar into simpler forms.
      ///
      /// For instance a<->b could be rewritten as a->b or b->a.
      Mut_Split_Ops = 1U << 4,
      /// \brief Rewrite some operators.
      ///
      /// Currently U can be changed to W.
      /// M can be changed to R or U.
      /// R can be changed to W.
      Mut_Rewrite_Ops = 1U << 5,
      /// Replace one atomic proposition by another one.
      Mut_Remove_One_Ap = 1U << 6,
      /// Attempt every mutation possible.
      Mut_All = -1U
    };

  /// \ingroup tl_rewriting
  /// \brief Generate mutations of a formula.
  ///
  /// Returns up to \a max_output mutated formulas derived from \a f
  /// by applying \a mutation_count simultaneous mutations selected by
  /// \a opts (a bitmask of mut_opts values).  If \a sort is true, the
  /// results are sorted.
  SPOT_API
  std::vector<formula> mutate(formula f,
                              unsigned opts = Mut_All,
                              unsigned max_output = -1U,
                              unsigned mutation_count = 1,
                              bool sort = true);
}
