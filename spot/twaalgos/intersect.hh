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

#include <spot/twa/twa.hh>

namespace spot
{
  /// \ingroup twa_algorithms
  /// \brief Whether two automata accept a common word.
  ///
  /// This runs an emptiness check on the synchronous product of the
  /// two automata, but never builds that product: product states are
  /// represented as pairs of state numbers, and the DFS stacks store
  /// one acceptance mark set per operand.  This avoids the cost of the
  /// abstract <code>state*</code> interface used by
  /// <code>otf_product(a, b)->is_empty()</code>.
  ///
  /// Both operands must be explicit (<code>twa_graph</code>),
  /// existential, and use a Fin-less acceptance condition.  A
  /// <code>std::runtime_error</code> is thrown otherwise.
  SPOT_API
  bool intersects(const const_twa_graph_ptr& left,
                  const const_twa_graph_ptr& right);

  /// \ingroup twa_algorithms
  /// \brief Return a word accepted by both automata, as a run of \a left.
  ///
  /// Return <code>nullptr</code> if the two automata do not accept a
  /// common word.  The states of the returned run belong to \a left,
  /// while the labels of its transitions are the conjunctions of the
  /// labels of the corresponding transitions of \a left and \a right.
  ///
  /// The same restrictions as spot::intersects() apply.
  SPOT_API
  twa_run_ptr intersecting_run(const const_twa_graph_ptr& left,
                               const const_twa_graph_ptr& right);
}
