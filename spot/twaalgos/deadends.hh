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

namespace spot
{
  /// \brief restrict labels from "dead-end edges"
  ///
  /// A dead-end edge is an edge between two states S and D such
  /// that D has only itself as successor.  I.e., once a run goes
  /// through this "dead-end" edge, it gets stuck in D.
  ///
  /// Let Lab(S,D) denote the disjunction of all labels between S and
  /// D.  Let UsefulLab(D,D) be the disjunction of labels of any
  /// subset of self-loops of D that will intersect all accepting
  /// cycles around D.
  ///
  /// Now, if the following implications are satisfied
  ///
  /// ⎧ UsefulLab(D,D) ⇒ Lab(S,D) ⇒ Lab(S,S),<br/>
  /// ⎨ <br/>
  /// ⎩ Lab(D,D) ⇒ Lab(S,S).<br/>
  ///
  /// then any edge between S and D, labeled by ℓ⊆Lab(S,D)
  /// can be replaced by ℓ∩UsefulLab(D,D).
  ///
  /// This algorithm has no effect on deterministic automata (where
  /// it is not possible that Lab(S,D) ⇒ Lab(S,S)).
  ///
  /// Computing UsefulLab(D,D) is the tricky part, as many subset of
  /// selfloops can be considered.  For instance, setting
  /// UsefulLab(D,D) := Lab(D,D) clearly interesect all accepting
  /// cycles, but it is very coarse.  Currently the code uses two
  /// smaller definitions for UsefulLab(D,D):
  ///
  /// - the first is like Lab(D,D), but ignoring transitions that
  ///   will force the acceptance to be unsatisfiable.  For instance,
  ///   if the acceptance condition is Fin(0)&... then any edge colored
  ///   with ⓪ will not contribute anything to UsefulLab.
  ///
  /// - the second definition is only used for Fin-less acceptance
  ///   conditions.  In this case, we select one color for each
  ///   disjunctive branch of the acceptance condition, and collect
  ///   all labels from edges matching those colors.  For instance if
  ///   the condition is Inf(0)&Inf(1)|Inf(2) any accepting run is
  ///   forced to visit some edges labeled by ⓪ or ②, so we gather the
  ///   labels of all edges colored with these two colors.
  SPOT_API twa_graph_ptr
  restrict_dead_end_edges_here(twa_graph_ptr& aut);
}
