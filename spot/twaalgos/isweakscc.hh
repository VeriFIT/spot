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

#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  /// \addtogroup twa_misc
  /// @{

  /// \brief Whether the SCC number \a scc in \a map has a rejecting
  /// cycle.
  SPOT_API bool
  scc_has_rejecting_cycle(scc_info& map, unsigned scc);

  /// \brief Whether the SCC number \a scc in \a map is inherently
  /// weak.
  ///
  /// An SCC is inherently weak if either its cycles are all
  /// accepting, or they are all non-accepting.
  ///
  /// Note that terminal SCCs are also inherently weak with that
  /// definition.
  SPOT_API bool
  is_inherently_weak_scc(scc_info& map, unsigned scc);

  /// \brief Whether the SCC number \a scc in \a map is weak.
  ///
  /// An SCC is weak if it is non-accepting, or if all its transitions
  /// are fully accepting (i.e., they belong to all acceptance sets).
  ///
  /// Note that terminal SCCs are also weak with that definition.
  SPOT_API bool
  is_weak_scc(scc_info& map, unsigned scc);

  /// \brief Whether the SCC number \a scc in \a map has a
  /// generalized co-Büchi acceptance condition.
  ///
  /// The acceptance condition of the automaton is first simplified
  /// for \a scc: acceptance sets that do not occur in \a scc are
  /// considered never visited (see acc_cond::restrict_to()), and
  /// acceptance sets that occur on all edges of \a scc are
  /// considered always visited (see acc_cond::remove()).  The
  /// remaining sets are then renumbered, and the function returns
  /// whether the resulting condition is generalized co-Büchi (see
  /// acc_cond::is_generalized_co_buchi()).
  ///
  /// This test is syntactic: a condition that is equivalent to a
  /// generalized co-Büchi condition without being written as one
  /// (e.g., <code>Fin(0)&Fin(0)</code>) is not recognized.  A
  /// simplified condition of <code>f</code> counts as generalized
  /// co-Büchi (with no Fin term), while <code>t</code> does not.
  ///
  /// This is one of the three alternative conditions (along with
  /// determinism and inherent weakness) under which an SCC is
  /// considered an elevator component of an Emerson-Lei elevator
  /// automaton; see is_emerson_lei_elevator_automaton().
  SPOT_API bool
  is_generalized_co_buchi_scc(scc_info& map, unsigned scc);

  /// \brief Whether the SCC number \a scc in \a map is complete.
  ///
  /// An SCC is complete iff for all states and all labels there exists
  /// a transition that stays into this SCC.  For this function,
  /// universal transitions are considered in the SCC if all their
  /// destinations are into the SCC.
  SPOT_API bool
  is_complete_scc(scc_info& map, unsigned scc);

  /// \brief Whether the SCC number \a scc in \a map is terminal.
  ///
  /// An SCC is terminal if it is weak, complete, and accepting.
  SPOT_API bool
  is_terminal_scc(scc_info& map, unsigned scc);

  /// @}
}
