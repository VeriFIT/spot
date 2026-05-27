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
#include <spot/twaalgos/emptiness.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/word.hh>
#include <climits>
#include <vector>

namespace spot
{
  /// \ingroup twa_algorithms
  /// \brief Lazily enumerate lasso-shaped accepted runs/words of bounded size.
  ///
  /// A lasso consists of a finite stem path followed by an infinite cycle.
  /// Given bounds on the stem and cycle lengths, this class enumerates all
  /// accepted lasso-shaped runs in order of increasing total length
  /// (stem + cycle), breaking ties by shorter stem first.
  ///
  /// All acceptance conditions are supported.
  ///
  /// If the automaton is non-deterministic, the enumeration does not remove
  /// duplicate words or runs.
  class SPOT_API lasso_enumerator final
  {
  public:
    /// \brief Construct a lasso enumerator.
    ///
    /// \param aut       automaton with any acceptance condition
    /// \param min_stem  minimum stem length (≥0)
    /// \param max_stem  maximum stem length (≥min_stem; UINT_MAX = unbounded)
    /// \param min_cycle minimum cycle length (≥1)
    /// \param max_cycle maximum cycle length (≥min_cycle; UINT_MAX = unbounded)
    ///
    /// \throw std::invalid_argument if the bounds are inconsistent.
    lasso_enumerator(const const_twa_graph_ptr& aut,
                     unsigned min_stem, unsigned max_stem,
                     unsigned min_cycle, unsigned max_cycle);

    ~lasso_enumerator() = default;
    lasso_enumerator(const lasso_enumerator&) = delete;
    lasso_enumerator& operator=(const lasso_enumerator&) = delete;

    /// \brief Return the next accepted run, or nullptr when exhausted.
    twa_run_ptr next_run();

    /// \brief Return the next accepted word, or nullptr when exhausted.
    twa_word_ptr next_word();

  private:
    const_twa_graph_ptr aut_;
    scc_info si_;             ///< SCC info, used to skip rejecting SCCs
    unsigned min_stem_, max_stem_;
    unsigned min_cycle_, max_cycle_;
    unsigned init_state_; ///< initial state number
    bool done_;           ///< true when all pairs exhausted

    // Current (stem_len, cycle_len) pair being enumerated.
    unsigned cur_stem_;   ///< current stem length
    unsigned cur_cycle_;  ///< current cycle length
    unsigned cur_total_;  ///< = cur_stem_ + cur_cycle_

    // DFS stacks: each element is an edge number in the automaton graph.
    std::vector<unsigned> stem_;   ///< current stem path (edge numbers)
    std::vector<unsigned> cycle_;  ///< current cycle path (edge numbers)

    unsigned stem_end_;        ///< state at the end of the current stem
    bool stem_ready_;          ///< stem_ holds a valid stem of length cur_stem_
    bool cycle_ready_;         ///< cycle_ holds a valid accepted cycle
    bool cycle_exhausted_;     ///< no more cycles exist for current stem

    // Graph access helpers.
    unsigned first_edge_(unsigned state) const;
    unsigned next_edge_(unsigned edge) const;
    unsigned edge_dst_(unsigned edge) const;
    bdd edge_cond_(unsigned edge) const;
    acc_cond::mark_t edge_acc_(unsigned edge) const;

    // DFS helpers.
    bool backtrack_(std::vector<unsigned>& path) const;
    bool extend_(std::vector<unsigned>& path,
                 unsigned from_state, unsigned target_len);
    bool is_valid_cycle_() const;

    // Advancement functions.
    bool advance_pair_();
    bool advance_stem_();
    bool advance_cycle_();

    // Build a twa_run from the current stem_ and cycle_.
    twa_run_ptr build_run_() const;
  };
}
