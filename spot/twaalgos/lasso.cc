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
#include <spot/twaalgos/lasso.hh>
#include <stdexcept>
#include <climits>

namespace spot
{
  lasso_enumerator::lasso_enumerator(const const_twa_graph_ptr& aut,
                                     unsigned min_stem, unsigned max_stem,
                                     unsigned min_cycle, unsigned max_cycle)
    : aut_(aut),
      si_(aut),
      min_stem_(min_stem),
      max_stem_(max_stem),
      min_cycle_(min_cycle),
      max_cycle_(max_cycle),
      init_state_(aut->get_init_state_number()),
      done_(false),
      cur_stem_(min_stem),
      cur_cycle_(min_cycle),
      stem_end_(init_state_),
      stem_ready_(false),
      cycle_ready_(false),
      cycle_exhausted_(false)
  {
    if (max_stem < min_stem)
      throw std::invalid_argument
        ("lasso_enumerator: max_stem < min_stem");
    if (min_cycle < 1)
      throw std::invalid_argument
        ("lasso_enumerator: min_cycle must be >= 1");
    if (max_cycle < min_cycle)
      throw std::invalid_argument
        ("lasso_enumerator: max_cycle < min_cycle");

    if (min_stem > UINT_MAX - min_cycle)
      throw std::invalid_argument
        ("lasso_enumerator: min_stem + min_cycle overflows");
    cur_total_ = min_stem + min_cycle;

    // If the SCC of the initial state is not useful (cannot reach an
    // accepting SCC), then no accepting run can exist.
    if (!si_.is_useful_scc(si_.initial()))
      done_ = true;
  }

  // Return the first outgoing edge of a state with a satisfiable label (0 if
  // none).
  unsigned
  lasso_enumerator::first_edge_(unsigned state) const
  {
    unsigned e = aut_->get_graph().state_storage(state).succ;
    while (e != 0 && edge_cond_(e) == bddfalse)
      e = aut_->get_graph().edge_storage(e).next_succ;
    return e;
  }

  // Return the next outgoing edge after edge with a satisfiable label (0 if
  // none).
  unsigned
  lasso_enumerator::next_edge_(unsigned edge) const
  {
    unsigned e = aut_->get_graph().edge_storage(edge).next_succ;
    while (e != 0 && edge_cond_(e) == bddfalse)
      e = aut_->get_graph().edge_storage(e).next_succ;
    return e;
  }

  // Return the destination state of an edge.
  unsigned
  lasso_enumerator::edge_dst_(unsigned edge) const
  {
    return aut_->get_graph().edge_storage(edge).dst;
  }

  // Return the BDD label of an edge.
  bdd
  lasso_enumerator::edge_cond_(unsigned edge) const
  {
    return aut_->get_graph().edge_storage(edge).cond;
  }

  // Return the acceptance marks of an edge.
  acc_cond::mark_t
  lasso_enumerator::edge_acc_(unsigned edge) const
  {
    return aut_->get_graph().edge_storage(edge).acc;
  }

  // Advance the last edge in path to its next sibling.
  // Returns false when the entire path is exhausted (path is emptied).
  bool
  lasso_enumerator::backtrack_(std::vector<unsigned>& path) const
  {
    while (!path.empty())
      {
        unsigned e = next_edge_(path.back());
        path.pop_back();
        if (e != 0)
          {
            path.push_back(e);
            return true;
          }
      }
    return false;
  }

  // Extend path to exactly target_len edges, starting from from_state.
  // path may already be partially built (and is assumed to be on a valid
  // prefix from from_state).  Backtracks on dead ends.
  // Returns false if no path of target_len edges exists.
  bool
  lasso_enumerator::extend_(std::vector<unsigned>& path,
                             unsigned from_state, unsigned target_len)
  {
    while (path.size() < target_len)
      {
        unsigned curr = path.empty() ? from_state : edge_dst_(path.back());
        unsigned e = first_edge_(curr);
        if (e == 0)
          {
            if (!backtrack_(path))
              return false;
          }
        else
          path.push_back(e);
      }
    return true;
  }

  // Check whether cycle_ is a valid accepted cycle for the current stem.
  // Requires cycle_.size() == cur_cycle_.
  bool
  lasso_enumerator::is_valid_cycle_() const
  {
    if (edge_dst_(cycle_.back()) != stem_end_)
      return false;
    acc_cond::mark_t marks = {};
    for (unsigned e : cycle_)
      marks |= edge_acc_(e);
    return aut_->acc().accepting(marks);
  }

  // Advance cycle_ to the next valid accepted cycle for the current stem.
  // If cycle_ready_ is true, advances past the current one.
  // Returns false if no more valid cycles exist for this stem.
  bool
  lasso_enumerator::advance_cycle_()
  {
    if (cycle_exhausted_)
      return false;
    if (cycle_ready_)
      {
        cycle_ready_ = false;
        if (!backtrack_(cycle_))
          {
            cycle_exhausted_ = true;
            return false;
          }
      }
    while (true)
      {
        if (!extend_(cycle_, stem_end_, cur_cycle_))
          {
            cycle_exhausted_ = true;
            return false;
          }
        if (is_valid_cycle_())
          {
            cycle_ready_ = true;
            return true;
          }
        if (!backtrack_(cycle_))
          {
            cycle_exhausted_ = true;
            return false;
          }
      }
  }

  // Advance stem_ to the next path of length cur_stem_ from init_state_.
  // Initializes the first stem when stem_ready_ is false.
  // Resets cycle state for the new stem.
  // Skips stem endpoints in trivial or rejecting SCCs.
  // Returns false if no more stems exist for the current pair.
  bool
  lasso_enumerator::advance_stem_()
  {
    auto endpoint_ok = [this](unsigned state)
    {
      unsigned scc = si_.scc_of(state);
      return !si_.is_trivial(scc) && si_.is_useful_scc(scc);
    };

    while (true)
      {
        cycle_.clear();
        cycle_ready_ = false;
        cycle_exhausted_ = false;

        if (!stem_ready_)
          {
            // Initialize: find first stem path.
            stem_.clear();
            if (cur_stem_ == 0)
              {
                stem_end_ = init_state_;
                if (endpoint_ok(stem_end_))
                  {
                    stem_ready_ = true;
                    return true;
                  }
                // init_state_ is in a rejecting SCC; no stem of length 0 works.
                stem_ready_ = false;
                return false;
              }
            if (!extend_(stem_, init_state_, cur_stem_))
              return false;
            stem_end_ = edge_dst_(stem_.back());
            stem_ready_ = true;
            if (endpoint_ok(stem_end_))
              return true;
            // Fall through to advance past this bad endpoint.
          }
        else
          {
            // Advance: no more stems for stem_len = 0.
            if (cur_stem_ == 0)
              {
                stem_ready_ = false;
                return false;
              }

            // Advance to the next stem path.
            if (!backtrack_(stem_) || !extend_(stem_, init_state_, cur_stem_))
              {
                stem_ready_ = false;
                return false;
              }
            stem_end_ = edge_dst_(stem_.back());
            if (endpoint_ok(stem_end_))
              return true;
          }
        // stem_end_ is in a rejecting/trivial SCC; try the next stem.
      }
  }

  // Advance to the next valid (cur_stem_, cur_cycle_) pair.
  // Returns false when all pairs within bounds are exhausted.
  bool
  lasso_enumerator::advance_pair_()
  {
    while (true)
      {
        // Try to increment cur_stem_ within the current total
        // (which decreases cur_cycle_ by 1).
        if (cur_stem_ < max_stem_ && cur_cycle_ > min_cycle_)
          {
            ++cur_stem_;
            --cur_cycle_;
            stem_ready_ = false;
            stem_.clear();
            cycle_.clear();
            cycle_ready_ = false;
            cycle_exhausted_ = false;
            return true;
          }

        // Must increment cur_total_.
        // Compute the maximum allowable total (with saturation).
        unsigned max_total;
        if (max_stem_ >= UINT_MAX - max_cycle_)
          max_total = UINT_MAX;
        else
          max_total = max_stem_ + max_cycle_;

        if (cur_total_ >= max_total)
          return false;

        ++cur_total_;

        // Compute stem range for new cur_total_:
        //   stem in [stem_lo, stem_hi]
        // where stem_lo = max(min_stem_, cur_total_ - max_cycle_)
        //       stem_hi = min(max_stem_, cur_total_ - min_cycle_)
        unsigned stem_lo = min_stem_;
        if (max_cycle_ != UINT_MAX && cur_total_ > max_cycle_)
          {
            unsigned lo = cur_total_ - max_cycle_;
            if (lo > stem_lo)
              stem_lo = lo;
          }
        // cur_total_ >= min_cycle_ is guaranteed by initialization.
        unsigned diff = cur_total_ - min_cycle_;
        unsigned stem_hi = (diff < max_stem_) ? diff : max_stem_;

        if (stem_lo > stem_hi)
          continue; // No valid pair for this total; try next.

        cur_stem_ = stem_lo;
        cur_cycle_ = cur_total_ - cur_stem_;
        stem_ready_ = false;
        stem_.clear();
        cycle_.clear();
        cycle_ready_ = false;
        cycle_exhausted_ = false;
        return true;
      }
  }

  // Build a twa_run from the current stem_ and cycle_.
  twa_run_ptr
  lasso_enumerator::build_run_() const
  {
    auto run = std::make_shared<twa_run>(aut_);
    unsigned state = init_state_;
    for (unsigned e : stem_)
      {
        run->prefix.emplace_back(aut_->state_from_number(state),
                                 edge_cond_(e), edge_acc_(e));
        state = edge_dst_(e);
      }
    state = stem_end_;
    for (unsigned e : cycle_)
      {
        run->cycle.emplace_back(aut_->state_from_number(state),
                                edge_cond_(e), edge_acc_(e));
        state = edge_dst_(e);
      }
    return run;
  }

  twa_run_ptr
  lasso_enumerator::next_run()
  {
    if (done_)
      return nullptr;

    // If we are already positioned at a valid cycle, advance past it.
    if (stem_ready_ && advance_cycle_())
      return build_run_();

    // Find the next (stem, cycle) pair with a valid accepted run.
    while (true)
      {
        if (!advance_stem_())
          {
            // No more stems for this pair; advance to the next pair.
            if (!advance_pair_())
              {
                done_ = true;
                return nullptr;
              }
            continue;
          }
        // New stem: find its first valid cycle.
        if (advance_cycle_())
          return build_run_();
        // No valid cycle for this stem; continue to the next stem.
      }
  }

  twa_word_ptr
  lasso_enumerator::next_word()
  {
    auto run = next_run();
    if (!run)
      return nullptr;
    return std::make_shared<twa_word>(run);
  }
}
