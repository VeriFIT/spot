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
#include <spot/twaalgos/intersect.hh>

#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/emptiness.hh>
#include "spot/priv/robin_hood.hh"

#include <algorithm>
#include <cassert>
#include <deque>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace spot
{
  namespace
  {
    using edge_iterator = twa_graph::graph_t::const_iterator;

    // A pair of acceptance marks, one for each operand of the product.
    // The two mark sets are kept separate: since the acceptance
    // condition of the product is the conjunction of the acceptance
    // conditions of both operands, a cycle is accepting iff each of
    // its mark sets satisfies the condition of the corresponding
    // operand.  No renumbering of the acceptance sets is needed.
    struct acc_pair
    {
      acc_cond::mark_t left = {};
      acc_cond::mark_t right = {};
    };

    // A strongly connected component of the product's DFS.
    struct scc
    {
      explicit scc(int i): index(i), marks()
      {
      }

      int index;
      acc_pair marks;
    };

    // Encode a pair of state numbers into a single 64-bit integer.
    static uint64_t product_key(unsigned l, unsigned r) noexcept
    {
      return (static_cast<uint64_t>(l) << 32) | r;
    }


    static unsigned left_state(uint64_t k) noexcept
    {
      return static_cast<unsigned>(k >> 32);
    }

    static unsigned right_state(uint64_t k) noexcept
    {
      return static_cast<unsigned>(k);
    }

    // Iterate over the successors of a product state, i.e., over the
    // pairs (l', r') such that l->l' and r->r' are transitions of the
    // left and right automata.
    class product_succ_iterator final
    {
    public:
      product_succ_iterator(const twa_graph& left, unsigned ls,
                            const twa_graph& right, unsigned rs)
        : right_(&right),
          rs_(rs),
          lit_(left.out(ls).begin()),
          lend_(left.out(ls).end())
      {
        auto out = right_->out(rs_);
        rit_ = out.begin();
        rend_ = out.end();
        skip_empty();
      }

      bool done() const
      {
        return lit_ == lend_;
      }

      // Whether some letter satisfies both the current left and the
      // current right transition.  Unlike label(), this does not build
      // the conjunction of the two labels: the exploration only needs to
      // know whether that conjunction is false.
      bool compatible() const
      {
        return bdd_have_common_assignment(lit_->cond, rit_->cond) != 0;
      }

      // The label of the product transition: a letter satisfying it
      // satisfies both transitions it is built from.
      bdd label() const
      {
        return lit_->cond & rit_->cond;
      }

      unsigned left_dst() const
      {
        return lit_->dst;
      }

      unsigned right_dst() const
      {
        return rit_->dst;
      }

      acc_cond::mark_t left_acc() const
      {
        return lit_->acc;
      }

      acc_cond::mark_t right_acc() const
      {
        return rit_->acc;
      }

      void next()
      {
        ++rit_;
        skip_empty();
      }

    private:
      // Move to the next left transition having at least one
      // compatible right transition.
      void skip_empty()
      {
        while (rit_ == rend_)
          {
            if (++lit_ == lend_)
              return;
            auto out = right_->out(rs_);
            rit_ = out.begin();
            rend_ = out.end();
          }
      }

      const twa_graph* right_;
      unsigned rs_;             // the right component of the product state
      edge_iterator lit_;
      edge_iterator lend_;
      edge_iterator rit_;
      edge_iterator rend_;
    };

    // A frame of the depth-first search: the product state being
    // explored and an iterator over its successors.
    struct frame
    {
      frame(uint64_t k, const product_succ_iterator& i) noexcept
        : key(k), succ(i)
      {
      }

      uint64_t key;
      product_succ_iterator succ;
    };

    // A transition of the product, stored as the state it leaves.
    // Only the acceptance marks of the left operand are needed: those
    // are the marks of the run we eventually build.
    struct path_edge
    {
      uint64_t src;
      bdd label;
      acc_cond::mark_t acc;
    };

    // Emptiness check on the synchronous product of two explicit
    // automata, using Couvreur's algorithm.  The product is never
    // built: its states are pairs of state numbers, and the DFS
    // stacks store such pairs.
    class product_emptiness_check final
    {
    public:
      product_emptiness_check(const const_twa_graph_ptr& left,
                              const const_twa_graph_ptr& right)
        : left_(left), right_(right)
      {
        if (left->acc().uses_fin_acceptance()
            || right->acc().uses_fin_acceptance())
          throw std::runtime_error
            ("intersects() requires Fin-less acceptance");
        if (!left->is_existential() || !right->is_existential())
          throw std::runtime_error
            ("intersects() does not support alternation");
      }

      // Whether the product accepts at least one word.
      bool has_word()
      {
        return check<false>(nullptr);
      }

      // An accepting run of the product, projected onto the left
      // operand, or nullptr if the product is empty.
      twa_run_ptr accepting_run()
      {
        twa_run_ptr run;
        if (check<true>(&run))
          return run;
        return nullptr;
      }

    private:
      template<bool need_run>
      bool check(twa_run_ptr* out)
      {
        // An automaton rejecting all words makes the product empty.
        if (left_->acc().get_acceptance().is_f()
            || right_->acc().get_acceptance().is_f())
          return false;
        // The product of two weak automata is weak, in which case the
        // acceptance marks do not have to be stored on the SCC stack.
        if (left_->prop_weak() && right_->prop_weak())
          return check_impl<need_run, false>(out);
        return check_impl<need_run, true>(out);
      }

      template<bool need_run, bool is_strong>
      bool check_impl(twa_run_ptr* out);

      twa_run_ptr build_run();

      uint64_t bfs_to_cycle(std::vector<path_edge>& cycle, uint64_t start,
                            int scc_root, acc_cond::mark_t& lreq,
                            acc_cond::mark_t& rreq);

      static void append_path(std::vector<path_edge>& cycle,
                              const std::unordered_map<uint64_t, path_edge>&
                              parent,
                              uint64_t src, bdd label,
                              acc_cond::mark_t acc);

      const_twa_graph_ptr left_;
      const_twa_graph_ptr right_;

      // The "hash" of Couvreur's algorithm: the order in which each
      // product state was visited, or -1 for states belonging to a
      // component that has been fully explored and discarded.  This
      // holds one entry per visited product state, so a flat
      // (open-addressing) table is used to avoid allocating a node for
      // each of them.
      robin_hood::unordered_flat_map<uint64_t, int> h_;
      // The stack of SCCs.
      std::vector<scc> root_;
      // The state where the accepting cycle starts.
      uint64_t cycle_seed_ = 0;
    };

    template<bool need_run, bool is_strong>
    bool product_emptiness_check::check_impl(twa_run_ptr* out)
    {
      // A stack of pairs of acceptance marks, one pair per SCC of
      // root_, recording the marks of the transitions leading back to
      // that SCC from the component above it.
      std::vector<acc_pair> arc;
      // The depth-first-search stack.
      std::vector<frame> todo;
      // The states on the current DFS path, in the order they were
      // discovered.
      std::vector<uint64_t> live;

      // The number of visited states, used to order them.
      int num = 1;

      // Growing the visited set rehashes all of its entries, so size it
      // after the product when that is reasonable.  The same bound
      // applies to the stacks, which cannot hold more than one entry
      // per product state.
      const uint64_t nprod = static_cast<uint64_t>(left_->num_states())
        * right_->num_states();
      const auto depth =
        static_cast<size_t>(std::min<uint64_t>(nprod, 1 << 16));
      h_.reserve(depth);
      todo.reserve(depth);
      live.reserve(depth);
      root_.reserve(depth);
      if (is_strong)
        arc.reserve(depth);

      uint64_t init = product_key(left_->get_init_state_number(),
                                  right_->get_init_state_number());
      h_.emplace(init, 1);
      root_.push_back(scc(1));
      if (is_strong)
        arc.push_back(acc_pair());
      todo.emplace_back(init, product_succ_iterator(*left_, left_state(init),
                                                    *right_,
                                                    right_state(init)));
      live.push_back(init);

      while (!todo.empty())
        {
          if (is_strong)
            assert(root_.size() == arc.size());

          auto& succ = todo.back().succ;

          // If there are no more successors, backtrack.
          if (succ.done())
            {
              uint64_t curr = todo.back().key;
              int hcurr = h_[curr];
              todo.pop_back();

              // When backtracking the root of an SCC, remove that SCC
              // from the ARC/ROOT stacks, and discard from H all the
              // states reachable from it.
              assert(!root_.empty());
              if (root_.back().index == hcurr)
                {
                  if (is_strong)
                    {
                      assert(!arc.empty());
                      arc.pop_back();
                    }
                  auto i = std::find(live.rbegin(), live.rend(), curr);
                  assert(i != live.rend());
                  ++i; // Because base() does -1
                  for (auto it = i.base(); it != live.end(); ++it)
                    h_[*it] = -1;
                  live.erase(i.base(), live.end());
                  root_.pop_back();
                }
              continue;
            }

          // Ignore pairs of transitions whose labels are disjoint.
          if (SPOT_UNLIKELY(!succ.compatible()))
            {
              succ.next();
              continue;
            }

          // Fetch the values we are interested in, then point the
          // iterator to the next successor.
          acc_pair acc = {succ.left_acc(), succ.right_acc()};
          unsigned ld = succ.left_dst();
          unsigned rd = succ.right_dst();
          succ.next();

          uint64_t dest = product_key(ld, rd);
          // Are we going to a new state?
          auto p = h_.emplace(dest, num + 1);
          if (p.second)
            {
              root_.push_back(scc(++num));
              if (is_strong)
                arc.push_back(acc);
              todo.emplace_back(dest, product_succ_iterator(*left_, ld,
                                                            *right_, rd));
              live.push_back(dest);
              continue;
            }

          // If we have reached a dead component, ignore it.
          if (p.first->second == -1)
            continue;

          // We have reached a state of a non-dead SCC: merge all the
          // SCCs stacked above it.
          int threshold = p.first->second;
          while (threshold < root_.back().index)
            {
              if (is_strong)
                {
                  assert(!arc.empty());
                  const scc& top = root_.back();
                  const acc_pair& top_arc = arc.back();
                  acc.left |= top.marks.left | top_arc.left;
                  acc.right |= top.marks.right | top_arc.right;
                  arc.pop_back();
                }
              root_.pop_back();
              assert(!root_.empty());
            }

          // Accumulate all acceptance conditions into the merged SCC.
          // The merged marks are kept in local variables, so that the
          // calls to accepting() below cannot make the compiler reload
          // them from root_.
          scc& top = root_.back();
          const acc_cond::mark_t lmarks = top.marks.left | acc.left;
          const acc_cond::mark_t rmarks = top.marks.right | acc.right;
          top.marks.left = lmarks;
          top.marks.right = rmarks;

          if (left_->acc().accepting(lmarks)
              && right_->acc().accepting(rmarks))
            {
              // We have found an accepting SCC.
              cycle_seed_ = dest;
              if (need_run)
                *out = build_run();
              return true;
            }
        }

      // The product recognizes no word.
      return false;
    }

    // Append to CYCLE the path from the root of the BFS (the first
    // state without a proper predecessor in PARENT) to SRC, followed
    // by the transition from SRC labeled by LABEL and marked by ACC.
    void product_emptiness_check::append_path
      (std::vector<path_edge>& cycle,
       const std::unordered_map<uint64_t, path_edge>& parent,
       uint64_t src, bdd label, acc_cond::mark_t acc)
    {
      std::vector<path_edge> rev;
      for (uint64_t s = src;;)
        {
          auto p = parent.find(s);
          // The root of the BFS points to itself, and every other state
          // of the tree has a predecessor, so S always has an entry.
          SPOT_ASSUME(p != parent.end());
          if (p->second.src == s)
            break;
          rev.push_back(p->second);
          s = p->second.src;
        }
      for (auto i = rev.rbegin(); i != rev.rend(); ++i)
        cycle.push_back(*i);
      cycle.push_back(path_edge{src, label, acc});
    }

    // Run a BFS from START, restricted to the states of the accepting
    // SCC, and append to CYCLE the path ending on the first transition
    // that removes one of the required acceptance marks (or that
    // reaches cycle_seed_ when no mark is required anymore).  Return
    // the state reached by that transition.
    uint64_t product_emptiness_check::bfs_to_cycle
      (std::vector<path_edge>& cycle, uint64_t start, int scc_root,
       acc_cond::mark_t& lreq, acc_cond::mark_t& rreq)
    {
      std::unordered_map<uint64_t, path_edge> parent;
      parent.emplace(start, path_edge{start, bddtrue, {}});
      std::deque<uint64_t> queue;
      queue.push_back(start);

      while (!queue.empty())
        {
          uint64_t src = queue.front();
          queue.pop_front();
          product_succ_iterator it(*left_, left_state(src),
                                   *right_, right_state(src));
          for (; !it.done(); it.next())
            {
              if (SPOT_UNLIKELY(!it.compatible()))
                continue;
              uint64_t dst = product_key(it.left_dst(), it.right_dst());
              auto hi = h_.find(dst);
              // Ignore unknown states, dead states, and states that
              // do not belong to the accepting SCC.
              if (hi == h_.end() || hi->second == -1
                  || hi->second < scc_root)
                continue;
              acc_cond::mark_t nl = lreq - it.left_acc();
              acc_cond::mark_t nr = rreq - it.right_acc();
              if (nl != lreq || nr != rreq
                  || (!lreq && !rreq && dst == cycle_seed_))
                {
                  append_path(cycle, parent, src, it.label(), it.left_acc());
                  lreq = nl;
                  rreq = nr;
                  return dst;
                }
              if (parent.emplace(dst, path_edge{src, it.label(), it.left_acc()})
                  .second)
                queue.push_back(dst);
            }
        }

      // The states of the accepting SCC are strongly connected, so
      // the BFS above has to succeed.
      throw std::runtime_error
        ("intersecting_run(): failed to build an accepting cycle");
    }

    twa_run_ptr product_emptiness_check::build_run()
    {
      const scc& top = root_.back();
      const int scc_root = top.index;
      const acc_cond::mark_t lmarks = top.marks.left;
      const acc_cond::mark_t rmarks = top.marks.right;
      acc_cond::mark_t lreq = left_->acc().accepting_sets(lmarks);
      acc_cond::mark_t rreq = right_->acc().accepting_sets(rmarks);

      // Build an accepting cycle by successive BFS, each one being
      // restarted from the state reached by the transition that
      // contributed a new acceptance mark.  This is the same idea as
      // in couvreur99_new()'s accepting_cycle().
      std::vector<path_edge> cycle;
      uint64_t substart = cycle_seed_;
      do
        {
          substart = bfs_to_cycle(cycle, substart, scc_root, lreq, rreq);
        }
      while (lreq || rreq || substart != cycle_seed_);

      // Compute the prefix: it is the shortest path from the initial
      // state of the product to any state of the cycle.
      uint64_t init = product_key(left_->get_init_state_number(),
                                  right_->get_init_state_number());

      std::unordered_set<uint64_t> cycle_states;
      for (auto& e: cycle)
        cycle_states.insert(e.src);

      std::vector<path_edge> prefix;
      uint64_t cycle_entry;
      auto init_on_cycle = cycle_states.find(init);
      if (init_on_cycle != cycle_states.end())
        {
          // The initial state is already on the cycle.
          cycle_entry = *init_on_cycle;
        }
      else
        {
          std::unordered_map<uint64_t, path_edge> parent;
          parent.emplace(init, path_edge{init, bddtrue, {}});
          std::deque<uint64_t> queue;
          queue.push_back(init);
          bool found = false;
          while (!queue.empty() && !found)
            {
              uint64_t src = queue.front();
              queue.pop_front();
              product_succ_iterator it(*left_, left_state(src),
                                       *right_, right_state(src));
              for (; !it.done(); it.next())
                {
                  if (SPOT_UNLIKELY(!it.compatible()))
                    continue;
                  uint64_t dst = product_key(it.left_dst(), it.right_dst());
                  if (cycle_states.find(dst) != cycle_states.end())
                    {
                      append_path(prefix, parent, src, it.label(),
                                  it.left_acc());
                      cycle_entry = dst;
                      found = true;
                      break;
                    }
                  auto hi = h_.find(dst);
                  // Ignore unknown states and dead states.
                  if (hi == h_.end() || hi->second == -1)
                    continue;
                  path_edge pe{src, it.label(), it.left_acc()};
                  if (parent.emplace(dst, pe).second)
                    queue.push_back(dst);
                }
            }
          if (!found)
            throw std::runtime_error
              ("intersecting_run(): failed to reach the accepting cycle");
        }

      // Rotate the cycle so that it starts on the state reached by
      // the prefix.
      auto i = std::find_if(cycle.begin(), cycle.end(),
                            [cycle_entry](const path_edge& e)
                            {
                              return e.src == cycle_entry;
                            });
      assert(i != cycle.end());
      std::rotate(cycle.begin(), i, cycle.end());

      auto run = std::make_shared<twa_run>(left_);
      for (auto& e: prefix)
        run->prefix.emplace_back(left_->state_from_number(left_state(e.src)),
                                 e.label, e.acc);
      for (auto& e: cycle)
        run->cycle.emplace_back(left_->state_from_number(left_state(e.src)),
                                e.label, e.acc);
      return run;
    }
  } // anonymous namespace

  bool intersects(const const_twa_graph_ptr& left,
                  const const_twa_graph_ptr& right)
  {
    if (SPOT_UNLIKELY(left->get_dict() != right->get_dict()))
      throw std::runtime_error("intersects(): left and right automata "
                               "should share their bdd_dict");
    if (left->num_states() == 0 || right->num_states() == 0)
      return false;
    product_emptiness_check ec(left, right);
    return ec.has_word();
  }

  twa_run_ptr intersecting_run(const const_twa_graph_ptr& left,
                               const const_twa_graph_ptr& right)
  {
    if (SPOT_UNLIKELY(left->get_dict() != right->get_dict()))
      throw std::runtime_error("intersecting_run(): left and right "
                               "automata should share their bdd_dict");
    if (left->num_states() == 0 || right->num_states() == 0)
      return nullptr;
    product_emptiness_check ec(left, right);
    return ec.accepting_run();
  }
} // namespace spot
