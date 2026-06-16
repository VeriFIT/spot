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
#include <spot/tl/sat.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/simplify.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twa/bdddict.hh>
#include <spot/priv/robin_hood.hh>
#include <stack>
#include <vector>
#include <algorithm>

namespace spot
{
  namespace
  {
    // An SCC entry for the on-the-fly emptiness check.
    // For the Couvreur FM translation, the acceptance condition is
    // internally Inf(!0)&Inf(!1)&...&Inf(!N).  An SCC is accepting
    // iff there is no color that appears on all edges of the SCC.
    // We track this using the intersection of all marks seen in the SCC.
    struct otf_scc
    {
      int index;
      acc_cond::mark_t acc; // intersection of marks within the SCC
    };

    // On-the-fly satisfiability check using ltl_to_tgba_fm_otf.
    // This implements a variant of Couvreur's emptiness check
    // specialized for the negated-Inf acceptance semantics used
    // internally by the Couvreur FM construction.
    //
    // The acceptance condition is Inf(!0)&Inf(!1)&...&Inf(!N-1)
    // (ever-growing N).  An SCC is accepting if the intersection
    // of all its edge marks is empty, i.e., no color appears on
    // every edge of the SCC.
    static bool
    otf_satisfiable(formula f)
    {
      auto dict = make_bdd_dict();
      auto aut = make_twa_graph(dict);

      // The formula has already been put in NNF by ltl_satisfiable(),
      // but the explorer will simplify it again; this is harmless.
      tl_simplifier simp(dict);

      ltl_to_tgba_fm_otf::options opts;
      ltl_to_tgba_fm_otf expl(f, aut, opts, &simp);

      // h: formula → DFS order.  0 = not yet assigned, -1 = dead
      robin_hood::unordered_node_map<formula, int> h;
      // Stack of SCCs being explored
      std::stack<otf_scc> root;
      // Stack of marks on edges that connect SCCs
      std::stack<acc_cond::mark_t> arc;
      // DFS stack: (state, next_edge_index)
      std::stack<std::pair<formula, unsigned>> todo;
      // Live states, ordered by DFS discovery (needed for dead marking)
      std::vector<formula> live;
      // Cache edge lists, since succ_as_acc_and_dest() is expensive
      robin_hood::unordered_node_map<formula,
                                     std::vector<fm_simple_edge>> edge_cache;

      int num = 1; // DFS order counter

      // Retrieve the edge list for a formula-state (cached).
      auto get_edges =
        [&](formula s) -> const std::vector<fm_simple_edge>&
        {
          auto it = edge_cache.find(s);
          if (it != edge_cache.end())
            return it->second;
          return edge_cache.emplace(s,
                    expl.succ_as_acc_and_dest(s)).first->second;
        };

      // Push the initial state.
      formula init = expl.init_state();
      h[init] = 1;
      root.push({1, acc_cond::mark_t::all()});
      arc.push({});
      todo.emplace(init, 0U);
      live.push_back(init);

      while (!todo.empty())
        {
          auto& top_pair = todo.top();
          formula curr = top_pair.first;
          unsigned& edge_idx = top_pair.second;
          const auto& edges = get_edges(curr);

          if (edge_idx >= edges.size())
            {
              // No more successors — backtrack.
              todo.pop();
              edge_cache.erase(curr);
              assert(!root.empty());
              if (root.top().index == h[curr])
                {
                  // curr is the root of an SCC.
                  if (!root.top().acc)
                    return true; // accepting SCC → formula is satisfiable

                  // Mark all states belonging to this SCC as dead.
                  auto rpos = std::find(live.rbegin(), live.rend(), curr);
                  assert(rpos != live.rend());
                  ++rpos;
                  for (auto it = rpos.base(); it != live.end(); ++it)
                    h[*it] = -1;
                  live.erase(rpos.base(), live.end());

                  arc.pop();
                  root.pop();
                }
              continue;
            }

          const auto& edge = edges[edge_idx];
          ++edge_idx; // advance the iterator for the next iteration

          formula dest = edge.dst;
          acc_cond::mark_t edge_acc = edge.acc;

          auto p = h.find(dest);
          if (p == h.end())
            {
              // New state discovered.
              ++num;
              h[dest] = num;
              root.push({num, acc_cond::mark_t::all()});
              arc.push(edge_acc);
              todo.emplace(dest, 0U);
              live.push_back(dest);
              continue;
            }

          int dest_order = p->second;

          // Skip dead states.
          if (dest_order == -1)
            continue;

          // Back-edge or cross-edge to a live (non-dead) state.
          // Merge all SCCs that are strictly above the threshold.
          int threshold = dest_order;
          while (threshold < root.top().index)
            {
              edge_acc &= root.top().acc;
              edge_acc &= arc.top();
              arc.pop();
              root.pop();
            }
          root.top().acc &= edge_acc;
          if (!root.top().acc)
            return true; // accepting SCC → formula is satisfiable
        }

      // All states explored, no accepting SCC found.
      return false;
    }
    // Split a conjunction into independent subformulas with disjoint
    // atomic proposition sets.  Children are grouped into connected
    // components based on shared APs; each component becomes one
    // formula in the returned vector.  If no splitting is possible
    // (all children share APs, or the formula is not a conjunction),
    // a vector containing just f is returned.
    static std::vector<formula>
    split_independent_conjunctions(formula f)
    {
      if (!f.is(op::And))
        return {f};

      unsigned n = f.size();
      if (n <= 1)
        return {f};

      // Collect APs for each child.
      std::vector<atomic_prop_set> child_aps(n);
      for (unsigned i = 0; i < n; ++i)
        atomic_prop_collect(f[i], &child_aps[i]);

      // Group children by connected components in the overlap graph
      // (two children are connected if they share an AP).
      std::vector<int> component(n, -1);
      int num_components = 0;
      for (unsigned i = 0; i < n; ++i)
        {
          if (component[i] != -1)
            continue;
          component[i] = num_components;
          // DFS from node i.
          std::vector<unsigned> queue = {i};
          while (!queue.empty())
            {
              unsigned u = queue.back();
              queue.pop_back();
              for (unsigned v = 0; v < n; ++v)
                {
                  if (component[v] != -1)
                    continue;
                  // Check if child_aps[u] and child_aps[v] intersect.
                  const auto& a = child_aps[u];
                  const auto& b = child_aps[v];
                  auto it_a = a.begin();
                  auto it_b = b.begin();
                  while (it_a != a.end() && it_b != b.end())
                    {
                      if (*it_a < *it_b)
                        ++it_a;
                      else if (*it_b < *it_a)
                        ++it_b;
                      else
                        {
                          component[v] = num_components;
                          queue.push_back(v);
                          break;
                        }
                    }
                }
            }
          ++num_components;
        }

      // If only one component, no splitting is possible.
      if (num_components <= 1)
        return {f};

      // Build a conjunction for each component, and count APs.
      std::vector<std::pair<formula, unsigned>> comps;
      comps.reserve(num_components);
      for (int c = 0; c < num_components; ++c)
        {
          std::vector<formula> group;
          atomic_prop_set aps;
          for (unsigned i = 0; i < n; ++i)
            if (component[i] == c)
              {
                group.push_back(f[i]);
                aps.insert(child_aps[i].begin(), child_aps[i].end());
              }
          comps.emplace_back(formula::And(std::move(group)),
                             static_cast<unsigned>(aps.size()));
        }
      // Order by increasing number of APs to check the easiest
      // (smallest) subformulas first.
      std::sort(comps.begin(), comps.end(),
                [](const auto& a, const auto& b)
                { return a.second < b.second; });
      std::vector<formula> result;
      result.reserve(num_components);
      for (auto& [subf, _]: comps)
        result.push_back(std::move(subf));
      return result;
    }

  } // anonymous namespace

  bool ltl_satisfiable(formula f)
  {
    // Remove atomic propositions that always have
    // the same polarity in the formula.   For instance
    // if P always appears positively, then f is satisfiable
    // iff f[P<-true] is satisfiable.
    {
      std::vector<std::string> no_inputs;
      realizability_simplifier rs(f, no_inputs);
      f = rs.simplified_formula();
    }

    if (f.is_tt())
      return true;
    if (f.is_ff())
      return false;

    // Apply syntax-based simplification (which also puts f in NNF).
    // Only basic rewriting rules are used: no syntactic-implication or
    // eventuality/universality checks, because those involve translating
    // subformulas, which would defeat the purpose of the on-the-fly
    // emptiness check.
    {
      tl_simplifier_options simp_opts(true, false, false);
      auto dict = make_bdd_dict();
      tl_simplifier simp(simp_opts, dict);
      f = simp.simplify(f);
    }

    // If the formula is a conjunction, try to split it into independent
    // subformulas whose children have disjoint sets of atomic propositions.
    // Each subformula can be checked independently.
    if (f.is(op::And))
      {
        auto subs = split_independent_conjunctions(f);
        if (subs.size() > 1)
          {
            for (auto sub: subs)
              if (!ltl_satisfiable(sub))
                return false;
            return true;
          }
      }

    // If the formula is a disjunction, check each disjunct recursively.
    // Since the formula is in NNF, a top-level Or is a true disjunction.
    if (f.is(op::Or))
      {
        for (auto child: f)
          if (ltl_satisfiable(child))
            return true;
        return false;
      }

    // The on-the-fly emptiness check using the Couvreur FM translation
    // only supports purely existential quantifiers (body unquantified)
    // and unquantified formulas.  For \forall or quantifier alternations
    // (\exists\forall, \forall\exists) that survived simplification,
    // use the full translator.
    if (f.is_quantified())
      {
        // \exists a: (\psi_1 \lor \psi_2 \lor \ldots)
        //   \equiv (\exists a: \psi_1) \lor (\exists a: \psi_2) \lor \ldots
        // Check each disjunct independently.
        if (f.is(op::exists) && f[f.size() - 1].is(op::Or))
          {
            unsigned sz = f.size();
            std::vector<formula> qaps;
            for (unsigned i = 0; i < sz - 1; ++i)
              qaps.push_back(f[i]);
            for (auto child: f[sz - 1])
              {
                formula sub = formula::quantify(op::exists, qaps, child);
                if (ltl_satisfiable(sub))
                  return true;
              }
            return false;
          }

        bool otf_ok = f.is(op::exists)
                       && !f[f.size() - 1].is_quantified();
        if (!otf_ok)
          {
            auto dict = make_bdd_dict();
            translator trans(dict);
            trans.set_type(postprocessor::Buchi);
            trans.set_level(postprocessor::Low);
            auto aut = trans.run(f);
            return !aut->is_empty();
          }
      }

    // On-the-fly emptiness check using the Couvreur FM translation.
    return otf_satisfiable(f);
  }
}
