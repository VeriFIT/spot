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

#include <spot/misc/bddlt.hh>
#include <spot/misc/hash.hh>
#include <spot/misc/timer.hh>
#include <spot/twa/formula2bdd.hh>
#include <spot/twaalgos/degen.hh>
#include <spot/twaalgos/determinize.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/mealy_machine.hh>
#include <spot/twaalgos/sbacc.hh>
#include <spot/twaalgos/synthesis.hh>
#include <spot/tl/apcollect.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twa/twa.hh>
#include <spot/twa/twagraph.hh>
#include <spot/twaalgos/aiger.hh>
#include <spot/twaalgos/game.hh>
#include <spot/twaalgos/mtdswa.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/zlktree.hh>
#include <spot/twaalgos/toparity.hh>
#include <spot/twaalgos/remprop.hh>
#include <spot/twaalgos/dualize.hh>
#include <spot/tl/parse.hh>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <map>
#include <regex>
#include <set>
#include <stdexcept>
#include <string>
#include <stack>
#include <variant>
#include <set>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <vector>

#ifndef NDEBUG
#include <spot/twaalgos/hoa.hh>
#endif
// Helper function/structures for split_2step
namespace{
  using namespace spot;
  // Computes and stores the restriction
  // of each cond to the input domain and the support
  // This is useful as it avoids recomputation
  // and often many conditions are mapped to the same
  // restriction
  struct small_cacher_t
  {
    //e to e_in and support (or e_out and support for Moore)
    std::unordered_map<bdd, std::pair<bdd, bdd>, bdd_hash> cond_hash_;
    // The BDD we exist-quantify: output_bdd for Mealy (restrict to input),
    // input_bdd for Moore (restrict to output).
    bdd restrict_bdd_;

    void fill(const const_twa_graph_ptr& aut, bdd output_bdd,
              bool moore = false)
    {
      cond_hash_.reserve(aut->num_edges()/5+1);
      // 20% is about lowest number of different edge conditions
      // for benchmarks taken from syntcomp

      restrict_bdd_ = (moore
                       ? bdd_exist(aut->ap_vars(), output_bdd)
                       : output_bdd);

      for (const auto& e : aut->edges())
        {
          // Check if stored
          if (cond_hash_.contains(e.cond))
            continue;

          cond_hash_[e.cond] =
              std::pair<bdd, bdd>(
                  bdd_exist(e.cond, restrict_bdd_),
                  bdd_exist(bdd_support(e.cond), restrict_bdd_));
        }
    }

    // Get the condition restricted to input (Mealy) or output (Moore)
    // and its support
    const std::pair<bdd, bdd>& operator[](const bdd& econd) const
    {
      return cond_hash_.at(econd);
    }
  };

  // Struct to locally store the information of all outgoing edges
  // of the state.
  struct e_info_t
  {
    e_info_t(const twa_graph::edge_storage_t& e,
             const small_cacher_t& sm)
        : dst(e.dst),
          econd(e.cond),
          einsup(sm[e.cond]),
          acc(e.acc)
    {
      pre_hash = (wang32_hash(dst)
                 ^ std::hash<acc_cond::mark_t>()(acc))
                 * fnv<size_t>::prime;
    }

    inline size_t hash() const
    {
      return wang32_hash(bdd_hash()(econdout)) ^ pre_hash;
    }

    unsigned dst;
    bdd econd;
    mutable bdd econdout;
    std::pair<bdd, bdd> einsup;
    acc_cond::mark_t acc;
    size_t pre_hash;
  };
  // We define an order between the edges to avoid creating multiple
  // states that in fact correspond to permutations of the order of the
  // outgoing edges
  struct less_info_t
  {
    // Note: orders via !econd!
    inline bool operator()(const e_info_t &lhs, const e_info_t &rhs) const
    {
      const int l_id = lhs.econd.id();
      const int r_id = rhs.econd.id();
      return std::tie(lhs.dst, lhs.acc, l_id)
             < std::tie(rhs.dst, rhs.acc, r_id);
    }
  }less_info;

  struct less_info_ptr_t
  {
    // Note: orders via !econdout!
    inline bool operator()(const e_info_t* lhs, const e_info_t* rhs)const
    {
      const int l_id = lhs->econdout.id();
      const int r_id = rhs->econdout.id();
      return std::tie(lhs->dst, lhs->acc, l_id)
             < std::tie(rhs->dst, rhs->acc, r_id);
    }
  }less_info_ptr;

  // Improved apply strat, that reduces the number of edges/states
  // while keeping the needed edge-properties
  // Note, this deals with deterministic strategies
  // Note, assumes that env starts playing if moore=false,
  // and ctrl starts playing if moore=true
  twa_graph_ptr
  apply_strategy(const const_twa_graph_ptr& arena,
                 bool unsplit, bool keep_acc, bool moore)
  {
    const region_t& win = get_state_winners(arena);
    const strategy_t& strat = get_strategy(arena);
    const region_t& sp = get_state_players(arena);
    auto outs = get_synthesis_outputs(arena);

    if (!win[arena->get_init_state_number()])
      throw std::runtime_error("Player does not win initial state, strategy "
                               "is not applicable");

    assert((sp[arena->get_init_state_number()] == moore)
           && "incorrect first player");
    (void)sp;

    assert(std::none_of(arena->edges().begin(), arena->edges().end(),
           [&sp](const auto& e)
             { bool same_player = sp.at(e.src) == sp.at(e.dst);
               if (same_player)
                 std::cerr << e.src << " and " << e.dst << " belong to same "
                           << "player, arena not alternating!\n";
               return same_player; }));

    auto strat_split = make_twa_graph(arena->get_dict());
    strat_split->copy_ap_of(arena);
    if (keep_acc)
      {
        strat_split->copy_acceptance_of(arena);
      }
    else
      {
        strat_split->acc().set_acceptance(acc_cond::acc_code::t());
        strat_split->prop_weak(true);
      }

    std::stack<unsigned> todo;
    todo.push(arena->get_init_state_number());

    struct dca{
      unsigned dst;
      unsigned condvar;
      acc_cond::mark_t acc;
    };
    struct dca_hash
    {
      size_t operator()(const dca& d) const noexcept
      {
        return pair_hash()(std::make_pair(d.dst, d.condvar))
               ^ wang32_hash(d.acc.hash());
      }
    };
    struct dca_equal
    {
      bool operator()(const dca& d1, const dca& d2) const noexcept
      {
        return std::tie(d1.dst, d1.condvar, d1.acc)
              == std::tie(d2.dst, d2.condvar, d2.acc);
      }
    };

    //env dst + player cond + acc -> p stat
    std::unordered_map<dca,
                       unsigned,
                       dca_hash,
                       dca_equal> p_map;
    // Track intermediate env states for Moore
    std::vector<unsigned> moore_env_states;

    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    // For Mealy (env-first): env_map maps env states to local states
    // For Moore  (ctrl-first): maps ctrl (original) states to local states
    std::vector<unsigned> env_map(arena->num_states(), unseen_mark);
    strat_split->set_init_state(strat_split->new_state());
    env_map[arena->get_init_state_number()] =
        strat_split->get_init_state_number();

    // The states in the new graph are qualified local
    // Get a local state (env for Mealy, ctrl for Moore)
    auto get_sel = [&](unsigned s)
      {
        if (SPOT_UNLIKELY(env_map[s] == unseen_mark))
          env_map[s] = strat_split->new_state();
        return env_map[s];
      };

    // local dst
    // Check if there exists already a local player state
    // that has the same dst, cond and (if keep_acc is true) acc
    auto get_spl = [&](unsigned dst, const bdd& cond, acc_cond::mark_t acc)
      {
        dca d{dst, (unsigned) cond.id(), acc};
        auto it = p_map.find(d);
        if (it != p_map.end())
          return it->second;
        unsigned ns = strat_split->new_state();
        p_map[d] = ns;
        strat_split->new_edge(ns, dst, cond, acc);
        return ns;
      };

    if (moore)
      {
        // Moore semantics: ctrl (first player) owns initial state.
        // Loop: ctrl (original) -> env (intermediate) -> ctrl (next).
        // For each ctrl state, create ONE output edge to a single
        // intermediate env state, which has edges for each possible
        // environment input.
        while (!todo.empty())
          {
            unsigned src_ctrl = todo.top();
            unsigned src_ctrll = get_sel(src_ctrl);
            todo.pop();
            // Get the ctrl strategy for this state
            const auto& e_strat = arena->edge_storage(strat[src_ctrl]);
            auto used_acc = keep_acc ? e_strat.acc : acc_cond::mark_t({});
            // Create a single intermediate env state
            unsigned env_state = strat_split->new_state();
            moore_env_states.push_back(env_state);
            // e_strat.dst is an env state, iterate its outgoing edges
            for (const auto& e_env : arena->out(e_strat.dst))
              {
                // Check if already explored
                if (env_map[e_env.dst] == unseen_mark)
                  todo.push(e_env.dst);
                unsigned dst_ctrll = get_sel(e_env.dst);
                strat_split->new_edge(env_state, dst_ctrll,
                                      e_env.cond, used_acc);
              }
            // One ctrl edge to the single env state
            strat_split->new_edge(src_ctrll, env_state,
                                  e_strat.cond, used_acc);
          }
      }
    else
      {
        // Mealy semantics: env plays first.
        // Loop: env (original) -> ctrl (intermediate) -> env (next)
        while (!todo.empty())
          {
            unsigned src_env = todo.top();
            unsigned src_envl = get_sel(src_env);
            todo.pop();
            // All env edges
            for (const auto& e_env : arena->out(src_env))
              {
                // Get the corresponding strat
                const auto& e_strat = arena->edge_storage(strat[e_env.dst]);
                // Check if already explored
                if (env_map[e_strat.dst] == unseen_mark)
                  todo.push(e_strat.dst);
                unsigned dst_envl = get_sel(e_strat.dst);
                // The new env edge, player is constructed automatically
                auto used_acc = keep_acc ? e_strat.acc : acc_cond::mark_t({});
                strat_split->new_edge(src_envl,
                                      get_spl(dst_envl, e_strat.cond, used_acc),
                                      e_env.cond, used_acc);
              }
          }
      }
    // All states exists, we can try to further merge them
    // Specialized merge
    std::vector<bool> spnew(strat_split->num_states(), moore);
    for (const auto& p : p_map)
      spnew[p.second] = !moore;
    // For Moore, the intermediate env states are not in p_map.
    if (moore)
      for (unsigned s : moore_env_states)
        spnew[s] = false;

    // Sorting edges in place
    auto comp_edge = [](const auto& e1, const auto& e2)
      {
        return std::tuple(e1.dst, e1.acc, e1.cond.id())
              < std::tuple(e2.dst, e2.acc, e2.cond.id());
      };
    // todo, replace with sort_edges_of_ in graph
    auto sort_edges_of =
        [&, &split_graph = strat_split->get_graph()](unsigned s)
      {
        static std::vector<unsigned> edge_nums;
        edge_nums.clear();

        auto eit = strat_split->out(s);
        const auto eit_e = eit.end();
        // 0 Check if it is already sorted
        if (std::is_sorted(eit.begin(), eit_e, comp_edge))
          return false; // No change
        // 1 Get all edges numbers and sort them
        std::transform(eit.begin(), eit_e, std::back_inserter(edge_nums),
                       [&](const auto& e)
                         { return strat_split->edge_number(e); });
        std::sort(edge_nums.begin(), edge_nums.end(),
                  [&](unsigned ne1, unsigned ne2)
                  { return comp_edge(strat_split->edge_storage(ne1),
                                    strat_split->edge_storage(ne2)); });
        // 2 Correct the order
        auto& sd = split_graph.state_storage(s);
        sd.succ = edge_nums.front();
        sd.succ_tail = edge_nums.back();
        const unsigned n_edges_p = edge_nums.size()-1;
        for (unsigned i = 0; i < n_edges_p; ++i)
          split_graph.edge_storage(edge_nums[i]).next_succ = edge_nums[i+1];
        split_graph.edge_storage(edge_nums.back()).next_succ = 0; //terminal
        // All nicely chained
        return true;
      };
    auto merge_edges_of = [&](unsigned s)
      {
        // Call this after sort edges of
        // Mergeable edges are nicely chained
        bool changed = false;
        auto eit = strat_split->out_iteraser(s);
        unsigned idx_last = strat_split->edge_number(*eit);
        ++eit;
        while (eit)
          {
            auto& e_last = strat_split->edge_storage(idx_last);
            if (std::tie(e_last.dst, e_last.acc)
                == std::tie(eit->dst, eit->acc))
              {
                //Same dest and acc -> or condition
                e_last.cond |= eit->cond;
                eit.erase();
                changed = true;
              }
            else
              {
                idx_last = strat_split->edge_number(*eit);
                ++eit;
              }
          }
        return changed;
      };
    auto merge_able = [&](unsigned s1, unsigned s2)
      {
        auto eit1 = strat_split->out(s1);
        auto eit2 = strat_split->out(s2);
        // Note: No self-loops here
        return std::equal(eit1.begin(), eit1.end(),
                          eit2.begin(), eit2.end(),
                          [](const auto& e1, const auto& e2)
                          {
                            return std::tuple(e1.dst, e1.acc, e1.cond.id())
                                   == std::tuple(e2.dst, e2.acc, e2.cond.id());
                          });
      };

    const unsigned n_sstrat = strat_split->num_states();
    std::vector<unsigned> remap(n_sstrat, -1u);
    bool changed_any;
    std::vector<unsigned> to_check;
    to_check.reserve(n_sstrat);
    // First iteration -> all env states are candidates
    for (unsigned i = 0; i < n_sstrat; ++i)
      if (!spnew[i])
        to_check.push_back(i);

    while (true)
    {
      changed_any = false;
      std::for_each(to_check.begin(), to_check.end(),
                    [&](unsigned s){ sort_edges_of(s); merge_edges_of(s); });
      // Check if we can merge env states
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (spnew[s2] || (s1 == s2))
              continue; // Player state or s1 == s2
            if ((remap[s2] < s2))
              continue; //s2 is already remapped
            if (merge_able(s1, s2))
              {
                changed_any = true;
                if (s1 < s2)
                  remap[s2] = s1;
                else
                  remap[s1] = s2;
                break;
              }
          }

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(spnew[e.src]);
          }

      // Now check the player states
      // We can skip sorting -> only one edge
      // todo change when multistrat
      changed_any = false;
      for (unsigned s1 : to_check)
        for (unsigned s2 = 0; s2 < n_sstrat; ++s2)
          {
            if (!spnew[s2] || (s1 == s2))
              continue; // Env state or s1 == s2
            if ((remap[s2] < s2))
              continue; //s2 is already remapped
            if (merge_able(s1, s2))
              {
                changed_any = true;
                if (s1 < s2)
                  remap[s2] = s1;
                else
                  remap[s1] = s2;
                break;
              }
          }

      if (!changed_any)
        break;
      // Redirect changed targets and set possibly mergeable states
      to_check.clear();
      for (auto& e : strat_split->edges())
        if (remap[e.dst] != -1u)
          {
            e.dst = remap[e.dst];
            to_check.push_back(e.src);
            assert(!spnew[e.src]);
          }
    }

    // Defrag and alternate
    if (remap[strat_split->get_init_state_number()] != -1u)
      strat_split->set_init_state(remap[strat_split->get_init_state_number()]);
    unsigned st = 0;
    for (auto& s: remap)
      if (s == -1U)
        s = st++;
      else
        s = -1U;

    strat_split->defrag_states(remap, st);

    alternate_players(strat_split, moore, false);
    // What we do now depends on whether we unsplit or not
    if (unsplit)
      {
        auto final = unsplit_2step(strat_split);
        set_synthesis_outputs(final, outs);
        return final;
      }

    set_synthesis_outputs(strat_split, outs);
    return strat_split;
  }
}

namespace spot
{
  namespace
  {
  twa_graph_ptr
  split_2step_expl_impl(const const_twa_graph_ptr& aut,
                        const bdd& output_bdd, bool complete_env,
                        bool moore = false)
  {
    assert(!aut->get_named_prop<region_t>("state-player")
           && "aut is already split!");
    auto split = make_twa_graph(aut->get_dict());

    auto [has_unsat, unsat_mark] = aut->acc().unsat_mark();
    bool max_par, odd_par, color_env;
    color_env = aut->acc().is_parity(max_par, odd_par, true);

    split->copy_ap_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    set_synthesis_outputs(split, output_bdd);

    const auto use_color = has_unsat;
    color_env &= use_color;
    if (has_unsat)
      split->copy_acceptance_of(aut);
    else
      {
        if (complete_env)
          {
            split->set_co_buchi(); // Fin(0)
            unsat_mark = acc_cond::mark_t({0});
            has_unsat = true;
          }
        else
          split->acc().set_acceptance(acc_cond::acc_code::t());
      }

    // The "letter BDD" is the BDD over which we enumerate minterms.
    // For Moore: we enumerate output letters instead of input letters.
    bdd letter_bdd = moore ? output_bdd : bdd_exist(aut->ap_vars(), output_bdd);

    // Original states (indices 0..aut->num_states()-1) are the first player's.
    // Intermediate states (created below) are the second player's.
    // We first loop over the original states and then deduce ownership.

    // a sort of hash-map for all new intermediate states
    // second is the color of the incoming transition
    std::unordered_multimap<size_t,
                            std::pair<unsigned, acc_cond::mark_t>> interm_hash;
    interm_hash.reserve((int) (1.5 * aut->num_states()));
    // a local map for edges leaving the current src
    // this avoids creating and then combining edges for each minterm
    // Note there are usually "few" edges leaving a state
    // and map has shown to be faster than unordered_map for
    // syntcomp examples
    std::map<unsigned, std::pair<unsigned, bdd>> interm_edge_hash;
    typedef std::map<unsigned, std::pair<unsigned, bdd>>::mapped_type ieh_t;

    small_cacher_t small_cacher;
    small_cacher.fill(aut, output_bdd, moore);

    // Cache vector for all outgoing edges of this states
    std::vector<e_info_t> e_cache;

    // Vector of destinations actually reachable for a given
    // minterm in ins (or outs for Moore)
    // Automatically "almost" sorted due to the sorting of e_cache
    std::vector<const e_info_t*> dests;

    // If a completion is demanded we might have to create sinks.
    // The sink pair alternates: first player -> second player -> first player.
    // For Mealy: first=env, second=ctrl.
    // For Moore: first=ctrl, second=env.
    unsigned sink_first = -1u;   // First player's sink state
    unsigned sink_second = -1u;  // Second player's sink state
    auto ensure_sinks = [&split, &sink_first, &sink_second,
                         um = unsat_mark, hu = has_unsat]()
      {
        assert(hu);
        if (SPOT_UNLIKELY(sink_first == -1u))
          {
            sink_first = split->new_state();
            sink_second = split->new_state();
            split->new_edge(sink_first, sink_second, bddtrue, um);
            split->new_edge(sink_second, sink_first, bddtrue, um);
          }
      };

    // Loop over all states
    const auto n_states = aut->num_states();
    for (unsigned src = 0; src < n_states; ++src)
      {
        interm_edge_hash.clear();
        e_cache.clear();

        auto out_cont = aut->out(src);

        // Avoid looping over all minterms
        // we only loop over the minterms that actually exist
        bdd all_letters = bddfalse;
        bdd support = bddtrue;

        for (const auto& e : out_cont)
          {
            e_cache.emplace_back(e, small_cacher);
            all_letters |= e_cache.back().einsup.first;
            support &= e_cache.back().einsup.second;
          }
        // Complete for env (first player in Mealy, from original states;
        // for Moore completeness is handled when creating intermediate states)
        if (complete_env && !moore && (all_letters != bddtrue))
          {
            ensure_sinks();
            split->new_edge(src, sink_second, bddtrue - all_letters);
          }

        // Sort to avoid that permutations of the same edges
        // get different intermediate states
        std::sort(e_cache.begin(), e_cache.end(), less_info);

        for (auto one_letter : minterms_of(all_letters, letter_bdd))
          {

            dests.clear();
            for (const auto& e_info : e_cache)
              if (bdd_implies(one_letter, e_info.einsup.first))
                {
                  e_info.econdout = bdd_restrict(e_info.econd, one_letter);
                  dests.push_back(&e_info);
                  assert(e_info.econdout != bddfalse);
                }
            // By construction this should not be empty
            assert(!dests.empty());
            // # dests is almost sorted -> insertion sort
            if (dests.size() > 1)
              for (auto it = dests.begin(); it != dests.end(); ++it)
                std::rotate(std::upper_bound(dests.begin(), it, *it,
                                             less_info_ptr),
                            it, it + 1);

            bool to_add = true;
            size_t h = fnv<size_t>::init;
            for (const auto& t: dests)
              h ^= t->hash();

            auto range_h = interm_hash.equal_range(h);
            for (auto it_h = range_h.first; it_h != range_h.second; ++it_h)
              {
                const auto& [i, this_color] = it_h->second;
                auto out = split->out(i);
                if (std::equal(out.begin(), out.end(),
                               dests.begin(), dests.end(),
                               [uc = use_color]
                               (const twa_graph::edge_storage_t& x,
                                  const e_info_t* y)
                               {
                                 // If there is no unsat -> we do not care
                                 // about color
                                 // todo further optim?
                                 return   x.dst == y->dst
                                          &&  (!uc
                                               || x.acc == y->acc)
                                          &&  x.cond.id() == y->econdout.id();
                               }))
                  {
                    to_add = false;
                    auto it = interm_edge_hash.find(i);
                    if (it != interm_edge_hash.end())
                      it->second.second |= one_letter;
                    else
                      interm_edge_hash.emplace(i,
                        ieh_t(split->new_edge(src, i, bddtrue,
                                              this_color),
                              one_letter));
                    break;
                  }
              }

            if (to_add)
              {
                unsigned d = split->new_state();
                auto this_color = acc_cond::mark_t({});
                bool has_uncolored = false;
                bdd all_inputs = bddfalse;
                 for (const auto &t: dests)
                  {
                    split->new_edge(d, t->dst, t->econdout,
                                    use_color ? t->acc
                                              : acc_cond::mark_t({}));
                    this_color |= t->acc;
                    has_uncolored |= !t->acc;
                    all_inputs |= t->econdout;
                  }
                // Complete for env: in Moore, intermediate states
                // are env (second player) and need input-complete
                // outgoing edges.
                if (complete_env && moore && (all_inputs != bddtrue))
                  {
                    ensure_sinks();
                    split->new_edge(d, sink_first, bddtrue - all_inputs);
                  }

                if (!color_env | has_uncolored)
                  this_color = acc_cond::mark_t({});
                else if (max_par)
                  this_color =
                    acc_cond::mark_t({this_color.min_set()-1});
                else // min_par
                  this_color =
                    acc_cond::mark_t({this_color.max_set()-1});

                unsigned n_e = split->new_edge(src, d, bddtrue, this_color);
                interm_hash.emplace(std::piecewise_construct,
                                    std::forward_as_tuple(h),
                                    std::forward_as_tuple(d, this_color));
                interm_edge_hash.emplace(d, ieh_t(n_e, one_letter));
              }
          } // letters
        // save locally stored condition
        for (const auto& elem : interm_edge_hash)
          split->edge_data(elem.second.first).cond = elem.second.second;
      } // v-src

    split->merge_edges();
    split->prop_universal(trival::maybe());

    // The named property
    // compute the owners
    // For Mealy: original states are env (false), new states are ctrl (true)
    // For Moore: original states are ctrl (true), new states are env (false)
    auto owner = std::vector<bool>(split->num_states(), false);
    if (moore)
      {
        // Original states are first player (ctrl=true)
        std::fill(owner.begin(), owner.begin() + aut->num_states(), true);
        // All "new" states belong to second player (env=false, default)
        // Check if sinks have been created
        if (sink_first != -1u)
          owner.at(sink_first) = true;
      }
    else
      {
        // All "new" states belong to the second player (ctrl=true)
        std::fill(owner.begin()+aut->num_states(), owner.end(), true);
        // Check if sinks have been created
        if (sink_first != -1u)
          owner.at(sink_first) = false;
      }

    // !use_color -> all words accepted
    // complete_env && sink_first == -1u
    // complet. for env demanded but already
    // satisfied -> split is also all true
    if (complete_env && sink_first == -1u && !use_color)
      split->acc() = acc_cond::acc_code::t();

    set_state_players(split, std::move(owner));

    // Done
    return split;
  } // End split old impl

  std::vector<bdd>
  do_bin_encode_(unsigned N, int var0, unsigned Nvar)
  {
    auto bddvec = std::vector<std::array<bdd, 2>>(Nvar);
    for (unsigned i = 0; i < Nvar; ++i)
      bddvec[i] = {bdd_nithvar(var0+i), bdd_ithvar(var0+i)};

    auto do_bin_encode_1 = [&bddvec, Nvar](unsigned s) -> bdd {
      bdd res = bddtrue;

      for (unsigned i = 0; i < Nvar; ++i)
        {
          res &= bddvec[i][s&1];
          s >>= 1;
        }
      return res;
    };

    auto s2bdd = std::vector<bdd>(N);
    for (unsigned s = 0; s < N; ++s)
      s2bdd[s] = do_bin_encode_1(s);

    return s2bdd;
  }

  struct bitVectDecodeIterator{
    const std::vector<unsigned>& v_;
    unsigned u_, idx_ = 0u, vsize_;
    bool first_ = true;

    bitVectDecodeIterator(const std::vector<unsigned>& v, unsigned init)
        : v_{v}
        , u_{init}
        , vsize_(v_.size())
    {
    }

    // Sets to zero all variable bits before the current idx
    void small_reset_() noexcept {
      // Skip current idx
      for (--idx_; idx_!= -1u; --idx_)
        u_ ^= (1u << v_[idx_]);
      idx_ = 0;
    }

    bitVectDecodeIterator& operator++() noexcept {
      first_ = false;
      // Search for the next variable bit to increase
      while (idx_ < vsize_)
        {
          auto curr = 1u << v_[idx_];
          if (!(u_ & curr)){
            u_ |= curr;
            small_reset_();
            return *this;
          }
          ++idx_;
        }
      return *this;
    }

    unsigned operator*() const noexcept {
      return u_;
    }

    explicit operator bool() const noexcept{
      // There is always at least one element
      return idx_ < vsize_ || first_;
    }

  };

  class bitVectDecodeRange
  {
  private:
    const std::vector<unsigned>& v_;
    const unsigned initval_;

  public:
    bitVectDecodeRange(const std::vector<unsigned>& v, unsigned init)
        : v_{v}
        , initval_{init}
    {
    }

    auto
    begin() const
    {
      return bitVectDecodeIterator(v_, initval_);
    }

  };

  template<bool FULLYSYM>
  twa_graph_ptr
  split_2step_sym_impl(const const_twa_graph_ptr& aut,
                       const bdd& output_bdd, bool complete_env,
                       bool moore = false)
  {
    // Moore semantics is not yet implemented for the symbolic path.
    // The dispatcher should have forced EXPL for Moore; we assert here.
    assert(!moore);
    (void)moore;

    assert(!aut->get_named_prop<region_t>("state-player")
           && "aut is already split!");

    auto split = make_twa_graph(aut->get_dict());

    auto [has_unsat, unsat_mark] = aut->acc().unsat_mark();
    bool max_par, odd_par, color_env;
    color_env = aut->acc().is_parity(max_par, odd_par, true);
    const unsigned Ncolor = aut->acc().all_sets().max_set();

    split->copy_ap_of(aut);
    split->new_states(aut->num_states());
    split->set_init_state(aut->get_init_state_number());
    set_synthesis_outputs(split, output_bdd);
    //split->prop_copy(aut, twa::prop_set::all()); // todo why?

    const auto use_color = has_unsat;
    color_env &= use_color;
    if (has_unsat)
      split->copy_acceptance_of(aut);
    else
      {
        if (complete_env)
          {
            split->set_co_buchi(); // Fin(0)
            unsat_mark = acc_cond::mark_t({0});
            has_unsat = true;
          }
        else
          split->acc().set_acceptance(acc_cond::acc_code::t());
      }

    // Reserve all the necessary variables
    const unsigned N = split->num_states();
    const unsigned Nstvars = std::ceil(std::log2(N));
    // we use one hot encoding for colors
    constexpr unsigned Ncolorvars = SPOT_MAX_ACCSETS;
    // Last one is for no color

    auto var_in = std::vector<int>();
    auto var_out = std::vector<int>();

    {
    bdd allbdd = split->ap_vars();
    while (allbdd != bddtrue)
      {
        int lvar = bdd_var(allbdd);
        bdd l = bdd_ithvar(lvar);
        if (bdd_implies(output_bdd, l))
          var_out.push_back(lvar);
        else
          var_in.push_back(lvar);
        allbdd = bdd_high(allbdd);
        assert(allbdd != bddfalse);
      }
    }

    const unsigned Nin = var_in.size();
    const unsigned Nout = var_out.size();

    // Register the vars
    // Need to be released
    // Two possibilities for the need of variables:
    // 1) FULLYSYM == false
    // in conditions, (dst) states, color x out
    // [(dst) states, color x out] is a player state
    // 2) FULLYSYM == true
    // (src) states, in conditions, (dst) states, color x out
    // [(dst) states, color x out] is a player state

    int zeroIdx = aut->get_dict()
                    ->register_anonymous_variables(Nstvars*(1+FULLYSYM)+Nout
                                                   +Nin+Ncolorvars, &N);

    int srcStIdx = zeroIdx;
    int inIdx = srcStIdx + Nstvars*FULLYSYM;
    int dstStIdx = inIdx + Nin;
    int colorIdx = dstStIdx + Nstvars;
    int outIdx = colorIdx + Ncolorvars;

    // Construct the pairs
    bddPair* replace_fwd = bdd_newpair();
    bddPair* replace_bkwd = bdd_newpair();
    bddPair* replace_in_fwd = bdd_newpair();
    bddPair* replace_in_bkwd = bdd_newpair();
    bddPair* replace_out_fwd = bdd_newpair();
    bddPair* replace_out_bkwd = bdd_newpair();

    if (not replace_fwd || not replace_in_fwd || not replace_out_fwd
        || not replace_bkwd || not replace_in_bkwd || not replace_out_bkwd)
      throw std::runtime_error("split_2step(): bddpair alloc error.");

    { // Map old and contiguous inputs and outputs
    auto var_new = std::vector<int>(Nin);
    std::iota(var_new.begin(), var_new.end(), inIdx);
    bdd_setpairs(replace_fwd, var_in.data(), var_new.data(), Nin);
    bdd_setpairs(replace_in_fwd, var_in.data(), var_new.data(), Nin);
    bdd_setpairs(replace_bkwd, var_new.data(), var_in.data(), Nin);
    bdd_setpairs(replace_in_bkwd, var_new.data(), var_in.data(), Nin);

    var_new.resize(Nout);
    std::iota(var_new.begin(), var_new.end(), outIdx);
    bdd_setpairs(replace_fwd, var_out.data(), var_new.data(), Nout);
    bdd_setpairs(replace_out_fwd, var_out.data(), var_new.data(), Nout);
    bdd_setpairs(replace_bkwd, var_new.data(), var_out.data(), Nout);
    bdd_setpairs(replace_out_bkwd, var_new.data(), var_out.data(), Nout);
    }

    // Encode states -> binary encoding (gray code for faster encode?)
    auto dstEnvs2bdd = do_bin_encode_(N, dstStIdx, Nstvars);
    //Source states are only needed once

    // Last bdd is no color
    auto color2bdd = std::vector<std::array<bdd, 2>>(Ncolorvars);
    for (int i = 0; i < (int) Ncolorvars; ++i)
      color2bdd[i] = {bdd_nithvar(colorIdx + i), bdd_ithvar(colorIdx + i)};

    // There are no colors -> All False
    const bdd noColorBdd
      = std::accumulate(color2bdd.begin(), color2bdd.end(),
                        (bdd) bddtrue,
                        [](const bdd& l, const auto& r) -> bdd
                        {return l & r[0]; });

    // Each player state corresponds to a set of (dst_state, colors, outs)
    // We also store the "least accepting" color
    auto playbdd2st
      = std::unordered_map<bdd,
                           std::pair<acc_cond::mark_t, unsigned>,
                           bdd_hash>();
    playbdd2st.reserve(N);

    // Encode (in, out, state) and split<
    auto invar2bdd = std::vector<std::array<bdd, 2>>(Nin);
    for (int i = 0; i < (int) Nin; ++i)
      invar2bdd[i] = {bdd_nithvar(inIdx+i), bdd_ithvar(inIdx+i)};

    enum class ctask{
      PUT = 0,
      VISIT,
      POP
    };

    // Fwd map complete condition
    // We could work with int, the bdd will stay in the graph
    auto fwd_comp_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    // Encode a single edge in from aut with the new variables
    auto encode_edge = [&](const auto& e) -> bdd
      {
        // Build color cond
        // No color -> No bdd
        bdd color_cond = noColorBdd;
        if (use_color && e.acc != acc_cond::mark_t{})
          {
            color_cond = bddtrue;

            for (unsigned acolor = 0; acolor < Ncolor; ++acolor)
              color_cond &= color2bdd[acolor][e.acc.has(acolor)];
          }
        // The whole edge; Order the and? N-ary and?

        auto [itc, insc]
            = fwd_comp_repl.try_emplace(e.cond, bddfalse);
        if (insc)
          itc->second = bdd_replace(e.cond, replace_fwd);
        return itc->second & color_cond & dstEnvs2bdd[e.dst];
      };

    auto abstract_traverse
        = [](auto& stack, auto&& fput, auto&& fpop, auto&& fvisit) -> void
      {
        while (not stack.empty())
          {
            auto [ct, current] = std::move(stack.back());

            stack.pop_back();

            switch (ct)
            {
              case ctask::PUT:
                fput(current);
                break;
              case ctask::POP:
                fpop(current);
                break;
              case ctask::VISIT:
                fvisit(current);
                break;
            }
          }
      };

    auto abstract_put = [](auto& stack, const bdd& ccond, auto&& metaf)
      {
        for (int polprime : {0, 1})
          {
            bdd cprime = polprime == 0 ? bdd_low(ccond) : bdd_high(ccond);

            if (cprime != bddfalse)
              {
                stack.emplace_back(ctask::POP, metaf(polprime));
                stack.emplace_back(ctask::VISIT, cprime);
                stack.emplace_back(ctask::PUT, metaf(polprime));
              }
          }
      };

    // Bkwd replace map
    auto bkwd_out_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    // Final step construct colors and conditions
    // cond is a bdd over color variables and new outputs
    auto construct_colorcond
      = [&](bdd cond)
      {
        // We need to do a final traversal of the color
        // It is similar to the traversal of the states

        // The result
        auto all_comb = std::vector<std::pair<acc_cond::mark_t, bdd>>();

        // int[2] is relative lvl and polarity
        using stack_type = std::variant<bdd, unsigned>;
        auto stack_colors = std::vector<std::pair<ctask, stack_type>>();
        // Variables that do not appear can take both values
        auto current_colors = acc_cond::mark_t{};


        auto fputCC = [&](const stack_type& ccond) -> void
        {
          auto lvl = std::get<unsigned>(ccond);
          //if (lvl != Ncolorvars - 1)
          //  current_colors.set(lvl);  // One hot
          assert(lvl < Ncolorvars || lvl == -1u);
          if (lvl != -1u)
            current_colors.set(lvl);  // One hot
        };

        auto fpopCC = [&](const stack_type& ccond) -> void
        {
          auto lvl = std::get<unsigned>(ccond);
          //if (lvl != Ncolorvars - 1)
          //  current_colors.clear(lvl); // One cold
          assert(lvl < Ncolorvars || lvl == -1u);
          if (lvl != -1u)
            current_colors.clear(lvl);  // One cold
        };

        auto fvisitCC = [&](const stack_type& ccondin) -> void
        {
          bdd ccond = std::get<bdd>(ccondin);
          //if (ccond == bddfalse)
          //  return;  // Nothing to do

          int clvl = ccond == bddtrue ? outIdx : bdd_var(ccond);
          // We either have a out condition or true
          if (clvl >= outIdx)
            {
              // We have found a new color comb
              // Leading to ccond -> add
              auto [itc, insc]
                = bkwd_out_repl.try_emplace(ccond, bddfalse);
              if (insc)
                itc->second = bdd_replace(ccond,
                                          replace_out_bkwd);
              all_comb.emplace_back(current_colors,
                                    itc->second);

            }
          else
            {
              int rel_lvl = clvl - colorIdx;
              // If the no color mark appears -> mark must be empty
              auto metaf = [&, ulvl = (unsigned) rel_lvl](int pol)
                {
                  // If the polarity is negative ("one cold")
                  // Then ignore it
                  assert(!pol || !current_colors.has(ulvl));
                  return pol == 0 ? -1u : ulvl;
                };
              abstract_put(stack_colors, ccond, metaf);
            }

        };

        stack_colors.emplace_back(ctask::VISIT, cond);
        abstract_traverse(stack_colors, fputCC, fpopCC, fvisitCC);

        return all_comb;
      };


    // The condition contains variables of dst_state, color x cond
    // In a much similar manner we need to traverse the states, as we traversed
    // the inputs
    // Mapping bdd(color x new outs) -> [mark x old outs]
    auto bdd2colorCond
      = std::unordered_map<bdd,
                           std::vector<std::pair<acc_cond::mark_t, bdd>>,
                           bdd_hash>();

    struct unsigedItDescr {
      unsigned val;
      std::array<char, 32> canChange;
      std::vector<unsigned> idx;

      unsigedItDescr()
        : val{0u}
        , idx{32, -1u}
      {
        canChange.fill(true);
      }
    };

    auto construct_ply_state
      = [&](bdd cond) -> std::pair<acc_cond::mark_t, unsigned>
      {

        // Needed to determine "least" accepting color for this state
        // That is the color that we can put on all incoming transitions
        auto thiscolor = acc_cond::mark_t{};
        bool has_uncolored = false;
        unsigned thisstate = split->new_state();

        // int[2] is relative lvl and polarity
        using stack_type = std::variant<bdd, std::array<int, 2>>;
        auto stack_states = std::vector<std::pair<ctask, stack_type>>();
        auto current_dst_states = unsigedItDescr{};

        auto fputPlySt
          = [&current_dst_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            auto [lvl, pol] = std::get<std::array<int, 2>>(ccond);
            // Fix the corresponding bit
            // Not changeable
            current_dst_states.canChange[lvl] = false;
            if (pol)
              // Set the bit true
              current_dst_states.val |= (1u << lvl);
            else
              // Unset it
              current_dst_states.val &= ~(1u << lvl);
          };

        auto fpopPlySt
          = [&current_dst_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            // We need to unset the bit and mark it as changeable
            auto lvl = std::get<std::array<int, 2>>(ccond)[0];
            current_dst_states.val &= ~(1u << lvl);
            current_dst_states.canChange[lvl] = true;
          };

        auto fvisitPlySt = [&](const stack_type& ccondin) -> void
          {
            assert(std::holds_alternative<bdd>(ccondin));
            const bdd& ccond = std::get<bdd>(ccondin);
            int clvl = ccond == bddtrue ? colorIdx : bdd_var(ccond);
            if (clvl >= colorIdx)
              {
                // We have found a new "cube of states"
                // Leading to ccond
                auto [it_cc, ins_cc]
                  = bdd2colorCond.try_emplace(ccond,
                                              std::vector<
                                                std::pair<acc_cond::mark_t,
                                                          bdd>>());
                if (ins_cc)
                  it_cc->second = construct_colorcond(ccond);

                // Loop over all the states in the "cube"
                //auto state_range = bitVectDecodeRange(current_dst_states);
                //for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                // Get all the modifiable idx
                current_dst_states.idx.clear();
                for (unsigned i = 0; i < Nstvars; ++i)
                  if (current_dst_states.canChange[i])
                    current_dst_states.idx.push_back(i);
                // Loop over them
                auto state_range = bitVectDecodeRange(current_dst_states.idx,
                                                      current_dst_states.val);
                for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                  // Loop over all edges
                  for (const auto& [acolor, acond] : it_cc->second)
                    {
                      split->new_edge(thisstate, *it_s, acond, acolor);
                      // Update color
                      thiscolor |= acolor;
                      has_uncolored |= !acolor;
                    }

              }
            else
              {
                int rel_lvl = clvl - dstStIdx;
                auto metaf = [rel_lvl](int pol)
                {
                  return std::array<int, 2>{rel_lvl, pol};
                };
                abstract_put(stack_states, ccond, metaf);
              }

          };

        stack_states.emplace_back(ctask::VISIT, cond);
        abstract_traverse(stack_states, fputPlySt, fpopPlySt, fvisitPlySt);

        // Adjust the color depending on options and acceptance conditions
        // Todo: check if dead ends are treated correctly
        if (!color_env | has_uncolored)
          // Do something smart for TELA?
          thiscolor = acc_cond::mark_t({});
        else if (max_par)
          thiscolor =
              acc_cond::mark_t({thiscolor.min_set()-1});
        else // min_par
          thiscolor =
              acc_cond::mark_t({thiscolor.max_set()-1});

        return std::make_pair(thiscolor, thisstate);
    };

    // Fwd map for replacing
    // Todo is this a good idea?
    auto bkwd_in_repl = std::unordered_map<bdd, bdd, bdd_hash>();

    auto stack_inputs = std::vector<std::pair<ctask, bdd>>();

    bdd current_in = bddtrue;

    // Define the abstract traverse
    auto fputInTrav = [&current_in](const bdd& ccond) -> void
      {
        current_in &= ccond;
      };

    auto fpopInTrav = [&current_in](const bdd& ccond) -> void
      {
        // At the end, exist is cheap (I hope)
        current_in = bdd_exist(current_in, ccond);
      };



    // If a completion is demanded we might have to create sinks
    unsigned sink_env = -1u;    // sink for environment
    unsigned sink_con = -1u;    // sink for controller
    auto get_sink_con_state =
      [&split, &sink_con, &sink_env, um = unsat_mark]()
      {
        if (SPOT_UNLIKELY(sink_con == -1u))
          {
            sink_con = split->new_states(2);
            sink_env = sink_con + 1;
            split->new_edge(sink_con, sink_env, bddtrue, um);
            split->new_edge(sink_env, sink_con, bddtrue, um);
          }
        return sink_con;
      };

    if constexpr (FULLYSYM)
      {
        // First we need to encode the complete automaton
        // Create the symbolic aut
        // To avoid reencoding, swap
        bddPair* replace_dstSt_srcSt = bdd_newpair();
        {
          auto varSrc = std::vector<int>(Nstvars);
          auto varDst = std::vector<int>(Nstvars);
          std::iota(varSrc.begin(), varSrc.end(), srcStIdx);
          std::iota(varDst.begin(), varDst.end(), dstStIdx);
          bdd_setpairs(replace_dstSt_srcSt, varDst.data(),
                       varSrc.data(), Nstvars);
        }
        auto getSrc = [&](unsigned s)
          {return bdd_replace(dstEnvs2bdd[s], replace_dstSt_srcSt); };

        bdd sym_aut = bddfalse;
        for (unsigned s = 0; s < N; ++s)
          {
            bdd enc_out_s = bddfalse;
            for (const auto& e : aut->out(s))
              enc_out_s |= encode_edge(e);
            sym_aut |= getSrc(s)&enc_out_s;
          }

        // Define how to construct an extended player state
        // An extended player is constructing the list
        // of (player state, input condition) from a bdd
        // containing (in const, dst state, color cond)
        // This function needs to traverse the incondition
        // put and pop can be reused
        auto construct_ext_ply_state
          = [&](auto& plystatedict, const bdd& ccond)
          {
            current_in = bddtrue;

            auto fvisitInTrav
              = [&](const bdd& ccond) -> void
              {
                auto& [plyconddict, plycondvect] = plystatedict;

                int clvl = bdd_var(ccond);
                assert(clvl >= inIdx);
                if (clvl >= dstStIdx) // States come after input
                  {
                    // We have found a new in cube
                    // Add to the existing ones if necessary
                    // Translate to old variables
                    auto [itc, insc]
                        = bkwd_in_repl.try_emplace(current_in, bddfalse);
                    if (insc)
                      itc->second = bdd_replace(current_in, replace_in_bkwd);
                    const bdd& current_in_old = itc->second;

                    // treat it
                    auto [it_s, ins_s]
                        = playbdd2st.try_emplace(
                            ccond,
                            std::make_pair(acc_cond::mark_t{},
                                           -1u));
                    if (ins_s)
                      // A new player state and the corresponding least
                      // accepting color
                      it_s->second = construct_ply_state(ccond);

                    // Add the condition
                    auto [it_e, ins_e]
                        = plyconddict.try_emplace(ccond, -1u);
                    // Add the input
                    if (ins_e)
                      {
                        it_e->second = plycondvect.size();
                        plycondvect.emplace_back(ccond, bddfalse);
                      }
                    // The second is the in
                    plycondvect[it_e->second].second |= current_in_old;
                    assert(plycondvect[it_e->second].second != bddfalse
                           && "bddfalse is not allowed as condition");
                  }
                else
                  {
                    auto metaf = [&bddopts = invar2bdd[clvl - inIdx]](int pol)
                      {
                        return bddopts[pol];
                      };
                    abstract_put(stack_inputs, ccond, metaf);
                  }
              };

            // Do the actual visit
            assert(stack_inputs.empty());
            stack_inputs.emplace_back(ctask::VISIT, ccond);
            abstract_traverse(stack_inputs, fputInTrav,
                              fpopInTrav, fvisitInTrav);
          }; // construct_ext_ply_state

        // What we want is
        // dict[bdd (in, dst, cc) -> dict[ ply state bdd -> input bdd]]
        // However this is not possible as it would possibly
        // reorder the transitions
        // So we need an additional vector and idx only into it
        // The vector holds the player state cond
        // (same as the key of the unordered_map)
        // To ensure efficient iteration
        auto ext_ply_dict
          = std::unordered_map<bdd,
              std::pair<std::unordered_map<bdd, unsigned, bdd_hash>,
                        std::vector<std::pair<bdd, bdd>>>, bdd_hash>();
        // bdd over new variables -> bdd over old variables, player state

        // Vist the src states
        using stack_type = std::variant<bdd, std::array<int, 2>>;
        auto stack_states = std::vector<std::pair<ctask, stack_type>>();
        // Variables that do not appear can take both values
        auto current_src_states = unsigedItDescr{};

        auto fputSrcSt
          = [&current_src_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            auto [lvl, pol] = std::get<std::array<int, 2>>(ccond);
            // Fix the corresponding bit
            // Not changeable
            current_src_states.canChange[lvl] = false;
            if (pol)
              // Set the bit true
              current_src_states.val |= (1u << lvl);
            else
              // Unset it
              current_src_states.val &= ~(1u << lvl);
          };

        auto fpopSrcSt
          = [&current_src_states](const stack_type& ccond) -> void
          {
            assert((std::holds_alternative<std::array<int, 2>>(ccond)));
            // We need to unset the bit and mark it as changeable
            auto lvl = std::get<std::array<int, 2>>(ccond)[0];
            current_src_states.val &= ~(1u << lvl);
            current_src_states.canChange[lvl] = true;
          };

        auto fvisitSrcSt = [&](const stack_type& ccondin) -> void
          {
            assert(std::holds_alternative<bdd>(ccondin));
            const bdd& ccond = std::get<bdd>(ccondin);
            if (ccond == bddfalse)
              return;
            int clvl = ccond == bddtrue ? inIdx : bdd_var(ccond);
            if (clvl >= inIdx)
              {
                // We have found a new "cube of states"
                // Leading to ccond
                auto [it_cc, ins_cc]
                    = ext_ply_dict.try_emplace(
                        ccond,
                        decltype(ext_ply_dict)::mapped_type{});
                if (ins_cc)
                  // Construct "in place"
                  construct_ext_ply_state(it_cc->second, ccond);

                assert(!it_cc->second.second.empty()
                       && "Dead ends should not be splitted");

                // Get all the modifiable idx
                current_src_states.idx.clear();
                for (unsigned i = 0; i < Nstvars; ++i)
                  if (current_src_states.canChange[i])
                    current_src_states.idx.push_back(i);
                // Loop over them
                auto state_range = bitVectDecodeRange(current_src_states.idx,
                                                      current_src_states.val);
                for (auto it_s = state_range.begin(); (bool) it_s; ++it_s)
                  {
                    bdd uncovered = bddtrue;
                    // Loop over all edges
                    for (const auto& [plystcond, incond]
                           : it_cc->second.second)
                      {
                        const auto& [acolor, plyst] =
                          playbdd2st[plystcond];
                        split->new_edge(*it_s, plyst, incond, acolor);
                        if (complete_env)
                          uncovered -= incond;
                      }
                    // Complete if necessary
                    if (complete_env && uncovered != bddfalse)
                      split->new_edge(*it_s, get_sink_con_state(), uncovered);
                  }
              }
            else
              {
                int rel_lvl = clvl - srcStIdx;
                auto metaf = [rel_lvl](int pol)
                  {
                    return std::array<int, 2>{rel_lvl, pol};
                  };
                abstract_put(stack_states, ccond, metaf);
              }

          };

        stack_states.emplace_back(ctask::VISIT, sym_aut);
        abstract_traverse(stack_states, fputSrcSt, fpopSrcSt, fvisitSrcSt);

        // Free the pairs
        bdd_freepair(replace_dstSt_srcSt);
      }
    else
      {
        // envstate -> edge number for current state
        auto s_edge_dict = std::unordered_map<unsigned, unsigned>();

        for (unsigned s = 0; s < N; ++s)
          {
            s_edge_dict.clear(); // "Local" dict, outgoing for this state

            // Encode the edge as new bdd over (input, state, color, out) vars
            bdd enc_out_s = bddfalse;
            for (const auto &e: aut->out(s))
              enc_out_s |= encode_edge(e);  // Switch to new ins and outs

            if (enc_out_s == bddfalse)
            {
              // Can only be false if there is no outgoing edge
              // In this case: Nothing to do
              assert(!(aut->out(s).begin()));
              continue;
            }

            // traverse the ins to do the actual split
            assert(stack_inputs.empty());
            stack_inputs.emplace_back(ctask::VISIT, enc_out_s);
            current_in = bddtrue;

            bdd all_in = bddfalse;  // Only needed for completion

            auto fvisitInTravS
              = [&](const bdd& ccond) -> void
              {
                int clvl = bdd_var(ccond);
                if (clvl >= dstStIdx) // States come after input
                  {
                    // We have found a new in cube
                    // Add to the existing ones if necessary
                    // Translate to old variables
                    auto [itc, insc]
                        = bkwd_in_repl.try_emplace(current_in, bddfalse);
                    if (insc)
                      itc->second = bdd_replace(current_in, replace_in_bkwd);
                    const bdd& current_in_old = itc->second;

                    if (complete_env)
                      all_in |= current_in_old;
                    // treat it
                    auto [it_s, ins_s]
                        = playbdd2st.try_emplace(
                            ccond,
                            std::make_pair(acc_cond::mark_t{},
                                           -1u));
                    if (ins_s)
                      // A new player state and the corresponding least
                      // accepting color
                      it_s->second = construct_ply_state(ccond);

                    // Add the condition
                    auto [it_e, ins_e]
                        = s_edge_dict.try_emplace(it_s->second.second, -1u);
                    if (ins_e)  // Create a new edge
                      it_e->second
                          = split->new_edge(s, it_s->second.second,
                                            current_in_old,
                                            it_s->second.first);
                    else  // Disjunction over input
                      split->edge_storage(it_e->second).cond
                        |= current_in_old;
                  }
                else
                  {
                    auto metaf = [&bddopts = invar2bdd[clvl - inIdx]](int pol)
                    {
                      return bddopts[pol];
                    };
                    abstract_put(stack_inputs, ccond, metaf);
                  }
              };

            // Traverse all the ins
            abstract_traverse(stack_inputs, fputInTrav,
                              fpopInTrav, fvisitInTravS);

            // Complete if necessary
            if (complete_env && (all_in != bddtrue))
              split->new_edge(s, get_sink_con_state(), bddtrue - all_in);

          }  // Current state is now split
      } // Else

    split->prop_universal(trival::maybe());

    // The named property
    // compute the owners
    // env is equal to false
    auto owner = std::vector<bool>(split->num_states(), false);
    // All "new" states belong to the player
    std::fill(owner.begin()+aut->num_states(), owner.end(), true);
    // Check if sinks have been created
    if (sink_env != -1u)
      owner.at(sink_env) = false;

    // !use_color -> all words accepted
    // complete_env && sink_env == -1u
    // complet. for env demanded but already
    // satisfied -> split is also all true
    if (complete_env && sink_env == -1u && !use_color)
      split->acc() = acc_cond::acc_code::t();

    set_state_players(split, std::move(owner));

    // release the variables
    // Release the pairs
    for (auto pair_ptr : {replace_fwd,
                          replace_bkwd,
                          replace_in_fwd,
                          replace_in_bkwd,
                          replace_out_fwd,
                          replace_out_bkwd})
      bdd_freepair(pair_ptr);
    aut->get_dict()->unregister_all_my_variables(&N);

    // Done
    return split;
  }  // New split impl

  twa_graph_ptr
  split_2step_(const const_twa_graph_ptr& aut,
               const bdd& output_bdd, bool complete_env,
               synthesis_info::splittype sp
                = synthesis_info::splittype::AUTO,
               bool moore = false)
  {
    // Heuristic for AUTO goes here
    // For the moment semisym is almost always best except if there are
    // really few inputs
    unsigned nIns = aut->ap().size() - bdd_nodecount(output_bdd);
    sp = sp == synthesis_info::splittype::AUTO ?
         (nIns < 4 ? synthesis_info::splittype::EXPL
                   : synthesis_info::splittype::SEMISYM)
         : sp;

    // Moore semantics is not yet implemented for symbolic splitting.
    // Force explicit enumeration for now.
    if (moore && sp != synthesis_info::splittype::EXPL)
      sp = synthesis_info::splittype::EXPL;

    switch (sp)
      {
      case synthesis_info::splittype::EXPL:
        return split_2step_expl_impl(aut, output_bdd, complete_env, moore);
      case synthesis_info::splittype::SEMISYM:
        return split_2step_sym_impl<false>(aut, output_bdd, complete_env,
                                           moore);
      case synthesis_info::splittype::FULLYSYM:
        return split_2step_sym_impl<true>(aut, output_bdd, complete_env,
                                          moore);
      default:
        throw std::runtime_error("split_2step_(): "
                                 "Expected explicit splittype.");
      }
  }

  }  // End anonymous


  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              const bdd& output_bdd, bool complete_env,
              synthesis_info::splittype sp,
              bool moore)
  {
    return split_2step_(aut, output_bdd, complete_env, sp, moore);
  }

  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut, bool complete_env,
              synthesis_info::splittype sp,
              bool moore)
  {
    return split_2step_(aut,
                        get_synthesis_outputs(aut),
                        complete_env, sp, moore);
  }

  twa_graph_ptr
  split_2step(const const_twa_graph_ptr& aut,
              synthesis_info& gi)
  {
    return split_2step_(aut,
                        get_synthesis_outputs(aut),
                        true,
                        gi.sp,
                        gi.moore);
  }

  twa_graph_ptr
  unsplit_2step(const const_twa_graph_ptr& aut)
  {
    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();

    twa_graph_ptr out = make_twa_graph(aut->get_dict());
    out->copy_acceptance_of(aut);
    out->copy_ap_of(aut);

    // split_2step is guaranteed to produce an alternating arena
    auto owner = get_state_players(aut);
#ifndef NDEGUB
    (void) owner;
#endif

    std::vector<unsigned> state_map(aut->num_states(), unseen_mark);
    auto seen = [&](unsigned s){return state_map[s] != unseen_mark; };
    auto map_s = [&](unsigned s)
      {
        if (!seen(s))
          state_map[s] = out->new_state();
        return state_map[s];
      };

    std::deque<unsigned> todo;
    todo.push_back(aut->get_init_state_number());
    map_s(aut->get_init_state_number());
    while (!todo.empty())
      {
        unsigned cur = todo.front();
        unsigned cur_m = map_s(cur);
        todo.pop_front();

        for (const auto& i : aut->out(cur))
          for (const auto& o : aut->out(i.dst))
            {
              assert((owner.at(cur) != owner.at(o.src))
                     && (owner.at(cur) == owner.at(o.dst)
                     && "Arena is not alternating!"));
              if (!seen(o.dst))
                todo.push_back(o.dst);
              out->new_edge(cur_m, map_s(o.dst),
                            i.cond & o.cond, i.acc | o.acc);
            }
      }
    out->set_init_state(map_s(aut->get_init_state_number()));
    // Try to set outputs
    if (bdd* outptr = aut->get_named_prop<bdd>("synthesis-outputs"))
      set_synthesis_outputs(out, *outptr);
    return out;
  }

  std::ostream& operator<<(std::ostream& os, synthesis_info::algo s)
  {
    using algo = synthesis_info::algo;
    const char* name = nullptr;
    switch (s)
    {
      case (algo::DET_SPLIT):
        name = "ds";
        break;
      case (algo::SPLIT_DET):
        name = "sd";
        break;
      case (algo::DPA_SPLIT):
        name = "ps";
        break;
      case (algo::LAR):
        name = "lar";
        break;
      case (algo::LAR_OLD):
        name = "lar.old";
        break;
      case (algo::ACD):
        name = "acd";
        break;
    }
    return os << name;
}

  std::ostream&
  operator<<(std::ostream& os, const synthesis_info& gi)
  {
    os << "force sbacc: " << gi.force_sbacc << '\n'
       << "solver: " << gi.s << '\n'
       << "minimization-lvl: " << gi.minimize_lvl << '\n'
       << (gi.verbose_stream ? "Is verbose\n" : "Is not verbose\n")
       << "the bdd_dict used is " << gi.dict.get();
    return os;
  }


  namespace // Anonymous ltl_to_game
  {
    static translator
    create_translator(synthesis_info& gi)
    {
      using algo = synthesis_info::algo;

      option_map& extra_options = gi.opt;
      auto sol = gi.s;
      const bdd_dict_ptr& dict = gi.dict;

      extra_options.set_if_unset("simul", 0);
      extra_options.set_if_unset("tls-impl", 1);
      extra_options.set_if_unset("wdba-minimize", 2);

      translator trans(dict, &extra_options);
      switch (sol)
      {
      case algo::ACD:
        SPOT_FALLTHROUGH;
      case algo::LAR:
        SPOT_FALLTHROUGH;
      case algo::LAR_OLD:
        trans.set_type(postprocessor::Generic);
        trans.set_pref(postprocessor::Deterministic);
        break;
      case algo::DPA_SPLIT:
        trans.set_type(postprocessor::ParityMaxOdd);
        trans.set_pref(postprocessor::Deterministic | postprocessor::Colored);
        break;
      case algo::DET_SPLIT:
        SPOT_FALLTHROUGH;
      case algo::SPLIT_DET:
        break;
      }
      return trans;
    }

    twa_graph_ptr
    ntgba2dpa(const twa_graph_ptr& aut, bool force_sbacc)
    {
      // if the input automaton is deterministic, degeneralize it to be sure to
      // end up with a parity automaton
      auto dpa = tgba_determinize(degeneralize_tba(aut),
                                        false, true, true, false);
      dpa->merge_edges();
      if (force_sbacc)
        dpa = sbacc(dpa);
      reduce_parity_here(dpa, true);
      assert((
                 [&dpa]() -> bool {
                   bool max, odd;
                   return dpa->acc().is_parity(max, odd);
                 }()));
      assert(is_deterministic(dpa));
      return dpa;
    }
  } // anonymous

  twa_graph_ptr
  ltl_to_game(formula f,
              const std::vector<std::string>& all_outs,
              synthesis_info& gi,
              const std::vector<std::string>* unobs)
  {
    using algo = synthesis_info::algo;

    [](std::vector<std::string> sv, std::string msg)
      {
        if (sv.size() < 2)
          return;
        std::sort(sv.begin(), sv.end());
        const unsigned svs = sv.size() - 1;
        for (unsigned i = 0; i < svs; ++i)
          if (sv[i] == sv[i+1])
            throw std::runtime_error(msg + sv[i]);
      }(all_outs, "Output propositions are expected to appear once "
                  "in all_outs. Violating: ");

    auto trans = create_translator(gi);
    // Shortcuts
    auto& bv = gi.bv;
    auto& vs = gi.verbose_stream;

    if (unobs && unobs->empty())
      unobs = nullptr;
    if (unobs)
      {
        // Quantifying unobservable variables universally will be done
        // by working on the negated automaton, doing existential
        // quantification before determinization, and then complementing
        // the DPA.   This cannot work with DPA/LAR approaches.
        std::vector<spot::formula> unobs_vec;
        unobs_vec.reserve(unobs->size());
        for (const std::string& s: *unobs)
          {
            spot::formula ap = spot::formula::ap(s);
            unobs_vec.push_back(ap);
          }
        f = formula::exists(unobs_vec, formula::Not(f));
      }

    stopwatch sw;

    if (bv)
      sw.start();
    auto aut = trans.run(f);
    if (bv)
      {
        bv->sum_trans_time += sw.stop();
        unsigned ns = aut->num_states();
        unsigned ne = aut->num_edges();
        unsigned nc = aut->num_sets();
        unsigned na = aut->ap().size();
        if (std::tie(bv->max_trans_states,
                     bv->max_trans_edges,
                     bv->max_trans_colors,
                     bv->max_trans_ap)
            < std::tie(ns, ne, nc, na))
          {
            bv->max_trans_states = ns;
            bv->max_trans_edges = ne;
            bv->max_trans_colors = nc;
            bv->max_trans_ap = na;
          }
      }
    if (vs)
      {
        assert(bv);
        *vs << "translating formula done in "
            << bv->sum_trans_time << " seconds\n";
        *vs << "automaton has " << aut->num_states()
            << " states and " << aut->num_sets() << " colors\n";
      }
    auto tobdd = [&aut](const std::string& ap_name)
      {
        return bdd_ithvar(aut->register_ap(ap_name));
      };
    auto is_out = [&all_outs](const std::string& ao)->bool
      {
        return std::find(all_outs.begin(), all_outs.end(),
                         ao) != all_outs.end();
      };

    // Check for each ap that actually appears in the graph
    // whether its an in or out
    bdd ins = bddtrue;
    bdd outs = bddtrue;
    for (auto&& aap : aut->ap())
      {
        if (is_out(aap.ap_name()))
          outs &= tobdd(aap.ap_name());
        else
          ins &= tobdd(aap.ap_name());
      }

    twa_graph_ptr dpa = nullptr;

    auto set_split = [&outs, &gi](auto& g)
      {
        set_synthesis_outputs(g, outs);
        return split_2step(g, gi);
      };

    switch (gi.s)
    {
      case algo::DET_SPLIT:
      {
        if (bv)
          sw.start();
        auto tmp = ntgba2dpa(aut, gi.force_sbacc);
        if (unobs)
          tmp = dualize(tmp);
        if (vs)
          *vs << "determinization done\nDPA has "
              << tmp->num_states() << " states, "
              << tmp->num_sets() << " colors\n";
        tmp->merge_states();
        if (bv)
          bv->sum_paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << tmp->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->sum_paritize_time << " seconds\n";
        if (bv)
          sw.start();

        dpa = set_split(tmp);
        if (bv)
          bv->sum_split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->sum_split_time
              << " seconds\nautomaton has "
              << tmp->num_states() << " states\n";
        break;
      }
      case algo::DPA_SPLIT:
      {
        if (bv)
          sw.start();
        aut->merge_states();
        if (unobs)
          aut = dualize(aut);
        if (bv)
          bv->sum_paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done in " << bv->sum_paritize_time
              << " seconds\nDPA has " << aut->num_states()
              << " states\n";
        if (bv)
          sw.start();
        dpa = set_split(aut);
        if (bv)
          bv->sum_split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->sum_split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
      case algo::SPLIT_DET:
      {
        sw.start();
        auto split = set_split(aut);
        if (bv)
          bv->sum_split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->sum_split_time
              << " seconds\nautomaton has "
              << split->num_states() << " states\n";
        if (bv)
          sw.start();
        dpa = ntgba2dpa(split, gi.force_sbacc);
        if (unobs)
          dpa = dualize(dpa);
        if (vs)
          *vs << "determinization done\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";
        // The named property "state-player" is set in split_2step
        // but not propagated by ntgba2dpa
        alternate_players(dpa);
        // Merge states knows about players
        dpa->merge_states();
        if (bv)
          bv->sum_paritize_time += sw.stop();
        if (vs)
          *vs << "simplification done\nDPA has "
              << dpa->num_states() << " states\n"
              << "determinization and simplification took "
              << bv->sum_paritize_time << " seconds\n";
        break;
      }
      case algo::ACD:
        SPOT_FALLTHROUGH;
      case algo::LAR:
        SPOT_FALLTHROUGH;
      case algo::LAR_OLD:
      {
        if (bv)
          sw.start();
        if (unobs)
          aut = dualize(aut);
        if (gi.s == algo::LAR)
          {
            dpa = to_parity(aut);
            reduce_parity_here(dpa, false);
          }
        else if (gi.s == algo::LAR_OLD)
          {
            dpa = to_parity_old(aut);
            reduce_parity_here(dpa, true);
          }
        else
          dpa = acd_transform(aut);
        if (bv)
          bv->sum_paritize_time += sw.stop();
        if (vs)
          *vs << (gi.s == algo::ACD ? "ACD" : "LAR")
              << " construction done in " << bv->sum_paritize_time
              << " seconds\nDPA has "
              << dpa->num_states() << " states, "
              << dpa->num_sets() << " colors\n";

        if (bv)
          sw.start();
        dpa = set_split(dpa);
        if (bv)
          bv->sum_split_time += sw.stop();
        if (vs)
          *vs << "split inputs and outputs done in " << bv->sum_split_time
              << " seconds\nautomaton has "
              << dpa->num_states() << " states\n";
        break;
      }
    } //end switch solver
    // Set the named properties
    assert(dpa->get_named_prop<std::vector<bool>>("state-player")
           && "DPA has no \"state-player\"");
    set_synthesis_outputs(dpa, outs);
    return dpa;
  }

  twa_graph_ptr
  ltl_to_game(formula f,
              const std::vector<std::string>& all_outs,
              const std::vector<std::string>* unobs)
  {
    synthesis_info dummy;
    return ltl_to_game(f, all_outs, dummy, unobs);
  }

  twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    // This currently always produces either separated or split mealy machines
    // if this changes, change also the other functions accordingly
    assert(arena->get_named_prop<region_t>("state-player")
           && "Need prop \"state-player\"");
    if (!arena)
      throw std::runtime_error("Arena can not be null");

    stopwatch sw;

    if (gi.bv)
      sw.start();

    if (!get_state_winner(arena, arena->get_init_state_number()))
      return nullptr;

    auto m = apply_strategy(arena, false, false, gi.moore);

    m->prop_universal(true);

    if (gi.bv)
      {
        gi.bv->sum_strat2aut_time += sw.stop();
        auto sp = get_state_players(m);
        auto n_s_env = sp.size() - std::accumulate(sp.begin(),
                                                   sp.end(),
                                                   0u);
        auto n_e_env = 0u;
        std::for_each(m->edges().begin(), m->edges().end(),
                      [&n_e_env, &sp](const auto& e)
                        {
                          n_e_env += sp[e.src];
                        });
        if (std::tie(gi.bv->max_strat_states, gi.bv->max_strat_edges)
            < std::tie(n_s_env, n_e_env))
          {
            gi.bv->max_strat_states = n_s_env;
            gi.bv->max_strat_edges = n_e_env;
          }
        gi.bv->sum_strat_states += n_s_env;
        gi.bv->sum_strat_edges += n_e_env;
      }

    assert(is_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_mealy(arena, dummy);
  }

  twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    auto m = solved_game_to_mealy(arena, gi);

    if (m->get_named_prop<region_t>("state-player"))
      m = unsplit_mealy(m);
    assert(is_separated_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_separated_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_separated_mealy(arena, dummy);
  }

  twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena, synthesis_info& gi)
  {
    auto m = solved_game_to_mealy(arena, gi);

    if (!m->get_named_prop<region_t>("state-player"))
      {
        assert(is_separated_mealy(m));
        split_separated_mealy_here(m);
      }
    assert(is_split_mealy(m));
    return m;
  }

  twa_graph_ptr
  solved_game_to_split_mealy(twa_graph_ptr arena)
  {
    synthesis_info dummy;
    return solved_game_to_split_mealy(arena, dummy);
  }

}

namespace spot
{
  //Anonymous for try_create_strat
  namespace
  {
    // Checks that 2 sets have a common element. Use it instead
    // of set_intersection when we just want to check if they have a common
    // element because it avoids going through the rest of the sets after an
    // element is found.
    static bool
    are_intersecting(const std::set<formula> &v1,
                    const std::set<formula> &v2)
    {
      auto v1_pos = v1.begin(), v2_pos = v2.begin(), v1_end = v1.end(),
          v2_end = v2.end();
      while (v1_pos != v1_end && v2_pos != v2_end)
        {
          if (*v1_pos < *v2_pos)
            ++v1_pos;
          else if (*v2_pos < *v1_pos)
            ++v2_pos;
          else
            return true;
        }
      return false;
    }
    class formula_2_inout_props
    {
    private:
      std::map<formula, std::pair<std::set<formula>, std::set<formula>>> data_;
      std::vector<std::string> outs_;

    public:

      formula_2_inout_props(std::vector<std::string> outs)
        : outs_(std::move(outs))
      {}

      std::pair<std::set<formula>, std::set<formula>>
      aps_of(formula f)
      {
        auto cache_value = data_.find(f);
        if (cache_value != data_.end())
          return cache_value->second;
        std::set<formula> ins_f, outs_f;
        f.traverse([&](const formula& f)
                  {
                    if (f.is(op::ap))
                    {
                      auto cache_value =
                        std::find(outs_.begin(), outs_.end(), f.ap_name());
                      if (cache_value != outs_.end())
                        outs_f.insert(f);
                      else
                        ins_f.insert(f);
                    }
                    return false;
                  });
        std::pair<std::set<formula>, std::set<formula>> res({ins_f, outs_f});
        data_.insert({f, res});
        return res;
      }
    };
  }

  mealy_like
  try_create_direct_strategy(formula f,
                             const std::vector<std::string>& output_aps,
                             synthesis_info &gi, bool want_strategy)
  {
    auto vs = gi.verbose_stream;
    auto& bv = gi.bv;
    bdd_dict_ptr& dict = gi.dict;
    int tmp;

    if (vs)
      *vs << "trying to create strategy directly for " << f << '\n';

    auto ret_sol_maybe = [&vs, &tmp, &dict]()
      {
        dict->unregister_all_my_variables(&tmp);
        if (vs)
          *vs << "direct strategy might exist but was not found.\n";
        return mealy_like{
                  mealy_like::realizability_code::UNKNOWN,
                  nullptr,
                  bddfalse};
      };
    auto ret_sol_none = [&vs, &tmp, &dict]()
      {
        dict->unregister_all_my_variables(&tmp);
        if (vs)
          *vs << "no strategy exists.\n";
        return mealy_like{
                  mealy_like::realizability_code::UNREALIZABLE,
                  nullptr,
                  bddfalse};
      };

    auto ret_sol_exists =
      [&vs, &want_strategy, &tmp, &dict, &output_aps]
      (twa_graph_ptr strat)
      {
        dict->unregister_all_my_variables(&tmp);
        if (strat)
          {
            strat->merge_edges();
            bdd outputs = bddtrue;
            std::for_each(
                  output_aps.begin(),
                  output_aps.end(),
                  [&strat, &outputs](const std::string& ap) -> void
                  { outputs &= bdd_ithvar(strat->register_ap(ap)); });

            set_synthesis_outputs(strat, outputs);
          }
        if (vs)
          {
            *vs << "direct strategy was found.\n";
            if (strat && want_strategy)
              *vs << "direct strategy has " << strat->num_states()
                  << " states and " << strat->num_edges() << " edges\n";
          }
        return mealy_like{
                  mealy_like::realizability_code::REALIZABLE_REGULAR,
                  strat,
                  bddfalse};
      };
    formula_2_inout_props form2props(output_aps);

    formula f_g, f_other;
    // If it is G(α) ∧ G(β) ∧ …
    if (f.is(op::And))
    {
      std::vector<formula> gs;
      std::vector<formula> others;
      for (auto child : f)
        if (child.is(op::G) && child[0].is_boolean())
          gs.push_back(child[0]);
        else
          others.push_back(child);

      f_g = formula::And(gs);
      f_other = formula::And(others);
    }
    else if (f.is(op::G) && f[0].is_boolean())
    {
      f_g = f[0];
      f_other = formula::tt();
    }
    else
    {
      f_g = formula::tt();
      f_other = f;
    }

    // We have to check if the content of G is realizable (input-complete)
    bdd output_bdd_tmp = bddtrue;
    for (auto& out : output_aps)
      output_bdd_tmp &= bdd_ithvar(
        dict->register_proposition(formula::ap(out), &tmp));

    if (!f_g.is_tt())
    {
      auto g_bdd = formula_to_bdd(f_g, dict, &tmp);
      if (bdd_exist(g_bdd, output_bdd_tmp) != bddtrue)
        return ret_sol_none();
    }

    if (f_other.is(op::Equiv))
    {
      // Check if FG or GF
      auto is_general = [&tmp, &output_bdd_tmp, &dict](const formula &f,
                                                       op first, op second)
      {
        if (!f.is({first, second}) || !f[0][0].is_boolean())
          return false;
        auto f_bdd = formula_to_bdd(f[0][0], dict, &tmp);
        if (bdd_exist(f_bdd, output_bdd_tmp) != bddtrue)
          return false;
        f_bdd = formula_to_bdd(formula::Not(f[0][0]), dict, &tmp);
        bool res = (bdd_exist(f_bdd, output_bdd_tmp) == bddtrue);
        return res;
      };

      auto is_gf = [is_general](const formula& f)
      {
        return is_general(f, op::G, op::F);
      };

      auto is_fg = [is_general](const formula& f)
      {
        return is_general(f, op::F, op::G);
      };

      auto is_co_bu = [](const formula &f, const std::set<formula>& outs)
      {
        return outs.empty() && f.is_syntactic_obligation();
      };

      auto is_buchi = [](const formula &f, const std::set<formula>& outs)
      {
        return outs.empty() && f.is_syntactic_recurrence();
      };

      auto properties_vector = [&](const formula &f,
                            const std::set<formula> &outs)
      {
        auto is_lgf = is_gf(f);
        auto is_lfg = is_fg(f);
        return std::vector<bool>{
            // f is GF(ins + outs) <-> buchi(ins)
            is_lgf,
            is_buchi(f, outs),
            // f is FG(ins + outs) <-> co-buchi(ins)
            is_lfg,
            is_co_bu(f, outs)};
      };


      auto [left_ins, left_outs] = form2props.aps_of(f_other[0]);
      auto [right_ins, right_outs] = form2props.aps_of(f_other[1]);

      auto left_properties = properties_vector(f_other[0], left_outs);
      auto right_properties = properties_vector(f_other[1], right_outs);

      unsigned combin = -1U;
      for (unsigned i = 0; i < 4; ++i)
        if (left_properties[i] && right_properties[(i % 2) ? (i - 1) : (i + 1)])
        {
          combin = i;
          break;
        }

      // If we don't match, we don't know
      if (combin == -1U)
        return ret_sol_maybe();

      formula f_left = f_other[(combin + 1) % 2];
      formula f_right = f_other[combin % 2];
      if (!(combin % 2))
      {
        std::swap(left_ins, right_ins);
        std::swap(left_outs, right_outs);
      }

      std::set<formula> g_outs = form2props.aps_of(f_g).second;
      if (are_intersecting(g_outs, right_outs))
        return ret_sol_maybe();

      // We know that a strategy exists and we don't want to construct it.
      if (!want_strategy)
        return ret_sol_exists(nullptr);

      auto trans = create_translator(gi);

      trans.set_pref(postprocessor::Deterministic | postprocessor::Complete
               | (gi.moore ? postprocessor::SBAcc : 0));
      if (combin < 2)
        trans.set_type(postprocessor::Buchi);
      else
        trans.set_type(postprocessor::CoBuchi);

      stopwatch sw;
      if (bv)
        sw.start();
      auto res = trans.run(f_left);

      if (!is_deterministic(res))
        {
          if (bv)
            {
              auto delta = sw.stop();
              bv->sum_trans_time += delta;
              if (vs)
                *vs << "translating formula done in " << delta
                    << " seconds...\n... but it gave a "
                    << "non-deterministic automaton (rejected)\n";
            }
          return ret_sol_maybe();
        }

      res->prop_complete(trival::maybe());

      bdd output_bdd = bddtrue;
      auto [is, os] = form2props.aps_of(f);
      for (auto i : is)
        res->register_ap(i);
      for (auto o : os)
        output_bdd &= bdd_ithvar(res->register_ap(o));

      bdd right_bdd = formula_to_bdd(f_right[0][0], dict, res);
      bdd neg_right_bdd = bdd_not(right_bdd);
      bdd g_bdd = formula_to_bdd(f_g, dict, res);

      if (combin > 1)
        std::swap(right_bdd, neg_right_bdd);

      right_bdd = bdd_and(right_bdd, g_bdd);
      neg_right_bdd = bdd_and(neg_right_bdd, g_bdd);

      bool is_true_acc = ((combin < 2) && res->acc().is_t())
                || ((combin > 1) && res->acc().is_f());
      if (gi.moore)
        {
          // For Moore all accepting states should have
          // outgoing edges labeled by b, regardless of whether
          // those edges are moving to other BDDs.
          auto& ev = res->edge_vector();
          for (unsigned i = 1; i < ev.size(); ++i)
            {
              auto &edge = ev[i];
              if (edge.acc || is_true_acc)
                edge.cond &= right_bdd;
              else
                edge.cond &= neg_right_bdd;
              edge.acc = {};
            }
        }
      else
        {
          scc_info si(res, scc_info_options::NONE);
          auto prop_vector = propagate_marks_vector(res);
          auto& ev = res->edge_vector();
          for (unsigned i = 1; i < ev.size(); ++i)
            {
              auto &edge = ev[i];
              if (si.scc_of(edge.src) == si.scc_of(edge.dst))
                {
                  if (edge.acc || is_true_acc)
                    edge.cond &= right_bdd;
                  // If we have a GF and an edge is not colored but
                  // prop_vector says that this edge could be colored,
                  // it means that we can do what we want
                  else if (!prop_vector[i])
                    edge.cond &= neg_right_bdd;
                  else
                    edge.cond &= g_bdd;
                }
              else
                edge.cond &= g_bdd;
              edge.acc = {};
            }
        }
      res->set_acceptance(acc_cond::acc_code::t());
      res->prop_weak(true);
      if (res->prop_terminal().is_false())
        res->prop_terminal(trival::maybe());
      res->set_named_prop<bdd>("synthesis-outputs", new bdd(output_bdd));

      if (bv)
        {
          auto delta = sw.stop();
          bv->sum_trans_time += delta;
          if (vs)
            *vs << "translating formula done in " << delta << " seconds\n";
        }
      return ret_sol_exists(res);
    }
    else if (f_other.is_tt())
    {
      if (!want_strategy)
        return ret_sol_exists(nullptr);
      stopwatch sw;
      if (bv)
        sw.start();

      auto res = make_twa_graph(dict);
      res->prop_weak(true);

      bdd output_bdd = bddtrue;
      std::set<formula> ins_f = form2props.aps_of(f_g).first;
      for (auto &out : output_aps)
        output_bdd &= bdd_ithvar(res->register_ap(out));

      for (auto &in : ins_f)
        res->register_ap(in);

      res->set_named_prop<bdd>("synthesis-outputs", new bdd(output_bdd));
      bdd g_bdd = formula_to_bdd(f_g, dict, res);
      res->new_state();
      res->new_edge(0, 0, g_bdd);
      if (bv)
        {
          auto delta = sw.stop();
          bv->sum_trans_time += delta;
          if (vs)
            *vs << "translating formula done in " << delta << " seconds\n";
        }
      return ret_sol_exists(res);
    }
    return ret_sol_maybe();
  }

} // spot

namespace // anonymous for subsformula
{
  using namespace spot;
  static std::pair<std::set<formula>, std::set<formula>>
  algo4(const std::vector<formula> &assumptions,
        const std::set<std::string> &outs,
        formula_2_inout_props& form2props)
  {
    // Two variables are "connected" if they share an assumption.
    // It creates a dependency graph and our goal is to find the propositions
    // that are in the same connected components as outputs.
    const auto ass_size = assumptions.size();
    std::vector<bool> done(ass_size, false);
    std::pair<std::set<formula>, std::set<formula>> result;
    // An output is in the result.
    for (auto &o : outs)
      result.second.insert(formula::ap(o));
    std::stack<unsigned> todo;
    unsigned first_free = 0;

    auto next_free = [&]()
      {
        while (first_free < ass_size)
          {
            if (done[first_free])
              {
                ++first_free;
                continue;
              }
            auto f = assumptions[first_free];
            auto o = form2props.aps_of(f).second;
            if (!o.empty())
              return true;
            ++first_free;
          }
        return false;
      };
    while (next_free())
      {
        todo.push(first_free);
        while (!todo.empty())
          {
            unsigned current_index = todo.top();
            todo.pop();
            const formula& current_form = assumptions[current_index];
            done[current_index] = true;
            auto [ins_current, outs_current]
              = form2props.aps_of(current_form);
            result.first.insert(ins_current.begin(), ins_current.end());
            result.second.insert(outs_current.begin(), outs_current.end());
            for (unsigned i = 0; i < ass_size; ++i)
              {
                if (done[i])
                  continue;
                const formula& other_form = assumptions[i];
                auto [ins_other, outs_other]
                  = form2props.aps_of(other_form);
                if (are_intersecting(ins_current, ins_other) ||
                    are_intersecting(outs_current, outs_other))
                  todo.push(i);
              }
          }
      }
    return result;
  }

  static formula
  split_implication(const formula &f, const std::set<std::string> &outs,
                    formula_2_inout_props& form2props)
  {
    assert(f.is(op::Implies));
    assert(f[0].is(op::And));
    if (!(f[1].is(op::And)))
      return f;
    std::vector<formula> assumptions, guarantees;
    for (auto a : f[0])
      assumptions.push_back(a);
    for (auto g : f[1])
      guarantees.push_back(g);
    // Set of input/output props that cannot be shared between
    // subspecifications
    auto decRelProps = algo4(assumptions, outs, form2props);
    auto &decRelProps_ins = decRelProps.first;
    auto &decRelProps_outs = decRelProps.second;
    // Assumptions that don't contain an atomic proposition in decRelProps
    auto free_assumptions = formula::tt();
    // The set of subspecifications described as [(assum, guar), (assum, guar)]
    std::vector<std::pair<formula, formula>> specs;
    // We merge two assumpt or guar. that share a proposition from decRelProps
    std::vector<formula> assumptions_split, guarantees_split;

    auto fus = [&](std::vector<formula> &forms, std::vector<formula> &res)
    {
      std::stack<unsigned> todo;
      todo.emplace(0);
      unsigned first_free = 1;
      const unsigned forms_size = forms.size();
      std::vector<bool> done(forms_size, false);
      while (!todo.empty())
        {
          auto current_res = formula::tt();
          while (!todo.empty())
            {
              auto current_index = todo.top();
              todo.pop();
              done[current_index] = true;
              auto current_form = forms[current_index];
              current_res = formula::And(current_res, current_form);
              auto [ins_f, outs_f] = form2props.aps_of(current_form);
              std::set<formula> ins_f_dec, outs_f_dec;
              std::set_intersection(ins_f.begin(), ins_f.end(),
                                    decRelProps_ins.begin(),
                                    decRelProps_ins.end(),
                                    std::inserter(ins_f_dec,
                                                  ins_f_dec.begin()));
              std::set_intersection(outs_f.begin(), outs_f.end(),
                                    decRelProps_outs.begin(),
                                    decRelProps_outs.end(),
                                    std::inserter(ins_f_dec,
                                                  ins_f_dec.begin()));
              for (unsigned i = 0; i < forms_size; ++i)
                {
                  if (done[i])
                    continue;
                  auto [ins_i, outs_i] = form2props.aps_of(forms[i]);
                  if (are_intersecting(ins_i, ins_f_dec)
                      || are_intersecting(outs_i, outs_f_dec))
                    todo.emplace(i);
                }
            }
          res.push_back(current_res);
          while (first_free < forms_size && done[first_free])
            ++first_free;
          if (first_free < forms_size)
            {
              todo.emplace(first_free);
              ++first_free;
            }
        }
    };

    fus(assumptions, assumptions_split);
    fus(guarantees, guarantees_split);

    // Now we just have to find connected components in a bipartite graph
    std::function<void(formula f, std::vector<formula> &,
                       std::vector<formula> &,
                       std::set<formula> &,
                       std::set<formula> &,
                       formula &, formula &,
                       std::vector<bool> &,
                       std::vector<bool> &)> bip;
    bip = [&bip, &form2props](formula f, std::vector<formula> &src_vect,
                        std::vector<formula> &dst_vect,
                        std::set<formula> &ins_dec,
                        std::set<formula> &outs_dec,
                        formula &left_res, formula &right_res,
                        std::vector<bool> &done_left,
                        std::vector<bool> &done_right)
    {
      left_res = formula::And(left_res, f);
      auto [ins_f, outs_f] = form2props.aps_of(f);
      std::set<formula> f_ins_dec, f_outs_dec;
      std::set_intersection(ins_f.begin(), ins_f.end(), ins_dec.begin(),
                            ins_dec.end(), std::inserter(f_ins_dec,
                            f_ins_dec.begin()));
      std::set_intersection(outs_f.begin(), outs_f.end(), outs_dec.begin(),
                            outs_dec.end(),
                            std::inserter(f_outs_dec, f_outs_dec.begin()));
      std::stack<unsigned> todo;
      for (unsigned i = 0; i < dst_vect.size(); ++i)
      {
        if (done_right[i])
          continue;
        auto f2 = dst_vect[i];
        auto [f2_ins, f2_outs] = form2props.aps_of(f2);
        if (are_intersecting(f2_ins, f_ins_dec)
          || are_intersecting(f2_outs, f_outs_dec))
        {
          todo.push(i);
          right_res = formula::And(right_res, f2);
          done_right[i] = true;
        }
      }
      while (!todo.empty())
      {
        auto right_index = todo.top();
        todo.pop();
        bip(dst_vect[right_index], dst_vect, src_vect, ins_dec, outs_dec,
            right_res, left_res, done_right, done_left);
      }
    };

    std::vector<bool> done_ass(assumptions_split.size(), false),
        done_gua(guarantees_split.size(), false);
    for (unsigned i = 0; i < assumptions_split.size(); ++i)
      {
        if (done_ass[i])
          continue;
        done_ass[i] = true;
        auto &ass = assumptions_split[i];
        std::set<formula> left_aps = form2props.aps_of(ass).first;
        // If an assumption hasn't any decRelProp, it is considered as
        // a free assumption.
        if (!are_intersecting(left_aps, decRelProps_ins))
          free_assumptions = formula::And(free_assumptions, ass);
        else
          {
            auto left = formula::tt(), right = formula::tt();
            bip(ass, assumptions_split, guarantees_split, decRelProps_ins,
                decRelProps_outs, left, right, done_ass, done_gua);
            specs.push_back({left, right});
          }
      }

    for (unsigned i = 0; i < guarantees_split.size(); ++i)
      if (!done_gua[i])
        specs.push_back({formula::tt(), guarantees_split[i]});

    if (!free_assumptions.is_tt())
      for (auto &sp : specs)
        sp.first = formula::And(sp.first, free_assumptions);
    std::vector<formula> elems;
    for (auto &[ass, gua] : specs)
      {
        auto new_impl = formula::Implies(ass, gua);
        elems.push_back(new_impl);
      }
    return formula::And(elems);
  }

  static formula
  extract_and(const formula& f, const std::set<std::string>& outs,
              bool can_extract_impl, formula_2_inout_props& form2props)
  {
    auto rec = [&] (const formula& fi)
    {
      return extract_and(fi, outs, false, form2props);
    };
    if (f.is(op::And))
      {
        std::vector<formula> children;
        for (formula fi: f)
          children.push_back(rec(fi));
        return formula::And(children);
      }
    else if (f.is(op::Not))
    {
      auto child = extract_and(f[0], outs, false, form2props);
      // ¬(⋀¬xᵢ) ≡ ⋁xᵢ
      if (child.is(op::And))
        {
          bool ok = true;
          for (formula sub: child)
            if (!(sub.is(op::Not)))
              {
                ok = false;
                break;
              }
          if (ok)
            {
              std::vector<formula> children;
              for (formula fi: child)
                children.push_back(rec(formula::Not(fi)));
              return formula::Or(children);
            }
        }
      // ¬Fφ ≡ G¬φ
      else if (child.is(op::F))
        {
          // The result can be G(And).
          return rec(formula::G(rec(formula::Not(child[0]))));
        }
      // ¬(φ→ψ) ≡ φ ∧ ¬ψ
      else if (child.is(op::Implies))
        {
          formula c0 = rec(child[0]);
          return formula::And(c0, rec(formula::Not(child[1])));
        }
      // ¬(φ ∨ ψ) ≡ ¬φ ∧ ¬ψ
      else if (child.is(op::Or))
        {
          std::vector<formula> children;
          for (formula fi: child)
            children.push_back(rec(formula::Not(fi)));
          return formula::And(children);
        }
    }
    // G(⋀φᵢ) = ⋀(G(φᵢ))
    // X(⋀φᵢ) = ⋀(X(φᵢ))
    // X[!](⋀φᵢ) = ⋀(X[!](φᵢ))
    else if (f.is(op::G, op::X, op::strong_X))
      {
        if (formula child_ex = rec(f[0]); child_ex.is(op::And))
          {
            std::vector<formula> children;
            op f_kind = f.kind();
            for (formula fi: child_ex)
              children.push_back(rec(formula::unop(f_kind, fi)));
            return formula::And(children);
          }
      }
    // ⋀φᵢ U ψ ≡ ⋀(φᵢ U ψ)
    else if (f.is(op::U))
      {

        if (formula left_ex = rec(f[0]); left_ex.is(op::And))
          {
            std::vector<formula> children;
            for (formula fi: left_ex)
              children.push_back(formula::U(fi, f[1]));
            return formula::And(children);
          }
      }
    else if (f.is(op::Implies))
      {
        formula right_extr = rec(f[1]);
        formula left_extr = rec(f[0]);
        // φ → (⋀ψᵢ) ≡ ⋀(φ → ψᵢ)
        if (!(left_extr.is(op::And)))
          {
            if (right_extr.is(op::And))
              {
                std::vector<formula> children;
                for (auto fi : right_extr)
                  children.push_back(formula::Implies(left_extr, fi));
                return formula::And(children);
              }
          }
        // ⋀φᵢ → ⋀ψᵢ
        else if (right_extr.is(op::And) && can_extract_impl)
          {
            formula extr_f = formula::Implies(left_extr, right_extr);
            return split_implication(extr_f, outs, form2props);
          }
      }
    return f;
  }

}

namespace spot
{
  std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(formula f, const std::vector<std::string>& outs)
  {
    formula_2_inout_props form2props(outs);
    std::set<std::string> outs_set(outs.begin(), outs.end());

    f = extract_and(f, outs_set, true, form2props);
    if (!(f.is(op::And)))
      return { {f}, { form2props.aps_of(f).second } };
    // Atomics prop of children
    std::vector<std::set<formula>> children_outs;
    // Independent formulas
    std::vector<formula> res;
    // And the appearing propositions
    std::vector<std::set<formula>> res_outs;
    // For each conj, we calculate the set of output AP
    for (auto child : f)
      children_outs.push_back(form2props.aps_of(child).second);
    unsigned nb_children = f.size();
    // flag to test if a conj is in a "class"
    std::vector<bool> children_class(nb_children, false);
    // The first element not in a class
    unsigned first_free = 0;
    std::stack<unsigned> todo;
    while (first_free < nb_children)
      {
        todo.emplace(first_free);
        std::vector<formula> current_and;
        std::set<formula> current_outs;
        while (!todo.empty())
          {
            auto current = todo.top();
            todo.pop();
            children_class[current] = true;
            current_and.push_back(f[current]);
            current_outs.insert(children_outs[current].begin(),
                                children_outs[current].end());
            for (unsigned i = 0; i < nb_children; ++i)
              if (!children_class[i]
                    && are_intersecting(children_outs[current],
                                      children_outs[i]))
                {
                  todo.emplace(i);
                  children_class[i] = true;
                }
          }
        auto elem = formula::And(current_and);
        res.push_back(elem);
        res_outs.push_back(current_outs);

        while (first_free < nb_children && children_class[first_free])
          ++first_free;
      }
    assert(res.size() == res_outs.size());

    return {res, res_outs};
  }

  std::pair<std::vector<formula>, std::vector<std::set<formula>>>
  split_independent_formulas(const std::string& f,
                             const std::vector<std::string>& outs)
  {
    return split_independent_formulas(parse_formula(f), outs);
  }

  formula
  get_negated_assumptions(formula f)
  {
    std::vector<formula> assumptions;

    auto add_antecedent = [&](formula a)
    {
      if (a.is(op::And))
        {
          for (formula c : a)
            assumptions.push_back(c);
        }
      else
        assumptions.push_back(a);
    };

    if (f.is(op::Implies))
      {
        add_antecedent(f[0]);
      }
    else if (f.is(op::And))
      {
        for (formula c : f)
          if (c.is(op::Implies))
            add_antecedent(c[0]);
      }
    else
      {
        return formula();
      }

    if (assumptions.empty())
      return formula();
    return formula::Not(formula::And(assumptions));
  }

  bool
  solve_game(twa_graph_ptr arena, synthesis_info& gi)
  {
    stopwatch sw;
    if (gi.bv)
      sw.start();
    if (gi.verbose_stream)
      {
        *(gi.verbose_stream) << "solving game with acceptance: ";
        std::string name = arena->acc().name();
        if (!name.empty())
          *(gi.verbose_stream) << name;
        else
          *(gi.verbose_stream) << arena->get_acceptance();
        *(gi.verbose_stream) << '\n';
      }
    bool res = solve_game(arena);
    if (gi.bv)
      gi.bv->sum_solve_time += sw.stop();
    if (gi.verbose_stream)
      *(gi.verbose_stream) << "game solved in "
                           << gi.bv->sum_solve_time << " seconds\n";
    return res;
  }

  namespace
  {
    const std::string in_mark_s("__AP_IN__");
    const std::string out_mark_s("__AP_OUT__");
  }

  game_relabeling_map
  partitioned_game_relabel_here(twa_graph_ptr& arena,
                                bool relabel_env,
                                bool relabel_play,
                                bool split_env,
                                bool split_play,
                                unsigned max_letter,
                                unsigned max_letter_mult)
  {
    if (!arena)
      throw std::runtime_error("arena is null.");
    auto& arena_r = *arena;

    const region_t& sp = get_state_players(arena);
    bdd all_ap = arena->ap_vars();

    if (std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                     [](const auto& ap)
                       {
                         return ap.ap_name() == out_mark_s
                                || ap.ap_name() == in_mark_s;
                       }) != arena->ap().cend())
      throw std::runtime_error("partitioned_game_relabel_here(): "
                               "You can not use "
                               + in_mark_s + " or " + out_mark_s +
                               " as propositions if relabeling.");

    bdd out_mark = bdd_ithvar(arena_r.register_ap(out_mark_s));
    bdd in_mark = bdd_ithvar(arena_r.register_ap(in_mark_s));

    bdd outs = get_synthesis_outputs(arena) & out_mark;
    bdd ins = bdd_exist(all_ap, outs) & in_mark;

    for (auto& e : arena_r.edges())
      e.cond = e.cond & (sp[e.src] ? out_mark : in_mark);

    game_relabeling_map res;

    if (relabel_env)
      res.env_map
        = partitioned_relabel_here(arena, split_env, max_letter,
                                   max_letter_mult, ins, "__nv_in");
    if (relabel_play)
      res.player_map
        = partitioned_relabel_here(arena, split_play, max_letter,
                                   max_letter_mult, outs, "__nv_out");
    return res;
  }

  void
  relabel_game_here(twa_graph_ptr& arena,
                    game_relabeling_map& rel_maps)
  {
    if (!arena)
      throw std::runtime_error("arena is null.");
    auto& arena_r = *arena;

    // Check that it was partitioned_game_relabel_here
    if (!((std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                        [](const auto& ap)
                          { return ap.ap_name() == out_mark_s; })
             != arena->ap().cend())
          && (std::find_if(arena->ap().cbegin(), arena->ap().cend(),
                           [](const auto& ap)
                             { return ap.ap_name() == in_mark_s; }))
               != arena->ap().cend()))
      throw std::runtime_error("relabel_game_here(): " +
                               in_mark_s + " or " + out_mark_s +
                               " not registered with arena. "
                               "Not relabeled?");

    if (!rel_maps.env_map.empty())
      relabel_here(arena, &rel_maps.env_map);
    if (!rel_maps.player_map.empty())
      relabel_here(arena, &rel_maps.player_map);

    bdd dummy_ap = bdd_ithvar(arena_r.register_ap(in_mark_s))
                   & bdd_ithvar(arena_r.register_ap(out_mark_s));

    for (auto& e : arena_r.edges())
      e.cond = bdd_exist(e.cond, dummy_ap);

    arena_r.unregister_ap(arena_r.register_ap(in_mark_s));
    arena_r.unregister_ap(arena_r.register_ap(out_mark_s));
  }


  namespace
  {
    // Deep copy a Mealy machine, preserving named properties such as
    // "synthesis-outputs" and "state-player".
    twa_graph_ptr
    clone_graph(const const_twa_graph_ptr& g)
    {
      return make_twa_graph(g, twa::prop_set::all(), true);
    }
  }

  struct synthesis_problem::data
  {
    // Input data.
    formula original_f;
    std::vector<std::string> input_aps;
    std::vector<std::string> output_aps;
    std::vector<std::string> unobs_aps;
    synthesis_info si;

    // Simplification and decomposition state.
    std::vector<std::string> input_and_unobs;
    std::unique_ptr<realizability_simplifier> rs;
    bool prepared_global = false;
    bool prepared_sub = false;
    bool sub_mapping_merged = false;
    formula f;
    std::vector<formula> sub_form;
    std::vector<std::unique_ptr<realizability_simplifier>> sub_rs;
    std::vector<std::set<formula>> sub_outs;
    std::vector<std::vector<std::string>> sub_outs_str;
    std::vector<formula> unobs_vec;
    std::unique_ptr<bdd_dict_preorder> preorder;

    // Negated-assumption pre-check state (item 1 of the report in
    // issue #665).  This is computed at most once, and reused when the
    // solution is rebuilt in another representation.
    bool precheck_done = false;
    bool precheck_accepted = false;
    mealy_like precheck_machine;

    // Solving state.
    bool solved = false;
    bool solved_with_strategy = false;
    bool solved_split = false;
    bool realizable = false;
    bool assumptions_violated = false;
    bool assumptions_checked = false;
    bool precheck_used = false;
    std::vector<mealy_like> mealy_machines;
    std::vector<twa_graph_ptr> raw_sub_strategies;
    std::vector<twa_graph_ptr> sub_strategies_;
    twa_graph_ptr strategy_;
    std::vector<twa_graph_ptr> games_;
    bool games_built = false;

    // AIG cache.
    std::string aig_mode;
    aig_ptr aig_;

    unsigned simplification_options() const;
    void prepare_global();
    void prepare_sub();
    void merge_sub_mappings();
    void prepare();
    void reset_solution();
    mealy_like solve_one(formula f,
                         const std::vector<std::string>& outs_str,
                         bool want_strategy,
                         bool split_out,
                         bool use_obligation);
    bool run_precheck();
    void accept_precheck(bool want_strategy, bool split_out);
    void solve_impl(bool want_strategy, bool split_out);
    void check_strategy(const twa_graph_ptr& strategy) const;
    void detect_assumptions_violated();
  };

  unsigned
  synthesis_problem::data::simplification_options() const
  {
    unsigned opt = 0;
    if (si.polarity != synthesis_info::simplification_stage::never)
      opt |= realizability_simplifier::polarity;
    if (si.global_equiv != synthesis_info::simplification_stage::never)
      opt |= si.game_output_only
        ? realizability_simplifier::global_equiv_output_only
        : (si.moore
           ? realizability_simplifier::global_equiv_moore
           : realizability_simplifier::global_equiv);
    return opt;
  }

  void
  synthesis_problem::data::prepare_global()
  {
    if (prepared_global)
      return;
    prepared_global = true;
    f = original_f;

    // Attempt to remove superfluous atomic propositions.
    if (si.polarity != synthesis_info::simplification_stage::never
        || si.global_equiv != synthesis_info::simplification_stage::never)
      {
        input_and_unobs.reserve(input_aps.size() + unobs_aps.size());
        input_and_unobs.insert(input_and_unobs.end(),
                               input_aps.begin(), input_aps.end());
        input_and_unobs.insert(input_and_unobs.end(),
                               unobs_aps.begin(), unobs_aps.end());

        rs = std::make_unique<realizability_simplifier>(
          original_f, input_and_unobs, simplification_options(),
          si.verbose_stream);
        f = rs->simplified_formula();
      }

    if (si.decompose)
      {
        auto subs = split_independent_formulas(f, output_aps);
        if (si.verbose_stream)
          *si.verbose_stream << "there are "
                             << subs.first.size()
                             << " subformulas\n";
        if (subs.first.size() > 1)
          {
            sub_form = std::move(subs.first);
            sub_outs = std::move(subs.second);
          }
      }

    // When trying to split the formula, we can apply transformations
    // that increase its size.  This is why we use the original formula
    // if it has not been cut.
    if (sub_form.empty())
      {
        sub_form = { f };
        sub_outs.resize(1);
        if (rs)
          {
            std::set<formula> removed_outputs;
            for (auto [from, from_is_input, to] : rs->get_mapping())
              {
                (void) to;
                if (!from_is_input)
                  removed_outputs.insert(from);
              }
            for (const std::string& apstr: output_aps)
              {
                formula ap = formula::ap(apstr);
                if (!removed_outputs.contains(ap))
                  sub_outs[0].insert(ap);
              }
          }
        else
          {
            for (const std::string& apstr: output_aps)
              sub_outs[0].insert(formula::ap(apstr));
          }
      }

    if (si.bv)
      si.bv->sub_specs = sub_form.size();

    sub_outs_str.reserve(sub_outs.size());
    for (const auto& forms: sub_outs)
      {
        std::vector<std::string> r;
        r.reserve(forms.size());
        for (auto f: forms)
          r.push_back(f.ap_name());
        sub_outs_str.push_back(std::move(r));
      }

    assert((sub_form.size() == sub_outs.size())
           && (sub_form.size() == sub_outs_str.size()));
  }

  void
  synthesis_problem::data::prepare_sub()
  {
    if (prepared_sub)
      return;
    prepared_sub = true;

    // Apply per-subformula polarity/global-equiv simplifications
    // before checking which subformulas are obligations, so that the
    // coming BDD variable preorder is set correctly.
    if (sub_form.size() > 1
        && (si.polarity
              == synthesis_info::simplification_stage::
                   before_and_after_decomposition
            || si.global_equiv
              == synthesis_info::simplification_stage::
                   before_and_after_decomposition))
      {
        unsigned opt = 0;
        if (si.polarity
            == synthesis_info::simplification_stage::
                 before_and_after_decomposition)
          opt |= realizability_simplifier::polarity;
        if (si.global_equiv
            == synthesis_info::simplification_stage::
                 before_and_after_decomposition)
          opt |= si.game_output_only
            ? realizability_simplifier::global_equiv_output_only
            : (si.moore
               ? realizability_simplifier::global_equiv_moore
               : realizability_simplifier::global_equiv);
        if (si.verbose_stream)
          *si.verbose_stream << "attempting to simplify subformulas\n";
        for (auto& sf: sub_form)
          {
            if (si.verbose_stream)
              *si.verbose_stream << "considering subformula " << sf << '\n';
            auto rsub = std::make_unique<realizability_simplifier>(
              sf, input_and_unobs, opt, si.verbose_stream);
            sf = rsub->simplified_formula();
            sub_rs.push_back(std::move(rsub));
          }
      }

    bool has_oblig = false;
    if (si.obligation_synthesis)
      for (const formula& sf: sub_form)
        if (sf.is_syntactic_obligation())
          {
            has_oblig = true;
            break;
          }

    if (has_oblig)
      {
        // For Mealy semantics, inputs should appear first in the
        // MTBDDs.  For Moore semantics, outputs should be first.
        // Pre-registering those variables will ensure that.  We want
        // to register them in the order they are found in the formula,
        // this way variables that are used together are more likely to
        // be close in the order.
        std::vector<unsigned char> come_first;
        come_first.resize(formula::apid_count(), 0U);

        unsigned val = si.moore ? 2 : 1;
        for (const std::string& s: input_aps)
          come_first[formula::ap(s).apid()] = val;
        val = 3 - val;
        for (const std::string& s: output_aps)
          come_first[formula::ap(s).apid()] = val;

        unobs_vec.reserve(unobs_aps.size());
        for (const std::string& s: unobs_aps)
          {
            formula ap = formula::ap(s);
            come_first[ap.apid()] = 3;
            unobs_vec.push_back(ap);
          }

        preorder = std::make_unique<bdd_dict_preorder>(si.dict);
        f.traverse([&](const formula& f) {
          if (!f.is(op::ap))
            return false;
          if (come_first[f.apid()] == 1)
            preorder->register_proposition(f);
          return false;
        });
        // obligation_synthesis() will register output variables, and
        // then all quantified variables.  If Moore semantics are used
        // we have already registered output variables, but if
        // quantified variables are used, let's register input
        // variables too, so that quantified variables are put below.
        if (si.moore && (!unobs_aps.empty() || f.is_quantified()))
          {
            f.traverse([&](const formula& f) {
              if (!f.is(op::ap))
                return false;
              if (come_first[f.apid()] == 2)
                preorder->register_proposition(f);
              return false;
            });
          }
      }
  }

  void
  synthesis_problem::data::merge_sub_mappings()
  {
    if (sub_mapping_merged)
      return;
    sub_mapping_merged = true;
    if (!rs)
      return;
    // The mapping of a subformula is only valid inside that
    // subformula, so it is merged into the global mapping only when a
    // complete strategy (or an AIG) is built.
    for (auto& rsub: sub_rs)
      rs->merge_mapping(*rsub);
  }

  void
  synthesis_problem::data::prepare()
  {
    prepare_global();
    prepare_sub();
  }

  void
  synthesis_problem::data::reset_solution()
  {
    solved = false;
    solved_with_strategy = false;
    solved_split = false;
    realizable = false;
    assumptions_violated = false;
    assumptions_checked = false;
    precheck_used = false;
    mealy_machines.clear();
    raw_sub_strategies.clear();
    sub_strategies_.clear();
    strategy_ = nullptr;
    aig_ = nullptr;
    aig_mode.clear();
    if (si.bv)
      {
        si.bv = synthesis_info::bench_var{};
        si.bv->sub_specs = sub_form.size();
      }
  }

  mealy_like
  synthesis_problem::data::solve_one(
    formula f,
    const std::vector<std::string>& outs_str,
    bool want_strategy,
    bool split_out,
    bool use_obligation)
  {
    mealy_like m_like
      {
        mealy_like::realizability_code::UNKNOWN,
        nullptr,
        bddfalse
      };

    auto& bv = si.bv;

    if (use_obligation && si.obligation_synthesis
        && f.is_syntactic_obligation())
      {
        if (si.verbose_stream)
          *si.verbose_stream << ("formula is an obligation; "
                                 "solving with the on-the-fly "
                                 "construction\n");
        stopwatch sw;
        if (bv)
          sw.start();
        formula sf = f;
        if (!unobs_vec.empty())
          sf = formula::forall(unobs_vec, sf);
        mtdswa_ptr aut =
          obligation_synthesis(sf, si.dict, outs_str,
                               !want_strategy);
        if (bv)
          {
            auto delta = sw.stop();
            bv->sum_trans_time += delta;
            if (si.verbose_stream)
              *si.verbose_stream << "solving done in " << delta
                                 << " seconds\n";
          }
        if (aut->acc.is_f())
          {
            m_like.success =
              mealy_like::realizability_code::UNREALIZABLE;
          }
        else
          {
            m_like.success =
              mealy_like::realizability_code::REALIZABLE_REGULAR;
            if (want_strategy)
              {
                if (bv)
                  sw.start();
                m_like.mealy_like =
                  mtdswa_strategy_to_mealy(aut, false, false);
                if (bv)
                  {
                    bv->sum_strat2aut_time += sw.stop();
                    unsigned ns = m_like.mealy_like->num_states();
                    unsigned ne = m_like.mealy_like->num_edges();
                    if (std::tie(bv->max_strat_states,
                                 bv->max_strat_edges)
                        < std::tie(ns, ne))
                      {
                        bv->max_strat_states = ns;
                        bv->max_strat_edges = ne;
                      }
                    bv->sum_strat_states += ns;
                    bv->sum_strat_edges += ne;
                  }
              }
          }
      }
    else
      {
        if (si.use_bypass && unobs_aps.empty())
          m_like = try_create_direct_strategy(f, outs_str, si,
                                              want_strategy);

        if (m_like.success == mealy_like::realizability_code::UNKNOWN)
          {
            auto arena = ltl_to_game(f, outs_str, si, &unobs_aps);
#ifndef NDEBUG
            auto spptr =
              arena->get_named_prop<std::vector<bool>>("state-player");
            assert(spptr);
            assert((spptr->at(arena->get_init_state_number()) == si.moore)
                   && "incorrect first player");
#endif
            if (bv)
              {
                unsigned ns = arena->num_states();
                unsigned nc = arena->num_sets();
                if (std::tie(bv->max_game_states, bv->max_game_colors)
                    < std::tie(ns, nc))
                  {
                    bv->max_game_states = ns;
                    bv->max_game_colors = nc;
                  }
              }
            if (!solve_game(arena, si))
              {
                m_like.success =
                  mealy_like::realizability_code::UNREALIZABLE;
                m_like.mealy_like = nullptr;
                m_like.glob_cond = bddfalse;
                return m_like;
              }
            m_like.success =
              mealy_like::realizability_code::REALIZABLE_REGULAR;
            if (want_strategy)
              {
                m_like.mealy_like = solved_game_to_mealy(arena, si);
                m_like.glob_cond = bddfalse;
              }
          }
      }

    switch (m_like.success)
      {
      case mealy_like::realizability_code::UNREALIZABLE:
        return m_like;

      case mealy_like::realizability_code::UNKNOWN:
        SPOT_UNREACHABLE();

      case mealy_like::realizability_code::REALIZABLE_REGULAR:
        assert(!want_strategy
               || (m_like.mealy_like
                   && "Expected success but found no mealy!"));
        if (want_strategy)
          simplify_mealy_here(m_like.mealy_like, si, split_out);
        return m_like;

      case mealy_like::realizability_code::REALIZABLE_DTGBA:
        return m_like;
      }
    SPOT_UNREACHABLE();
  }

  bool
  synthesis_problem::data::run_precheck()
  {
    if (precheck_done)
      return precheck_accepted;
    precheck_done = true;

    // The pre-check is only needed when the syntactic decomposition
    // would actually split the specification: otherwise the ordinary
    // solver already handles the assumptions correctly.
    if (!si.decompose || sub_form.size() <= 1)
      return false;

    // rs holds the mapping of the global simplification only: the
    // mappings of the subformulas are merged by merge_sub_mappings(),
    // which runs after this pre-check, because they are not
    // necessarily valid for the whole specification.  This also means
    // the simplifier is run only once.
    formula neg_ass = get_negated_assumptions(f);
    if (!neg_ass)
      return false;

    if (si.verbose_stream)
      *si.verbose_stream << "checking the negation of the assumptions: "
                         << neg_ass << '\n';

    // Solve the negation of the assumptions without decomposing it
    // again.  There is no need for the on-the-fly obligation path
    // here, and disabling it avoids having to set up the MTBDD
    // variable preorder for this formula.
    mealy_like m =
      solve_one(neg_ass, output_aps, true, true, false);
    if (m.success != mealy_like::realizability_code::REALIZABLE_REGULAR
        || !m.mealy_like)
      return false;

    // When several implications are conjoined, the candidate strategy
    // may satisfy the negation of all assumptions while violating one
    // of the guarantees.  Check it against the complete specification
    // before accepting it.
    twa_graph_ptr cand = m.mealy_like;
    if (cand->get_named_prop<region_t>("state-player"))
      cand = unsplit_mealy(cand);
    cand = clone_graph(cand);
    if (rs)
      rs->patch_mealy(cand);
    try
      {
        check_strategy(cand);
      }
    catch (const std::runtime_error&)
      {
        if (si.verbose_stream)
          *si.verbose_stream
            << "the negated-assumption strategy does not satisfy the "
               "specification; falling back to decomposition\n";
        return false;
      }

    precheck_machine = std::move(m);
    precheck_accepted = true;
    return true;
  }

  void
  synthesis_problem::data::accept_precheck(bool want_strategy,
                                           bool split_out)
  {
    assumptions_violated = true;
    assumptions_checked = true;
    precheck_used = true;
    realizable = true;
    if (si.bv)
      si.bv->realizable = true;

    if (want_strategy)
      {
        if (split_out)
          {
            mealy_machines.clear();
            mealy_machines.push_back(precheck_machine);
          }
        else
          {
            twa_graph_ptr raw = precheck_machine.mealy_like;
            if (raw->get_named_prop<region_t>("state-player"))
              raw = unsplit_mealy(raw);
            twa_graph_ptr patched = clone_graph(raw);
            if (rs)
              rs->patch_mealy(patched);
            sub_strategies_.clear();
            sub_strategies_.push_back(std::move(patched));
            strategy_ = clone_graph(raw);
            if (rs)
              rs->patch_mealy(strategy_);
          }
        solved_with_strategy = true;
        solved_split = split_out;
      }
    solved = true;
  }

  void
  synthesis_problem::data::solve_impl(bool want_strategy, bool split_out)
  {
    if (solved)
      {
        if (!want_strategy)
          return;
        if (solved_with_strategy && solved_split == split_out)
          return;
        reset_solution();
      }

    stopwatch sw_total;
    if (si.bv)
      sw_total.start();

    prepare();

    auto finish = [&]()
    {
      if (si.bv)
        si.bv->total_time = sw_total.stop();
    };

    // Item 1 of the report in issue #665: before decomposing, check
    // whether the negation of the assumptions is realizable.  If so,
    // the strategy violating the assumptions also solves the
    // specification.
    if (run_precheck())
      {
        accept_precheck(want_strategy, split_out);
        finish();
        return;
      }

    // Only a complete strategy needs the mappings of the subformulas;
    // applying them any earlier would pollute the pre-check above.
    merge_sub_mappings();

    for (size_t i = 0; i < sub_form.size(); ++i)
      {
        if (sub_form.size() > 1 && si.verbose_stream)
          *si.verbose_stream << "working on subformula "
                             << sub_form[i] << '\n';

        mealy_like m_like = solve_one(sub_form[i], sub_outs_str[i],
                                      want_strategy, split_out, true);
        switch (m_like.success)
          {
          case mealy_like::realizability_code::UNREALIZABLE:
            realizable = false;
            finish();
            return;

          case mealy_like::realizability_code::UNKNOWN:
            SPOT_UNREACHABLE();

          case mealy_like::realizability_code::REALIZABLE_REGULAR:
          case mealy_like::realizability_code::REALIZABLE_DTGBA:
            if (want_strategy)
              mealy_machines.push_back(std::move(m_like));
            break;
          }
      }

    realizable = true;
    if (si.bv)
      si.bv->realizable = true;

    if (want_strategy)
      {
        assert(mealy_machines.size() == sub_form.size()
               && "There is a subformula for which no mealy-like object"
               " has been created.");

        // When split_out is true the machines are only needed by aig().
        // Otherwise build the user-facing separated strategies now, in
        // the same order as the historical ltlsynt pipeline.
        if (!split_out)
          {
            raw_sub_strategies.clear();
            sub_strategies_.clear();
            for (auto& ml: mealy_machines)
              {
                if (!ml.mealy_like || !is_mealy(ml.mealy_like))
                  throw std::runtime_error("synthesis_problem: strategy is "
                                           "not a Mealy machine");
                raw_sub_strategies.push_back(ml.mealy_like);
                twa_graph_ptr patched = clone_graph(ml.mealy_like);
                if (rs)
                  rs->patch_mealy(patched);
                sub_strategies_.push_back(std::move(patched));
              }

            if (raw_sub_strategies.size() == 1)
              strategy_ = clone_graph(raw_sub_strategies[0]);
            else
              {
                strategy_ = raw_sub_strategies[0];
                for (size_t i = 1; i < raw_sub_strategies.size(); ++i)
                  strategy_ = mealy_product(strategy_,
                                            raw_sub_strategies[i]);
              }
            if (rs)
              rs->patch_mealy(strategy_);
          }
        solved_with_strategy = true;
        solved_split = split_out;
      }

    solved = true;
    finish();
  }

  void
  synthesis_problem::data::check_strategy(const twa_graph_ptr& strategy) const
  {
    const char* incomplete_machine =
      si.moore
      ? "Strategy is not an output-complete Moore machine"
      : "Strategy is not an input-complete Mealy machine";
    const char* nondeterministic_machine =
      "Strategy is not an input-deterministic machine";

    unsigned num_states = strategy->num_states();
    if (num_states == 0)
      throw std::runtime_error(incomplete_machine);

    translator trans(si.dict, &si.opt);
    twa_graph_ptr neg_spec = trans.run(formula::Not(original_f));

    if (neg_spec->intersects(strategy))
      throw std::runtime_error("Strategy and negated specification "
                               "do intersect");

    bdd bdd_outs;
    try
      {
        bdd_outs = get_synthesis_outputs(strategy);
      }
    catch (const std::runtime_error& error)
      {
        assert(std::string(error.what())
               == "get_synthesis_outputs(): synthesis-outputs not defined");
        throw std::runtime_error("Outputs are not defined");
      }

    // For Moore: we check output-consistency (all edges from a state
    // must agree on the output), plus input-completeness and
    // input-determinism.
    // For Mealy: we check input-completeness and input-determinism.
    if (si.moore)
      {
        bdd bdd_ins = bdd_exist(strategy->ap_vars(), bdd_outs);
        for (unsigned state = 0; state < num_states; ++state)
          {
            bdd bdd_state_input = bddfalse;
            bdd output_cond = bddfalse;
            for (const auto& edge: strategy->out(state))
              {
                bdd edge_out = bdd_exist(edge.cond, bdd_ins);
                bdd edge_in = bdd_exist(edge.cond, bdd_outs);
                if (output_cond == bddfalse)
                  output_cond = edge_out;
                else if (edge_out != output_cond)
                  throw std::runtime_error("Strategy has inconsistent "
                                           "output (not a Moore machine)");
                if (bdd_have_common_assignment(edge_in, bdd_state_input))
                  throw std::runtime_error(nondeterministic_machine);
                bdd_state_input |= edge_in;
              }
            if (bdd_state_input != bddtrue)
              throw std::runtime_error(incomplete_machine);
          }
      }
    else
      {
        for (unsigned state = 0; state < num_states; ++state)
          {
            bdd bdd_state_cond = bddfalse;
            for (const auto& edge: strategy->out(state))
              {
                bdd edge_cond = bdd_exist(edge.cond, bdd_outs);
                if (bdd_have_common_assignment(edge_cond, bdd_state_cond))
                  throw std::runtime_error(nondeterministic_machine);
                bdd_state_cond |= edge_cond;
              }
            if (bdd_state_cond != bddtrue)
              throw std::runtime_error(incomplete_machine);
          }
      }
  }

  // The pre-check can only flag the solution it builds itself.  When
  // the specification is not split into independent conjuncts, the
  // ordinary solver is used instead, and it may well return a strategy
  // that never satisfies the assumptions (this is the only way to
  // answer specifications that are not realizable under the
  // assumptions).  Detect that case so that
  // assumptions_violated() stays accurate.
  void
  synthesis_problem::data::detect_assumptions_violated()
  {
    if (assumptions_checked)
      return;
    assumptions_checked = true;
    if (assumptions_violated || !realizable || !strategy_)
      return;

    formula neg_ass = get_negated_assumptions(original_f);
    if (!neg_ass)
      return;

    // The strategy violates the assumptions iff none of its behaviours
    // satisfy them, i.e. iff it does not intersect the assumptions
    // A = not (not A).
    translator trans(si.dict, &si.opt);
    twa_graph_ptr ass = trans.run(formula::Not(neg_ass));
    if (!ass->intersects(strategy_))
      assumptions_violated = true;
  }

  namespace
  {
    // Classification of an atomic proposition, mirroring the
    // --ins/--outs/--unobservable-ins options of ltlsynt.
    enum class ap_type
    {
      input,
      output,
      unobservable
    };

    // Element of an input/output list: either a proposition name, or
    // a regular expression between slashes.
    static bool
    is_a_pattern(const std::string& s)
    {
      return s.size() >= 2 && s.front() == '/' && s.back() == '/';
    }

    static std::vector<std::regex>
    compile_patterns(const std::vector<std::string>& patterns,
                     const char* list)
    {
      std::vector<std::regex> res;
      for (const std::string& p: patterns)
        if (is_a_pattern(p))
          try
            {
              res.emplace_back(p.substr(1, p.size() - 2));
            }
          catch (const std::regex_error& e)
            {
              throw std::invalid_argument("invalid regular expression " + p
                                          + " in the " + list + " list: "
                                          + e.what());
            }
      return res;
    }

    static bool
    matches(const std::vector<std::regex>& regexes, const std::string& ap)
    {
      for (const std::regex& r: regexes)
        if (std::regex_search(ap, r))
          return true;
      return false;
    }

    // Decide in which class a proposition that was not named exactly
    // falls.  \a ins_given, \a outs_given, and \a unobs_given tell
    // which lists the user provided; unclassified propositions are
    // inferred from them, as in ltlsynt.
    static ap_type
    find_ap_type(const std::string& ap,
                 const std::vector<std::regex>& regex_in,
                 const std::vector<std::regex>& regex_out,
                 const std::vector<std::regex>& regex_unobs,
                 bool ins_given, bool outs_given, bool unobs_given)
    {
      bool found_unobs = matches(regex_unobs, ap);
      bool found_in = !found_unobs && matches(regex_in, ap);
      bool found_out = matches(regex_out, ap);
      bool has_input_specs = ins_given || unobs_given;

      if (has_input_specs == outs_given)
        {
          if (!has_input_specs)
            {
              // Nothing was specified: guess from the first letter.
              switch (ap[0])
                {
                case 'i':
                case 'I':
                  found_in = true;
                  break;
                case 'o':
                case 'O':
                  found_out = true;
                  break;
                case 'u':
                case 'U':
                  found_unobs = true;
                  break;
                }
            }
          if (found_in && found_out)
            throw std::invalid_argument("'" + ap + "' matches both the "
                                        "input and the output list");
          if (found_unobs && found_out)
            throw std::invalid_argument("'" + ap + "' matches both the "
                                        "unobservable-input and the "
                                        "output list");
          if (!found_in && !found_out && !found_unobs)
            {
              if (has_input_specs && !ins_given)
                // Only outputs (and maybe unobservable inputs) were
                // given, so the inputs were not specified.
                found_in = true;
              else if (unobs_given && !ins_given)
                throw std::invalid_argument("one of the input, "
                                            "unobservable-input, or "
                                            "output lists should match '"
                                            + ap + "'");
              else if (has_input_specs || outs_given)
                throw std::invalid_argument("one of the input or output "
                                            "lists should match '"
                                            + ap + "'");
              else
                throw std::invalid_argument("since '" + ap + "' does not "
                                            "start with 'i', 'o', or 'u', "
                                            "it is unclear whether it is "
                                            "an input, an output, or an "
                                            "unobservable input; give the "
                                            "input or output list");
            }
        }
      else
        {
          // Only one side was specified.
          if (outs_given && !found_out)
            found_in = true;
          else if (ins_given && !outs_given && !found_in && !found_unobs)
            found_out = true;
          else if (!found_unobs && !found_in && !found_out)
            throw std::invalid_argument("one of the input, "
                                        "unobservable-input, or output "
                                        "lists should match '" + ap + "'");
        }
      if (found_unobs)
        return ap_type::unobservable;
      if (found_in)
        return ap_type::input;
      return ap_type::output;
    }

    struct ap_partition
    {
      std::vector<std::string> ins;
      std::vector<std::string> outs;
      std::vector<std::string> unobs;
    };

    // Split the atomic propositions of \a f into inputs, outputs, and
    // unobservable inputs, following the rules of the ltlsynt options.
    // The synthesis pipeline relies on such a partition: propositions
    // that would be left out are treated as inputs by some stages and
    // as outputs by others.
    static ap_partition
    classify_aps(formula f,
                 const std::vector<std::string>* input_aps,
                 const std::vector<std::string>* output_aps,
                 const std::vector<std::string>* unobs_aps)
    {
      // An unspecified list is a null pointer, while a specified one
      // may be empty (as with "--ins=" on the command line).
      static const std::vector<std::string> no_list;
      const std::vector<std::string>& ins =
        input_aps ? *input_aps : no_list;
      const std::vector<std::string>& outs =
        output_aps ? *output_aps : no_list;
      const std::vector<std::string>& unobs =
        unobs_aps ? *unobs_aps : no_list;

      // First, handle the propositions that are named exactly, and
      // diagnose conflicts.  An unobservable input is also an input,
      // so naming it in both lists is not a conflict.
      std::map<std::string, ap_type> named;
      std::vector<std::string> named_order;
      for (const std::string& n: ins)
        if (!is_a_pattern(n) && named.try_emplace(n, ap_type::input).second)
          named_order.push_back(n);
      for (const std::string& n: unobs)
        if (!is_a_pattern(n))
          {
            auto [it, is_new] = named.try_emplace(n, ap_type::unobservable);
            if (is_new)
              named_order.push_back(n);
            else if (it->second == ap_type::input)
              it->second = ap_type::unobservable;
          }
      for (const std::string& n: outs)
        if (!is_a_pattern(n))
          {
            auto [it, is_new] = named.try_emplace(n, ap_type::output);
            if (is_new)
              named_order.push_back(n);
            else if (it->second == ap_type::input)
              throw std::invalid_argument("'" + n + "' appears in both "
                                          "the input and the output "
                                          "lists");
            else if (it->second == ap_type::unobservable)
              throw std::invalid_argument("'" + n + "' appears in both "
                                          "the unobservable-input and "
                                          "the output lists");
          }

      auto regex_in = compile_patterns(ins, "input");
      auto regex_out = compile_patterns(outs, "output");
      auto regex_unobs = compile_patterns(unobs, "unobservable-input");

      ap_partition res;
      std::set<std::string> seen;
      auto add = [&](const std::string& n, ap_type t)
        {
          switch (t)
            {
            case ap_type::input:
              res.ins.push_back(n);
              break;
            case ap_type::output:
              res.outs.push_back(n);
              break;
            case ap_type::unobservable:
              res.unobs.push_back(n);
              break;
            }
          seen.insert(n);
        };
      // Named propositions keep the order in which they were given.
      for (const std::string& n: named_order)
        add(n, named[n]);

      // Classify the remaining propositions, in order of appearance.
      bool ins_given = input_aps != nullptr;
      bool outs_given = output_aps != nullptr;
      bool unobs_given = unobs_aps != nullptr;
      std::vector<std::string> aps;
      f.traverse([&](const formula& g)
                 {
                   if (g.is(op::ap))
                     {
                       std::string n = g.ap_name();
                       if (!seen.contains(n))
                         aps.push_back(std::move(n));
                     }
                   return false;
                 });
      for (const std::string& ap: aps)
        add(ap, find_ap_type(ap, regex_in, regex_out, regex_unobs,
                             ins_given, outs_given, unobs_given));
      return res;
    }
  }

  synthesis_problem::synthesis_problem(
    formula f,
    const std::vector<std::string>* input_aps,
    const std::vector<std::string>* output_aps,
    const std::vector<std::string>* unobservable_aps,
    synthesis_info si)
    : data_(new data)
  {
    ap_partition part = classify_aps(f, input_aps, output_aps,
                                     unobservable_aps);
    data_->original_f = f;
    data_->input_aps = std::move(part.ins);
    data_->output_aps = std::move(part.outs);
    data_->unobs_aps = std::move(part.unobs);
    data_->si = std::move(si);
    // Always collect statistics in the problem object; the caller can
    // inspect them with statistics().
    data_->si.bv = synthesis_info::bench_var{};
  }

  synthesis_problem::~synthesis_problem() = default;

  bool
  synthesis_problem::is_realizable()
  {
    data_->solve_impl(false, false);
    return data_->realizable;
  }

  twa_graph_ptr
  synthesis_problem::strategy()
  {
    data_->solve_impl(true, false);
    return data_->strategy_;
  }

  const std::vector<twa_graph_ptr>&
  synthesis_problem::sub_strategies()
  {
    data_->solve_impl(true, false);
    return data_->sub_strategies_;
  }

  aig_ptr
  synthesis_problem::aig(const char* mode)
  {
    data_->solve_impl(true, true);
    if (!data_->realizable)
      return nullptr;

    if (data_->aig_ && data_->aig_mode == mode)
      return data_->aig_;

    stopwatch sw;
    if (data_->si.bv)
      sw.start();
    std::vector<std::vector<std::string>> outs_for_aig;
    if (data_->precheck_used)
      outs_for_aig.push_back(data_->output_aps);
    else
      outs_for_aig = data_->sub_outs_str;
    data_->aig_ = mealy_machines_to_aig(data_->mealy_machines, mode,
                                        data_->input_aps,
                                        outs_for_aig,
                                        data_->rs.get());
    if (data_->si.bv)
      {
        auto& bv = data_->si.bv;
        bv->aig_time = sw.stop();
        bv->aig_latches = data_->aig_->num_latches();
        bv->aig_gates = data_->aig_->num_gates();
      }
    data_->aig_mode = mode;
    return data_->aig_;
  }

  const std::vector<twa_graph_ptr>&
  synthesis_problem::games()
  {
    auto& d = *data_;
    if (d.games_built)
      return d.games_;

    stopwatch sw;
    if (d.si.bv)
      sw.start();
    d.prepare();
    d.merge_sub_mappings();

    d.games_.reserve(d.sub_form.size());
    for (size_t i = 0; i < d.sub_form.size(); ++i)
      {
        auto arena = ltl_to_game(d.sub_form[i], d.sub_outs_str[i],
                                 d.si, &d.unobs_aps);
        if (d.rs)
          d.rs->patch_game(arena);
        d.games_.push_back(std::move(arena));
      }
    d.games_built = true;
    if (d.si.bv)
      d.si.bv->total_time = sw.stop();
    return d.games_;
  }

  const std::vector<formula>&
  synthesis_problem::sub_specifications()
  {
    static const std::vector<formula> empty;
    data_->prepare();
    if (data_->precheck_used)
      return empty;
    return data_->sub_form;
  }

  const std::vector<std::vector<std::string>>&
  synthesis_problem::sub_outputs()
  {
    static const std::vector<std::vector<std::string>> empty;
    data_->prepare();
    if (data_->precheck_used)
      return empty;
    return data_->sub_outs_str;
  }

  bool
  synthesis_problem::assumptions_violated() const
  {
    // Answering this needs the strategy, so solve on demand.  This is
    // a diagnostic: building the strategy eagerly would slow down the
    // callers that only need is_realizable().
    if (!data_->solved
        || (data_->realizable && !data_->solved_with_strategy))
      data_->solve_impl(true, false);
    data_->detect_assumptions_violated();
    return data_->assumptions_violated;
  }

  const synthesis_info&
  synthesis_problem::options() const
  {
    return data_->si;
  }

  const synthesis_info::bench_var&
  synthesis_problem::statistics() const
  {
    return *data_->si.bv;
  }

  void
  synthesis_problem::verify_strategy()
  {
    data_->solve_impl(true, false);
    if (!data_->realizable || !data_->strategy_)
      throw std::runtime_error("synthesis_problem::verify_strategy(): "
                               "no strategy to verify");
    data_->check_strategy(data_->strategy_);
  }

  void
  synthesis_problem::verify_aig(const const_aig_ptr& circuit)
  {
    if (!circuit)
      throw std::runtime_error("synthesis_problem::verify_aig(): "
                               "no circuit to verify");
    translator trans(data_->si.dict, &data_->si.opt);
    auto neg_spec = trans.run(formula::Not(data_->original_f));
    auto saigaut = circuit->as_automaton(false);
    if (neg_spec->intersects(saigaut))
      throw std::runtime_error("Aiger and negated specification do "
                               "intersect: circuit is not OK.");
  }
} // spot
