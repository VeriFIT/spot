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
#include <queue>
#include <unordered_map>
#include <algorithm>
#include <memory>
#include <spot/twaalgos/mtdswa.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/priv/robin_hood.hh>
#include <spot/misc/escape.hh>
#include <spot/tl/print.hh>
#include <spot/tl/apcollect.hh>
#include <spot/tl/simplify.hh>
#include <spot/twaalgos/backprop.hh>

// Some of the MTBDD operations may share the same operation cache, so
// they need an hash key to be distinguished.
constexpr int hash_key_and = 1;
constexpr int hash_key_or = 2;
constexpr int hash_key_implies = 3;
constexpr int hash_key_equiv = 4;
constexpr int hash_key_xor = 5;
constexpr int hash_key_not = 6;
constexpr int hash_key_rename = 7;
constexpr int hash_key_propeq = 8;
constexpr int hash_key_finalstrat = 9;
constexpr int hash_key_quantify = 10;


namespace spot
{
  namespace
  {
    static constexpr const char palette[][8] =
      {
        "#1F78B4", /* blue */
        "#FF4DA0", /* pink */
        "#FF7F00", /* orange */
        "#6A3D9A", /* purple */
        "#33A02C", /* green */
        "#E31A1C", /* red */
        "#C4C400", /* yellowish */
        "#505050", /* gray */
        "#6BF6FF", /* light blue */
        "#FF9AFF", /* light pink */
        "#FF9C67", /* light orange */
        "#B2A4FF", /* light purple */
        "#A7ED79", /* light green */
        "#FF6868", /* light red */
        "#FFE040", /* light yellowish */
        "#C0C090", /* light gray */
      };

    constexpr int palette_mod = sizeof(palette) / sizeof(*palette);

    static int size_estimate_unary(const mtdswa_ptr& aut)
    {
      int states = aut->num_roots();
      states /= 2;
      ++states;
      int num_aps = aut->aps.size();
      int prod = states * num_aps;
      if ((num_aps > 0) && ((prod / num_aps != states) || // overflow
                            prod > (INT_MAX / 16)))
        return INT_MAX / 16;
      if (prod < (1 << 14))
        return 1<<14;
      return prod;
    }

    static int size_estimate_product(int left_states,
                                     int right_states,
                                     int sum_aps)
    {
      if (right_states > left_states)
        std::swap(left_states, right_states);
      left_states /= 4;
      ++left_states;
      int prod1 = left_states * right_states;
      if (prod1 / left_states != right_states) // overflow
        return INT_MAX / 16;
      int prod2 = prod1 * sum_aps;
      if ((sum_aps > 0) && ((prod2 / sum_aps != prod1) || // overflow
                            prod2 > (INT_MAX / 16)))
        return INT_MAX / 16;
      if (prod2 < (1 << 14))
        return 1 << 14;
      return prod2;
    }

    static int size_estimate_product(const mtdswa_ptr& left,
                                     const mtdswa_ptr& right)
    {
      // Compute the number of atomic propositions in the product.
      // The logic is similar to std::set_union except we only
      // count the number of elements in the union.
      auto lbegin = left->aps.begin();
      auto lend = left->aps.end();
      auto rbegin = right->aps.begin();
      auto rend = right->aps.end();
      int apsz = 0;
      while (lbegin != lend && rbegin != rend)
        {
          ++apsz;
          bool adv_left = *lbegin <= *rbegin;
          bool adv_right = *rbegin <= *lbegin;
          lbegin += adv_left;
          rbegin += adv_right;
        }
      // Parentheses are important here, because rend should not be
      // added to (lend - lbegin) in theory even if it's ok in
      // practice..  (Compile the STL in debug mode will catch this.)
      apsz += (lend - lbegin) + (rend - rbegin);

      return size_estimate_product(left->num_roots(),
                                   right->num_roots(),
                                   apsz);
    }

    static int size_estimate_quantify(const mtdswa_ptr& aut)
    {
      // quantify_mtdswa_aux first combines a set of state BDDs with
      // bdd_mt_apply2_leaves().  The cache therefore needs to accommodate the
      // this phase, so we use the product-style estimate.
      return size_estimate_product(aut->num_roots(),
                                   aut->num_roots(),
                                   aut->aps.size());
    }

    void outset(std::ostream& os, int v)
    {
      constexpr int MAX_BULLET = 20;
      os << "<font color=\"" << palette[v % palette_mod] << "\">";
      if ((v >= 0) & (v <= MAX_BULLET))
        {
          static const char* const tab[MAX_BULLET + 1] = {
            "⓿", "❶", "❷", "❸",
            "❹", "❺", "❻", "❼",
            "❽", "❾", "❿", "⓫",
            "⓬", "⓭", "⓮", "⓯",
            "⓰", "⓱", "⓲", "⓳",
            "⓴",
          };
          os << tab[v];
        }
      else
        {
          os << v;
        }
      os << "</font>";
    }
  }

  // convert the MTBDD DFA representation into a DFA.
  twa_graph_ptr mtdswa::as_twa(bool state_based, bool labels,
                               bool complete) const
  {
    // If the initial state is bddtrue, we can simply return an
    // all-accepting automaton.
    if (states[0] == bddtrue)
      {
        auto res = make_twa_graph(dict_);
        res->new_state();
        res->prop_terminal(true);
        res->prop_stutter_invariant(true);
        res->prop_universal(true);
        res->prop_complete(true);
        res->new_edge(0, 0, bddtrue);
        return res;
      }
    if (states[0] == bddfalse)
      {
        auto res = make_twa_graph(dict_);
        res->new_state();
        res->prop_terminal(true);
        res->prop_stutter_invariant(true);
        res->prop_universal(true);
        res->prop_complete(false);
        return res;
      }

    twa_graph_ptr res = make_twa_graph(dict_);
    res->set_acceptance(acc);
    dict_->register_all_propositions_of(this, res);
    res->register_aps_from_dict();
    res->prop_state_acc(state_based);
    res->prop_universal(true);

    unsigned n = states.size();
    assert(n > 0);

    acc_cond::mark_t sat_colors{};
    auto true_state = [&res, this, &sat_colors, sink = -1]() mutable -> int {
      if (sink >= 0)
        return sink;

      auto [satisfiable, satcols] = acc.sat_mark();
      if (SPOT_UNLIKELY(!satisfiable))
        {
          // Tweak the acceptance conditions to allow the accepting
          // state to be accepting.  Since the acceptance was not
          // accepting we could actually reduce the acceptance
          // conditions to inf(0) and ingnore existing colors, but in
          // case these colors have some purpose to the user, let's
          // just augment the acceptance condition with ...|inf(n)
          // where n is a new color used only for sink states.
          unsigned n = acc.num_sets();
          res->set_acceptance(n + 1,
                              acc.get_acceptance() |
                              acc_cond::acc_code::inf({n}));
          satcols = {n};
        }

      sat_colors = satcols;
      sink = res->new_state();
      res->new_edge(sink, sink, bddtrue, satcols);
      return sink;
    };

    acc_cond::mark_t unsat_colors{};
    auto false_state = [&res, this, &unsat_colors, sink = -1]() mutable -> int {
      if (sink >= 0)
        return sink;

      auto [unsatisfiable, unsatcols] = acc.unsat_mark();
      if (SPOT_UNLIKELY(!unsatisfiable))
        {
          // see comment above in true_state.
          unsigned n = acc.num_sets();
          res->set_acceptance(n + 1,
                              acc.get_acceptance() &
                              acc_cond::acc_code::fin({n}));
          unsatcols = {n};
        }

      unsat_colors = unsatcols;
      sink = res->new_state();
      res->new_edge(sink, sink, bddtrue, unsatcols);
      return sink;
    };

    // in case we need to rename states
    std::vector<int> new_num;

    if (!state_based)
      {
        if (complete)
          {
            res->new_states(n);
            for (unsigned i = 0; i < n; ++i)
              for (auto [b, t]: all_paths_mt_of(states[i]))
                if (t == bddtrue)
                  {
                    res->new_edge(i, true_state(), b, sat_colors);
                  }
                else if (t == bddfalse)
                  {
                    res->new_edge(i, false_state(), b, unsat_colors);
                  }
                else
                  {
                    unsigned dst = bdd_get_terminal(t);
                    res->new_edge(i, dst, b, colors[dst]);
                  }
            res->prop_complete(true);
          }
        else
          {
            // Scan all states to renumber them ignoring rejecting sinks.
            new_num.reserve(n);
            unsigned cur_num = 0;
            for (unsigned i = 0; i < n; ++i)
              if (!acc.accepting(colors[i]) && states[i] == bdd_terminal(i))
                new_num.push_back(-1);
              else
                new_num.push_back(cur_num++);
            res->new_states(std::max(1U, cur_num));
            bool so_far_complete = cur_num > 0;
            for (unsigned i = 0; i < n; ++i)
              {
                int ni = new_num[i];
                if (ni < 0)
                  continue;
                if (so_far_complete)
                  for (auto [b, t]: all_paths_mt_of(states[i]))
                    if (t == bddtrue)
                      {
                        res->new_edge(ni, true_state(), b, colors[i]);
                      }
                    else if (t == bddfalse)
                      {
                        so_far_complete = false;
                      }
                    else
                      {
                        int dst = new_num[bdd_get_terminal(t)];
                        if (dst < 0) // edge going to a sink
                          {
                            so_far_complete = false;
                            continue;
                          }
                        res->new_edge(ni, dst, b, colors[i]);
                      }
                else
                  for (auto [b, t]: paths_mt_of(states[i]))
                    if (t == bddtrue)
                      {
                        res->new_edge(ni, true_state(), b, colors[i]);
                      }
                    else
                      {
                        int dst = new_num[bdd_get_terminal(t)];
                        if (dst < 0) // edge going to a sink
                          continue;
                        res->new_edge(ni, dst, b, colors[i]);
                      }
              }
            res->prop_complete(so_far_complete);
          }
        res->merge_edges();
      }
    else                        // state-based
      {
        // The set of states in the new automaton is STATES,
        // plus optionally an accepting sink (if bddtrue appears in
        // the MTBDDs).

        // For now, just declare states for each of terminal_data_map.
        unsigned ns = states.size();
        // We are going to merge edges while we create the automaton,
        // to avoid calling merge_edges() which is costly.

        // For a given state i, edge_dst[j] is going to store label of
        // the edge going to j.  used_dst will record the different j
        // for which edge_dst[j]!=bddfalse.
        std::vector<bdd> edge_dst(ns + 1 + complete, bddfalse);
        std::vector<int> used_dst;
        used_dst.reserve(ns);

        if (complete)
          {
            res->new_states(ns);
            for (unsigned i = 0; i < ns; ++i)
              {
                auto& col = colors[i];
                for (auto [b, t]: all_paths_mt_of(states[i]))
                  {
                    int dst;
                    if (t == bddtrue)
                      dst = true_state();
                    else if (t == bddfalse)
                      dst = false_state();
                    else
                      dst = bdd_get_terminal(t);

                    if (edge_dst[dst] == bddfalse)
                      used_dst.push_back(dst);
                    edge_dst[dst] |= b;
                  }
                for (unsigned dst: used_dst)
                  {
                    res->new_edge(i, dst, edge_dst[dst], col);
                    edge_dst[dst] = bddfalse;
                  }
                used_dst.clear();
              }
            res->prop_complete(true);
          }
        else
          {
            // Scan all states to renumber them ignoring rejecting sinks.
            new_num.reserve(n);
            unsigned cur_num = 0;
            for (unsigned i = 0; i < n; ++i)
              if (!acc.accepting(colors[i]) && states[i] == bdd_terminal(i))
                new_num.push_back(-1);
              else
                new_num.push_back(cur_num++);
            res->new_states(std::max(1U, cur_num));
            bool so_far_complete = cur_num > 0;
            for (unsigned i = 0; i < ns; ++i)
              {
                int ni = new_num[i];
                if (ni < 0)
                  continue;

                auto& col = colors[i];
                if (so_far_complete)
                  // Use all_paths_mt_of until we have found that
                  // the automaton is incomplete.
                  for (auto [b, t]: all_paths_mt_of(states[i]))
                    {
                      if (t == bddfalse)
                        {
                          so_far_complete = false;
                          continue;
                        }
                      int dst = (t != bddtrue) ?
                        new_num[bdd_get_terminal(t)] : true_state();
                      if (dst < 0)
                        {
                          so_far_complete = false;
                          continue;
                        }
                      if (edge_dst[dst] == bddfalse)
                        used_dst.push_back(dst);
                      edge_dst[dst] |= b;
                    }
                else
                  for (auto [b, t]: paths_mt_of(states[i]))
                    {
                      int dst = (t != bddtrue) ?
                        new_num[bdd_get_terminal(t)] : true_state();
                      if (dst < 0)
                        continue;
                      if (edge_dst[dst] == bddfalse)
                        used_dst.push_back(dst);
                      edge_dst[dst] |= b;
                    }

                for (unsigned dst: used_dst)
                  {
                    res->new_edge(ni, dst, edge_dst[dst], col);
                    edge_dst[dst] = bddfalse;
                  }
                used_dst.clear();
              }
            res->prop_complete(so_far_complete);
          }
      }

    res->set_init_state(0);

    std::vector<std::string>* names = nullptr;
    if (labels && this->names.size() == this->states.size())
      {
        names = new std::vector<std::string>;
        names->reserve(n);
        res->set_named_prop("state-names", names);
        if (new_num.empty())
          for (unsigned i = 0; i < n; ++i)
            names->push_back(str_psl(this->names[i]));
        else
          for (unsigned i = 0; i < n; ++i)
            if (int ni = new_num[i]; ni >= 0)
              names->push_back(str_psl(this->names[ni]));
      }

    return res;
  }


  namespace
  {
    unsigned global_next_state;
    unsigned global_acc_sink;
    unsigned global_rej_sink;

    static int tfmap_callback(int root, int)
    {
      if (root == 0)
        {
          if (global_rej_sink == -1U)
            global_rej_sink = global_next_state++;
          return bdd_terminal_as_int(global_rej_sink);
        }
      if (root == 1)
        {
          if (global_acc_sink == -1U)
            global_acc_sink = global_next_state++;
          return bdd_terminal_as_int(global_acc_sink);
        }
      return root;
    }
  }

  void mtdswa::sinks_as_states()
  {
    // Scan the states to find potential accepting and rejecting sinks
    // that already exist.
    unsigned ns = states.size();
    global_acc_sink = -1;
    global_rej_sink = -1;
    for (unsigned s = 0; s < ns; ++s)
      {
        if (!bdd_is_terminal(states[s]))
          continue;
        unsigned t = bdd_get_terminal(states[s]);
        // a sink is a state that only has itself as successor
        if (t != s)
          continue;
        if (acc.accepting(colors[s]))
          global_acc_sink = s;
        else
          global_rej_sink = s;
      }
    global_next_state = ns;

    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(shared_from_this()), false);

    // Now scan the states again to replace bddtrue/bddfalse
    for (unsigned s = 0; s < ns; ++s)
      states[s] = bdd_mt_apply1_leaves(states[s], tfmap_callback,
                                       &cache, 0);

    bdd_extcache_done(&cache);

    // If a new accepting sink was introduced, we need to create it.
    // However if the acceptance condition is unsatisfiable, we have to
    // change it.  The following code just deals with the change of
    // acceptance condition.

    acc_cond::mark_t accepting_mark{};
    acc_cond::mark_t rejecting_mark{};
    if (global_acc_sink >= ns)
      {
        std::pair<bool, acc_cond::mark_t> sm = acc.sat_mark();
        if (sm.first)
          {
            accepting_mark = sm.second;
          }
        else
          {
            acc = acc_cond(1, acc_cond::acc_code::buchi());
            accepting_mark = {0};
            rejecting_mark = {};
            for (unsigned s = 0; s < ns; ++s)
              colors[s] = rejecting_mark;
          }
      }
    if (global_rej_sink >= ns)
      {
        std::pair<bool, acc_cond::mark_t> sm = acc.unsat_mark();
        if (sm.first)
          {
            rejecting_mark = sm.second;
          }
        else
          {
            acc = acc_cond(1, acc_cond::acc_code::buchi());
            accepting_mark = {0};
            rejecting_mark = {};
            for (unsigned s = 0; s < ns; ++s)
              colors[s] = accepting_mark;
          }
      }

    // Now create the new states if any.
    while (global_next_state > ns)
      {
        states.push_back(bdd_terminal(ns));
        if (global_acc_sink == ns)
          {
            colors.push_back(accepting_mark);
            if (ns == names.size())
              names.push_back(formula::tt());
          }
        else
          {
            colors.push_back(rejecting_mark);
            if (ns == names.size())
              names.push_back(formula::ff());
          }
        ++ns;
      }
  }


  namespace
  {
    static std::vector<int>* global_state_map;

    static int sinkcst_callback(int root, int term)
    {
      if (root <= 1)
        return root;
      assert((unsigned)term < global_state_map->size());
      int new_s = (*global_state_map)[term];
      if (new_s == term)
        return root;
      if (new_s == -1)
        return 0;
      if (new_s == -2)
        return 1;
      return bdd_terminal_as_int(new_s);
    }
  }

  void mtdswa::sinks_as_constants(bool keep_all_states)
  {
    unsigned ns = states.size();
    std::vector<int> new_state_number;
    new_state_number.reserve(ns);
    unsigned next_num = 0;
    for (unsigned i = 0; i < ns; ++i)
      {
        new_state_number.push_back(next_num++);
        bdd s = states[i];
        if (s == bddfalse)
          {
          rejecting_sink:
            new_state_number[i] = -1;
            if (!keep_all_states)
              --next_num;
            continue;
          }
        if (s == bddtrue)
          {
          accepting_sink:
            new_state_number[i] = -2;
            if (!keep_all_states)
              --next_num;
            continue;
          }
        if (!bdd_is_terminal(s))
          continue;
        unsigned d = bdd_get_terminal(s);
        if (d != i)
          continue;
        if (acc.accepting(colors[i]))
          goto accepting_sink;
        else
          goto rejecting_sink;
      }

    // Handle the exceptional case where the initial state should
    // become bddfalse or bddtrue.
    if (int z = new_state_number[0]; z < 0)
      {
        if (z == -1)
          states[0] = bddfalse;
        else
          states[0] = bddtrue;
        states.resize(1);
        colors.resize(1);
        if (names.size() != ns)
          names.clear();        // don't bother
        else
          names.resize(1);
        return;
      }

    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(shared_from_this()), false);

    global_state_map = &new_state_number;
    // Now scan the states again to replace bddtrue/bddfalse
    int last_state = -1;
    for (unsigned i = 0; i < ns; ++i)
      {
        unsigned new_i = new_state_number[i];
        if (!keep_all_states && (int) new_i < 0)
          continue;
        bdd b = bdd_mt_apply1_leaves(states[i], sinkcst_callback,
                                     &cache, 0);
        if (keep_all_states)
          {
            states[i] = b;
          }
        else
          {
            states[new_i] = b;
            last_state = new_i;
            if (new_i != i)
              {
                colors[new_i] = colors[i];
                if (names.size() > i)
                  names[new_i] = names[i];
              }
          }
      }
    bdd_extcache_done(&cache);

    if (!keep_all_states)
      {
        int new_sz = last_state + 1;
        states.resize(new_sz);
        colors.resize(new_sz);
        if (names.size() != ns)
          names.clear();        // don't bother
        else
          names.resize(new_sz);
      }
    global_state_map = nullptr;
  }

  namespace
  {
    static bdd
    ap_to_bdd(mtdswa_ptr dfa, const std::vector<std::string>& controllable,
              bool ignore_non_registered_ap)
    {
      bdd_dict_ptr dict = dfa->get_dict();
      // build the conjunction of all controllable variables
      bdd controllable_bdd = bddtrue;
      for (const std::string& s: controllable)
        {
          int v = dict->has_registered_proposition(formula::ap(s), dfa);
          if (v < 0)
            {
              if (ignore_non_registered_ap)
                continue;
              throw std::runtime_error
                ("atomic proposition " + s + " is not registered by automaton");
            }
          controllable_bdd &= bdd_ithvar(v);
        }
      return controllable_bdd;
    }

    // Convert a vector of atomic proposition formulas to a positive
    // cube (conjunction) of BDD variables.  Atomic propositions that
    // are not registered in the automaton's dictionary are ignored.
    static bdd
    aps_to_bdd(const mtdswa_ptr& swa,
               const std::vector<formula>& aps)
    {
      bdd_dict_ptr d = swa->get_dict();
      bdd res = bddtrue;
      for (const formula& ap: aps)
        {
          int v = d->has_registered_proposition(ap, swa);
          if (v >= 0)
            res &= bdd_ithvar(v);
        }
      return res;
    }
  }

  void
  mtdswa::set_controllable_variables(bdd vars)
  {
    controllable_variables_ = vars;
  }

  void
  mtdswa::set_controllable_variables(const std::vector<std::string>& vars,
                                     bool ignore_non_registered_ap)
  {
    set_controllable_variables(ap_to_bdd(shared_from_this(), vars,
                                         ignore_non_registered_ap));
  }

  std::ostream& mtdswa::print_dot(std::ostream& os, const char* opts) const
  {
    bool opt_scc = false;
    bool opt_labels = true;
    if (opts)
      while (char c = *opts++)
        switch (c)
          {
          case '0':
            opt_labels = false;
            break;
          case 's':
            opt_scc = true;
            break;
          }

    std::unordered_set<int> controllable;
    {
      bdd b = get_controllable_variables();
      while (b != bddtrue)
        {
          controllable.insert(bdd_var(b));
          b = bdd_high(b);
        }
    }

    std::unordered_map<int, int> scc_map;
    std::vector<int> sccs;
    if (opt_scc)
      {
        auto identity = [] (int x) { return x; };
        sccs = bdd_mt_sccs(states, identity, &scc_map);
      }

    std::ostringstream edges;

    os << "digraph mtdswa {\n  rankdir=TB;\n  node [shape=circle];\n";
    static std::string extra = []()
    {
      auto s = getenv("SPOT_DOTEXTRA");
      return s ? s : "";
    }();
    // Any extra text passed in the SPOT_DOTEXTRA environment
    // variable should be output at the end of the "header", so
    // that our setup can be overridden.
    if (!extra.empty())
      os << "  " << extra << '\n';

    const char* opt_font_ = "Lato";
    os << "  fontname=\"" << opt_font_
        << "\"\n  node [fontname=\"" << opt_font_
       << "\"]\n  edge [fontname=\"" << opt_font_
       << "\"]\n";
    if (opt_scc)
      os << "  newrank=true\n";

    os << "  labelloc=\"t\"\n  label=<";

    acc.get_acceptance().to_html(os, outset);
    std::string accstr = acc.name("d");
    if (!accstr.empty())
      os << "<br/>[" << accstr << ']';
    os  << ">\n";

    os << "  { rank = source; I [label=\"\", style=invis, width=0]; }\n";
    edges << "  I -> S0 [tooltip=\"initial state\"]\n";

    os << "  { rank = same;\n";
    unsigned ns = states.size();
    unsigned colorsz = colors.size();
    unsigned namesz = names.size();
    unsigned maxsz = std::max(1U, std::max(ns, colorsz));

    for (unsigned i = 0; i < maxsz; ++i)
      {
        os << "    S" << i << " [shape=box, style=\"filled,rounded";
        if (i >= ns)
          os << ",dashed";
        os << "\", fillcolor=\"#e9f4fb\", label=<";
        if (opt_labels && i < namesz)
          escape_html(os, str_psl(names[i]));
        else
          os << i;
        if (i < colorsz)
          {
            os << "<br/>";
            for (auto v: colors[i].sets())
              outset(os, v);
          }
        os << ">, tooltip=\"";
        if (opt_labels || i >= namesz)
          os << '[' << i << ']';
        else
          os << str_psl(names[i]);
        os << "\"];\n";
      }

    for (unsigned i = 0; i < ns; ++i)
      edges << "  S" << i << " -> B" << states[i].id()
            << " [tooltip=\"[" << i << "]\"];\n";

    // This is a heap of BDD nodes, with smallest level at the top.
    std::vector<bdd> nodes;
    robin_hood::unordered_set<int> seen;

    robin_hood::unordered_map<int, std::ostringstream> scc_txt;

    nodes.reserve(ns);
    for (unsigned i = 0; i < ns; ++i)
      {
        bdd b = states[i];
        if (seen.insert(b.id()).second)
          nodes.push_back(b);
        if (opt_scc && terminal_to_state_map.empty())
          {
            int tmp = bdd_terminal_as_int(i);
            if (auto it = scc_map.find(tmp); it != scc_map.end())
              scc_txt[it->second] << "  S" << i;
          }
      }

    auto bylvl = [&] (bdd a, bdd b) {
      return bdd_level(a) > bdd_level(b);
    };
    std::make_heap(nodes.begin(), nodes.end(), bylvl);

    int oldvar = -1;

    while (!nodes.empty())
      {
        std::pop_heap(nodes.begin(), nodes.end(), bylvl);
        bdd n = nodes.back();
        nodes.pop_back();
        if (n.id() <= 1)
          {
            if (oldvar != -2)
              os << "  }\n  { rank = sink;\n";
            os << "    B" << n.id()
               << " [shape=square, style=filled, fillcolor=\"";
            if (auto it = highlight_nodes.find(n.id());
                it != highlight_nodes.end())
              os << palette[it->second % palette_mod];
            else
              os << "#ffe6cc";
            os << "\", label=\"" << n.id()
               << "\", tooltip=\"bdd(" << n.id() << ")\" ";
            if (n.id() == 1)
              os << ", peripheries=2";
            os << "];\n";
            oldvar = -2;
            continue;
          }
        if (opt_scc)
          {
            auto it = scc_map.find(n.id());
            if (it != scc_map.end())
              scc_txt[it->second] << "  B" << n.id();
          }
        if (bdd_is_terminal(n))
          {
            if (oldvar != -2)
              os << "  }\n  { rank = sink;\n";

            unsigned t = bdd_get_terminal(n);
            unsigned state = t;
            if (auto it = terminal_to_state_map.find(t);
                it != terminal_to_state_map.end())
              state = it->second;

            os << "    B" << n.id()
               << " [shape=box, style=\"filled,rounded";
            if (state >= ns)
              os << ",dashed";
            os << "\", fillcolor=\"";
            if (auto it = highlight_nodes.find(n.id());
                it != highlight_nodes.end())
              os << palette[it->second % palette_mod];
            else
              os << "#ffe5f1";
            os << "\", label=<";
            if (opt_labels && state < namesz)
              escape_html(os, str_psl(names[state]));
            else
              os << state;
            if (state < colorsz)
              {
                os << "<br/>";
                for (auto v: colors[state].sets())
                  outset(os, v);
              }
            os << ">, tooltip=\"bdd(" << n.id()
               << ")=term(" << t << ")=[" << state << "]\"";
            os << "];\n";
            oldvar = -2;
            continue;
          }
        int var = bdd_var(n);
        if (var != oldvar)
          {
            os << "  }\n  { rank = same;\n";
            oldvar = var;
          }
        std::string label;

        if (formula f = dict_->ap_from_var(var))
          label = escape_str(str_psl(f));
        else
          label = "var" + std::to_string(var);

        bool outputnode = (!controllable.empty()
                           && controllable.contains(var));
        const char* shape = outputnode ? "diamond" : "circle";

        os << "    B" << n.id() << " [shape=" << shape
           << ", style=filled, fillcolor=\"";
        if (auto it = highlight_nodes.find(n.id());
            it != highlight_nodes.end())
          os << palette[it->second % palette_mod];
        else
          os << "#ffffff";
        os << "\", label=\"" << label
           << "\", tooltip=\"bdd(" << n.id() << ")\"];\n";

        bdd low = bdd_low(n);
        bdd high = bdd_high(n);
        if (seen.insert(low.id()).second)
          {
            nodes.push_back(low);
            std::push_heap(nodes.begin(), nodes.end(), bylvl);
          }
        if (seen.insert(high.id()).second)
          {
            nodes.push_back(high);
            std::push_heap(nodes.begin(), nodes.end(), bylvl);
          }
        edges << "  B" << n.id() << " -> B" << low.id()
              << " [style=dotted, tooltip=\"" << label
              << "=0\"];\n  B" << n.id()
              << " -> B" << high.id() << " [style=filled, tooltip=\""
              << label << "=1\"];\n";
      }

    os << "  }\n";

    if (opt_scc)
      {
        for (unsigned i = 0; i < ns; ++i)
          {
            bdd tmp = bdd_terminal(i);
            if (auto it = scc_map.find(tmp.id()); it != scc_map.end())
              {
                // We have a non-trivial SCC, print it.
                auto it2 = scc_txt.find(it->second);
                if (it2 == scc_txt.end()) // already printed, or trivial SCC
                  continue;
                os << "  subgraph cluster_" << sccs[i]
                   << " {\n    color=gray\n    label=\"\"\n   "
                   << it2->second.str() << "\n  }\n";
                // remove this entry from scc_txt so we do not reprint it
                scc_txt.erase(it2);
              }
          }
      }
    os << edges.str();
    os << "}\n";
    return os;
  }

  mtdswa_ptr dtwa_to_mtdswa(const twa_graph_ptr& twa)
  {
    if (!is_deterministic(twa))
      throw std::runtime_error("dtwa_to_mtdswa: input is not deterministic");
    if (!twa->prop_state_acc())
      throw std::runtime_error
        ("dtwa_to_mtdswa: input does not have state-based acceptance");

    mtdswa_ptr dfa = std::make_shared<mtdswa>(twa->get_dict());
    dfa->get_dict()->register_all_propositions_of(twa, dfa);
    unsigned n = twa->num_states();
    unsigned init = twa->get_init_state_number();

    acc_cond acc = twa->acc();

    // twa's state i should be named remap[i] in dfa.  The remaping is
    // needed because
    //  (1) the swa only accepts 0 as initial state, and
    //  (2) we do not want to represent sink states.
    std::vector<unsigned> remap;
    remap.reserve(n);
    unsigned next = 1;
    for (unsigned i = 0; i < n; ++i)
      {
        // Is it a sink?
        bool sink = false;
        for (auto& e: twa->out(i))
          if (e.dst == i && acc.accepting(e.acc) && e.cond == bddtrue)
            {
              sink = true;
              break;
            }
        if (sink)
          {
            remap.push_back(-1U);
            continue;
          }
        if (i == init)
          remap.push_back(0);
        else
          remap.push_back(next++);
      }

    dfa->states.resize(next);
    dfa->colors.resize(next);

    for (unsigned i = 0; i < n; ++i)
      {
        unsigned state = remap[i];
        if (state == -1U) // skip sink states except initial
          {
            if (i == init)
              state = 0;
            else
              continue;
          }
        bdd b = bddfalse;
        for (auto& e: twa->out(i))
          {
            unsigned dst = remap[e.dst];
            if (dst == -1U)   // sink
              b |= e.cond;
            else
              b |= e.cond & bdd_terminal(dst);
          }
        dfa->states[state] = b;
        dfa->colors[state] = twa->state_acc_sets(i);
      }
    dfa->acc = acc;
    return dfa;
  }

  std::vector<int> scc_vector(const mtdswa_ptr& aut)
  {
    auto identity = [] (int x) { return x; };
    return bdd_mt_sccs(aut->states, identity);
  }


  std::vector<unsigned> loding_weak_ranking(const mtdswa_ptr& aut,
                                            bool fix)
  {
    std::vector<int> scc_of_state = scc_vector(aut);

    // Reorder the states, so that they appear in increasing order of
    // SCCs.  This is done in linear time using an implementation
    // similar to counting sort.

    int scc_count = *std::max_element(scc_of_state.begin(),
                                      scc_of_state.end()) + 1;
    std::vector<int> scc_index(scc_count + 1, 0);
    for (int scc: scc_of_state)
      ++scc_index[scc];
    int max_scc_size = scc_index[0];
    for (int scc = 1; scc < scc_count; ++scc)
      {
        max_scc_size = std::max(max_scc_size, scc_index[scc]);
        scc_index[scc] += scc_index[scc - 1];
      }
    unsigned ns = scc_of_state.size();
    scc_index[scc_count] = ns;
    assert(ns == (unsigned)scc_index[scc_count - 1]);
    std::vector<int> ordered_states(ns, 0);
    for (unsigned s = 0; s < ns; ++s)
      ordered_states[--scc_index[scc_of_state[s]]] = s;

    // At this point, ordered_states contains the state
    // in the desired order, and scc_index[i] has the first state of
    // SCC #i, and SCC #i has size scc_index[i+1] - scc_index[i].

    // ---

    // Now, compute the rank of each SCC using Löding coloring
    // function.  bddfalse, and bddtrue, which do not appear in the
    // SCC, are assumed to have rank 0 and 1 respectively.  Odd ranks
    // represent accepting SCCs, and even ranks are for rejecting
    // SCCs.   Each SCC should try to use the maximum rank of its
    // successors, possibly incremented by one if needed to match
    // its acceptance status.  Transient SCCs, which can be considered
    // as accepting or not,
    std::vector<unsigned> scc_rank;
    scc_rank.reserve(scc_count);
    std::vector<bdd> cur_scc_states;
    cur_scc_states.reserve(max_scc_size);
    for (int scc = 0; scc < scc_count; ++scc)
      {
        int begin = scc_index[scc];
        int end = scc_index[scc + 1];
        for (int idx = begin; idx < end; ++idx)
          cur_scc_states.push_back(aut->states[ordered_states[idx]]);
        unsigned max_rank = 0;
        bool transient = true; // assume transient SCC unless proven otherwise
        for (auto& b: leaves_of(cur_scc_states))
          {
            if (b == bddfalse)
              {
                // max_rank = std::max(max_rank, 0); // is a no-op
                continue;
              }
            if (b == bddtrue)
              {
                max_rank = std::max(max_rank, 1U);
                continue;
              }
            int dst = bdd_get_terminal(b);
            int dst_scc = scc_of_state[dst];
            assert(dst_scc <= scc);
            if (dst_scc == scc)
              {
                transient = false;
                continue;
              }
            max_rank = std::max(max_rank, scc_rank[dst_scc]);
          }
        cur_scc_states.clear();
        if (!transient)
          {
            // Check if the first state of the SCC is accepting.
            // All states in the SCC should have the same colors.
            bool is_accepting =
              aut->acc.accepting(aut->colors[ordered_states[begin]]);
            // Increment the rank if the acceptance if this SCC does
            // not match the acceptance of the rank.
            if ((max_rank & 1) != is_accepting)
              ++max_rank;
          }
        scc_rank.push_back(max_rank);
      }
    std::vector<unsigned> state_rank;
    state_rank.reserve(ns);
    for (unsigned s = 0; s < ns; ++s)
      state_rank.push_back(scc_rank[scc_of_state[s]]);

    if (fix)
      {
        acc_cond::mark_t accmark{};
        acc_cond::mark_t rejmark{};
        if (aut->acc.is_co_buchi())
          {
            rejmark.set(0);
          }
        else if (aut->acc.is_buchi())
          {
            accmark.set(0);
          }
        else
          {
            aut->acc = acc_cond::acc_code::buchi();
            accmark.set(0);
          }
        for (unsigned s = 0; s < ns; ++s)
          aut->colors[s] = (state_rank[s] & 1) ? accmark : rejmark;
      }
    return state_rank;
  }

  simple_ltl_translator::simple_ltl_translator(const bdd_dict_ptr& dict,
                                               bool simplify_terms)
    : dict_(dict), simplify_terms_(simplify_terms)
  {
    bdd_extcache_init(&cache_, -4, true);

    int_to_formula_.reserve(32);
  }

  simple_ltl_translator::~simple_ltl_translator()
  {
    bdd_extcache_done(&cache_);
    dict_->unregister_all_my_variables(this);
  }

  namespace
  {
    // A top-level operator that is weak (G, R, W) is accepting (true)
    // A top-level operator that is strong (F, M, U) is rejecting (false);
    // X(f) is accepting iff f is accepting.
    // Boolean operators follow boolean rules.
    bool obligation_is_accepting(formula f)
    {
      // Δ₀ do not contribute anything useful to the acceptance of the
      // formula, they only yield trivial SCCs.  Except true and
      // false, they can be considered jokers, from the point of view
      // of acceptance.
      auto is_delta0 = [](formula f)
      {
        return f.is_syntactic_safety() && f.is_syntactic_guarantee();
      };

      // Shortcut any potential recursion on formulas that are already
      // known to be safety or guarantee.
      if (f.is_tt())
        return true;
      if (f.is_syntactic_guarantee()) // includes false
        return false;
      if (f.is_syntactic_safety())
        return true;

      switch (f.kind())
        {
        case op::tt:
          SPOT_UNREACHABLE();
          return true;
        case op::ap:            // can return false or true
        case op::ff:
          SPOT_UNREACHABLE();
          return false;
        case op::Not:
          return !obligation_is_accepting(f[0]);
        case op::And:
          for (const formula& sub: f)
            {
              if (is_delta0(sub))
                continue;
              if (!obligation_is_accepting(sub))
                return false;
            }
          return true;
        case op::Or:
          for (const formula& sub: f)
            {
              // ignore Δ₀ formulas
              if (is_delta0(sub))
                continue;
              if (obligation_is_accepting(sub))
                return true;
            }
          return false;
        case op::Xor:
          {
            formula left = f[0];
            formula right = f[1];
            if (is_delta0(left) || is_delta0(right))
              return true;
            return
              obligation_is_accepting(left) != obligation_is_accepting(right);
          }
        case op::Implies:
          {
            // if an operand is Δ₀ set its acceptance in a way that it
            // does not contribute to the final acceptance.
            formula left = f[0];
            formula right = f[1];
            bool lacc = is_delta0(left) ?
              true : obligation_is_accepting(left);
            bool racc = is_delta0(right) ?
              false : obligation_is_accepting(right);
            return !lacc || racc;
          }
        case op::Equiv:
          {
            formula left = f[0];
            formula right = f[1];
            if (is_delta0(left) || is_delta0(right))
              return true;
            return
              obligation_is_accepting(left) == obligation_is_accepting(right);
          }
        case op::X:
        case op::strong_X:
          return obligation_is_accepting(f[0]);
        case op::U:
        case op::F:
        case op::M:
          return false;
        case op::W:
        case op::R:
        case op::G:
          return true;
        case op::eword:
        case op::AndNLM:
        case op::AndRat:
        case op::Closure:
        case op::Concat:
        case op::UConcat:
        case op::EConcat:
        case op::EConcatMarked:
        case op::first_match:
        case op::FStar:
        case op::Fusion:
        case op::NegClosure:
        case op::NegClosureMarked:
        case op::OrRat:
        case op::Star:
        case op::exists:
        case op::forall:
          // These are not supported by the translator.
          throw
            std::runtime_error("obligation_is_accepting: unsupported operator");
        }
      SPOT_UNREACHABLE();
      return false;
    }

    // bool is_temporal(formula f)
    // {
    //   switch (f.kind())
    //     {
    //     case op::ff:
    //     case op::tt:
    //     case op::ap:
    //     case op::Not:
    //     case op::Xor:
    //     case op::Implies:
    //     case op::Equiv:
    //     case op::And:
    //     case op::Or:
    //       return false;
    //     default:
    //       return true;
    //     }
    // }

    // bool has_dup_temporal_subformulas(formula f, formula g)
    // {
    //   robin_hood::unordered_set<formula> seen_in_f;
    //   f.traverse([&seen_in_f](formula sub) {
    //     seen_in_f.emplace(sub);
    //     return is_temporal(sub);
    //   });
    //   bool dup = false;
    //   g.traverse([&seen_in_f, &dup](formula sub) {
    //     if (dup)
    //       return true;
    //     if (seen_in_f.find(sub) != seen_in_f.end())
    //       {
    //         dup = true;
    //         return true;
    //       }
    //     return is_temporal(sub);
    //   });
    //   return dup;
    // }
  }


  // Convert the formula at a given level to a BDD suitable for
  // propositional equivalence.  Any subformula that has a non-boolean
  // operator is replaced by atomic proposition, but X are traversed
  // so that we get the effect of calling distribute_next() without
  // calling it.
  bdd simple_ltl_translator::propeq_encode(formula f, int level)
  {
    auto encode_new = [&] (formula f) -> bdd
    {
      switch (f.kind())
        {
        case op::tt:
          return bddtrue;
        case op::ff:
          return bddfalse;
        case op::ap:
          if (level == 0)
            return bdd_ithvar(dict_->register_proposition(f, this));
          else
            return bdd_ithvar(dict_->register_anonymous_variables(1, this));
        case op::Not:
          if (f[0].is_leaf())   // skip one application of bdd_not.
            {
              if (f[0].is_tt())
                return bddfalse;
              if (f[0].is_ff())
                return bddtrue;
              if (level == 0)
                return bdd_nithvar(dict_->register_proposition(f[0], this));
              else
                return bdd_nithvar(dict_->register_anonymous_variables(1,
                                                                       this));
            }
          return bdd_not(propeq_encode(f[0], level));
        case op::And:
          {
            bdd res = bddtrue;
            for (const formula& sub: f)
              res &= propeq_encode(sub, level);
            return res;
          }
        case op::Or:
          {
            bdd res = bddfalse;
            for (const formula& sub: f)
              res |= propeq_encode(sub, level);
            return res;
          }
        case op::Xor:
          {
            bdd left = propeq_encode(f[0], level);
            return left ^ propeq_encode(f[1], level);
          }
        case op::Implies:
          {
            bdd left = propeq_encode(f[0], level);
            return left >> propeq_encode(f[1], level);
          }
        case op::Equiv:
          {
            bdd left = propeq_encode(f[0], level);
            return bdd_biimp(left, propeq_encode(f[1], level));
          }
        case op::X:
        case op::strong_X:
          SPOT_UNREACHABLE();
        default:
          // For any temporal operator (not X), create a BDD variable.
          // The variable represents this formula at this specific level
          return bdd_ithvar(dict_->register_anonymous_variables(1, this));
        }
    };

    // Process X operators by incrementing level instead of
    // distributing if multiple X are nested, let's just go through
    // them all, to reduce the entries in propositional_equiv_bdd_.
    while (f.is(op::X, op::strong_X))
      {
        f = f[0];
        ++level;
      }

    formula_level_pair flp = {f, level};
    if (auto it = propositional_equiv_bdd_.find(flp);
        it != propositional_equiv_bdd_.end())
      return it->second;
    // We cannot insert into the map while doing the search
    // above, because the iterator would be invalidated by
    // other insertions performed in encode_new.
    bdd b = encode_new(f);
    return propositional_equiv_bdd_[flp] = b;
  }

  // This implement propositional equivalence plus some very light
  // simplifications
  formula simple_ltl_translator::propeq_representative(formula f, bool isacc)
  {
    // We start with the simplifications
  again:
    switch (f.kind())
      {
      case op::And:
        {
          if (!simplify_terms_)
            break;
          // The following cheap simplifications avoid creating
          // unnecessary terminals that will eventually be found
          // to be equivalent.
          //
          // (α M β) ∧ β ≡ (α M β)
          // (α R β) ∧ β ≡ (α R β)
          // Gα ∧ α ≡ Gα
          robin_hood::unordered_set<formula> removable;
          for (const formula& sub: f)
            if (sub.is(op::M) || sub.is(op::R))
              removable.insert(sub[1]);
            else if (sub.is(op::G))
              removable.insert(sub[0]);
          if (removable.empty())
            break;
          std::vector<formula> vec;
          for (const formula& sub: f)
            if (!removable.contains(sub))
              vec.push_back(sub);
          if (vec.size() == f.size())
            break;
          f = formula::And(std::move(vec));
          goto again;
          // Rules that are not implemented but for which I have
          // seen both sides of the equality during some translation:
          //
          //  α ∧ Fα ≡ α  (generalizes to α ∧ (β [UW∨] α) ≡ α).
          //  Gα ∧ (β ∨ α) ≡ Gα
          //  Fα ∨ (β ∧ α) ≡ Fα
          //
          // All of these can be seen as some type of unit-propagation.
          // See Issue #606.
        }
      case op::Or:
        {
          if (!simplify_terms_)
            break;
          // (α U β) ∨ β ≡ (α U β)
          // (α W β) ∨ β ≡ (α W β)
          // Fα ∨ α ≡ Fα
          robin_hood::unordered_set<formula> removable;
          for (const formula& sub: f)
            if (sub.is(op::U) || sub.is(op::W))
              removable.insert(sub[1]);
            else if (sub.is(op::F))
              removable.insert(sub[0]);
          if (removable.empty())
            break;
          std::vector<formula> vec;
          for (const formula& sub: f)
            if (!removable.contains(sub))
              vec.push_back(sub);
          if (vec.size() == f.size())
            break;
          f = formula::Or(std::move(vec));
          goto again;
        }
      case op::Not:
      case op::Xor:
      case op::Implies:
      case op::Equiv:
        break;
      default:
        // abort immediately if the top-level operator is not Boolean
        return f;
      }

    bdd enc = propeq_encode(f);  // Always start at level 0
    if (enc == bddtrue)
      f = formula::tt();
    else if (enc == bddfalse)
      f = formula::ff();
    auto [it, _] = propositional_equiv_[isacc].emplace(enc, f);
    (void) _;
    // std::cerr << f << " ≡ " << it->second << '\n';
    return it->second;
  }

  formula simple_ltl_translator::terminal_to_formula(int v) const
  {
    assert((unsigned) v < int_to_formula_.size());
    return int_to_formula_[v];
  }

  formula simple_ltl_translator::leaf_to_formula(int b, int v) const
  {
    if (b == 0)
      return formula::ff();
    if (b == 1)
      return formula::tt();
    return terminal_to_formula(v);
  }

  int simple_ltl_translator::formula_to_int(formula f)
  {
    if (auto it = formula_to_int_.find(f);
        it != formula_to_int_.end())
      return it->second;
    int v = int_to_formula_.size();
    int_to_formula_.push_back(f);
    formula_to_int_[f] = v;
    return v;
  }

  int simple_ltl_translator::formula_propeq_to_int(formula f)
  {
    std::unordered_map<formula, int>& propeq = propeq_to_int_;

    if (auto it = propeq.find(f); it != propeq.end())
      return it->second;

    formula g = propeq_representative(f, obligation_is_accepting(f));

    int v;
    auto it = formula_to_int_.find(g);
    if (it == formula_to_int_.end())
      {
        v = int_to_formula_.size();
        int_to_formula_.push_back(g);
        formula_to_int_[g] = v;
      }
    else
      {
        v = it->second;
      }
    propeq[g] = v;
    if (f != g)
      {
        formula_to_int_[f] = v;
        propeq[f] = v;
      }
    return v;
  }

  int simple_ltl_translator::formula_to_terminal(formula f)
  {
    return formula_to_int(f);
  }

  int simple_ltl_translator::formula_to_terminal_bdd_as_int(formula f)
  {
    if (SPOT_UNLIKELY(f.is_ff()))
      return 0;
    if (SPOT_UNLIKELY(f.is_tt()))
      return 1;
    int v = formula_to_int(f);
    return bdd_terminal_as_int(v);
  }

  int simple_ltl_translator::formula_propeq_to_terminal_bdd_as_int(formula f)
  {
    if (SPOT_UNLIKELY(f.is_ff()))
      return 0;
    if (SPOT_UNLIKELY(f.is_tt()))
      return 1;
    int v = formula_propeq_to_int(f);
    f = int_to_formula_[v];     // The formula might have been reduced to tt/ff.
    if (SPOT_UNLIKELY(f.is_ff()))
      return 0;
    if (SPOT_UNLIKELY(f.is_tt()))
      return 1;
    return bdd_terminal_as_int(v);
  }

  bdd simple_ltl_translator::formula_to_terminal_bdd(formula f)
  {
    return bdd_from_int(formula_to_terminal_bdd_as_int(f));
  }

  namespace
  {
    // For AND and OR, the callbacks will never been called with a constant
    // argument because those are simplified during the BDD operations.

    static simple_ltl_translator* term_combine_trans;
    static int term_combine_and(int, int left_term,
                                int, int right_term)
    {
      formula lf = term_combine_trans->terminal_to_formula(left_term);
      formula rf = term_combine_trans->terminal_to_formula(right_term);
      formula res = formula::And(lf, rf);
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_or(int, int left_term,
                               int, int right_term)
    {
      formula lf = term_combine_trans->terminal_to_formula(left_term);
      formula rf = term_combine_trans->terminal_to_formula(right_term);
      formula res = formula::Or(lf, rf);
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_implies(int, int left_term,
                                    int right, int right_term)
    {
      formula lf = term_combine_trans->terminal_to_formula(left_term);
      formula rf = term_combine_trans->leaf_to_formula(right, right_term);
      formula res = formula::Implies(lf, rf);
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_equiv(int left, int left_term,
                                  int right, int right_term)
    {
      formula lf = term_combine_trans->leaf_to_formula(left, left_term);
      formula rf = term_combine_trans->leaf_to_formula(right, right_term);
      formula res = formula::Equiv(lf, rf);
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_xor(int left, int left_term,
                                int right, int right_term)
    {
      formula lf = term_combine_trans->leaf_to_formula(left, left_term);
      formula rf =  term_combine_trans->leaf_to_formula(right, right_term);
      formula res = formula::Xor(lf, rf);
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_not(int left)
    {
      formula ll = term_combine_trans->terminal_to_formula(left);
      formula res = formula::Not(ll);
      return term_combine_trans->formula_to_terminal(res);
    }

    static int terminal_propeq(int root, int termval)
    {
      if (root == 0 || root == 1)
        return root;
      formula f = term_combine_trans->terminal_to_formula(termval);
      int res = term_combine_trans->formula_propeq_to_terminal_bdd_as_int(f);
      return res;
    }

  }

  bdd simple_ltl_translator::combine_and(bdd left, bdd right)
  {
    term_combine_trans = this;
    return bdd_mt_apply2_leaves(left, right,
                                term_combine_and, &cache_, hash_key_and,
                                bddop_and);
  }

  bdd simple_ltl_translator::combine_or(bdd left, bdd right)
  {
    term_combine_trans = this;
    return bdd_mt_apply2_leaves(left, right,
                                term_combine_or, &cache_, hash_key_or,
                                bddop_or);
  }

  bdd simple_ltl_translator::combine_implies(bdd left, bdd right)
  {
    term_combine_trans = this;
    return bdd_mt_apply2_leaves(left, right,
                                term_combine_implies, &cache_, hash_key_implies,
                                bddop_imp);
  }

  bdd simple_ltl_translator::combine_equiv(bdd left, bdd right)
  {
    term_combine_trans = this;
    return bdd_mt_apply2_leaves(left, right,
                                term_combine_equiv, &cache_, hash_key_equiv,
                                bddop_biimp);
  }

  bdd simple_ltl_translator::combine_xor(bdd left, bdd right)
  {
    term_combine_trans = this;
    return bdd_mt_apply2_leaves(left, right,
                                term_combine_xor, &cache_, hash_key_xor,
                                bddop_xor);
  }

  bdd simple_ltl_translator::combine_not(bdd left)
  {
    term_combine_trans = this;
    return bdd_mt_apply1(left, term_combine_not,
                         bddtrue, bddfalse,
                         &cache_, hash_key_not);
  }

  bdd simple_ltl_translator::ltl_to_mtbdd(formula f)
  {
    if (auto it = formula_to_bdd_.find(f); it != formula_to_bdd_.end())
      return it->second;

    bdd res = bddfalse;
    switch (f.kind())
      {
      case op::tt:
        res = bddtrue;
        break;
      case op::ff:
        res = bddfalse;
        break;
      case op::ap:
        res = bdd_ithvar(dict_->register_proposition(f, this));
        break;
      case op::Not:
        // For all purely Boolean subformulas, we want to use the
        // regular BDD operators, so that the cache entries are long
        // lived.
        if (f.is_boolean())
          res = !ltl_to_mtbdd(f[0]);
        else
          res = combine_not(ltl_to_mtbdd(f[0]));
        break;
      case op::Xor:
        {
          bdd left = ltl_to_mtbdd(f[0]);
          bdd right = ltl_to_mtbdd(f[1]);
          if (f.is_boolean())
            res = left ^ right;
          else
            res = combine_xor(left, right);
          break;
        }
      case op::Implies:
        {
          bdd left = ltl_to_mtbdd(f[0]);
          bdd right = ltl_to_mtbdd(f[1]);
          if (f.is_boolean())
            res = left >> right;
          else
            res = combine_implies(left, right);
          break;
        }
      case op::Equiv:
        {
          bdd left = ltl_to_mtbdd(f[0]);
          bdd right = ltl_to_mtbdd(f[1]);
          if (f.is_boolean())
            res = bdd_apply(left, right, bddop_biimp);
          else
            res = combine_equiv(left, right);
          break;
        }
      case op::eword:
      case op::AndNLM:
      case op::AndRat:
      case op::Closure:
      case op::Concat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::first_match:
      case op::FStar:
      case op::Fusion:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::OrRat:
      case op::Star:
      case op::UConcat:
      case op::exists:
      case op::forall:
        throw std::runtime_error("ltl_to_mtbdd: unsupported operator");
      case op::And:
        {
          unsigned n = f.size();
          res = ltl_to_mtbdd(f[0]);
          for (unsigned i = 1; i < n; ++i)
            res = combine_and(res, ltl_to_mtbdd(f[i]));
          break;
        }
      case op::Or:
        {
          unsigned n = f.size();
          res = ltl_to_mtbdd(f[0]);
          for (unsigned i = 1; i < n; ++i)
            res = combine_or(res, ltl_to_mtbdd(f[i]));
          break;
        }
      case op::X:
      case op::strong_X:
        res = formula_to_terminal_bdd(f[0]);
        break;
      case op::U:
      case op::W:
        {
          bdd f0 = ltl_to_mtbdd(f[0]);
          bdd f1 = ltl_to_mtbdd(f[1]);
          bdd term = formula_to_terminal_bdd(f);
          res = combine_or(f1, combine_and(f0, term));
          break;
        }
      case op::R:
      case op::M:
        {
          bdd f0 = ltl_to_mtbdd(f[0]);
          bdd f1 = ltl_to_mtbdd(f[1]);
          bdd term = formula_to_terminal_bdd(f);
          res = combine_and(f1, combine_or(f0, term));
          break;
        }
      case op::G:
        {
          bdd term = formula_to_terminal_bdd(f);
          res = combine_and(ltl_to_mtbdd(f[0]), term);
          break;
        }
      case op::F:
        {
          bdd term = formula_to_terminal_bdd(f);
          res = combine_or(ltl_to_mtbdd(f[0]), term);
          break;
        }
      }
    formula_to_bdd_[f] = res;
    return res;
  }

  namespace
  {
    static std::unordered_map<int, int> terminal_to_state_map;

    static int terminal_to_state(int terminal)
    {
#if NDEBUG
      int v = terminal_to_state_map[terminal];
#else
      int v = terminal_to_state_map.at(terminal);
#endif
      return v;
    }
  }

  namespace
  {
    struct backprop_bdd_encoder
    {
      backprop_graph backprop;
      robin_hood::unordered_map<int, unsigned> rootnum_to_backprop_state;
      robin_hood::unordered_map<int, unsigned> bdd_to_backprop_state;
      // only used if recompute_succ
      robin_hood::unordered_set<int> bdd_seen;

      backprop_bdd_encoder(bool stop_asap)
        : backprop(stop_asap)
      {
      }

      bool root_is_determined(unsigned root_number) const
      {
        auto it = rootnum_to_backprop_state.find(root_number);
        if (it == rootnum_to_backprop_state.end())
          return false;
        return backprop.is_determined(it->second);
      }

      bool root_winner(unsigned root_number) const
      {
        auto it = rootnum_to_backprop_state.find(root_number);
        assert(it != rootnum_to_backprop_state.end());
        return backprop.winner(it->second);
      }

      // ~backprop_bdd_encoder()
      // {
      //   std::cerr << "backprop graph had size: "
      //             << backprop.new_state(false) << '\n';
      // }

      bool root_winner_set_if_unknown(unsigned root_number, bool winner)
      {
        auto it = rootnum_to_backprop_state.find(root_number);
        assert(it != rootnum_to_backprop_state.end());
        if (backprop.is_determined(it->second))
          return false;
        else
          return backprop.set_winner(it->second, winner);
      }

      // This encodes an MTBDD-represented state into the
      // backpropagation graph (aka game arena)
      //
      // The state is specified by its root_number, and the MTBDD
      // encoding the successors.  Vertices of the game arena will be
      // created for all nodes, including terminals.  The terminal
      // corresponding to the root is created as well.
      //
      // For the purpose of debugging, a name may be passed.  It will
      // be attached to the root.
      //
      // As a side effect, the function will record the root numbers stored
      // on the terminals it reaches in new_rootnums or old_rootnums
      // depending on whether the corresponding vertex had to be created
      // in the game or if it was already existing.
      //
      // If recompute_succ is false, the encoding stops its
      // "recursion" whenever it finds a node that has already been
      // encoded into the game.  If it is true, it will continue the
      // recursion even through nodes that have already been encoded,
      // provided they correspond to undetermined vertices.  Doing
      // so allows to collect all undetermined successors even if
      // they were already encoded.  This is necessary for our DFS
      // construction.
      template<bool recompute_succ = false>
      bool encode_state(unsigned root_number, bdd mtbdd,
                        std::string* name = nullptr,
                        std::vector<int>* new_rootnums = nullptr,
                        std::vector<int>* old_rootnums = nullptr)
      {
        if constexpr (recompute_succ)
          bdd_seen.clear();
        // hold (backprop state, low bdd, high bdd)
        std::deque<std::tuple<unsigned, int, int>> todo;

        auto rootnum_to_state = [&] (int t) -> unsigned
        {
          auto [it, is_new] = rootnum_to_backprop_state.emplace(t, 0);
          if (is_new)
            {
              // owner does not matter, because this state will have only
              // one successor.
              it->second = backprop.new_state(false);
              if (new_rootnums)
                new_rootnums->push_back(t);
            }
          else if (old_rootnums)
            old_rootnums->push_back(t);
          return it->second;
        };

        auto bdd_to_state = [&] (int b) -> unsigned
        {
          auto [it, is_new] = bdd_to_backprop_state.emplace(b, 0);
          if (!is_new)
            {
              if (!recompute_succ || b == 0 || b == 1)
                return it->second;
            }
          if (b == 0 || b == 1)
            {
              unsigned s = backprop.new_state(!b);
              it->second = s;
              backprop.set_winner(s, b);
              if (name)
                backprop.set_name(s, b ? "true" : "false");
              return s;
            }
          if constexpr (recompute_succ)
            {
              // Make sure we see each node only once per call to
              // encode_state.
              if (!bdd_seen.emplace(b).second)
                return it->second;
            }
          if (bdd_is_terminal(b))
            {
              int term = bdd_get_terminal(b);
              if constexpr (recompute_succ)
                if (!is_new)
                  return rootnum_to_state(term);
              return it->second = rootnum_to_state(term);
            }
          // We have to continue even if the node is determined, or our DFS
          // would be wrong.
          //if constexpr (recompute_succ)
          //  if (!is_new && backprop.is_determined(it->second))
          //    return it->second;
          auto [owner, low, high] = bdd_mt_quantified_low_high(b);
          if constexpr (recompute_succ)
            if (!is_new)
              {
                todo.emplace_back(it->second, low, high);
                return it->second;
              }
          unsigned s = backprop.new_state(owner);
          it->second = s;
          todo.emplace_back(s, low, high);
          return s;
        };

        // create one state for the root number, if it does not exist yet.
        // we do note use rootnum_to_state, because we do not want to update
        // the new_rootnums and old_rootnums vectors.
        auto [it, is_new] = rootnum_to_backprop_state.emplace(root_number, 0);
        if (is_new)
          // owner does not matter, because this state will have only
          // one successor.
          it->second = backprop.new_state(false);
        unsigned root_state = it->second;

        if (name)
          backprop.set_name(root_state, *name);
        // std::cerr << "encoding term " << root_number
        //           << " on vertex " << root_state << '\n';

        // link it to the actual BDD root, as the only child
        if (backprop.new_edge(root_state, bdd_to_state(mtbdd.id())))
          return true;
        if (backprop.freeze_state(root_state))
          return true;

        // now encode all that BDD, when they reach terminal, this
        // will create "root number" nodes for those, and those can
        // later be connected to their BDD encoding once we know it.
        while (!todo.empty())
          {
            auto [state, low, high] = todo.front();
            todo.pop_front();
            if constexpr (recompute_succ)
              if (backprop.is_frozen(state))
                {
                  //assert(!backprop.is_determined(state));
                  bdd_to_state(low);
                  bdd_to_state(high);
                  continue;
                }
            // We could encode high before low if we wanted.  That
            // makes sense if we know that a state for high already
            // exists and is determined.  However, deciding this is an
            // extra hash lookup, so this is unlikely to be worth it.
            unsigned low_state = bdd_to_state(low);
            if (backprop.new_edge(state, low_state))
              return true;
            if constexpr (!recompute_succ)
              // If the previous edge determined the source state, no
              // need to process the other branch.
              if (backprop.is_determined(state))
                continue;
            unsigned high_state = bdd_to_state(high);
            if (backprop.new_edge(state, high_state))
              return true;
            if (backprop.freeze_state(state))
              return true;
          }
        return false;
      }

      int get_choice(int node)
      {
        //assert(it != bdd_to_backprop_state.end());
        //assert(backprop.is_determined(it->second));
        auto it = bdd_to_backprop_state.find(node);
        if ((it == bdd_to_backprop_state.end())
            || !backprop.winner(it->second))
          return 0;
        unsigned ch = backprop.choice(it->second);
        //if (ch == -1U)
        //  std::cerr << "choice is target!\n";
        int lowid = bdd_low(node);
        auto it2 = bdd_to_backprop_state.find(lowid);
        assert(it2 != bdd_to_backprop_state.end());
        if (it2->second == ch)
          return lowid;
        int highid = bdd_high(node);
#ifndef NDEBUG
        auto it3 = bdd_to_backprop_state.find(highid);
        assert(it3 != bdd_to_backprop_state.end());
        assert(it3->second == ch);
#endif
        return highid;
      }
    };

    static backprop_bdd_encoder* global_backprop = nullptr;

    static int strategy_choice(int bddid)
    {
      return global_backprop->get_choice(bddid);
    }

    static int strategy_map_finalize(int* root_ptr, int term)
    {
      //if (!global_backprop->root_is_determined(term))
      //  std::cerr << term << " NOT DETERMINED!\n";
      // replace losing terminals by bddfalse
      if (!global_backprop->root_winner(term))
        {
          *root_ptr = 0;
          return 0;
        }
      // keep winning terminals, just replace them by their state
      // number
#if NDEBUG
      int v = terminal_to_state_map[term];
#else
      int v = terminal_to_state_map.at(term);
#endif
      if (v != term)
        *root_ptr = bdd_terminal_as_int(v);
      return 1;
    }

    static int term_id(int x)
    {
      return x;
    }
  }


  // This is the main translation function.
  mtdswa_ptr
  simple_ltl_translator::ltl_to_mtdswa(formula f,
                                       bool fuse_same_bdds)
  {
    mtdswa_ptr dfa = std::make_shared<mtdswa>(dict_);
    // the fist int is the bdd's id, complemented if the formula is accepting.
    robin_hood::unordered_map<int, int> bdd_to_state;
    robin_hood::unordered_map<formula, int> formula_to_state;
    std::vector<bdd> states;
    std::vector<formula> names;
    std::deque<formula> todo;
    terminal_to_state_map.clear();

    // Each entry is (existential_vars, universal_vars), with the outermost
    // quantifier block first.  For a purely existential block, universal_vars
    // is bddtrue; for a purely universal block, existential_vars is bddtrue.
    // After building the initial list, consecutive blocks are merged when all
    // BDD variable levels of the outer block are smaller than those of the
    // inner block; bdd_mt_quantify2 then handles both quantification types in
    // a single pass.  Un-merged blocks pass bddtrue for the inactive side,
    // making bdd_mt_quantify2 behave as a single-type quantification with no
    // assumption on relative variable ordering.
    std::vector<std::pair<bdd, bdd>> quantifier_blocks;
    bool is_quantified = false;

    // Keep track of atomic propositions used in the automaton.
    // Actually, the automaton might use fewer atomic propositions
    // than what appears in the formula, but we do not pay attention
    // to that.
    {
      f = normalize_quantifiers(f);

      atomic_prop_set* a = atomic_prop_collect(f);
      dfa->aps.reserve(a->size());

      // Peel quantifier blocks from outermost to innermost, building
      // one (existential_vars, universal_vars) entry per block in
      // quantifier_blocks.  Variable registration order within each block
      // follows the order in which the variables appear in the formula body.
      if (f.is_quantified())
        {
          is_quantified = true;
          std::vector<unsigned char> inblock;
          while (f.is(op::exists, op::forall))
            {
              bool is_exists = f.is(op::exists);
              bdd block_vars = bddtrue;

              inblock.clear();
              inblock.resize(formula::apid_count(), 0U);
              unsigned last = f.size() - 1;
              for (unsigned i = 0; i < last; ++i)
                inblock[f[i].apid()] = 1;

              f.traverse([&](const spot::formula& g)
              {
                if (!g.is(spot::op::ap))
                  return false;
                unsigned id = g.apid();
                if (inblock[id] && a->erase(g))
                  block_vars &= bdd_ithvar(dict_->register_proposition(g, dfa));
                return false;
              });
              if (is_exists)
                quantifier_blocks.emplace_back(block_vars, bddtrue);
              else
                quantifier_blocks.emplace_back(bddtrue, block_vars);
              f = f[last];
            }
        }
      // Anything left in a are unquantified APs.
      dfa->aps.insert(dfa->aps.end(), a->begin(), a->end());
      delete a;

      // Merge consecutive quantifier blocks when the BDD variable indices of
      // the outer block are all strictly smaller than those of the inner block.
      // Such merged blocks can be handled by bdd_mt_quantify2 in a single pass.
      if (quantifier_blocks.size() > 1)
        {
          // Return the largest BDD level in a set, or -1 if bddtrue.
          auto max_set_level = [](bdd set) -> int
          {
            int v = -1;
            for (bdd b = set; b != bddtrue; b = bdd_high(b))
              v = bdd_level(b);
            return v;
          };

          size_t i = 0;
          while (i + 1 < quantifier_blocks.size())
            {
              auto& [e0, u0] = quantifier_blocks[i];
              auto& [e1, u1] = quantifier_blocks[i + 1];
              int max0 = std::max(max_set_level(e0), max_set_level(u0));
              // Set BDDs are ordered: the root holds the smallest level.
              int min1 = std::min(e1 != bddtrue ? bdd_level(e1) : INT_MAX,
                                  u1 != bddtrue ? bdd_level(u1) : INT_MAX);
              if (max0 < min1)
                {
                  e0 &= e1;
                  u0 &= u1;
                  quantifier_blocks.erase(quantifier_blocks.begin() + i + 1);
                  // Re-check block i against the new block i+1.
                }
              else
                ++i;
            }
        }
    }

    // We are going to build a Büchi automaton.
    dfa->acc = acc_cond::acc_code::buchi();
    acc_cond::mark_t acc_mark{0};
    acc_cond::mark_t rej_mark{};
    std::vector<acc_cond::mark_t> colors;

    term_combine_trans = this;

    // Keep track of whether we have seen an accepting or rejecting
    // state.  If we are missing one of them, we can reduce the
    // automaton to a single state.
    //bool has_accepting = false;
    //bool has_rejecting = false;

    todo.push_back(f);
    do
      {
        formula label= todo.front();
        todo.pop_front();

        int label_term = formula_to_terminal(label);

        // already processed
        if (terminal_to_state_map.find(label_term)
            != terminal_to_state_map.end())
          continue;

        bdd b = ltl_to_mtbdd(label);
        if (is_quantified)
          // Apply quantifier blocks from innermost to outermost using
          // bdd_mt_quantify2.  For un-merged blocks, one of
          // exists_vars or forall_vars is bddtrue (no-op for that
          // quantification type).  For merged blocks both are
          // non-bddtrue; bdd_mt_quantify2 handles both quantification
          // types in one pass, which is valid because the merge
          // condition guarantees that all outer-block variable levels
          // are below those of the inner block.
          for (int qi = quantifier_blocks.size() - 1; qi >= 0; --qi)
            {
              auto [exists_vars, forall_vars] = quantifier_blocks[qi];
              bdd_mt_quantify_prepare(bddtrue, exists_vars, forall_vars);
              b = bdd_mt_quantify2(b, term_id,
                                   term_combine_or, term_combine_and,
                                   &cache_,
                                   hash_key_quantify,
                                   hash_key_or, bddop_or,
                                   hash_key_and, bddop_and);
            }
        // propositional equivalence on all terminals.
        b = bdd_mt_apply1_leaves(b, terminal_propeq, &cache_, hash_key_propeq);

        int key = b.id();
        bool accepting = obligation_is_accepting(label);
        if (accepting)
          key = ~key;

        if (fuse_same_bdds)
          if (auto it = bdd_to_state.find(key); it != bdd_to_state.end())
            {
              formula_to_state[label] = it->second;
              terminal_to_state_map[label_term] = it->second;
              continue;
            }
        unsigned n = states.size();
        formula_to_state[label] = n;
        if (fuse_same_bdds)
          bdd_to_state[key] = n;
        states.push_back(b);
        names.push_back(label);
        colors.push_back(accepting ? acc_mark : rej_mark);
        terminal_to_state_map[label_term] = n;

        for (bdd leaf: leaves_of(b))
          {
            if (leaf == bddfalse)
              {
                //has_rejecting = true;
                continue;
              }
            if (leaf == bddtrue)
              {
                //has_accepting = true;
                continue;
              }
            int term = bdd_get_terminal(leaf);
            if (terminal_to_state_map.find(term)
                == terminal_to_state_map.end())
              todo.push_back(terminal_to_formula(term));
          }
      }
    while (!todo.empty());

    // Currently, state[i] contains a bdd representing outgoing
    // transitions from state i, however the terminal values represent
    // formulas.  We need to remap the terminal values to state values.
    unsigned sz = states.size();
    for (unsigned i = 0; i < sz; ++i)
      states[i] = bdd_mt_apply1(states[i], terminal_to_state,
                                bddfalse, bddtrue,
                                &cache_, hash_key_rename);

    dfa->states = std::move(states);
    dfa->names = std::move(names);
    dfa->colors = std::move(colors);
    dict_->register_all_propositions_of(this, dfa);
    for (auto& [exists_vars, forall_vars] : quantifier_blocks)
      {
        for (bdd b = exists_vars; b != bddtrue; b = bdd_high(b))
          dict_->unregister_variable(bdd_var(b), dfa);
        for (bdd b = forall_vars; b != bddtrue; b = bdd_high(b))
          dict_->unregister_variable(bdd_var(b), dfa);
      }
    return dfa;
  }

  mtdswa_ptr
  simple_ltl_translator::ltl_to_mtdswa_synthesis
  (formula f, const std::vector<std::string>& outvars,
   bool realizability, int debug)
  {
    mtdswa_ptr dfa = std::make_shared<mtdswa>(dict_);

    robin_hood::unordered_map<formula, int> formula_to_state;
    std::vector<bdd> states;
    std::vector<formula> names;

    // data structure for DFS with SCC enumeration
    std::deque<int> todo;       // stack of MTBDD root numbers
    // The LIVE stack contains all states that belong to SCC that
    // interesect the DFS path.  The states of the current SCC are
    // necessarily at the top of the LIVE stack, so whenever we
    // backtrack from an SCC, we can easily pop all its states from
    // this stack.
    std::deque<int> live_states;
    // An entry (state, size) in prev indicates that
    // when todo.size() == size, we have processed
    // all successors of state and should backtrack;
    std::deque<std::pair<int, unsigned>> prev;
    /// Current view of the stack of SCCs, as a list of root numbers.
    std::deque<unsigned> scc_roots;

    // To be passed to the game encoder function.
    std::vector<int> new_rootnums;
    std::vector<int> old_rootnums;

    backprop_bdd_encoder backprop(realizability);
    global_backprop = &backprop;

    terminal_to_state_map.clear();

    bdd forallvars = bddtrue;
    bdd existsvars = bddtrue;
    bdd bddoutvars = bddtrue;   // used if outvars was passed;
    // this is the number of variables we had the last time
    // we called bdd_mt_quantify_prepare().
    int varnum = 0;

    auto quantify_prepare_maybe = [&] {
      // Everytime a new BDD variable is created, the quantification
      // buffer is wiped out.  Adding variables can happen as a
      // side-effect of ltlf_to_mtbdd().  As a consequence, we have to
      // call bdd_mt_quantify_prepare() when the number of BDD
      // variables changed.
      if (int vn = bdd_varnum(); vn != varnum)
        {
          bdd_mt_quantify_prepare(bddoutvars, forallvars, existsvars);
          varnum = vn;
        }
    };

    bool is_quantified = false;

    // Keep track of atomic propositions used in the automaton.
    // Actually, the automaton might use fewer atomic propositions
    // than what appears in the formula, but we do not pay attention
    // to that.
    {
      f = normalize_quantifiers(f);

      atomic_prop_set* a = atomic_prop_collect(f);
      dfa->aps.reserve(a->size());

      if (!outvars.empty())
        {
          // We need to register (unquantified) output variables
          // already so we can call bdd_mt_quantify_prepare.  Let's do
          // it in the order in which they will be discovered in the
          // formula.
          std::vector<unsigned char> quantified = collect_quantified_apids(f);
          std::vector<unsigned char> outputs;
          outputs.resize(formula::apid_count(), 0U);
          for (const std::string& s: outvars)
            outputs[spot::formula::ap(s).apid()] = 1U;

          f.traverse([&](const spot::formula& g)
          {
            if (!g.is(spot::op::ap))
              return false;
            unsigned id = g.apid();
            if (outputs[id] && !quantified[id] && a->erase(g))
              {
                dfa->aps.push_back(g);
                int i = dict_->register_proposition(g, dfa);
                bddoutvars &= bdd_ithvar(i);
              }
            return false;
          });
          dfa->set_controllable_variables(bddoutvars);
        }
      // Declare quantified variables in the order of the quantifiers.
      // But inside each block, register the variables in the order
      // they are found in the formula.
      if (f.is_quantified())
        {
          is_quantified = true;
          std::vector<unsigned char> inblock;
          int max_level_of_last_block = -1;
          while (f.is(op::exists, op::forall))
            {
              bool is_exists = f.is(op::exists);

              inblock.clear();
              inblock.resize(formula::apid_count(), 0U);
              unsigned last = f.size() - 1;
              for (unsigned i = 0; i < last; ++i)
                inblock[f[i].apid()] = 1;

              int max_level_of_current_block = -1;
              f.traverse([&](const spot::formula& g)
              {
                if (!g.is(spot::op::ap))
                  return false;
                unsigned id = g.apid();
                if (inblock[id] && a->erase(g))
                  {
                    bdd bi = bdd_ithvar(dict_->register_proposition(g, dfa));
                    int lvl = bdd_level(bi);
                    if (lvl > max_level_of_current_block)
                      max_level_of_current_block = lvl;
                    if (lvl < max_level_of_last_block)
                      // The variables in one quantified block should all
                      // have a level greater than the variables in the previous
                      // block for bdd_mt_quantify2 to work.
                      throw std::runtime_error("quantified variable was "
                                               "already registered with an "
                                               "incompatible level");
                    if (is_exists)
                      existsvars &= bi;
                    else
                      forallvars &= bi;
                  }
                return false;
              });
              f = f[last];
              max_level_of_last_block = max_level_of_current_block;
            }
        }
      // Anything left in a are input
      dfa->aps.insert(dfa->aps.end(), a->begin(), a->end());
      delete a;
    }

    auto trans_succ = [&](formula g) -> bdd {
      bdd b = ltl_to_mtbdd(g);
      if (is_quantified)
        {
          quantify_prepare_maybe();
          b = bdd_mt_quantify2(b, term_id,
                               term_combine_and, term_combine_or,
                               &cache_,
                               hash_key_quantify,
                               hash_key_and, bddop_and,
                               hash_key_or, bddop_or);
        }
      // propositional equivalence on all terminals.
      b = bdd_mt_apply1_leaves(b, terminal_propeq, &cache_, hash_key_propeq);
      return b;
    };


    term_combine_trans = this;

    todo.emplace_back(formula_propeq_to_int(f));
    do
      {
        // the debug parameter can be set to something postive to
        // stop the algorithm after debug iteration.
        if (SPOT_UNLIKELY(debug >= 0))
          {
            if (debug == 0 || backprop.root_is_determined(0))
              break;
            --debug;

            // std::cerr << "TODO:";
            // for (int t: todo)
            //   std::cerr << ' ' << t;
            // std::cerr << "\nPREV:";
            // for (auto [p, s]: prev)
            //   std::cerr << " [" << p << ',' << s << ']';
            // std::cerr << "\nROOTS:";
            // for (int r: scc_roots)
            //   std::cerr << ' ' << r;
            // std::cerr << "\nLIVE:";
            // for (int r: live_states)
            //   std::cerr << ' ' << r;
            // std::cerr << '\n';
          }
        if (SPOT_LIKELY(!prev.empty()))
          if (auto [prev_state, size] = prev.back();
              todo.size() == size) // DFS backtrack
            {
              prev.pop_back();
              auto it = terminal_to_state_map.find(prev_state);
              assert(it != terminal_to_state_map.end());
              SPOT_ASSUME(it != terminal_to_state_map.end());
              unsigned prev_rank = it->second;

              assert(!scc_roots.empty());
              if (scc_roots.back() == prev_rank) // Is this the root of the SCC?
                {
                  // We are leaving an SCC!
                  scc_roots.pop_back();

                  // This is an accepting SCC?
                  formula label = int_to_formula_[prev_state];
                  bool is_acc = obligation_is_accepting(label);

                  // Mark all states in the SCC as losing or winning,
                  // depending on is_acc. Spot if status of the initial
                  // state becomes known.
                  int s;
                  do
                    {
                      s = live_states.back();
                      live_states.pop_back();
                      // if realizability is not set, make sure we mark all the
                      // SCC as accepting, otherwise we will have undetermined
                      // nodes below accepting terminals in the SCC and we
                      // won't be able to extract a strategy.
                      if (backprop.root_winner_set_if_unknown(s, is_acc)
                          && realizability)
                        break;
                      auto it = terminal_to_state_map.find(s);
                      assert(it != terminal_to_state_map.end());
                      SPOT_ASSUME(it != terminal_to_state_map.end());
                      it->second = ~it->second;
                    }
                  while (s != prev_state);
                  if (backprop.root_is_determined(0))
                    break;
                }
              continue;
            }

        assert(!todo.empty());

        int label_term = todo.back();
        todo.pop_back();

        // already processed
        if (terminal_to_state_map.find(label_term)
            != terminal_to_state_map.end())
          continue;

        // Gather states entered during the DFS.  These
        // will only be popped when we leave the current SCC.
        live_states.push_back(label_term);

        formula label = int_to_formula_[label_term];

        bdd b = trans_succ(label);

        quantify_prepare_maybe();
        std::string name = str_psl(label);
        backprop.encode_state<true>(label_term, b, &name,
                                    &new_rootnums, &old_rootnums);

        // For the purpose of cycle detection, n is also the rank in
        // the DFS order.
        unsigned n = states.size();
        scc_roots.push_back(n);
        formula_to_state[label] = n;
        states.push_back(b);
        names.push_back(label);
        terminal_to_state_map[label_term] = n;

        if (SPOT_LIKELY(debug < 0))
          {
            if (SPOT_UNLIKELY(backprop.root_is_determined(0)))
              break;
            //if (SPOT_UNLIKELY(backprop.root_is_determined(label_term)))
            //  continue;
          }
        // Schedule all successors for processing in DFS order
        prev.emplace_back(label_term, todo.size());
        for (unsigned root: new_rootnums)
          todo.push_back(root);
        for (unsigned root: old_rootnums)
          {
            auto it = terminal_to_state_map.find(root);
            if (it == terminal_to_state_map.end())
              {
                todo.push_back(root);
                continue;
              }
            int rank = it->second;
            if (rank < 0)         // already processed SCC
              continue;
            // We are closing a cycle.
            while (scc_roots.back() > (unsigned) rank)
              scc_roots.pop_back();
          }
        old_rootnums.clear();
        new_rootnums.clear();
      }
    while (!prev.empty());

    // If we were passed the debug parameter, let's build an automaton
    // representing our current state after DEBUG iterations.
    if (debug >= 0)
      {
        std::unordered_map<int, unsigned> highlight_nodes;
        highlight_nodes.emplace(0, 5);
        highlight_nodes.emplace(1, 4);
        for (auto [bddid, state] : backprop.bdd_to_backprop_state)
          {
            if (backprop.backprop.is_determined(state))
              {
                bool winner = backprop.backprop.winner(state);
                highlight_nodes.emplace(bddid, 5 - winner);
              }
          }
        // highlight next state to process
        if (!prev.empty() && todo.size() != prev.back().second && !todo.empty())
          highlight_nodes.emplace(bdd_terminal(todo.back()).id(), 6);

        unsigned n = states.size();

        for (auto& [term, rank]: terminal_to_state_map)
          if (rank < 0)
            rank = ~rank;

        // declare all missing states.
        while (!todo.empty())
          {
            int label_term = todo.front();
            todo.pop_front();
            if (terminal_to_state_map.find(label_term)
                != terminal_to_state_map.end())
              continue;
            formula label = int_to_formula_[label_term];
            names.push_back(label);
            terminal_to_state_map[label_term] = n++;
          }

        unsigned sz = states.size();
        dfa->terminal_to_state_map = terminal_to_state_map;
        dfa->highlight_nodes = std::move(highlight_nodes);
        dfa->states = std::move(states);
        dfa->names = std::move(names);
        dfa->colors = std::vector<acc_cond::mark_t>(sz, acc_cond::mark_t{});
        dict_->register_all_propositions_of(this, dfa);
        for (bdd b = forallvars; b != bddtrue; b = bdd_high(b))
          dict_->unregister_variable(bdd_var(b), dfa);
        for (bdd b = existsvars; b != bddtrue; b = bdd_high(b))
          dict_->unregister_variable(bdd_var(b), dfa);
        for (auto [term, st]: terminal_to_state_map)
          if (backprop.root_is_determined(term))
            dfa->colors[st].set(5 - backprop.root_winner(term));
        return dfa;
      }


    assert(backprop.root_is_determined(0));
    bool realizable = backprop.root_winner(0);

    dfa->acc = realizable ? acc_cond::acc_code::t() : acc_cond::acc_code::f();

    if (realizability || !realizable)
      {
        if (realizable)
          {
            dfa->states.push_back(bddtrue);
            dfa->names.push_back(formula::tt());
          }
        else
          {
            dfa->states.push_back(bddfalse);
            dfa->names.push_back(formula::ff());
          }
        dfa->colors.emplace_back(acc_cond::mark_t{});
        return dfa;
      }

    for (auto& [term, rank]: terminal_to_state_map)
      if (rank < 0)
        rank = ~rank;

    // backprop.backprop.print_dot(std::cerr);
    unsigned sz = states.size();
    for (unsigned i = 0; i < sz; ++i)
      bdd_mt_apply1_synthesis_with_choice(states[i],
                                          strategy_choice,
                                          strategy_map_finalize,
                                          &cache_, hash_key_finalstrat);

    dfa->states = std::move(states);
    dfa->names = std::move(names);
    dfa->colors = std::vector<acc_cond::mark_t>(sz, acc_cond::mark_t{});
    dict_->register_all_propositions_of(this, dfa);
    for (bdd b = forallvars; b != bddtrue; b = bdd_high(b))
      dict_->unregister_variable(bdd_var(b), dfa);
    for (bdd b = existsvars; b != bddtrue; b = bdd_high(b))
      dict_->unregister_variable(bdd_var(b), dfa);
    return dfa;
  }

  mtdswa_ptr obligation_to_mtdswa(formula f, const bdd_dict_ptr& dict,
                                  bool fuse_same_bdds, bool simplify_terms)
  {
    if (SPOT_UNLIKELY(!f.is_syntactic_obligation()))
      throw std::runtime_error
        ("obligation_to_mtdswa(): input is not a syntactic obligation");

    simple_ltl_translator trans(dict, simplify_terms);
    return trans.ltl_to_mtdswa(f, fuse_same_bdds);
  }

  mtdswa_ptr obligation_synthesis(formula f, const bdd_dict_ptr& dict,
                                  const std::vector<std::string>& outvars,
                                  bool realizability, bool simplify_terms,
                                  int debug)
  {
    if (SPOT_UNLIKELY(!f.is_syntactic_obligation()))
      throw std::runtime_error
        ("obligation_synthesis(): input is not a syntactic obligation");

    simple_ltl_translator trans(dict, simplify_terms);
    return trans.ltl_to_mtdswa_synthesis(f, outvars, realizability, debug);
  }


  /////////////////////////////////////////////////////////////////////////
  //                       minimization of MTDSWA                        //
  /////////////////////////////////////////////////////////////////////////

  // callback for minimize_mtdfa
  namespace
  {
    static std::vector<int> classes;
    //static int num_states;
    //static bool accepting_false_seen;
    //static bool rejecting_true_seen;

    static int rename_class(int val)
    {
      assert((unsigned) val < classes.size());
      val = classes[val];
      //if (val >= num_states)
      //  {
      //    if (accepting)
      //      accepting_false_seen = true;
      //    else
      //      rejecting_true_seen = true;
      //  }
      return val;
    }
  }

  namespace
  {
    typedef std::pair<bdd, acc_cond::mark_t> sig_t;
    struct sig_hash
    {
      size_t operator()(const sig_t& sig) const noexcept
      {
        return sig.second.hash() ^ sig.first.id();
      }
    };

  }

  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa,
                             bddExtCache* cache,
                             const std::vector<unsigned>* initial_partition,
                             int& iteration)
  {
    if (iteration >= (1 << 20))
      {
        // wipe the cache every 2^20 iterations.
        bdd_extcache_reset(cache);
        iteration = 0;
      }

    unsigned n = dfa->num_roots();

    // This minimization implements Moore's partition-refinement
    // algorithm using MTBDDs.  The idea is relatively simple: each
    // state of the MTDSWA is assigned a class. Initially every state
    // is in a class that corresponds to its colors.  The MTBDD used
    // to represent the states are all rewritten, replacing each
    // terminal dst by class[dst].  After this rewriting,
    // states whose MTBDD are different are put into different
    // classes, and we start again.  We iterate the process until no
    // more classes are created.

    // class is a global vector assigning classes to each state
    classes.clear();
    classes.reserve(n);

    if (!initial_partition)
      {
        // loop over all states, and give them a class that match
        // their color
        std::unordered_map<acc_cond::mark_t, int> col2cl;
        for (unsigned i = 0; i < n; ++i)
          {
            acc_cond::mark_t col = dfa->colors[i];
            auto it = col2cl.emplace(col, col2cl.size()).first;
            classes.push_back(it->second);
          }
      }
    else
      {
        if (SPOT_UNLIKELY(initial_partition->size() != n))
          throw std::runtime_error
            ("minimize_mtdswa(): initial partition has incorrect size");
        std::unordered_map<unsigned, int> block2cl;
        for (unsigned i = 0; i < n; ++i)
          {
            unsigned block = (*initial_partition)[i];
            auto it = block2cl.emplace(block, block2cl.size()).first;
            classes.push_back(it->second);
          }
      }

    // The "signature" of each state is their encoding using
    // the current set of classes.  The following vector remember
    // each unique signature in the order they were discovered.
    std::vector<bdd> sig_states;
    std::vector<acc_cond::mark_t> sig_colors;
    sig_states.reserve(n);
    sig_colors.reserve(n);
    // For each distinct signature, GROUPS retains the list of
    // states that have this signature & color.

    robin_hood::unordered_map<sig_t, std::vector<int>, sig_hash> groups;
    for (;;)
      {
        ++iteration;
        for (unsigned i = 0; i < n; ++i)
          {
            bdd b = bdd_mt_apply1(dfa->states[i], rename_class,
                                  bddfalse, bddtrue,
                                  cache, iteration);
            sig_t sig(b, dfa->colors[i]);
            auto& v = groups[sig];
            if (v.empty())
              {
                sig_states.push_back(sig.first);
                sig_colors.push_back(sig.second);
              }
            v.push_back(i);
          }
        // { // debug
        //   std::cerr << "iteration " << iteration << '\n';
        //   std::cerr << signatures.size() << " states\n";
        // }

        // Assign each state to its class number, using the order in
        // which signatures were discovered.  In this order, the
        // initial state will always have class 0.
        //
        // An exception is if the class contains the fake true/false
        // state.  In this case, we map the class back to n/n+1.
        int curclass = 0;
        bool changed = false;
        unsigned sn = sig_states.size();
        for (unsigned s = 0; s < sn; ++s)
          {
            int mapclass = curclass++;
            sig_t sig(sig_states[s], sig_colors[s]);
            auto& v = groups[sig];
            for (unsigned i: v)
              if (classes[i] != mapclass)
                {
                  changed = true;
                  classes[i] = mapclass;
                }
            // { // debug
            //   std::cerr << "class " << mapclass << ':';
            //   for (unsigned i: v)
            //     std::cerr << ' ' << i;
            //   if (mapclass == (int) n)
            //     std::cerr << "  (true)";
            //   else if (mapclass == (int) n + 1)
            //     std::cerr << "  (false)";
            //   std::cerr << "\n      " << sig << '\n';
            // }
          }
        // for (unsigned i = 0; i <= n + 1; ++i)
        //    std::cerr << "classes[" << i << "]=" << classes[i] << '\n';
        if (!changed)
          break;
        groups.clear();
        sig_states.clear();
        sig_colors.clear();
      }

    // The BDDs in SIG_STATES are actually our new MTBDD
    // representation, with SIG_COLORS as colors.
    //
    // if WANT_NAMES is set we also have to keep one name per class
    // for display.
    bool want_names = dfa->names.size() == n;
    std::vector<formula> names;
    if (want_names)
      {
        // Our automaton will have SZ states;
        unsigned sz = sig_states.size();
        names.reserve(sz);
        for (unsigned s = 0; s < sz; ++s)
          {
            sig_t sig(sig_states[s], sig_colors[s]);
            auto& v = groups[sig];
            // We can pick any state in v as representative of the
            // class.  Here we simply pick the first one, but this
            // can be changed if needed (e.g. pick the one with
            // the shortest name since it is more readable?)
            unsigned repr = v.front();
            assert(repr < dfa->names.size());
            names.push_back(dfa->names[repr]);
          }
      }

    bdd_dict_ptr dict = dfa->get_dict();
    mtdswa_ptr res = std::make_shared<mtdswa>(dict);
    dict->register_all_propositions_of(dfa, res);
    std::swap(res->names, names);
    std::swap(res->states, sig_states);
    std::swap(res->colors, sig_colors);
    res->aps = dfa->aps;
    res->acc = dfa->acc;

    return res;
  }

  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(dfa), false);
    int iteration = 0;
    mtdswa_ptr res = minimize_mtdswa(dfa, &cache, nullptr, iteration);
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa,
                             const std::vector<unsigned>& initial_partition)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(dfa), false);
    int iteration = 0;
    mtdswa_ptr res = minimize_mtdswa(dfa, &cache, &initial_partition,
                                     iteration);
    bdd_extcache_done(&cache);
    return res;
  }

  twa_graph_ptr
  mtdswa_strategy_to_mealy(mtdswa_ptr strategy, bool labels, bool loop)
  {
    bdd_dict_ptr dict = strategy->get_dict();
    twa_graph_ptr res = make_twa_graph(dict);
    dict->register_all_propositions_of(strategy, res);
    res->register_aps_from_dict();
    res->prop_universal(true);
    res->prop_weak(true);

    unsigned n = strategy->num_roots();
    assert(n > 0);

    bdd outputs = strategy->get_controllable_variables();
    res->set_named_prop<bdd>("synthesis-outputs", new bdd(outputs));

    std::vector<std::string>* names = nullptr;
    if (labels && strategy->names.size() == strategy->states.size())
      {
        names = new std::vector<std::string>;
        names->reserve(n);
        res->set_named_prop("state-names", names);
      }

    robin_hood::unordered_map<int, unsigned> bdd_to_state_map;
    std::vector<bdd> states;
    states.reserve(n);

    auto map_state = [&](int state_index) {
      bdd succs = bddtrue;
      if (state_index >= 0)
        succs = strategy->states[state_index];
      auto [it, b] = bdd_to_state_map.emplace(succs.id(), 0);
      if (!b)
        return it->second;
      unsigned res_index = res->new_state();
      assert(res_index == states.size());
      it->second = res_index;
      states.push_back(succs);
      if (names)
        {
          if (state_index >= 0)
            names->push_back(str_psl(strategy->names[state_index]));
          else
            names->push_back("1");
        }
      return res_index;
    };

    map_state(0);
    // states.size() will increase in this loop
    for (unsigned i = 0; i < states.size(); ++i)
      {
        bdd succs = states[i];
        if (succs == bddfalse)
          continue;
        if (succs == bddtrue)
          {
            res->new_edge(i, i, bddtrue);
            continue;
          }
        bdd previous_output_label = bddfalse;
        unsigned previous_dst = -1U;
        unsigned previous_edge = 0;
        for (auto [b, t]: paths_mt_of(succs))
          {
            int dst = -1;
            if (t != bddtrue)
              dst = bdd_get_terminal(t);
            unsigned dst_idx = (loop && dst < 0) ? i : map_state(dst);
            bdd output_label = bdd_existcomp(b, outputs);
            if (previous_dst == dst_idx
                && previous_output_label == output_label)
              {
                res->edge_storage(previous_edge).cond |= b;
                continue;
              }
            previous_edge = res->new_edge(i, dst_idx, b);
            previous_dst = dst_idx;
            previous_output_label = output_label;
          }
      }
    return res;
  }



  //////////////////////////////////////////////////////////////////////
  //                 Boolean operations on MTDSwAs                    //
  //////////////////////////////////////////////////////////////////////

  namespace
  {

    typedef std::pair<unsigned, unsigned> product_state;

    struct product_state_hash
    {
      size_t
      operator()(product_state s) const noexcept
      {
        return wang32_hash(s.first ^ wang32_hash(s.second));
      }
    };


    inline std::pair<bdd, formula>
    bdd_and_formula_from_state(unsigned s, const mtdswa_ptr& swa)
    {
      if (s == -2U)
        return {bddfalse, formula::ff()};
      if (s == -1U)
        return {bddtrue, formula::tt()};
      if (s >= swa->names.size())
        return {swa->states[s], nullptr};
      return {swa->states[s], swa->names[s]};
    }

    struct product_data
    {
      // A cache for the BDD terminals (as ints) in the product automaton
      // associated to a pair of states of the original automata.
      std::unordered_map<product_state, int,
                         product_state_hash> pair_to_terminal_map;
      // Used to store the product states that still need to be processed.
      // When new states are created, they are added here.
      std::queue<product_state> todo;

      // The two input automata, the operator, and the shift amount for
      // swa2's colors.
      mtdswa_ptr swa1_;
      mtdswa_ptr swa2_;
      op o_ = op::And;
      unsigned swa1_max_color_ = 0;
      // For operators that need to distinguish degenerate-side alive/dead
      // states (IMPLIES, EQUIV, XOR), a fresh acceptance set is used as a
      // status marker.  It is placed after all used sets of both sides.
      unsigned status_set_ = 0;
      acc_cond::mark_t status_mark_{};

      // Cached sat/unsat marks and degenerate flags for the two acceptances.
      // Computed by setup(), called once from product_mtdswa_aux().
      acc_cond::mark_t swa1_unsat_{};
      acc_cond::mark_t swa1_sat_{};
      acc_cond::mark_t swa2_unsat_{};
      acc_cond::mark_t swa2_sat_{};
      bool swa1_taut_ = false;
      bool swa1_unsatis_ = false;
      bool swa2_taut_ = false;
      bool swa2_unsatis_ = false;

      // Type for a color strategy: a const member function of product_data
      // that computes colors for a product state under a specific
      // degenerate-acceptance scenario.
      using color_strategy_t
      = acc_cond::mark_t (product_data::*)(product_state) const;

      unsigned leaf_to_state(int b, int v) const
      {
        if (b == 0)  // terminal bddfalse
          return -2U;
        if (b == 1)  // terminal bddtrue
          return -1U;
        return v;
      }

      int pair_to_terminal(unsigned left, unsigned right)
      {
        // If a terminal for this pair exists then return it.
        if (auto it = pair_to_terminal_map.find({left, right});
            it != pair_to_terminal_map.end())
          {
            return it->second;
          }
        // Otherwise create a new one, cache it and return it.
        unsigned new_id = pair_to_terminal_map.size();
        product_state ps{left, right};
        int res = bdd_terminal_as_int(new_id);
        pair_to_terminal_map.emplace(ps, res);
        todo.emplace(ps);
        return res;
      }

      // Maps pairs of states from the original automata to terminals
      // in the product automaton.
      int pair_to_terminal_bdd(unsigned left, unsigned right)
      {
        // (bddfalse, bddfalse) is always mapped to bddfalse (0), bddtrue to 1.
        if (SPOT_UNLIKELY(left == -2U && right == -2U))
          return 0;
        else if (SPOT_UNLIKELY(left == -1U && right == -1U))
          return 1;
        else
          return pair_to_terminal(left, right);
      }

      // Initialize the product_data for a new product construction.
      // Called once from product_mtdswa_aux().
      void setup(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2, op o)
      {
        swa1_ = swa1;
        swa2_ = swa2;
        o_ = o;
        swa1_max_color_
          = swa1->acc.get_acceptance().used_sets().max_set();
        auto u1 = swa1->acc.unsat_mark();
        swa1_taut_ = !u1.first;
        swa1_unsat_ = u1.first ? u1.second : acc_cond::mark_t{};
        auto s1 = swa1->acc.sat_mark();
        swa1_unsatis_ = !s1.first;
        swa1_sat_ = s1.first ? s1.second : acc_cond::mark_t{};
        auto u2 = swa2->acc.unsat_mark();
        swa2_taut_ = !u2.first;
        swa2_unsat_ = u2.first ? u2.second : acc_cond::mark_t{};
        auto s2 = swa2->acc.sat_mark();
        swa2_unsatis_ = !s2.first;
        swa2_sat_ = s2.first ? s2.second : acc_cond::mark_t{};
        // When a side is degenerate (tautology or unsatisfiable),
        // its acceptance and colors should be ignored as if it had
        // pure t/f with 0 sets.  Zero out its max_color and clear
        // its cached marks to prevent accidental misuse.
        if (swa1_taut_ || swa1_unsatis_)
          {
            swa1_max_color_ = 0;
            swa1_sat_ = {};
            swa1_unsat_ = {};
          }
        // The status set is placed after all acceptance sets used by
        // the non-degenerate side.  It is only needed by operators
        // that must distinguish degenerate-side alive/dead states
        // (IMPLIES, EQUIV, XOR).
        if (o == op::Implies || o == op::Equiv || o == op::Xor)
          {
            unsigned swa2_max_color
              = swa2->acc.get_acceptance().used_sets().max_set();
            // Same as swa1 above: zero out degenerate-side contribution.
            if (swa2_taut_ || swa2_unsatis_)
              swa2_max_color = 0;
            status_set_ = swa1_max_color_ + swa2_max_color;
            status_mark_ = {status_set_};
          }
      }

      // Color strategies.  Each is a simple function with no degenerate
      // or operator checks — only sentinel handling.  The degenerate
      // checks happen once in the wrapper, which selects the right strategy.

      acc_cond::mark_t
      colors_general(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first]
            | (swa2_unsat_ << swa1_max_color_);
        if (s.first == -2U)
          return swa1_unsat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        if (s.second == -1U)
          return swa1_->colors[s.first]
            | (swa2_sat_ << swa1_max_color_);
        if (s.first == -1U)
          return swa1_sat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        return swa1_->colors[s.first]
          | (swa2_->colors[s.second] << swa1_max_color_);
      }

      // Used when both sides are degenerate: the acceptance is
      // simplified to pure t/f (0 sets), so all colors must be empty.
      acc_cond::mark_t
      colors_both_degenerate(product_state) const
      {
        return {};
      }

      // --- swa2 tautology (t) strategies ---
      acc_cond::mark_t
      colors_swa2_taut_and(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first] | swa1_unsat_;
        return swa1_->colors[s.first];
      }
      acc_cond::mark_t
      colors_swa2_taut_or(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first] | swa1_unsat_;
        return swa1_->colors[s.first] | swa1_sat_;
      }
      acc_cond::mark_t
      colors_swa2_taut_implies(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first];
        return swa1_->colors[s.first] | swa1_sat_ | status_mark_;
      }
      acc_cond::mark_t
      colors_swa2_taut_equiv_xor(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first];
        return swa1_->colors[s.first] | status_mark_;
      }

      // --- swa2 unsatisfiable (f) strategies ---
      acc_cond::mark_t
      colors_swa2_unsat_and(product_state s) const
      {
        return swa1_->colors[s.first] | swa1_unsat_;
      }
      acc_cond::mark_t
      colors_swa2_unsat_or_implies_xor(product_state s) const
      {
        return swa1_->colors[s.first];
      }
      acc_cond::mark_t
      colors_swa2_unsat_equiv(product_state s) const
      {
        if (s.second == -2U)
          return swa1_->colors[s.first] | swa1_sat_;
        return swa1_->colors[s.first] | status_mark_;
      }

      // --- swa1 tautology (t) strategies ---
      acc_cond::mark_t
      colors_swa1_taut_and(product_state s) const
      {
        if (s.first == -2U)
          return swa1_unsat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        return swa2_->colors[s.second] << swa1_max_color_;
      }
      acc_cond::mark_t
      colors_swa1_taut_or(product_state s) const
      {
        if (s.first == -2U)
          return swa1_unsat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        return swa1_sat_
          | (swa2_->colors[s.second] << swa1_max_color_);
      }
      acc_cond::mark_t
      colors_swa1_taut_implies(product_state s) const
      {
        if (s.first == -2U)
          return swa2_sat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        return (swa2_->colors[s.second] << swa1_max_color_)
          | status_mark_;
      }
      acc_cond::mark_t
      colors_swa1_taut_equiv_xor(product_state s) const
      {
        if (s.first == -2U)
          return swa2_->colors[s.second] << swa1_max_color_;
        return (swa2_->colors[s.second] << swa1_max_color_)
          | status_mark_;
      }

      // --- swa1 unsatisfiable (f) strategies ---
      acc_cond::mark_t
      colors_swa1_unsat_and(product_state s) const
      {
        return swa1_unsat_
          | (swa2_->colors[s.second] << swa1_max_color_);
      }
      acc_cond::mark_t
      colors_swa1_unsat_or_xor(product_state s) const
      {
        return swa2_->colors[s.second] << swa1_max_color_;
      }
      acc_cond::mark_t
      colors_swa1_unsat_implies(product_state s) const
      {
        return swa2_sat_
          | (swa2_->colors[s.second] << swa1_max_color_);
      }
      acc_cond::mark_t
      colors_swa1_unsat_equiv(product_state s) const
      {
        if (s.first == -2U)
          return swa2_sat_
            | (swa2_->colors[s.second] << swa1_max_color_);
        return (swa2_->colors[s.second] << swa1_max_color_)
          | status_mark_;
      }
    } the_product_data;

    // Combine two leaves of the product automaton with AND.
    static int leaf_combine_and(int left, int left_term,
                                int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 0 || right == 0))
        return 0;
      unsigned ls = the_product_data.leaf_to_state(left, left_term);
      unsigned rs = the_product_data.leaf_to_state(right, right_term);
      return the_product_data.pair_to_terminal_bdd(ls, rs);
    }

    // Combine two leaves of the product automaton with OR.
    static int leaf_combine_or(int left, int left_term,
                               int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 1 || right == 1))
        return 1;
      unsigned ls = the_product_data.leaf_to_state(left, left_term);
      unsigned rs = the_product_data.leaf_to_state(right, right_term);
      return the_product_data.pair_to_terminal_bdd(ls, rs);
    }

    // Combine two leaves of the product automaton with IMPLIES.
    static int leaf_combine_implies(int left, int left_term,
                                    int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 0 || right == 1))
        return 1;
      unsigned ls = the_product_data.leaf_to_state(left, left_term);
      unsigned rs = the_product_data.leaf_to_state(right, right_term);
      return the_product_data.pair_to_terminal_bdd(ls, rs);
    }

    // Combine two leaves of the product automaton with EQUIV (XNOR).
    static int leaf_combine_equiv(int left, int left_term,
                                  int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 0 || left == 1))
        {
          if (left == right)
            return 1;
          if ((left ^ right) == 1)
            return 0;
        }
      unsigned ls = the_product_data.leaf_to_state(left, left_term);
      unsigned rs = the_product_data.leaf_to_state(right, right_term);
      return the_product_data.pair_to_terminal_bdd(ls, rs);
    }

    // Combine two leaves of the product automaton with XOR.
    static int leaf_combine_xor(int left, int left_term,
                                int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 0 || left == 1))
        {
          if (left == right)
            return 0;
          if ((left ^ right) == 1)
            return 1;
        }
      unsigned ls = the_product_data.leaf_to_state(left, left_term);
      unsigned rs = the_product_data.leaf_to_state(right, right_term);
      return the_product_data.pair_to_terminal_bdd(ls, rs);
    }

    // Create a product of two MTDSwAs with the given operator.
    static mtdswa_ptr
    product_mtdswa_aux(const mtdswa_ptr& swa1,
                       const mtdswa_ptr& swa2, op o,
                       product_data::color_strategy_t color_strategy,
                       bddExtCache* cache, int hash_key)
    {
      if (swa1->get_dict() != swa2->get_dict())
        throw std::runtime_error
          ("product_mtdswa_aux: MTDSwAs should share their dictionaries");
      // Prepare the function to combine two leaves of the product automaton.
      int (*combine)(int, int, int, int);
      int applyop_shortcut = -1;
      switch (o)
        {
        case op::And:
          combine = leaf_combine_and;
          applyop_shortcut = bddop_and_zero;
          break;
        case op::Or:
          combine = leaf_combine_or;
          applyop_shortcut = bddop_or_one;
          break;
        case op::Implies:
          combine = leaf_combine_implies;
          applyop_shortcut = bddop_imp_one;
          break;
        case op::Equiv:
          combine = leaf_combine_equiv;
          applyop_shortcut = -1;
          break;
        case op::Xor:
          combine = leaf_combine_xor;
          applyop_shortcut = -1;
          break;
        default:
          throw std::runtime_error("product_mtdswa_aux: unsupported operator");
        }
      // Create result automaton, and register all propositions.
      bdd_dict_ptr dict = swa1->get_dict();
      mtdswa_ptr res = std::make_shared<mtdswa>(dict);
      dict->register_all_propositions_of(swa1, res);
      dict->register_all_propositions_of(swa2, res);

      // We will construct the states of the product automaton on-the-fly.
      // The colors of swa2 will be shifted by the maximum color of swa1,
      // to avoid collisions.
      the_product_data.setup(swa1, swa2, o);

      // This will initialize todo with the initial state of the product.
      std::queue<product_state>& todo = the_product_data.todo;
      (void) the_product_data.pair_to_terminal(0, 0);

      while (!todo.empty())
        {
          product_state s = todo.front();
          todo.pop();

          // Construct state of the product automaton corresponding to the pair
          auto [left, left_f] = bdd_and_formula_from_state(s.first, swa1);
          auto [right, right_f] = bdd_and_formula_from_state(s.second, swa2);
          bdd b = bdd_mt_apply2_leaves(left, right, combine, cache, hash_key,
                                       applyop_shortcut);
          res->states.push_back(b);
          // Skip color computation for pairs where both sides are
          // constants (bddtrue/bddfalse).  These map directly to
          // terminals and their colors are irrelevant.
          if (SPOT_UNLIKELY((s.first == -2U || s.first == -1U)
                            && (s.second == -2U || s.second == -1U)))
            res->colors.push_back(acc_cond::mark_t{});
          else
            res->colors.push_back
              ((the_product_data.*color_strategy)(s));
          // Construct name of the product state if both states have names.
          if (left_f && right_f)
            switch (o)
              {
              case op::And:
                res->names.push_back(formula::And(left_f, right_f));
                break;
              case op::Or:
                res->names.push_back(formula::Or(left_f, right_f));
                break;
              case op::Implies:
                res->names.push_back(formula::Implies(left_f, right_f));
                break;
              case op::Equiv:
                res->names.push_back(formula::Equiv(left_f, right_f));
                break;
              case op::Xor:
                res->names.push_back(formula::Xor(left_f, right_f));
                break;
              default:
                SPOT_UNREACHABLE();
              }
        }

      // Combine the sorted list of atomic propositions from SWA1 and SWA2
      // keeping the result sorted.
      res->aps.reserve(swa1->aps.size() + swa2->aps.size());
      std::set_union(swa1->aps.begin(), swa1->aps.end(),
                     swa2->aps.begin(), swa2->aps.end(),
                     std::back_inserter(res->aps));

      the_product_data.pair_to_terminal_map.clear();
      the_product_data.swa1_.reset();
      the_product_data.swa2_.reset();
      return res;
    }

    static mtdswa_ptr
    complement_aux(const mtdswa_ptr& swa, bddExtCache* cache, int hash_key)
    {
      unsigned n = swa->names.size();
      unsigned ns = swa->states.size();

      bdd_dict_ptr dict = swa->get_dict();
      mtdswa_ptr res = std::make_shared<mtdswa>(dict);
      dict->register_all_propositions_of(swa, res);
      res->names.reserve(n);
      res->states.reserve(ns);
      res->colors = swa->colors;
      res->aps = swa->aps;
      res->acc = acc_cond{swa->acc.get_acceptance().complement()};

      // Replace bddtrue by bddfalse and vice versa.
      for (unsigned i = 0; i < ns; ++i)
        res->states.push_back(bdd_mt_apply1(swa->states[i],
                                            [](int v){ return v; },
                                            bddtrue, bddfalse, cache,
                                            hash_key));
      for (unsigned i = 0; i < n; ++i)
        res->names.push_back(formula::Not(swa->names[i]));
      return res;
    }
  }

  mtdswa_ptr product(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_product(swa1, swa2), true);
    the_product_data.setup(swa1, swa2, op::And);
    mtdswa_ptr res;
    product_data::color_strategy_t cs;
    if (the_product_data.swa2_taut_
        && !the_product_data.swa1_taut_
        && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_taut_and;
        res = product_mtdswa_aux(swa1, swa2, op::And, cs, &cache, 0);
        // AND(A, t) = A.
        res->acc = acc_cond{swa1->acc.get_acceptance()};
      }
    else if (the_product_data.swa2_unsatis_
             && !the_product_data.swa1_taut_
             && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_unsat_and;
        res = product_mtdswa_aux(swa1, swa2, op::And, cs, &cache, 0);
        // AND(A, f) = f.
        res->acc = acc_cond{acc_cond::acc_code::f()};
      }
    else if (the_product_data.swa1_taut_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_taut_and;
        res = product_mtdswa_aux(swa1, swa2, op::And, cs, &cache, 0);
        // AND(t, B) = B.
        res->acc = acc_cond{swa2->acc.get_acceptance()
                            << the_product_data.swa1_max_color_};
      }
    else if (the_product_data.swa1_unsatis_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_unsat_and;
        res = product_mtdswa_aux(swa1, swa2, op::And, cs, &cache, 0);
        // AND(f, B) = f.
        res->acc = acc_cond{acc_cond::acc_code::f()};
      }
    else
      {
        bool both_degen = (the_product_data.swa1_taut_
                           || the_product_data.swa1_unsatis_);
        cs = (both_degen
              ? &product_data::colors_both_degenerate
              : &product_data::colors_general);
        res = product_mtdswa_aux(swa1, swa2, op::And, cs, &cache, 0);
        if (SPOT_UNLIKELY(both_degen))
          // Both sides degenerate: AND(t,t)=t, otherwise f.
          res->acc = acc_cond{((the_product_data.swa1_taut_
                                && the_product_data.swa2_taut_)
                               ? acc_cond::acc_code::t()
                               : acc_cond::acc_code::f())};
        else
          res->acc = acc_cond{swa1->acc.get_acceptance()
                              & (swa2->acc.get_acceptance()
                                 << the_product_data.swa1_max_color_)};
      }
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr product_or(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_product(swa1, swa2), true);
    the_product_data.setup(swa1, swa2, op::Or);
    mtdswa_ptr res;
    product_data::color_strategy_t cs;
    if (the_product_data.swa2_taut_
        && !the_product_data.swa1_taut_
        && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_taut_or;
        res = product_mtdswa_aux(swa1, swa2, op::Or, cs, &cache, 0);
        // OR(A, t): override A|t→t with just A.
        res->acc = acc_cond{swa1->acc.get_acceptance()};
      }
    else if (the_product_data.swa2_unsatis_
             && !the_product_data.swa1_taut_
             && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_unsat_or_implies_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Or, cs, &cache, 0);
        // OR(A, f) = A.
        res->acc = acc_cond{swa1->acc.get_acceptance()};
      }
    else if (the_product_data.swa1_taut_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_taut_or;
        res = product_mtdswa_aux(swa1, swa2, op::Or, cs, &cache, 0);
        // OR(t, B): override t|B→t with just B.
        res->acc = acc_cond{swa2->acc.get_acceptance()
                            << the_product_data.swa1_max_color_};
      }
    else if (the_product_data.swa1_unsatis_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_unsat_or_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Or, cs, &cache, 0);
        // OR(f, B) = B.
        res->acc = acc_cond{swa2->acc.get_acceptance()
                            << the_product_data.swa1_max_color_};
      }
    else
      {
        bool both_degen = (the_product_data.swa1_taut_
                           || the_product_data.swa1_unsatis_);
        cs = (both_degen
              ? &product_data::colors_both_degenerate
              : &product_data::colors_general);
        res = product_mtdswa_aux(swa1, swa2, op::Or, cs, &cache, 0);
        if (SPOT_UNLIKELY(both_degen))
          // Both sides degenerate: OR(t,_)=t, OR(_,t)=t, OR(f,f)=f.
          res->acc = acc_cond{((the_product_data.swa1_taut_
                                || the_product_data.swa2_taut_)
                               ? acc_cond::acc_code::t()
                               : acc_cond::acc_code::f())};
        else
          res->acc = acc_cond{swa1->acc.get_acceptance()
                              | (swa2->acc.get_acceptance()
                                 << the_product_data.swa1_max_color_)};
      }
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr product_implies(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_product(swa1, swa2), true);
    the_product_data.setup(swa1, swa2, op::Implies);
    mtdswa_ptr res;
    product_data::color_strategy_t cs;
    auto inf_st = acc_cond::acc_code::inf(the_product_data.status_mark_);
    auto fin_st = acc_cond::acc_code::fin(the_product_data.status_mark_);
    if (the_product_data.swa2_taut_
        && !the_product_data.swa1_taut_
        && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_taut_implies;
        res = product_mtdswa_aux(swa1, swa2, op::Implies, cs, &cache, 0);
        // IMPLIES(A, t): alive→true, dead→!A.
        // = Inf(status) | !A.acc.
        res->acc = acc_cond{inf_st
                            | swa1->acc.get_acceptance().complement()};
      }
    else if (the_product_data.swa2_unsatis_
             && !the_product_data.swa1_taut_
             && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_unsat_or_implies_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Implies, cs, &cache, 0);
        // IMPLIES(A, f) = !A.
        res->acc = acc_cond{swa1->acc.get_acceptance().complement()};
      }
    else if (the_product_data.swa1_taut_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_taut_implies;
        res = product_mtdswa_aux(swa1, swa2, op::Implies, cs, &cache, 0);
        // IMPLIES(t, B): alive→B, dead→true.
        // = Fin(status) | B.acc.
        res->acc = acc_cond{fin_st
                            | (swa2->acc.get_acceptance()
                               << the_product_data.swa1_max_color_)};
      }
    else if (the_product_data.swa1_unsatis_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_unsat_implies;
        res = product_mtdswa_aux(swa1, swa2, op::Implies, cs, &cache, 0);
        // IMPLIES(f, B) = t.
        res->acc = acc_cond{acc_cond::acc_code::t()};
      }
    else
      {
        bool both_degen = (the_product_data.swa1_taut_
                           || the_product_data.swa1_unsatis_);
        cs = (both_degen
              ? &product_data::colors_both_degenerate
              : &product_data::colors_general);
        res = product_mtdswa_aux(swa1, swa2, op::Implies, cs, &cache, 0);
        if (SPOT_UNLIKELY(both_degen))
          // Both sides degenerate: IMPLIES(f,_)=t, IMPLIES(_,t)=t,
          // IMPLIES(t,f)=f.
          res->acc = acc_cond{((!the_product_data.swa1_taut_
                                || the_product_data.swa2_taut_)
                               ? acc_cond::acc_code::t()
                               : acc_cond::acc_code::f())};
        else
          res->acc
            = acc_cond{(swa1->acc.get_acceptance().complement())
                       | (swa2->acc.get_acceptance()
                          << the_product_data.swa1_max_color_)};
      }
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr product_xnor(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_product(swa1, swa2), true);
    the_product_data.setup(swa1, swa2, op::Equiv);
    mtdswa_ptr res;
    product_data::color_strategy_t cs;
    auto inf_st = acc_cond::acc_code::inf(the_product_data.status_mark_);
    auto fin_st = acc_cond::acc_code::fin(the_product_data.status_mark_);
    if (the_product_data.swa2_taut_
        && !the_product_data.swa1_taut_
        && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_taut_equiv_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Equiv, cs, &cache, 0);
        // EQUIV(A, t): alive→A, dead→!A.
        res->acc = acc_cond{(inf_st & swa1->acc.get_acceptance())
                            | (fin_st
                               & swa1->acc.get_acceptance().complement())};
      }
    else if (the_product_data.swa2_unsatis_
             && !the_product_data.swa1_taut_
             && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_unsat_equiv;
        res = product_mtdswa_aux(swa1, swa2, op::Equiv, cs, &cache, 0);
        // EQUIV(A, f): alive→!A, dead→true.
        // = Fin(status) | !A.acc.
        res->acc = acc_cond{fin_st
                            | swa1->acc.get_acceptance().complement()};
      }
    else if (the_product_data.swa1_taut_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_taut_equiv_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Equiv, cs, &cache, 0);
        // EQUIV(t, B): alive→B, dead→!B.
        auto acc2 = swa2->acc.get_acceptance()
          << the_product_data.swa1_max_color_;
        res->acc = acc_cond{(inf_st & acc2)
                            | (fin_st & acc2.complement())};
      }
    else if (the_product_data.swa1_unsatis_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_unsat_equiv;
        res = product_mtdswa_aux(swa1, swa2, op::Equiv, cs, &cache, 0);
        // EQUIV(f, B): alive→!B, dead→true.
        // = Fin(status) | !B.acc.
        res->acc = acc_cond{fin_st
                            | (swa2->acc.get_acceptance()
                               << the_product_data.swa1_max_color_)
                            .complement()};
      }
    else
      {
        bool both_degen = (the_product_data.swa1_taut_
                           || the_product_data.swa1_unsatis_);
        cs = (both_degen
              ? &product_data::colors_both_degenerate
              : &product_data::colors_general);
        res = product_mtdswa_aux(swa1, swa2, op::Equiv, cs, &cache, 0);
        if (SPOT_UNLIKELY(both_degen))
          // Both sides degenerate: EQUIV(t,t)=t, EQUIV(f,f)=t,
          // EQUIV(t,f)=f.
          res->acc = acc_cond{((the_product_data.swa1_taut_
                                == the_product_data.swa2_taut_)
                               ? acc_cond::acc_code::t()
                               : acc_cond::acc_code::f())};
        else
          {
            auto A = swa1->acc.get_acceptance();
            auto B = swa2->acc.get_acceptance()
              << the_product_data.swa1_max_color_;
            res->acc = acc_cond{(A & B)
                                | (A.complement() & B.complement())};
          }
      }
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr product_xor(const mtdswa_ptr& swa1, const mtdswa_ptr& swa2)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_product(swa1, swa2), true);
    the_product_data.setup(swa1, swa2, op::Xor);
    mtdswa_ptr res;
    product_data::color_strategy_t cs;
    auto inf_st = acc_cond::acc_code::inf(the_product_data.status_mark_);
    auto fin_st = acc_cond::acc_code::fin(the_product_data.status_mark_);
    if (the_product_data.swa2_taut_
        && !the_product_data.swa1_taut_
        && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_taut_equiv_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Xor, cs, &cache, 0);
        // XOR(A, t): alive→!A, dead→A.
        res->acc = acc_cond{(inf_st
                             & swa1->acc.get_acceptance().complement())
                            | (fin_st & swa1->acc.get_acceptance())};
      }
    else if (the_product_data.swa2_unsatis_
             && !the_product_data.swa1_taut_
             && !the_product_data.swa1_unsatis_)
      {
        cs = &product_data::colors_swa2_unsat_or_implies_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Xor, cs, &cache, 0);
        // XOR(A, f) = A.
        res->acc = acc_cond{swa1->acc.get_acceptance()};
      }
    else if (the_product_data.swa1_taut_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_taut_equiv_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Xor, cs, &cache, 0);
        // XOR(t, B): alive→!B, dead→B.
        auto acc2 = swa2->acc.get_acceptance()
          << the_product_data.swa1_max_color_;
        res->acc = acc_cond{(inf_st & acc2.complement())
                            | (fin_st & acc2)};
      }
    else if (the_product_data.swa1_unsatis_
             && !the_product_data.swa2_taut_
             && !the_product_data.swa2_unsatis_)
      {
        cs = &product_data::colors_swa1_unsat_or_xor;
        res = product_mtdswa_aux(swa1, swa2, op::Xor, cs, &cache, 0);
        // XOR(f, B) = B.
        res->acc = acc_cond{swa2->acc.get_acceptance()
                            << the_product_data.swa1_max_color_};
      }
    else
      {
        bool both_degen = (the_product_data.swa1_taut_
                           || the_product_data.swa1_unsatis_);
        cs = (both_degen
              ? &product_data::colors_both_degenerate
              : &product_data::colors_general);
        res = product_mtdswa_aux(swa1, swa2, op::Xor, cs, &cache, 0);
        if (SPOT_UNLIKELY(both_degen))
          // Both sides degenerate: XOR(t,t)=f, XOR(f,f)=f,
          // XOR(t,f)=t.
          res->acc = acc_cond{((the_product_data.swa1_taut_
                                != the_product_data.swa2_taut_)
                               ? acc_cond::acc_code::t()
                               : acc_cond::acc_code::f())};
        else
          {
            auto A = swa1->acc.get_acceptance();
            auto B = swa2->acc.get_acceptance()
              << the_product_data.swa1_max_color_;
            res->acc = acc_cond{(A & B.complement())
                                | (A.complement() & B)};
          }
      }
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr complement(const mtdswa_ptr& swa)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, 0, true);
    mtdswa_ptr res = complement_aux(swa, &cache, 0);
    bdd_extcache_done(&cache);
    return res;
  }


  namespace
  {
    // Used to renumber states.
    static std::vector<int> renum;

    static int trim_renumber(int bdd, int term)
    {
      // bddtrue and bddfalse are left unchanged.
      if (bdd == 0 || bdd == 1)
        return bdd;
      assert((unsigned) term < renum.size());
      int newterm = renum[term];
      // Renumbered state.
      if (newterm != -1)
        return bdd_terminal_as_int(newterm);
      return 0;
    }

    // Light version of trim_mtdswa that only removes inaccessible states.
    void trim_dead_states(mtdswa_ptr swa, bddExtCache* cache, int hash_key)
    {
      // Do a BFS from the initial state, and mark all accessible states.
      unsigned n = swa->num_roots();
      std::vector<bool> accessible(n, false);
      std::queue<int> q;
      q.push(0);
      accessible[0] = true;
      while (!q.empty())
        {
          int s = q.front();
          q.pop();
          // Mark all leaves rechable from s as accessible.
          for (bdd term : leaves_of(swa->states[s]))
            {
              if (SPOT_UNLIKELY(term != bddfalse && term != bddtrue))
                {
                  int next = bdd_get_terminal(term);
                  if (!accessible[next])
                    {
                      // Only continue the BFS from states that are not
                      // already marked as accessible.
                      accessible[next] = true;
                      q.push(next);
                    }
                }
            }
        }
      // Compute renumbering of states.
      renum = std::vector<int>(n, -1);
      int newnum = 0;
      for (unsigned s = 0; s < n; ++s)
        {
          if (accessible[s])
            {
              // This state is kept, and gets new number newnum.
              renum[s] = newnum;
              ++newnum;
            }
        }

      // Apply renumbering and remove inaccessible states.
      std::vector<bdd> new_states;
      std::vector<formula> new_names;
      std::vector<acc_cond::mark_t> new_colors;
      new_states.reserve(newnum);
      new_names.reserve(newnum);
      new_colors.reserve(newnum);

      // Renumber the states
      for (unsigned s = 0; s < n; ++s)
        if (renum[s] != -1)
          {
            bdd new_state = bdd_mt_apply1_leaves(swa->states[s],
                                                 trim_renumber,
                                                 cache, hash_key);
            new_states.push_back(new_state);
            new_colors.push_back(swa->colors[s]);
            if (s < swa->names.size())
              new_names.push_back(swa->names[s]);
          }
      swa->states = new_states;
      swa->names = new_names;
      swa->colors = new_colors;
    }

    typedef std::set<unsigned> quantify_state;

    struct quantify_state_hash
    {
      size_t
      operator()(const quantify_state s) const noexcept
      {
        std::size_t seed = 0;
        for (int x : s)
          {
            seed ^= wang32_hash(x) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
          }
        return seed;
      }
    };

    struct quantify_data
      {
        // A cache for the BDD terminals (as ints) in the product automaton
        // associated to a set of states of the original automata.
        std::unordered_map<quantify_state, int,
                           quantify_state_hash> set_to_terminal_map;
        // Maps terminal values of the quantified automaton to the corresponding
        // set of states of the original automaton.
        std::vector<quantify_state> terminal_to_set_map;
        // Used to store the product states that still need to be processed.
        // When new states are created, they are added here.
        std::queue<quantify_state> todo;
        // The value of the first terminal created for a set of states.  Set to
        // max terminal value of the original automaton + 1 to avoid collisions.
        unsigned state_offset;


        // Maps a set of states from the original automaton to terminals in
        // the quantified automaton.
        int set_to_terminal(const quantify_state& s)
        {
          // If a terminal for this set exists then return it.
          if (auto it = set_to_terminal_map.find(s);
              it != set_to_terminal_map.end())
            {
              return it->second;
            }
          // Otherwise create a new one, cache it and return it.
          unsigned new_id = state_offset + set_to_terminal_map.size();
          terminal_to_set_map.push_back(s);
          int res = bdd_terminal_as_int(new_id);
          set_to_terminal_map.emplace(s, res);
          todo.emplace(s);
          return res;
        }

        // Adds the state(s) correponding to a terminal value to the given set.
        void add_state_to_set(quantify_state& s, unsigned v) const
        {
          if (v < state_offset)
            {
              // State from the original automaton.
              s.insert(v);
            }
          else
            {
              // State from the quantified automaton, corresponding to a set of
              // states from the original automaton.
              quantify_state st = terminal_to_set_map[v - state_offset];
              s.insert(st.begin(), st.end());
            }
        }

      }
      the_quantify_data;

    // Compute the intersection of the colors of a set of states.
    static inline acc_cond::mark_t
    colors_of_qstate_and(mtdswa_ptr swa, quantify_state state)
    {
      auto it = state.begin();
      acc_cond::mark_t res = swa->colors[*it];
      for (++it; it != state.end(); ++it)
        res &= swa->colors[*it];
      return res;
    }

    // Compute the union of the colors of a set of states.
    static inline acc_cond::mark_t
    colors_of_qstate_or(mtdswa_ptr swa, quantify_state state)
    {
      acc_cond::mark_t res = {};
      for (unsigned s: state)
        res |= swa->colors[s];
      return res;
    }

    // Combine two leaves of the automaton with AND.
    static int quant_leaf_combine_and(int left, int left_term,
                                int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 1 && right == 1))
        return 1;
      if (SPOT_UNLIKELY(left == 0 || right == 0))
        return 0;
      quantify_state s;
      if (left != 1)
        the_quantify_data.add_state_to_set(s, left_term);
      if (right != 1)
        the_quantify_data.add_state_to_set(s, right_term);

      if (s.empty())
        return 1;
      return the_quantify_data.set_to_terminal(s);
    }

    // Combine two leaves of the automaton with OR.
    static int quant_leaf_combine_or(int left, int left_term,
                                int right, int right_term)
    {
      if (SPOT_UNLIKELY(left == 0 && right == 0))
        return 0;
      if (SPOT_UNLIKELY(left == 1 || right == 1))
        return 1;
      quantify_state s;
      if (left != 0)
        the_quantify_data.add_state_to_set(s, left_term);
      if (right != 0)
        the_quantify_data.add_state_to_set(s, right_term);

      if (s.empty())
        return 0;
      return the_quantify_data.set_to_terminal(s);
    }

    static int quant_leaf_combine1(int bdd, int term)
    {
      if (SPOT_UNLIKELY(bdd == 0))
        return 0;
      if (SPOT_UNLIKELY(bdd == 1))
        return 1;
      return the_quantify_data.set_to_terminal({(unsigned)term});
    }

    // temporary
    static int unshift_terminals(int bdd, int term)
    {
      if (SPOT_UNLIKELY(bdd == 0))
        return 0;
      if (SPOT_UNLIKELY(bdd == 1))
        return 1;
      return bdd_terminal_as_int(term - the_quantify_data.state_offset);
    }


    // Combines a vector of BDDs with the given operator and combine
    // function.  combine1 is used when the vector has only one element.
    static bdd applyn_leaves(const std::vector<bdd>& bdds, op o,
                             int (*combine)(int, int, int, int),
                             int (*combine1)(int, int),
                             bddExtCache* cache, int hash_key,
                             int applyop_shortcut)
    {
      // If empty vector, return the neutral element of the operator.
      if (SPOT_UNLIKELY(bdds.empty()))
        {
          switch (o)
            {
            case op::And:
              return bddtrue;
            case op::Or:
              return bddfalse;
            default:
              throw std::runtime_error("applyn_leaves: unsupported operator");
            }
        }
      // If only one element in the vector, apply combine1 to it.
      if (bdds.size() == 1)
        return bdd_mt_apply1_leaves(bdds[0], combine1, cache, hash_key);
      // Otherwise, combine elements left to right.
      bdd res = bdds[0];
      for (size_t i = 1; i < bdds.size(); ++i)
        res = bdd_mt_apply2_leaves(res, bdds[i], combine, cache, hash_key,
                                   applyop_shortcut);
      return res;
    }


    // Quantify the given variable(s) in a weak mtdswa.
    // \a vars is a positive cube (conjunction) of BDD variables to remove.
    static mtdswa_ptr
    quantify_mtdswa_aux(const mtdswa_ptr& swa, bdd vars, op o,
                        bddExtCache* cache, int quant_hash, int apply_hash)
    {
      // Prepare the function to combine two leaves of the product automaton.
      int (*combine)(int, int, int, int);
      int applyop_shortcut = -1;
      switch (o)
        {
        case op::And:
          combine = quant_leaf_combine_and;
          applyop_shortcut = bddop_and_zero;
          break;
        case op::Or:
          combine = quant_leaf_combine_or;
          applyop_shortcut = bddop_or_one;
          break;
        default:
          throw std::runtime_error("product_mtdswa_aux: unsupported operator");
        }
      // Create result automaton, and register all propositions.
      bdd_dict_ptr dict = swa->get_dict();
      mtdswa_ptr res = std::make_shared<mtdswa>(dict);
      dict->register_all_propositions_of(swa, res);
      res->aps = swa->aps;
      res->acc = swa->acc;

      // The terminal ids of states in the quantified automaton will be shifted
      // by the max terminal value of the original automaton.
      the_quantify_data.state_offset = swa->states.size();
      // This will initialize todo with the initial state of the quantification.
      std::queue<quantify_state>& todo = the_quantify_data.todo;
      (void) the_quantify_data.set_to_terminal(quantify_state{0});

      // Prepare quantification once, before the main loop.
      bdd_mt_quantify_prepare(vars);

      while (!todo.empty())
        {
          quantify_state state = todo.front();
          todo.pop();

          // 1 - Combine all states in s with the operator and adjust names.
          std::vector<bdd> bdds;
          unsigned ns = swa->names.size();
          formula combined_f = o == op::And ? formula::tt() : formula::ff();
          for (unsigned s: state)
          {
            bdds.push_back(swa->states[s]);
            // Combine names if not null.
            formula f = s < ns ? swa->names[s] : nullptr;
            if (combined_f)
            {
              if (f)
              {
                switch (o)
                  {
                  case op::And:
                    combined_f = formula::And(combined_f, f);
                    break;
                  case op::Or:
                    combined_f = formula::Or(combined_f, f);
                    break;
                  default:
                    SPOT_UNREACHABLE();
                  }
              }
              else
                combined_f = nullptr;
            }
          }
          // Combine all states in the quantify_state with the operator.
          bdd b = applyn_leaves(bdds, o, combine, quant_leaf_combine1, cache,
                                 apply_hash, applyop_shortcut);

          // 2 - Quantify the given variables in the resulting BDD.
          bdd qb = bdd_mt_quantify(b, [](int v){ return v; }, combine, cache,
                                   quant_hash, apply_hash, applyop_shortcut);
          // Unshift the terminal values of the resulting BDD to match
          // the new state ids.
          qb = bdd_mt_apply1_leaves(qb, unshift_terminals, cache, apply_hash);

          res->states.push_back(qb);

          // Compute the colors of the quantified state.
          acc_cond::mark_t col = o == op::And
                                 ? colors_of_qstate_and(swa, state)
                                 : colors_of_qstate_or(swa, state);
          res->colors.push_back(col);

          // Construct name of the quantified state.
          // Collect all APs for the variables in the cube.
          std::vector<formula> aps;
          if (vars != bddtrue)
            {
              bdd cube = vars;
              while (cube != bddtrue)
                {
                  formula ap = swa->get_dict()->ap_from_var(bdd_var(cube));
                  if (ap)
                    aps.push_back(ap);
                  cube = bdd_high(cube);
                }
            }
          if (combined_f && !aps.empty())
            switch (o)
              {
              case op::And:
                res->names.push_back(formula::forall(aps, combined_f));
                break;
              case op::Or:
                res->names.push_back(formula::exists(aps, combined_f));
                break;
              default:
                SPOT_UNREACHABLE();
              }
        }
      the_quantify_data.set_to_terminal_map.clear();
      the_quantify_data.terminal_to_set_map.clear();
      return res;
    }
  }


  mtdswa_ptr quantify_exists(const mtdswa_ptr& swa, bdd vars, bool trim)
  {
    if (vars == bddtrue)
      return swa;
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_quantify(swa), true);
    mtdswa_ptr res = quantify_mtdswa_aux(swa, vars, op::Or, &cache, 0, 1);
    if (trim)
      trim_dead_states(res, &cache, 2);
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr quantify_forall(const mtdswa_ptr& swa, bdd vars, bool trim)
  {
    if (vars == bddtrue)
      return swa;
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_quantify(swa), true);
    mtdswa_ptr res = quantify_mtdswa_aux(swa, vars, op::And, &cache, 0, 1);
    if (trim)
      trim_dead_states(res, &cache, 2);
    bdd_extcache_done(&cache);
    return res;
  }

  mtdswa_ptr quantify_exists(const mtdswa_ptr& swa, const formula& ap,
                             bool trim)
  {
    return quantify_exists(swa, aps_to_bdd(swa, {ap}), trim);
  }

  mtdswa_ptr quantify_exists(const mtdswa_ptr& swa,
                             const std::vector<formula>& aps, bool trim)
  {
    return quantify_exists(swa, aps_to_bdd(swa, aps), trim);
  }

  mtdswa_ptr quantify_forall(const mtdswa_ptr& swa, const formula& ap,
                             bool trim)
  {
    return quantify_forall(swa, aps_to_bdd(swa, {ap}), trim);
  }

  mtdswa_ptr quantify_forall(const mtdswa_ptr& swa,
                             const std::vector<formula>& aps, bool trim)
  {
    return quantify_forall(swa, aps_to_bdd(swa, aps), trim);
  }

}
