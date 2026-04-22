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
                        res->new_edge(ni, true_state(), b, colors[ni]);
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
                        res->new_edge(ni, dst, b, colors[ni]);
                      }
                else
                  for (auto [b, t]: paths_mt_of(states[i]))
                    if (t == bddtrue)
                      {
                        res->new_edge(ni, true_state(), b, colors[ni]);
                      }
                    else
                      {
                        int dst = new_num[bdd_get_terminal(t)];
                        if (dst < 0) // edge going to a sink
                          continue;
                        res->new_edge(ni, dst, b, colors[ni]);
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

        if ((unsigned) var < dict_->bdd_map.size()
            && dict_->bdd_map[bdd_var(n)].type == bdd_dict::var)
          label = escape_str(str_psl(dict_->bdd_map[var].f));
        else
          label = "var" + std::to_string(var);

        bool outputnode = (!controllable.empty()
                           && controllable.find(var) != controllable.end());
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
            if (removable.find(sub) == removable.end())
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
            if (removable.find(sub) == removable.end())
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
      // For the purpose of debuging, a name may be passed.  It will
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
      // provided they correspond to underterminate vertices.  Doing
      // so allows to collect all undeterminate successors even if
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
      // remplace losing terminals by bddfalse
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

    // Keep track of atomic propositions used in he automaton.
    // Actually, the automaton might use fewer atomic propositions
    // than what appears in the formula, but we do not pay attention
    // to that.
    {
      atomic_prop_set* a = atomic_prop_collect(f);
      dfa->aps.assign(a->begin(), a->end());
      delete a;
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
          while (f.is(op::exists, op::forall))
            {
              bool is_exists = f.is(op::exists);

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
                  {
                    bdd bi = bdd_ithvar(dict_->register_proposition(g, dfa));
                    if (is_exists)
                      existsvars &= bi;
                    else
                      forallvars &= bi;
                  }
                return false;
              });
              f = f[last];
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
                      // SCC as accepting, otherwise we will have undeterminate
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

}
