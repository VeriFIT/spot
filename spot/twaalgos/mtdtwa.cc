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
#include <spot/twaalgos/mtdtwa.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/priv/robin_hood.hh>
#include <spot/misc/escape.hh>
#include <spot/tl/print.hh>
#include <spot/tl/apcollect.hh>

// Some of the MTBDD operations may share the same operation cache, so
// they need an hash key to be distinguished.
constexpr int hash_key_and = 1;
constexpr int hash_key_or = 2;
constexpr int hash_key_implies = 3;
constexpr int hash_key_equiv = 4;
constexpr int hash_key_xor = 5;
constexpr int hash_key_not = 6;
constexpr int hash_key_rename = 7;
//constexpr int hash_key_strat = 8;
//constexpr int hash_key_strat_bool = 9;
//constexpr int hash_key_finalstrat = 10;


namespace spot
{
  namespace
  {
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

    struct pairmu_hash
    {
      std::size_t operator()(const std::pair<acc_cond::mark_t,
                                             unsigned>& p) const
      {
        return std::hash<unsigned>()(p.second) ^ p.first.hash();
      }
    };


    void outset(std::ostream& os, int v)
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

  mtdtwa_ptr dtwa_to_mtdtwa(const twa_graph_ptr& twa)
  {
    if (!is_deterministic(twa))
      throw std::runtime_error("dtwa_to_mtdtwa: input is not deterministic");
    mtdtwa_ptr dfa = std::make_shared<mtdtwa>(twa->get_dict());
    dfa->dict_->register_all_variables_of(&twa, dfa);
    unsigned n = twa->num_states();
    unsigned init = twa->get_init_state_number();

    robin_hood::unordered_map<std::pair<acc_cond::mark_t,
                                        unsigned>,
                              unsigned, pairmu_hash> term_map;

    auto new_terminal([&term_map, &dfa](acc_cond::mark_t acc, unsigned state) {
      auto p = std::make_pair(acc, state);
      auto it = term_map.find(p);
      if (it != term_map.end())
        return bdd_terminal(it->second);
      unsigned t = dfa->terminal_data_map.size();
      dfa->terminal_data_map.push_back({acc, state});
      term_map[p] = t;
      return bdd_terminal(t);
    });

    acc_cond acc = twa->acc();

    // twa's state i should be named remap[i] in dfa.  The remapping is
    // needed because the dfa only accept 0 as initial state, and we
    // do not want to represent sink states.
    std::vector<unsigned> remap;
    remap.reserve(n);
    unsigned next = 1;
    for (unsigned i = 0; i < n; ++i)
      {
        if (i == init)
          {
            remap.push_back(0);
            continue;
          }
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
        remap.push_back(next++);
      }

    dfa->states.resize(next);

    for (unsigned i = 0; i < n; ++i)
      {
        unsigned state = remap[i];
        if (state == -1U)     // sink
          continue;
        bdd b = bddfalse;
        for (auto& e: twa->out(i))
          {
            unsigned dst = remap[e.dst];
            if (dst == -1U)   // sink
              b |= e.cond;
            else
              b |= e.cond & new_terminal(e.acc, dst);
          }
        dfa->states[state] = b;
      }
    dfa->acc = acc;
    return dfa;
  }

  // convert the MTBDD DFA representation into a DFA.
  twa_graph_ptr mtdtwa::as_twa(bool state_based, bool labels) const
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
    auto true_state = [&res, this, &sat_colors, sink = -1] () mutable -> int {
      if (sink >= 0)
        return sink;

      auto [satisfiable, satcols] = acc.sat_mark();
      if (SPOT_UNLIKELY(!satisfiable))
        throw std::runtime_error
          ("mtdtwa::as_twa cannot declare "
           "an accepting sink with this acceptance");

      sat_colors = satcols;
      sink = res->new_state();
      res->new_edge(sink, sink, bddtrue, satcols);
      return sink;
    };

    (void) labels;
    // std::vector<std::string>* names = nullptr;
    // if (labels && this->names.size() == this->states.size())
    //   {
    //     names = new std::vector<std::string>;
    //     names->reserve(n);
    //     res->set_named_prop("state-names", names);
    //     if (!state_based)
    //       for (unsigned i = 0; i < n; ++i)
    //         names->push_back(str_psl(this->names[i]));
    //   }

    if (!state_based)
      {
        res->new_states(n);
        for (unsigned i = 0; i < n; ++i)
          for (auto [b, t]: paths_mt_of(states[i]))
            if (t != bddtrue)
              {
                unsigned v = bdd_get_terminal(t);
                assert(v < terminal_data_map.size());
                auto [colors, dst] = terminal_data_map[v];
                res->new_edge(i, dst, b, colors);
              }
            else
              {
                res->new_edge(i, true_state(), b, sat_colors);
              }
        res->merge_edges();
      }
    else                        // state-based
      {

        // The set of states in the new automaton is terminal_data_map
        // plus optionally an accepting sink (if bddtrue appears in
        // the MTBDDs), and the initial state (if no compatible state
        // exists in terminal_data_map).

        // For now, just declare states for each of terminal_data_map.
        unsigned ns = terminal_data_map.size();
        res->new_states(ns);

        // See if one of these states can be used as initial state.
        unsigned init = -1U;
        for (unsigned i = 0; i < ns; ++i)
          if (terminal_data_map[i].second == 0)
            {
              init = i;
              break;
            }
        // Else, declare a new state for the initial state.
        if (init == -1U)
          {
            init = res->new_state();
            for (auto [b, t]: paths_mt_of(states[0]))
              {
                if (t != bddtrue)
                  res->new_edge(init, bdd_get_terminal(t), b);
                else
                  res->new_edge(init, true_state(), b);
              }
          }
        res->set_init_state(init);
        for (unsigned i = 0; i < ns; ++i)
          {
            auto&[colors, dst] = terminal_data_map[i];
            for (auto [b, t]: paths_mt_of(states[dst]))
              {
                if (t != bddtrue)
                  res->new_edge(i, bdd_get_terminal(t), b, colors);
                else
                  res->new_edge(i, true_state(), b, colors);
              }
          }
        res->merge_edges();
      }
    return res;
  }

  std::ostream& mtdtwa::print_dot(std::ostream& os) const
  {
    std::ostringstream edges;

    os << "digraph mtdtwa {\n  rankdir=TB;\n  node [shape=circle];\n";
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
    for (unsigned i = 0; i < ns; ++i)
      {
        os << "    S" << i << (" [shape=box, style=\"filled,rounded\", "
                               "fillcolor=\"#e9f4fb\", label=\"")
           << i;
        os <<  "\"];\n";
      }

    for (unsigned i = 0; i < ns; ++i)
      edges << "  S" << i << " -> B" << states[i].id()
            << " [tooltip=\"[" << i << "]\"];\n";

    // This is a heap of BDD nodes, with smallest level at the top.
    std::vector<bdd> nodes;
    robin_hood::unordered_set<int> seen;

    nodes.reserve(ns);
    for (unsigned i = 0; i < ns; ++i)
      if (bdd b = states[i]; seen.insert(b.id()).second)
        nodes.push_back(b);

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
               << (" [shape=square, style=filled, fillcolor=\"#ffe6cc\", "
                   "label=\"")
               << n.id()
               << "\", tooltip=\"bdd(" << n.id() << ")\" ";
            if (n.id() == 1)
              os << ", peripheries=2";
            os << "];\n";
            oldvar = -2;
            continue;
          }
        if (bdd_is_terminal(n))
          {
            if (oldvar != -2)
              os << "  }\n  { rank = sink;\n";
            os << "    B" << n.id()
               << (" [shape=box, style=\"filled,rounded\", "
                   "fillcolor=\"#ffe5f1\", label=<");
            int t = bdd_get_terminal(n);
            auto [m, dst] = terminal_data_map[t];
            os << dst << "<br/>";
            for (auto v: m.sets())
              outset(os, v);
            os << ">, tooltip=\"bdd(" << n.id()
               << ")=term(" << t << ")=[" << dst << "]\"";
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

        os << "    B" << n.id()
           << " [style=filled, fillcolor=\"#ffffff\", label=\"" << label
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
    os << edges.str();
    os << "}\n";
    return os;
  }

  // convert the MTBDD DFA representation into a DFA.
  twa_graph_ptr mtdswa::as_twa(bool state_based, bool labels) const
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
    auto true_state = [&res, this, &sat_colors, sink = -1] () mutable -> int {
      if (sink >= 0)
        return sink;

      auto [satisfiable, satcols] = acc.sat_mark();
      if (SPOT_UNLIKELY(!satisfiable))
        throw std::runtime_error
          ("mtdtwa::as_twa cannot declare "
           "an accepting sink with this acceptance");

      sat_colors = satcols;
      sink = res->new_state();
      res->new_edge(sink, sink, bddtrue, satcols);
      return sink;
    };

    (void) labels;
    // std::vector<std::string>* names = nullptr;
    // if (labels && this->names.size() == this->states.size())
    //   {
    //     names = new std::vector<std::string>;
    //     names->reserve(n);
    //     res->set_named_prop("state-names", names);
    //     if (!state_based)
    //       for (unsigned i = 0; i < n; ++i)
    //         names->push_back(str_psl(this->names[i]));
    //   }

    if (!state_based)
      {
        res->new_states(n);
        for (unsigned i = 0; i < n; ++i)
          for (auto [b, t]: paths_mt_of(states[i]))
            if (t != bddtrue)
              {
                unsigned dst = bdd_get_terminal(t);
                res->new_edge(i, dst, b, colors[dst]);
              }
            else
              {
                res->new_edge(i, true_state(), b, sat_colors);
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
        res->new_states(ns);

        res->set_init_state(0);
        for (unsigned i = 0; i < ns; ++i)
          {
            auto& col = colors[i];
            for (auto [b, t]: paths_mt_of(states[i]))
              {
                if (t != bddtrue)
                  res->new_edge(i, bdd_get_terminal(t), b, col);
                else
                  res->new_edge(i, true_state(), b, col);
              }
          }
        res->merge_edges();
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
    // However is the accepting condition is unsatisfiable, we have to
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
    global_state_map = &new_state_number;
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

    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(shared_from_this()), false);

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
    assert(ns == colors.size());
    unsigned namesz = names.size();

    for (unsigned i = 0; i < ns; ++i)
      {
        os << "    S" << i << (" [shape=box, style=\"filled,rounded\", "
                               "fillcolor=\"#e9f4fb\", label=<");
        if (opt_labels && i < namesz)
          escape_html(os, str_psl(names[i]));
        else
          os << i;
        os << "<br/>";
        for (auto v: colors[i].sets())
          outset(os, v);
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
        if (opt_scc)
          {
            bdd tmp = bdd_terminal(i);
            if (auto it = scc_map.find(tmp.id()); it != scc_map.end())
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
               << (" [shape=square, style=filled, fillcolor=\"#ffe6cc\", "
                   "label=\"")
               << n.id()
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
            os << "    B" << n.id()
               << (" [shape=box, style=\"filled,rounded\", "
                   "fillcolor=\"#ffe5f1\", label=<");
            unsigned t = bdd_get_terminal(n);
            if (opt_labels && t < namesz)
              escape_html(os, str_psl(names[t]));
            else
              os << t;
            os << "<br/>";
            for (auto v: colors[t].sets())
              outset(os, v);
            os << ">, tooltip=\"bdd(" << n.id()
               << ")=term(" << t << ")=[" << t << "]\"";
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

        os << "    B" << n.id()
           << " [style=filled, fillcolor=\"#ffffff\", label=\"" << label
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
    dfa->get_dict()->register_all_variables_of(&twa, dfa);
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

  // This implement propositional equivalence plus some very light
  // simplifications
  formula simple_ltl_translator::propeq_representative(formula f)
  {
    // We start we the simplifications
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


    auto formula_to_bddvar = [&] (formula f) -> int
    {
      if (auto it = formula_to_var_.find(f);
          it != formula_to_var_.end())
        return it->second;
      if (f.is(op::ap))
        {
          int v = dict_->register_proposition(f, this);
          formula_to_var_[f] = v;
          return v;
        }
      int v = dict_->register_anonymous_variables(1, this);
      formula_to_var_[f] = v;
      return v;
    };

    // Convert the formula to a BDD suitable for propositional
    // equivalence.  Any subformula that has a non-boolean
    // operator is replaced by atomic proposition.
    auto encode_rec = [&] (formula f, auto rec) -> bdd
    {
      switch (f.kind())
        {
        case op::tt:
          return bddtrue;
        case op::ff:
          return bddfalse;
        case op::ap:
          return bdd_ithvar(formula_to_bddvar(f));
        case op::Not:
          if (f[0].is_leaf())   // skip one application of bdd_not.
            {
              if (f[0].is_tt())
                return bddfalse;
              if (f[0].is_ff())
                return bddtrue;
              return bdd_nithvar(formula_to_bddvar(f[0]));
            }
          return bdd_not(rec(f[0], rec));
        case op::And:
          {
            bdd res = bddtrue;
            for (const formula& sub: f)
              res &= rec(sub, rec);
            return res;
          }
        case op::Or:
          {
            bdd res = bddfalse;
            for (const formula& sub: f)
              res |= rec(sub, rec);
            return res;
          }
        case op::Xor:
          {
            bdd left = rec(f[0], rec);
            return left ^ rec(f[1], rec);
          }
        case op::Implies:
          {
            bdd left = rec(f[0], rec);
            return left >> rec(f[1], rec);
          }
        case op::Equiv:
          {
            bdd left = rec(f[0], rec);
            return bdd_biimp(left, rec(f[1], rec));
          }
        default:
          return bdd_ithvar(formula_to_bddvar(f));
        }
    };

    bdd enc = encode_rec(f, encode_rec);
    if (enc == bddtrue)
      f = formula::tt();
    else if (enc == bddfalse)
      f = formula::ff();
    auto [it, _] = propositional_equiv_.emplace(enc, f);
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

    if (formula g = propeq_representative(f); g != f)
      {
        auto it = formula_to_int_.find(g);
        if (it == formula_to_int_.end())
          {
            // This can occur if propeq_representative simplifies
            // the formula.
            int v = int_to_formula_.size();
            int_to_formula_.push_back(g);
            formula_to_int_[g] = v;
            formula_to_int_[f] = v;
            return v;
          }
        int v = it->second;
        formula_to_int_[f] = v;
        return v;
      }

    int v = int_to_formula_.size();
    int_to_formula_.push_back(f);
    formula_to_int_[f] = v;
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
    static simple_ltl_translator* term_combine_trans;
    static int term_combine_and(int left, int left_term,
                                int right, int right_term)
    {
      formula lf = term_combine_trans->leaf_to_formula(left, left_term);
      formula rf = term_combine_trans->leaf_to_formula(right, right_term);
      formula res = formula::And({lf, rf});
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_or(int left, int left_term,
                               int right, int right_term)
    {
      formula lf = term_combine_trans->leaf_to_formula(left, left_term);
      formula rf = term_combine_trans->leaf_to_formula(right, right_term);
      formula res = formula::Or({lf, rf});
      return term_combine_trans->formula_to_terminal_bdd_as_int(res);
    }

    static int term_combine_implies(int left, int left_term,
                                    int right, int right_term)
    {
      formula lf = term_combine_trans->leaf_to_formula(left, left_term);
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

      switch (f.kind())
        {
        case op::tt:
          return true;
        case op::ap:            // can return false or true
        case op::ff:
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
              return false;     // or true, it's irrelevant
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
              return false;     // or true, it's irrelevant
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
          // These are not supported by the translator.
          throw
            std::runtime_error("obligation_is_accepting: unsupported operator");
        }
      SPOT_UNREACHABLE();
      return false;
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

  // This is the main translation function.  It has grown to do a bit
  // too much, as it optionally performs on-the-fly game solving.
  mtdswa_ptr
  simple_ltl_translator::ltl_to_mtdswa(formula f,
                                       bool fuse_same_bdds)
  {
    mtdswa_ptr dfa = std::make_shared<mtdswa>(dict_);
    std::unordered_map<bdd, int, bdd_hash> bdd_to_state;
    std::unordered_map<formula, int> formula_to_state;
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

        if (fuse_same_bdds)
          if (auto it = bdd_to_state.find(b); it != bdd_to_state.end())
            {
              formula_to_state[label] = it->second;
              terminal_to_state_map[label_term] = it->second;
              continue;
            }
        unsigned n = states.size();
        formula_to_state[label] = n;
        bdd_to_state[b] = n;
        states.push_back(b);
        names.push_back(label);
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

    //if (detect_empty_univ)
    //  {
    //    if (!has_accepting)     // return a false MTDFA.
    //      {
    //        dfa->states.push_back(bddfalse);
    //        dfa->names.push_back(formula::ff());
    //        return dfa;
    //      }
    //    if (!has_rejecting)     // return a true MTDFA.
    //      {
    //        dfa->states.push_back(bddtrue);
    //        dfa->names.push_back(formula::tt());
    //        return dfa;
    //      }
    //  }

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
    dfa->colors.resize(dfa->states.size());
    dict_->register_all_propositions_of(this, dfa);

    // Fix the acceptance of states.  We are going for Büchi, but we
    // could go for Co-Büchi as well.
    dfa->acc = acc_cond::acc_code::buchi();
    acc_cond::mark_t macc{0};
    for (unsigned i = 0; i < dfa->states.size(); ++i)
      if (obligation_is_accepting(dfa->names[i]))
        dfa->colors[i] = macc;

    return dfa;
  }

  mtdswa_ptr obligation_to_mtdswa(formula f, const bdd_dict_ptr& dict,
                                  bool fuse_same_bdds, bool simplify_terms)
  {
    simple_ltl_translator trans(dict, simplify_terms);
    return trans.ltl_to_mtdswa(f, fuse_same_bdds);
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

  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa,
                             bddExtCache* cache,
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
    // terminal (dst, b) by (class[dst], b).  After this rewriting,
    // states whose MTBDD are different are put into different
    // classes, and we start again.  We iterate the process until no
    // more classes are created.

    // class is a global vector assigning classes to each state
    classes.clear();
    classes.reserve(n); // two extra classes for bddtrue/bddfalse

    // loop over all states, and give them a class that match their color
    {
      std::unordered_map<acc_cond::mark_t, int> col2cl;
      for (unsigned i = 0; i < n; ++i)
        {
          acc_cond::mark_t col = dfa->colors[i];
          auto it = col2cl.emplace(col, col2cl.size()).first;
          classes.push_back(it->second);
        }
    }

    // The "signature" of each state is their encoding using
    // the current set of classes.  The following vector remember
    // each unique signature in the order they were discovered.
    std::vector<bdd> signatures;
    signatures.reserve(n);
    // For each distinct signature, GROUPS retains the list of
    // states that have this signature.
    std::unordered_map<bdd, std::vector<int>, bdd_hash> groups;
    for (;;)
      {
        ++iteration;
        for (unsigned i = 0; i < n; ++i)
          {
            bdd sig = bdd_mt_apply1(dfa->states[i], rename_class,
                                    bddfalse, bddtrue,
                                    cache, iteration);
            auto& v = groups[sig];
            if (v.empty())
              signatures.push_back(sig);
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
        for (bdd sig: signatures)
          {
            int mapclass = curclass++;
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
        signatures.clear();
      }

    // The BDDs in SIGNATURES are actually our new MTBDD
    // representation.
    //
    // if WANT_NAMES is set we also have to keep one name per class
    // for display.
    bool want_names = dfa->names.size() == n;
    std::vector<formula> names;
    std::vector<acc_cond::mark_t> colors;
    // Our automaton will have SZ states;
    unsigned sz = signatures.size();
    if (want_names)
      names.reserve(sz);
    for (bdd sig: signatures)
      {
        auto& v = groups[sig];
        // We can pick any state in v as representative of the
        // class.  Here we simply pick the first one, but this
        // can be changed if needed (e.g. pick the one with
        // the shortest name since it is more readable?)
        unsigned repr = v.front();
        assert(repr < dfa->names.size());
        if (want_names)
          names.push_back(dfa->names[repr]);
        colors.push_back(dfa->colors[repr]);
      }

    mtdswa_ptr res = std::make_shared<mtdswa>(dfa->get_dict());
    std::swap(res->names, names);
    std::swap(res->states, signatures);
    std::swap(res->colors, colors);
    return res;
  }

  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa)
  {
    bddExtCache cache;
    bdd_extcache_init(&cache, size_estimate_unary(dfa), false);
    int iteration = 0;
    mtdswa_ptr res = minimize_mtdswa(dfa, &cache, iteration);
    bdd_extcache_done(&cache);
    return res;
  }


}
