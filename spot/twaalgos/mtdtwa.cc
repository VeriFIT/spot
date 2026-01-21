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
#include <spot/twaalgos/backprop.hh>

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
    dfa->dict_->register_all_propositions_of(twa, dfa);
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
    //     for (unsigned i = 0; i < n; ++i)
    //       names->push_back(str_psl(this->names[i]));
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
}
