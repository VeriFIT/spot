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

#include <vector>
#include <spot/twaalgos/deadends.hh>

namespace spot
{
  namespace
  {
    // Gather a disjunction of labels that appears on the edges of a
    // dead-end state that have to be seen in order to make an
    // accepting cycle.
    //
    // We actually return two candidates: (U1, U2).
    // - U1 is the union of labels of edges that are not immediately rejecting
    // - U2 is only used for Fin-less acceptances, and is a subset of labels
    //   that are necessary to satisfy one Inf(x) in each branch of the
    //   acceptance condition.   For acceptance involving Fin, U2 is set to
    //   bddtrue.
    static std::pair<bdd, bdd>
    gather_useful_labels(const const_twa_graph_ptr& aut,
                         acc_cond::mark_t used_in_cond,
                         unsigned state)
    {
      // First, simplify the acceptance condition c based on the set
      // of colors occurring around the state.
      acc_cond c = aut->get_acceptance();
      acc_cond::mark_t used_on_no_edge = used_in_cond;
      acc_cond::mark_t used_on_all_edges = used_in_cond;
      for (auto& e: aut->out(state))
        {
          used_on_no_edge -= e.acc;
          used_on_all_edges &= e.acc;
        }

      // if x appears on all edges, then
      //   Fin(x) = false and Inf(x) = true
      if (used_on_all_edges)
        c = c.remove(used_on_all_edges, false);
      // if x appears on no edge at all, then
      //   Fin(x) = true and Inf(x) = false
      if (used_on_no_edge)
        c = c.remove(used_on_no_edge, true);

      if (c.is_f())
        return {bddfalse, bddfalse};
      if (c.is_t())
        return {bddtrue, bddtrue};

      // any edge that isn't immediately rejecting is useful.
      bdd useful = bddfalse;
      for (auto& e: aut->out(state))
        if (c.inf_satisfiable(e.acc))
          useful |= e.cond;
      if (useful == bddfalse || c.uses_fin_acceptance())
        return {useful, useful};

      // For Fin-less acceptance, we can try to pick one inf() per
      // branch of the AST and see if that can be used to restrict the
      // incoming edge (this might not always work, depending on how
      // the incoming edge is labeled).
      acc_cond d = c.keep_one_inf_per_branch();

      // We consider an edge as useful if its colors satisfy at
      // least one Fin(x) or Inf(x) in the acceptance.
      bdd subset = bddfalse;
      for (auto& e: aut->out(state))
        if (d.accepting(e.acc))
          subset |= e.cond;
      return {useful, subset};
    }
  }

  twa_graph_ptr
  restrict_dead_end_edges_here(twa_graph_ptr& aut)
  {
    // We don't have anything to do if the automaton is deterministic.
    if (aut->prop_universal())
      return aut;
    if (!aut->is_existential())
      throw std::runtime_error
        ("restrict_dead_end_edges_here() does not support alternation");
    unsigned ns = aut->num_states();
    // Find the states that are dead ends, i.e., that
    // have only themselves as successors.
    std::vector<bool> dead_end_states(ns, true);
    // Also record the disjunction of all self-loops around each
    // state.
    std::vector<bdd> self_loops(ns, bddfalse);
    for (auto& e: aut->edges())
      if (e.src == e.dst)
        self_loops[e.src] |= e.cond;
      else
        dead_end_states[e.src] = false;

    // If the automaton is weak, we can consider every label of
    // the dead-end state as useful.
    bool is_weak = aut->prop_weak().is_true();

    // This will hold the labels of the useful self-loops of the
    // dead-end states.  But we don't want to initialize it until we
    // need it.
    //
    // For each dead-end state S, DEAD_END_USEFUL[S] stores a sequence of
    // union labels for candidate useful subsets.
    std::vector<std::pair<bdd, bdd>> dead_end_useful(is_weak ? 0U : ns,
                                                     {bddfalse, bddfalse});
    std::vector<bool> dead_end_useful_computed(is_weak ? 0U : ns, false);

    acc_cond::mark_t used_in_cond = aut->get_acceptance().used_sets();

    // LABEL_UNION[DST] is the union of all labels between current
    // state S and DST.
    std::vector<bdd> label_unions(ns, bddfalse);
    bool created_false_labels = false;
    bool nondeterministic_for_sure = false;
    for (unsigned s = 0; s < ns; ++s)
      {
        // compute a union of labels per dead-end destination
        for (auto& e: aut->out(s))
          if (e.src != e.dst && dead_end_states[e.dst])
            label_unions[e.dst] |= e.cond;

        // Iterate over all edges (SRC,COND,DST), find those such that
        // (1) DST is a dead-end,
        // (2) Lab(DST,DST)⇒Lab(SRC,SRC)
        // (3) UsefulLab(DST)⇒Lab(SRC,DST)⇒Lab(SRC,SRC)
        //
        // where Lab(X,Y) is the union of all labels between X and Y
        // (this is stored in label_union[Y]),
        // and UsefulLab(DST) are the labels of the "useful" self
        // loops of DST (see gather_useful_labels).
        for (auto& e: aut->out(s))
          if (e.src != e.dst && dead_end_states[e.dst])
            {
              if (bdd u = label_unions[e.dst], sl = self_loops[e.src];
                  bdd_implies(u, sl) && bdd_implies(self_loops[e.dst], sl))
                {
                  auto restrict_edge_maybe = [&](bdd d) {
                    if (bdd_implies(d, u))
                      {
                        // Restrict the dead-end transition's label.
                        bdd cond = e.cond;
                        cond &= d;
                        if (cond != e.cond)
                          {
                            e.cond = cond;
                            if (cond == bddfalse)
                              created_false_labels = true;
                            else
                              nondeterministic_for_sure = true;
                          }
                      }
                  };

                  // Find the edges of DST that are necessary to an
                  // accepting loop, and gather their labels.
                  if (is_weak)
                    {
                      restrict_edge_maybe(self_loops[e.dst]);
                    }
                  else
                    {
                      if (!dead_end_useful_computed[e.dst])
                        {
                          dead_end_useful[e.dst] =
                            gather_useful_labels(aut, used_in_cond, e.dst);
                          dead_end_useful_computed[e.dst] = true;
                        }
                      auto [d1, d2] = dead_end_useful[e.dst];
                      if (d1 == bddtrue)
                        d1 = self_loops[e.dst];
                      restrict_edge_maybe(d1);
                      restrict_edge_maybe(d2);
                    }
                }
            }
        // reset unions before next iteration
        for (auto& e: aut->out(s))
          label_unions[e.dst] = bddfalse;
      }
    // Note that restricting those label will never make the automaton
    // deterministic.  In fact, it could make the automaton
    // non-deterministic.  Additionally, completeness will not be
    // changed.  This is because the restricted Lab(SRC,DST) still
    // implies Lab(SRC,SRC).
    if (nondeterministic_for_sure)
      aut->prop_universal(false);
    if (created_false_labels)
      aut->merge_edges();
    return aut;
  }

}
