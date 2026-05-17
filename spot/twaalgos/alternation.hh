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
#include <spot/twaalgos/powerset.hh>
#include <utility>

namespace spot
{
  /// \ingroup twa_algorithms
  /// \brief Helper class to combine outgoing edges in alternating
  /// automata
  ///
  /// The idea is that you can call the operator() on some state to get a
  /// BDD representation of its outgoing edges (labels and
  /// destinations, but not acceptance marks).  The BDD representation
  /// of different states can be combined using & or | to build a new
  /// representation of some outgoing edges that can be attached to
  /// some state with new_dests.  The use of BDDs helps removing
  /// superfluous edges.
  ///
  /// Beware that new_dests() just *appends* the transitions to the
  /// supplied state, it does not remove existing ones.
  ///
  /// operator() can be called on states with universal branching
  /// (that's actually the point), and can be called on state number
  /// that designate groups of destination states (in that case the
  /// conjunction of all those states are taken).
  class SPOT_API outedge_combiner
  {
  private:
    const twa_graph_ptr& aut_;
    std::map<unsigned, int> state_to_var;
    std::map<int, unsigned> var_to_state;
    bdd vars_;
  public:
    /// \brief Construct from an alternating automaton.
    outedge_combiner(const twa_graph_ptr& aut);
    ~outedge_combiner();
    /// \brief Combine outgoing edges of state \a st.
    bdd operator()(unsigned st);
    /// \brief Compute new destinations for state \a st under condition \a out.
    void new_dests(unsigned st, bdd out) const;
  };

  /// \ingroup twa_algorithms
  /// \brief Combine two states in a conjunction.
  ///
  /// This creates a new state whose outgoing transitions are the
  /// conjunctions of the compatible transitions of s1 and s2.
  ///
  /// Acceptance marks are dropped.
  ///
  /// The result is very likely to be alternating.
  /// @{
  template<class I>
  SPOT_API
  unsigned states_and(const twa_graph_ptr& aut, I begin, I end)
  {
    if (begin == end)
      throw std::runtime_error
        ("state_and() expects a non-empty list of states");
    outedge_combiner combiner(aut);
    bdd combination = bddtrue;
    while (begin != end)
      combination &= combiner(*begin++);
    unsigned new_s = aut->new_state();
    combiner.new_dests(new_s, combination);
    return new_s;
  }

  template<class T>
  SPOT_API
  unsigned states_and(const twa_graph_ptr& aut,
                      const std::initializer_list<T>& il)
  {
    return states_and(aut, il.begin(), il.end());
  }
  /// @}

  /// \ingroup twa_algorithms
  /// \brief Remove universal edges from a weak alternating automaton.
  ///
  /// This procedure is restricted to weak alternating automata as
  /// input, and produces TGBAs as output.  (Generalized Büchi
  /// acceptance is only used in presence of size-1 rejecting-SCCs.)
  ///
  /// \param aut input weak alternating automaton
  ///
  /// \param named_states name each state for easier debugging
  ///
  /// \param aborter Return nullptr if the built automaton would
  /// be larger than the size specified by the \a aborter, or
  /// if it would require too many acceptance sets.
  ///
  /// \param raise_if_too_many_sets when set to false, return
  /// nullptr in cases where we would need too many colors
  SPOT_API
  twa_graph_ptr remove_alternation(const const_twa_graph_ptr& aut,
                                   bool named_states = false,
                                   const output_aborter* aborter = nullptr,
                                   bool raise_if_too_many_sets = true);


  /// \ingroup twa_algorithms
  /// \brief State used during on-the-fly removal of universal edges from an
  /// alternating automaton.
  class SPOT_API univ_remover_state: public state
  {
  protected:
    std::set<unsigned> states_; ///< The set of original states represented.
    bool is_reset_; ///< Whether this state represents a reset.

  public:
    /// \brief Construct a state from a set of original states.
    univ_remover_state(const std::set<unsigned>& states);
    /// \brief Copy constructor.
    univ_remover_state(const univ_remover_state& other)
      : states_(other.states_), is_reset_(other.is_reset_)
    {
    }
    int compare(const state* other) const override;
    size_t hash() const override;
    state* clone() const override;
    /// \brief Return the set of original states.
    const std::set<unsigned>& states() const;
    /// \brief Check if this is a reset state.
    bool is_reset() const;
  };

  /// \ingroup twa_algorithms
  /// \brief On-the-fly TωA that removes universal edges from an alternating
  /// automaton.
  class SPOT_API twa_univ_remover: public twa
  {

  private:
    const_twa_graph_ptr aut_;
    std::vector<int> state_to_var_;
    std::map<int, unsigned> var_to_state_;
    bdd all_states_;

  public:
    /// \brief Construct from an alternating automaton.
    twa_univ_remover(const const_twa_graph_ptr& aut);
    /// \brief Allocate BDD variables for the states.
    void allocate_state_vars();
    const state* get_init_state() const override;
    twa_succ_iterator* succ_iter(const state* s) const override;
    std::string format_state(const state* s) const override;
  };

  /// \ingroup twa_algorithms
  /// \brief Shared pointer to a twa_univ_remover.
  typedef std::shared_ptr<twa_univ_remover> twa_univ_remover_ptr;

  /// \ingroup twa_algorithms
  /// \brief Remove universal edges on the fly from an alternating
  /// Büchi automaton.
  ///
  /// This function uses Miyano & Hayashi's \cite miyano.84.tcs
  /// breakpoint algorithm to construct a non-deterministic Büchi
  /// automaton from an alternating Büchi automaton on the fly.
  SPOT_API
  twa_univ_remover_ptr remove_univ_otf(const const_twa_graph_ptr& aut);
}
