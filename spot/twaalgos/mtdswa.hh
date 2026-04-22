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
#include <spot/misc/bddlt.hh>
#include <unordered_map>

namespace spot
{
  /// \ingroup mtdswa
  /// \brief MTBDD-based representation of a state-based ω-automaton.
  struct SPOT_API mtdswa: public std::enable_shared_from_this<mtdswa>
  {
  public:
    mtdswa(const bdd_dict_ptr& dict) noexcept
      : dict_(dict)
     {
     }

    ~mtdswa()
    {
      dict_->unregister_all_my_variables(this);
    }

    /// \brief The list of atomic propositions possibly used by the automaton.
    ///
    /// This is actually the list of atomic propositions that appeared
    /// in the formulas/automata that were used to build this
    /// automaton.  The automaton itself may use fewer atomic
    /// propositions, for instance in cases some of them canceled each other.
    ///
    /// This vector is sorted by formula ID, to make it easy to merge
    /// with another sorted vector.
    std::vector<formula> aps;

    std::vector<bdd> states;
    std::vector<formula> names;
    std::vector<acc_cond::mark_t> colors;
    acc_cond acc;

    // If this map is non-empty, it is used to map terminal values
    // to states while printing the automaton.  Use this only for debugging,
    // other algorithms will ignore it.
    std::unordered_map<int, int> terminal_to_state_map;
    // colors some nodes
    std::unordered_map<int, unsigned> highlight_nodes;
    // for each element (A, B) put state A in cluster B
    std::unordered_map<int, int> highlight_groups;

    /// \brief get the bdd_dict associated to this automaton
    bdd_dict_ptr get_dict() const
    {
      return dict_;
    }

    unsigned num_roots() const
    {
      return states.size();
    }

    /// \brief The number of states in the automaton
    ///
    /// This counts the number of roots, plus one if the `bddtrue` state
    /// is reachable.  This is therefore the size that the
    /// transition-based output of `as_twa()` would have.
    unsigned num_states() const
    {
      return states.size() + bdd_has_true(states);
    }

    /// \brief Print the MTBDD.
    ///
    /// Add opts="s" to show SCCs.
    std::ostream& print_dot(std::ostream& os, const char* opts = nullptr) const;

    /// \brief convert to twa
    twa_graph_ptr as_twa(bool state_based = false,
                         bool labels = true,
                         bool complete = false) const;

    /// \brief convert bddtrue/bddfalse nodes to actual states
    ///
    /// This modifies the automaton in place so that it does not use the
    /// bddtrue and bddfalse constants.  Those will be replaced by accepting
    /// and rejecting sinks respectively.   Those new states are introduced
    /// only if no existing state can serve the same purpose.
    ///
    /// When the acceptance condition is always accepting, or when it
    /// is always rejecting, introducing a sink state might require
    /// changing the acceptance condition.  When that happens, the
    /// acceptance will be set to Büchi.
    ///
    /// If the automaton had named states, newly introduced sinks will be
    /// named as formula::tt() or formula::ff().
    void sinks_as_states();

    /// \brief converse sink states to bddtrue/bddfalse constants
    ///
    /// This modifies the automaton in place so that any sink state
    /// is turned into bddtrue or bddfalse depending on its acceptance.
    ///
    /// The original sink states will be removed and the other state
    /// will be renumbered, unless \a keep_all_states is set.
    void sinks_as_constants(bool keep_all_states = false);

    /// \brief declare a list of controllable variables
    ///
    /// Doing so affect the way the automaton is printed in dot
    /// format, but this is also a prerequisite for interpreting
    /// the automaton as a game.
    ///
    /// This function is expected to be after you have built the
    /// automaton, in some way (causing atomic propositions to be
    /// registered).  If \a ignore_non_registered_ap is set, variable
    /// listed as output but not registered by the automaton will be
    /// dropped.  Else, an exception will be raised for those
    /// variables.
    /// @{
    void set_controllable_variables(const std::vector<std::string>& vars,
                                    bool ignore_non_registered_ap = false);
    void set_controllable_variables(bdd vars);
    /// @}

    /// \brief Returns the conjunction of controllable variables.
    bdd get_controllable_variables() const
    {
      return controllable_variables_;
    }

  private:
    bdd_dict_ptr dict_;
    bdd controllable_variables_ = bddtrue;
  };


  typedef std::shared_ptr<mtdswa> mtdswa_ptr;
  typedef std::shared_ptr<const mtdswa> const_mtdswa_ptr;

  /// \ingroup mtdswa
  /// \brief convert deterministic TwA to MTDSwA
  SPOT_API mtdswa_ptr dtwa_to_mtdswa(const twa_graph_ptr& aut);

  /// \ingroup mtdswa
  /// \brief find the SCC of each state
  ///
  /// This builds a vector as large as the number of states in \a aut,
  /// and giving the SCC number each state belongs too.  SCC are
  /// numbered in topological order (the SCC of the initial state has
  /// the highest number, and SCC with number 0 is a terminal/leaf
  /// SCC).
  SPOT_API std::vector<int> scc_vector(const mtdswa_ptr& aut);

  /// \ingroup mtdswa
  /// \brief preprocess a weak MTDSwA before minimization
  ///
  /// This implement's Löding's ranking function \cite loding.01.ipl
  /// that can be used to decide which transient states (i.e., state
  /// that are not part of any cycles) should be marked as accepting
  /// or rejecting in order to guarantee minimality after the
  /// automaton is minimized like a DFA.
  ///
  /// Contrary to Löding's paper, we use a ranking function that is
  /// decreasing.  A state can only go to another state with a rank
  /// that is equal or smaller.  Even ranks designate rejecting
  /// states, and odd ranks designate accepting states.
  ///
  /// The function returns a vector that gives the rank of each state.
  /// If the MTDSwA uses constants `bddfalse` and `bddtrue` as terminals,
  /// those can be assumed to have rank 0 and 1 respectively.
  ///
  /// If \a fix is set, the acceptance of the states of the input
  /// automaton will be fixed according to the computed ranks.
  ///
  /// The returned ranking vector can be passed minimize_mtdswa()
  /// to be used as initial partition.
  SPOT_API std::vector<unsigned> loding_weak_ranking(const mtdswa_ptr& aut,
                                                     bool fix = false);

  /// \ingroup mtdswa
  /// \brief Minimization of MTDSwA
  ///
  /// This is called minimization because it implements a variant of
  /// Moore's partition-refinement algorithms (that is normally used
  /// to minimize DFAs).   However for general deterministic ω-automata,
  /// this does not guarantee minimality.
  ///
  /// One exception is weak deterministic ω-automata, which can be minimized
  /// precisely if they are first preprocessed with loding_weak_ranking().
  ///
  /// The implementation of this minimization currently is unable to merge
  /// states with any bddfalse or bddtrue constant.  You can work around
  /// this by converting constants to states before minimizing, and possibly
  /// back to constants afterwards:
  /// ```
  ///     dfa->sinks_as_states();
  ///     dfa = minimize_mtdsw(dfa);
  ///     dfa->sinks_as_constants();  // if really needed
  /// ```
  ///
  /// By default, the initial partition is based on the colors that
  /// label each states.  If you know a better one, you can pass it as
  /// \a initial_partition.
  ///
  /// @{
  SPOT_API
  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa);
  SPOT_API
  mtdswa_ptr minimize_mtdswa(const mtdswa_ptr& dfa,
                             const std::vector<unsigned>& initial_partition);
  /// @}

  /// \ingroup mtdswa
  /// \brief "Semi-internal" for translating LTL using MTBDDs
  ///
  /// It is public only to make it possible to demonstrate the inner
  /// working of the translation.  Do not rely on the interface to be
  /// stable.
  class SPOT_API simple_ltl_translator
  {
  public:
    simple_ltl_translator(const bdd_dict_ptr& dict,
                          bool simplify_terms = true);

    mtdswa_ptr ltl_to_mtdswa(formula f, bool fuse_same_bdds);
    mtdswa_ptr ltl_to_mtdswa_synthesis(formula f,
                                       const std::vector<std::string>& outvars,
                                       bool realizability, int debug = -1);

    bdd ltl_to_mtbdd(formula f);
    formula leaf_to_formula(int b, int term) const;

    formula terminal_to_formula(int t) const;
    int formula_to_int(formula f);
    int formula_propeq_to_int(formula f);
    int formula_to_terminal(formula f);
    bdd formula_to_terminal_bdd(formula f);
    int formula_to_terminal_bdd_as_int(formula f);
    int formula_propeq_to_terminal_bdd_as_int(formula f);

    bdd combine_and(bdd left, bdd right);
    bdd combine_or(bdd left, bdd right);
    bdd combine_implies(bdd left, bdd right);
    bdd combine_equiv(bdd left, bdd right);
    bdd combine_xor(bdd left, bdd right);
    bdd combine_not(bdd b);

    bdd propeq_encode(formula f, int level = 0);
    formula propeq_representative(formula f, bool isacc);

    bddExtCache* get_cache()
    {
      return &cache_;
    }

    ~simple_ltl_translator();
  private:
    // Pair representing a formula at a given X-nesting level
    struct formula_level_pair
    {
      formula f;
      int level;

      bool operator==(const formula_level_pair& other) const
      {
        return f == other.f && level == other.level;
      }
    };

    struct formula_level_pair_hash
    {
      std::size_t operator()(const formula_level_pair& p) const
      {
        return p.f.id() ^ (p.level * 0x9e3779b9);
      }
    };

    std::unordered_map<formula_level_pair, bdd,
                       formula_level_pair_hash> propositional_equiv_bdd_;
    std::unordered_map<bdd, formula, bdd_hash> propositional_equiv_[2];

    std::unordered_map<formula, bdd> formula_to_bdd_;
    std::unordered_map<formula, int> formula_to_int_;
    std::unordered_map<formula, int> propeq_to_int_;
    std::vector<formula> int_to_formula_;
    bdd_dict_ptr dict_;
    bddExtCache cache_;
    bool simplify_terms_;
  };

  /// \ingroup mtdswa
  /// \brief Convert a syntactic-obligation to an MTDSwA
  SPOT_API
  mtdswa_ptr obligation_to_mtdswa(formula f, const bdd_dict_ptr& dict,
                                  bool fuse_same_bdds = true,
                                  bool simplify_terms = true);

  /// \ingroup mtdswa
  /// \brief Reactive synthesis of syntactic-obligations
  ///
  /// The formula may use quantified atomic propositions (\forall or \exists).
  SPOT_API
  mtdswa_ptr obligation_synthesis(formula f, const bdd_dict_ptr& dict,
                                  const std::vector<std::string>& outvars,
                                  bool realizability = false,
                                  bool simplify_terms = true,
                                  int debug = -1);

  /// \ingroup mtdswa
  /// \brief Convert a strategy represented as MTDSwA into a Mealy machine.
  ///
  /// If \a loop is set, a strategy reaching bddtrue will instead loop on
  /// the last assignment.
  SPOT_API twa_graph_ptr
  mtdswa_strategy_to_mealy(mtdswa_ptr strategy, bool labels = true,
                           bool loop = false);
}
