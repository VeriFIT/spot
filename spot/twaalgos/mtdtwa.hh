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

namespace spot
{
  typedef std::pair<acc_cond::mark_t, unsigned> terminal_data_t;
  typedef std::vector<terminal_data_t> terminal_data_map_t;

  struct SPOT_API mtdtwa
  {
  public:
    mtdtwa(const bdd_dict_ptr& dict) noexcept
      : dict_(dict)
     {
     }

    ~mtdtwa()
    {
      dict_->unregister_all_my_variables(this);
    }

    std::vector<bdd> states;
    acc_cond acc;
    bdd_dict_ptr dict_;
    terminal_data_map_t terminal_data_map;

    unsigned num_roots() const
    {
      return states.size();
    }

    // Print the MTBDD.
    std::ostream& print_dot(std::ostream& os) const;

    // convert to twa
    twa_graph_ptr as_twa(bool state_based = false, bool labels = true) const;
  };


  typedef std::shared_ptr<mtdtwa> mtdtwa_ptr;
  typedef std::shared_ptr<const mtdtwa> const_mtdtwa_ptr;

  SPOT_API mtdtwa_ptr dtwa_to_mtdtwa(const twa_graph_ptr& aut);



  struct SPOT_API mtdswa
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
    bdd_dict_ptr dict_;

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

    // Print the MTBDD.
    //
    // Add opts="s" to show SCCs.
    std::ostream& print_dot(std::ostream& os, const char* opts = nullptr) const;

    // convert to twa
    twa_graph_ptr as_twa(bool state_based = false, bool labels = true) const;
  };


  typedef std::shared_ptr<mtdswa> mtdswa_ptr;
  typedef std::shared_ptr<const mtdswa> const_mtdswa_ptr;


  SPOT_API mtdswa_ptr dtwa_to_mtdswa(const twa_graph_ptr& aut);

  /// \brief find the SCC of each state
  ///
  /// This builds an SCC as large as the number of states in \a aut,
  /// and giving the SCC number each state belongs too.  SCC are
  /// numbered in topological order (the SCC of the initial state has
  /// the highest numbers, and SCC with number 0 is a terminal/leaf
  /// SCC).
  SPOT_API std::vector<int> scc_vector(const mtdswa_ptr& aut);

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

    bdd ltl_to_mtbdd(formula f);
    formula leaf_to_formula(int b, int term) const;

    formula terminal_to_formula(int t) const;
    int formula_to_int(formula f);
    int formula_to_terminal(formula f);
    bdd formula_to_terminal_bdd(formula f);
    int formula_to_terminal_bdd_as_int(formula f);

    bdd combine_and(bdd left, bdd right);
    bdd combine_or(bdd left, bdd right);
    bdd combine_implies(bdd left, bdd right);
    bdd combine_equiv(bdd left, bdd right);
    bdd combine_xor(bdd left, bdd right);
    bdd combine_not(bdd b);

    formula propeq_representative(formula f);

    bddExtCache* get_cache()
    {
      return &cache_;
    }

    ~simple_ltl_translator();
  private:
    std::unordered_map<formula, int> formula_to_var_;
    std::unordered_map<bdd, formula, bdd_hash> propositional_equiv_;

    std::unordered_map<formula, bdd> formula_to_bdd_;
    std::unordered_map<formula, int> formula_to_int_;
    std::vector<formula> int_to_formula_;
    bdd_dict_ptr dict_;
    bddExtCache cache_;
    bool simplify_terms_;
  };

  SPOT_API
  mtdswa_ptr obligation_to_mtdswa(formula f, const bdd_dict_ptr& dict,
                                  bool fuse_same_bdds = true,
                                  bool simplify_terms = true);

}
