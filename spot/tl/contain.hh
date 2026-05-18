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

#include <spot/tl/formula.hh>
#include <spot/twa/bdddict.hh>
#include <spot/twaalgos/powerset.hh>

namespace spot
{
  class tl_simplifier_cache;

  /// \ingroup containment
  /// Check containment between LTL formulas.
  class SPOT_API language_containment_checker
  {
    struct record_;
    struct trans_map_;
  public:
    /// This class uses spot::ltl_to_tgba_fm to translate LTL
    /// formulas.  See that function for the meaning of these options.
    language_containment_checker(bdd_dict_ptr dict = make_bdd_dict(),
                                 bool exprop = false,
                                 bool symb_merge = true,
                                 bool branching_postponement = false,
                                 bool fair_loop_approx = false,
                                 unsigned max_states = 0U);

    ~language_containment_checker();

    /// Clear the cache.
    void clear();

    /// Check whether L(l) is a subset of L(g).
    bool contained(formula l, formula g);
    /// Check whether L(!l) is a subset of L(g).
    bool neg_contained(formula l, formula g);
    /// Check whether L(l) is a subset of L(!g).
    bool contained_neg(formula l, formula g);

    /// Check whether L(l) = L(g).
    bool equal(formula l, formula g);

  protected:
    /// \brief Test whether two cached formulas are incompatible.
    bool incompatible_(record_* l, record_* g);

    /// \brief Register a formula in the translation cache.
    record_* register_formula_(formula f);

    /* Translation options */
    bdd_dict_ptr dict_; ///< Dictionary used for translations.
    bool exprop_;       ///< Use existential properties.
    bool symb_merge_;   ///< Merge symbolic states.
    bool branching_postponement_; ///< Postpone branching choices.
    bool fair_loop_approx_;       ///< Approximate fair loops.
    /* Translation Maps */
    trans_map_* translated_; ///< Translation cache.
    tl_simplifier_cache* c_; ///< Formula simplifier cache.
    /// \brief Optional output aborter.
    std::unique_ptr<const output_aborter> aborter_ = nullptr;
  };
}
