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
#include <vector>

namespace spot
{
  typedef std::vector<std::pair<bool, bdd>> quantifier_list;

  /// \ingroup twa_ltl
  /// \brief Convert quantified LTL to unquantified LTL + quantifier_list.
  ///
  /// If the input is `∀a,b:∃c,d:φ`, this returns `([(true, a&b),
  /// (false, c&d)], φ)` where φ is an unquitified LTL, `a&b` and
  /// `c&d` are BDDs, and the true/false indicate
  /// universal/existential quantifications.
  ///
  /// The atomic propositions used in BDD variables will be registered
  /// into \a dict for \a for_me.
  ///
  /// @{
  SPOT_API std::pair<quantifier_list, formula>
  extract_quantifier_list(formula f, bdd_dict_ptr dict, void *for_me);

  template <typename T>
  SPOT_API std::pair<quantifier_list, formula>
  extract_quantifier_list(formula f, bdd_dict_ptr dict,
                          std::shared_ptr<T> for_me)
  {
    return extract_quantifier_list(f, dict, for_me.get());
  }
  /// @}



}
