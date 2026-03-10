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
#include <quantify.hh>

namespace spot
{
  std::pair<quantifier_list, formula>
  extract_quantifier_list(formula f, bdd_dict_ptr dict, void *for_me)
  {
    if (!f.is(op::exists, op::forall))
      return make_pair(quantifier_list{}, f);

    unsigned sz = f.size();
    std::pair<quantifier_list, formula> res =
      extract_quantifier_list(f[sz - 1], dict, for_me);

    bdd aps = bddtrue;
    for (unsigned i = 0; i < sz - 1; ++i)
      aps &= bdd_ithvar(dict->register_proposition(f[i], for_me));

    res.first.emplace_back(f.is(op::forall), aps);
    return res;
  }
}
