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
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/forq_contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/translate.hh>

namespace spot
{
  namespace
  {
    static spot::const_twa_graph_ptr
    translate(formula f, const bdd_dict_ptr& dict)
    {
      if (f.is_quantified())
        {
          // Use the full translator (which handles quantifiers via
          // run_q()) rather than ltl_to_tgba_fm.  We create a fresh
          // translator per call; this is fine because
          // register_formula_() already caches results per formula.
          //
          // Use Low optimization level to avoid containment checks
          // in the simplifier, which could recursively call back into
          // register_formula_() with negated (and possibly universally
          // quantified) formulas.
          //
          // Note: the translator does not support output_aborter,
          // so max_states is not enforced for quantified formulas.
          translator trans(dict);
          trans.set_level(postprocessor::Low);
          return trans.run(f);
        }
      return ltl_to_tgba_fm(f, dict);
    }

    static const_twa_graph_ptr
    ensure_graph(const const_twa_ptr& aut_in)
    {
      const_twa_graph_ptr aut =
        std::dynamic_pointer_cast<const twa_graph>(aut_in);
      if (aut)
        return aut;
      return make_twa_graph(aut_in, twa::prop_set::all());
    }
  }

  bool contains(const_twa_graph_ptr left, const_twa_ptr right)
  {
    if (containment_select_version() == 1
        && left->acc().is_buchi() && right->acc().is_buchi())
      return contains_forq(left, ensure_graph(right));
    else
      return !complement(left)->intersects(right);
  }

  bool contains(const_twa_graph_ptr left, formula right)
  {
    return contains(left, translate(right, left->get_dict()));
  }

  bool contains(formula left, const_twa_ptr right)
  {
    return !translate(formula::Not(left), right->get_dict())->intersects(right);
  }

  bool contains(formula left, formula right)
  {
    return contains(left, translate(right, make_bdd_dict()));
  }

  bool are_equivalent(const_twa_graph_ptr left, const_twa_graph_ptr right)
  {
    bool right_is_det = is_deterministic(right);
    // If both automata are deterministic, use product_xor + is_empty
    // which is more direct than the double containment check.
    if (right_is_det && is_deterministic(left))
      return product_xor(left, right)->is_empty();
    // Start with a deterministic automaton at right if possible to
    // avoid a determinization (in case the first containment check
    // fails).
    if (!right_is_det)
      std::swap(left, right);
    return contains(left, right) && contains(right, left);
  }

  bool are_equivalent(const_twa_graph_ptr left, formula right)
  {
    // The first containment check does not involve a
    // complementation, the second might.
    return contains(left, right) && contains(right, left);
  }

  bool are_equivalent(formula left, const_twa_graph_ptr right)
  {
    // The first containment check does not involve a
    // complementation, the second might.
    return contains(right, left) && contains(left, right);
  }

  bool are_equivalent(formula left, formula right)
  {
    return contains(right, left) && contains(left, right);
  }

  int containment_select_version(const char* version)
  {
    static int pref = -1;
    const char *env = nullptr;
    if (!version && pref < 0)
      version = env = getenv("SPOT_CONTAINMENT_CHECK");
    if (version)
      {
        if (!strcasecmp(version, "default"))
          pref = 0;
        else if (!strcasecmp(version, "forq"))
          pref = 1;
        else
          {
            const char* err = ("containment_select_version(): argument"
                               " should be one of {default,forq}");
            if (env)
              err = "SPOT_CONTAINMENT_CHECK should be one of {default,forq}";
            throw std::runtime_error(err);
          }
      }
    else if (pref < 0)
      {
        pref = 0;
      }
    return pref;
  }
}
