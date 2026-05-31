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

namespace spot
{
  /// \ingroup tl_ltlf
  /// \brief Convert an LTLf into an LTL formula.
  ///
  /// \param f      an LTLf formula
  /// \param alive  name of the "alive" proposition (default: "alive").
  ///               If the name starts with '!', e.g., <code>!dead</code>,
  ///               the atomic proposition is built from the rest of the
  ///               string and its negation is used in the transformation.
  ///               Using <code>!dead</code> rather than <code>alive</code>
  ///               makes more sense if the state-space introduces a
  ///               <code>dead</code> property on states representing the
  ///               end of finite computations.
  /// \param algo   translation algorithm to use:
  ///               <b>1</b> (default) — translation that guarantees
  ///               the result is a syntactic-obligation formula;
  ///               <b>0</b> — original De Giacomo & Vardi (IJCAI'13)
  ///               translation \cite degiacomo.13.ijcai.
  ///
  /// Note that the description of the translation in
  /// \cite degiacomo.13.ijcai has a typo in the definition of $t(a U b)$.
  /// This typo is fixed in \cite dutta.14.memocode but that second
  /// paper forgets to ensure that $alive$ holds initially.
  SPOT_API formula
  from_ltlf(formula f, const char* alive, int algo);

  /// \ingroup tl_ltlf
  /// \brief Convert an LTLf into an LTL formula.
  ///
  /// \param f      an LTLf formula
  /// \param alive  name of the "alive" proposition (default: "alive").
  ///               If the name starts with '!', e.g., <code>!dead</code>,
  ///               the atomic proposition is built from the rest of the
  ///               string and its negation is used in the transformation.
  ///               Using <code>!dead</code> rather than <code>alive</code>
  ///               makes more sense if the state-space introduces a
  ///               <code>dead</code> property on states representing the
  ///               end of finite computations.
  ///
  /// This overload reads the environment variable
  /// <code>SPOT_FROM_LTLF</code> (values: <b>0</b> = original,
  /// <b>1</b> = syntactic-obligation) exactly once and caches the result.
  /// The default when the variable is unset is <b>1</b>.
  SPOT_API formula
  from_ltlf(formula f, const char* alive = "alive");

  /// \ingroup tl_ltlf
  /// \brief Cheap simplification rules for LTLf formulas.
  class SPOT_API ltlf_simplifier
  {
  public:
    /// \brief Build an LTLf simplifier.
    ltlf_simplifier();
    /// \brief Destroy the simplifier.
    ~ltlf_simplifier();
    /// \brief Simplify an LTLf formula.
    formula simplify(formula f, bool negated = false);
  private:
    formula simplify_aux(formula f, bool negated);
    class cache;
    cache* cache_;
  };


  /// \ingroup tl_ltlf
  /// \brief One-step satisfiability rewriting for LTLf formulas.
  SPOT_API formula ltlf_one_step_sat_rewrite(formula f);

  /// \ingroup tl_ltlf
  /// \brief Cached version of the one-step satisfiability rewriting for LTLf
  /// formulas.
  class SPOT_API ltlf_one_step_sat_rewrite_with_cache
  {
  public:
    /// \brief Build the cache.
    ltlf_one_step_sat_rewrite_with_cache();
    /// \brief Destroy the cache.
    ~ltlf_one_step_sat_rewrite_with_cache();
    /// \brief Rewrite an LTLf formula.
    formula rewrite(formula f);
  private:
    void *cache_;
  };

  /// \ingroup tl_ltlf
  /// \brief One-step unsatisfiability rewriting for LTLf formulas.
  SPOT_API formula ltlf_one_step_unsat_rewrite(formula f,
                                               bool negate = false);

  /// \ingroup tl_ltlf
  /// \brief Cached version of the one-step unsatisfiability rewriting for LTLf
  /// formulas.
  class SPOT_API ltlf_one_step_unsat_rewrite_with_cache
  {
  public:
    /// \brief Build the cache.
    ltlf_one_step_unsat_rewrite_with_cache();
    /// \brief Destroy the cache.
    ~ltlf_one_step_unsat_rewrite_with_cache();
    /// \brief Rewrite an LTLf formula.
    formula rewrite(formula f);
  private:
    void *cache_;
  };
}
