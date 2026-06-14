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
#include <bddx.h>
#include <spot/twa/bdddict.hh>
#include <iosfwd>

namespace spot
{
  // forward declaration
  class option_map;

  /// \brief Options controlling which simplification passes the tl_simplifier
  /// applies.
  class SPOT_API tl_simplifier_options
  {
  public:
    /// \brief Construct with individual option flags.
    tl_simplifier_options(bool basics = true,
                          bool synt_impl = true,
                          bool event_univ = true,
                          bool containment_checks = false,
                          bool containment_checks_stronger = false,
                          bool nenoform_stop_on_boolean = false,
                          bool reduce_size_strictly = false,
                          bool boolean_to_isop = false,
                          bool favor_event_univ = false,
                          bool keep_top_xor = false,
                          bool unit_prop = false)
      : reduce_basics(basics),
        synt_impl(synt_impl),
        event_univ(event_univ),
        containment_checks(containment_checks),
        containment_checks_stronger(containment_checks_stronger),
        nenoform_stop_on_boolean(nenoform_stop_on_boolean),
        reduce_size_strictly(reduce_size_strictly),
        boolean_to_isop(boolean_to_isop),
        favor_event_univ(favor_event_univ),
        keep_top_xor(keep_top_xor),
        unit_prop(unit_prop)
    {
    }

    /// \brief Construct from a simplification level (0–3).
    ///
    /// Level 0: no simplification; level 1: basics + event_univ;
    /// level 2: + synt_impl; level 3: + containment checks.
    tl_simplifier_options(int level) :
      tl_simplifier_options(false, false, false)
    {
      switch (level)
        {
        case 3:
          containment_checks = true;
          containment_checks_stronger = true;
          SPOT_FALLTHROUGH;
        case 2:
          synt_impl = true;
          SPOT_FALLTHROUGH;
        case 1:
          reduce_basics = true;
          event_univ = true;
          SPOT_FALLTHROUGH;
        default:
          break;
        }
    }

    bool reduce_basics;      ///< Enable basic rewriting rules.
    bool synt_impl;          ///< Enable syntactic implication simplifications.
    bool event_univ;         ///< Enable eventuality/universality reductions.
    bool containment_checks; ///< Enable language containment checks.
    bool containment_checks_stronger; ///< Enable stronger containment checks.
    /// If true, Boolean subformulae will not be put into
    /// negative normal form.
    bool nenoform_stop_on_boolean;
    /// If true, some rules that produce slightly larger formulas
    /// will be disabled.  Those larger formulas are normally easier
    /// to translate, so we recommend to set this to false.
    bool reduce_size_strictly;
    /// If true, Boolean subformulae will be rewritten in ISOP form.
    bool boolean_to_isop;
    /// Try to isolate subformulae that are eventual and universal.
    bool favor_event_univ;
    /// Keep Xor and Equiv at the top of the formula, possibly under
    /// &,|, and X operators.  Only rewrite Xor and Equiv under
    /// temporal operators.
    bool keep_top_xor;
    /// Enable unit-propagation-based simplification (see
    /// spot::unit_propagate) as a first pass before recursive
    /// rewriting.
    bool unit_prop;
    /// If greater than 0, bound the number of states used by automata
    /// in containment checks.
    unsigned containment_max_states = 0;
    /// If greater than 0, maximal number of terms in a multop to perform
    /// containment checks on this multop.
    unsigned containment_max_ops = 16;

    /// Return true if any simplification option is enabled.
    bool is_enabled() const
    {
      return reduce_basics || synt_impl || event_univ
        || containment_checks || containment_checks_stronger
        || nenoform_stop_on_boolean || reduce_size_strictly
        || boolean_to_isop || favor_event_univ || keep_top_xor
        || unit_prop;
    }

    /// Save this set of options into \a om with keys prefixed by \a prefix.
    /// All fields are stored as integers.
    void save_to_option_map(option_map& om, const char* prefix) const;

    /// Load options from \a om with keys prefixed by \a prefix.
    /// Only keys that exist in \a om are updated; missing keys leave
    /// the corresponding field unchanged.
    /// \return true if \a om contained at least one key with the given prefix.
    bool load_from_option_map(const option_map& om, const char* prefix);
  };

  // fwd declaration to hide technical details.
  class tl_simplifier_cache;

  /// \ingroup tl_rewriting
  /// \brief Rewrite or simplify \a f in various ways.
  class SPOT_API tl_simplifier
  {
  public:
    /// \brief Construct with default options and given BDD dictionary.
    tl_simplifier(const bdd_dict_ptr& dict = make_bdd_dict());
    /// \brief Construct with given options and BDD dictionary.
    tl_simplifier(const tl_simplifier_options& opt,
                   bdd_dict_ptr dict = make_bdd_dict());
    ~tl_simplifier();

    /// Simplify the formula \a f (using options supplied to the
    /// constructor).
    formula simplify(formula f);

#ifndef SWIG
    /// The simplifier options.
    ///
    /// Those can still be changed before the first formula is
    /// simplified.
    tl_simplifier_options& options();
#endif

    /// Build the negative normal form of formula \a f.
    /// All negations of the formula are pushed in front of the
    /// atomic propositions.  Operators <=>, =>, xor are all removed
    /// (calling spot::unabbreviate for those is not needed).
    ///
    /// \param f The formula to normalize.
    /// \param negated If \c true, return the negative normal form of
    ///        \c !f
    formula
      negative_normal_form(formula f, bool negated = false);

    /// \brief Syntactic implication.
    ///
    /// Returns whether \a f syntactically implies \a g.
    ///
    /// This is adapted from the rules of Somenzi and
    /// Bloem. \cite somenzi.00.cav
    bool syntactic_implication(formula f, formula g);
    /// \brief Syntactic implication with one negated argument.
    ///
    /// If \a right is true, this method returns whether
    /// \a f implies !\a g.  If \a right is false, this returns
    /// whether !\a f implies \a g.
    bool syntactic_implication_neg(formula f, formula g,
                                   bool right);

    /// \brief check whether two formulas are equivalent.
    ///
    /// This costly check performs up to four translations,
    /// two products, and two emptiness checks.
    bool are_equivalent(formula f, formula g);


    /// \brief Check whether \a f implies \a g.
    ///
    /// This operation is costlier than syntactic_implication()
    /// because it requires two translations, one product and one
    /// emptiness check.
    bool implication(formula f, formula g);

    /// \brief Convert a Boolean formula as a BDD.
    ///
    /// If you plan to use this method, be sure to pass a bdd_dict
    /// to the constructor.
    bdd as_bdd(formula f);

    /// \brief Clear the as_bdd() cache.
    ///
    /// Calling this function is recommended before running other
    /// algorithms that create BDD variables in a more natural
    /// order.  For instance ltl_to_tgba_fm() will usually be more
    /// efficient if the BDD variables for atomic propositions have
    /// not been ordered before hand.
    ///
    /// This also clears the language containment cache.
    void clear_as_bdd_cache();

    /// \brief Clear all caches.
    ///
    /// This empties all the cache used by the simplifier.
    void clear_caches();

    /// Return the bdd_dict used.
    bdd_dict_ptr get_dict() const;

    /// Cached version of spot::star_normal_form().
    formula star_normal_form(formula f);

    /// \brief Rewrite a Boolean formula \a f into as an irredundant
    /// sum of product.
    ///
    /// This uses a cache, so it is OK to call this with identical
    /// arguments.
    formula boolean_to_isop(formula f);

    /// Dump statistics about the caches.
    void print_stats(std::ostream& os) const;

  private:
    tl_simplifier_cache* cache_;
    // Copy disallowed.
    tl_simplifier(const tl_simplifier&) = delete;
    void operator=(const tl_simplifier&) = delete;
  };


  /// \brief Remove unnecessary quantified variables
  ///
  /// If a quantified variable does not appear in the body of the
  /// formula, simply remove it from the list of quantified variables.
  /// If a quantified variable always has the same polarity in the
  /// formula, it can be replaced by the appropriate constant.
  SPOT_API formula normalize_quantifiers(formula);
}
