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

#include <spot/tl/apcollect.hh>
#include <iosfwd>

#include <unordered_set>
#include <spot/misc/optionmap.hh>
#include <spot/misc/hash.hh>
#include <spot/tl/simplify.hh>

namespace spot
{
  /// \ingroup tl_io
  /// \brief Base class for random formula generators
  class SPOT_API random_formula
  {
  public:
    /// \brief Construct with \a proba_size operator slots
    /// and atomic propositions \a ap.
    random_formula(unsigned proba_size,
                   const atomic_prop_set* ap,
                   const atomic_prop_set* output_ap = nullptr,
                   std::function<bool(formula)> is_output = nullptr):
    proba_size_(proba_size), proba_(new op_proba[proba_size_]), ap_(ap),
    output_ap_(output_ap), is_output_(is_output)
    {
    }

    virtual ~random_formula()
    {
      delete[] proba_;
    }

    /// Return the set of atomic proposition used to build formulas.
    const atomic_prop_set* ap() const
    {
      return ap_;
    }

    /// Return the set of atomic proposition used to build formulas.
    const atomic_prop_set* output_ap() const
    {
      return output_ap_;
    }

    /// Return the predicate that classifies propositions as output.
    std::function<bool(formula)> is_output_fun() const
    {
      return is_output_;
    }

    /// Return the set of patterns (sub-formulas) used to build formulas.
    const atomic_prop_set* patterns() const
    {
      return patterns_;
    }

    /// Check whether relabeling APs should use literals.
    bool draw_literals() const
    {
      return draw_literals_;
    }

    /// Set whether relabeling APs should use literals.
    void draw_literals(bool lit)
    {
      draw_literals_ = lit;
    }

    /// \brief Generate a formula of size \a n.
    ///
    /// It is possible to obtain formulas that are smaller than \a
    /// n, because some simple simplifications are performed by the
    /// AST.  (For instance the formula <code>a | a</code> is
    /// automatically reduced to <code>a</code> by spot::multop.)
    formula generate(int n) const;

    /// \brief Print the priorities of each operator, constants,
    /// and atomic propositions.
    std::ostream& dump_priorities(std::ostream& os) const;

    /// \brief Update the priorities used to generate the formulas.
    ///
    /// \a options should be comma-separated list of KEY=VALUE
    /// assignments, using keys from the above list.
    /// For instance <code>"xor=0, F=3"</code> will prevent \c xor
    /// from being used, and will raise the relative probability of
    /// occurrences of the \c F operator.
    const char* parse_options(char* options);

    /// \brief whether we can use unary operators
    bool has_unary_ops() const
    {
      return total_2_ > 0.0;
    }

  protected:
    /// Recompute running probability sums after priorities have changed.
    void update_sums();

    /// \brief Entry describing one operator and its probability for random
    /// formula generation.
    struct op_proba
    {
      const char* name;  ///< Name of the operator.
      int min_n;         ///< Minimum formula size needed for this operator.
      double proba;      ///< Cumulative probability weight.
      /// Function pointer type for building a formula of this operator.
      typedef formula (*builder)(const random_formula* rl, int n);
      builder build;     ///< Builder function for this operator.
      /// Initialize the entry with \a name, \a min_n, and \a build.
      void setup(const char* name, int min_n, builder build);
    };
    unsigned proba_size_;       ///< Number of entries in the operator table.
    op_proba* proba_;           ///< Operator probability table.
    double total_1_;            ///< Total weight of unary operators.
    op_proba* proba_2_;         ///< Pointer to binary operators in the table.
    double total_2_;            ///< Total weight of binary operators.
    op_proba* proba_2_or_more_; ///< Pointer to operators needing ≥2 children.
    /// Total weight of operators needing two or more children.
    double total_2_and_more_;
    const atomic_prop_set* ap_; ///< Atomic propositions used to build formulas.
    /// Output atomic propositions (may be null if not used).
    const atomic_prop_set* output_ap_ = nullptr;
    /// Sub-formula patterns used as atoms (may be null).
    const atomic_prop_set* patterns_ = nullptr;
    /// Predicate classifying a proposition as an output (may be null).
    std::function<bool(formula)> is_output_ = nullptr;
    bool draw_literals_; ///< Whether relabeling APs should use literals.
  };


  /// \ingroup tl_io
  /// \brief Generate random LTL formulas.
  ///
  /// This class recursively constructs LTL formulas of a given
  /// size.  The formulas will use atomic propositions from
  /// the set of propositions passed to the constructor, in addition
  /// to the constant and all LTL operators supported by Spot.
  ///
  /// By default each operator has equal chance to be selected.
  /// Also, each atomic proposition has as much chance as each
  /// constant (i.e., true and false) to be picked.  This can be
  /// tuned using parse_options().
  class SPOT_API random_ltl: public random_formula
  {
  public:
    /// Create a random LTL generator using atomic propositions from \a ap.
    ///
    /// The default priorities are defined as follows, depending on the
    /// presence of \a subformulas.
    ///
    /** \verbatim
        ap      n              sub     n
        false   1              false   1
        true    1              true    1
        not     1              not     1
        F       1              F       1
        G       1              G       1
        X       1              X       1
        strongX 0              strongX 0
        equiv   1              equiv   1
        implies 1              implies 1
        xor     1              xor     1
        R       1              R       1
        U       1              U       1
        W       1              W       1
        M       1              M       1
        and     1              and     1
        or      1              or      1
        \endverbatim */
    ///
    /// Where \c n is the number of atomic propositions in the
    /// set passed to the constructor.
    ///
    /// This means that each operator has equal chance to be
    /// selected.  Also, each atomic proposition has as much chance
    /// as each constant (i.e., true and false) to be picked.
    ///
    /// These priorities can be changed using the parse_options method.
    ///
    /// If a set of subformulas is passed to the constructor, the generator
    /// will build a Boolean formulas using patterns as atoms.  Atomic
    /// propositions in patterns will be rewritten randomly by drawing
    /// some from \a ap.  The probability of false/true to be generated
    /// default to 0 in this case.
    random_ltl(const atomic_prop_set* ap,
               const atomic_prop_set* output_ap = nullptr,
               std::function<bool(formula)> is_output = nullptr,
               const atomic_prop_set* subformulas = nullptr);

  protected:
    /// Initialize the probability table, optionally using \a patterns as atoms.
    void setup_proba_(const atomic_prop_set* patterns);
    /// \brief Construct with explicit table \a size (for subclasses).
    random_ltl(int size, const atomic_prop_set* ap,
               const atomic_prop_set* output_ap = nullptr,
               std::function<bool(formula)> is_output = nullptr);
  };

  /// \ingroup tl_io
  /// \brief Generate random Boolean formulas.
  ///
  /// This class recursively constructs Boolean formulas of a given size.
  /// The formulas will use atomic propositions from the
  /// set of propositions passed to the constructor, in addition to the
  /// constant and all Boolean operators supported by Spot.
  ///
  /// By default each operator has equal chance to be selected.
  class SPOT_API random_boolean final: public random_formula
  {
  public:
    /// Create a random Boolean formula generator using atomic
    /// propositions from \a ap.
    ///
    /// The default priorities are defined as follows depending on
    /// the presence of \a subformulas.
    ///
    /** \verbatim
        ap      n         sub     n
        false   1         false   0
        true    1         true    0
        not     1         not     1
        equiv   1         equiv   1
        implies 1         implies 1
        xor     1         xor     1
        and     1         and     1
        or      1         or      1
        \endverbatim */
    ///
    /// Where \c n is the number of atomic propositions in the
    /// set passed to the constructor.
    ///
    /// This means that each operator has equal chance to be
    /// selected.  Also, each atomic proposition has as much chance
    /// as each constant (i.e., true and false) to be picked.
    ///
    /// These priorities can be changed using the parse_options method.
    ///
    /// If a set of \a subformulas is passed to the constructor, the
    /// generator will build a Boolean formulas using patterns as
    /// atoms.  Atomic propositions in patterns will be rewritten
    /// randomly by drawing some from \a ap.
    random_boolean(const atomic_prop_set* ap,
                   const atomic_prop_set* output_ap = nullptr,
                   std::function<bool(formula)> is_output = nullptr,
                   const atomic_prop_set* subformulas = nullptr);
  };

  /// \ingroup tl_io
  /// \brief Generate random SERE.
  ///
  /// This class recursively constructs SERE of a given size.
  /// The formulas will use atomic propositions from the
  /// set of propositions passed to the constructor, in addition to the
  /// constant and all SERE operators supported by Spot.
  ///
  /// By default each operator has equal chance to be selected.
  class SPOT_API random_sere final: public random_formula
  {
  public:
    /// Create a random SERE generator using atomic propositions from \a ap.
    ///
    /// The default priorities are defined as follows:
    ///
    /** \verbatim
        eword    1
        boolform 1
        star     1
        star_b   1
        equal_b  1
        goto_b   1
        and      1
        andNLM   1
        or       1
        concat   1
        fusion   1
        \endverbatim */
    ///
    /// Where "boolfrom" designates a Boolean formula generated
    /// by random_boolean.
    ///
    /// These priorities can be changed using the parse_options method.
    ///
    /// In addition, you can set the properties of the Boolean
    /// formula generator used to build Boolean subformulas using
    /// the parse_options method of the \c rb attribute.
    random_sere(const atomic_prop_set* ap);

    /// The Boolean formula generator used to build Boolean sub-expressions.
    random_boolean rb;
  };

  /// \ingroup tl_io
  /// \brief Generate random PSL formulas.
  ///
  /// This class recursively constructs PSL formulas of a given size.
  /// The formulas will use atomic propositions from the
  /// set of propositions passed to the constructor, in addition to the
  /// constant and all PSL operators supported by Spot.
  class SPOT_API random_psl: public random_ltl
  {
  public:
    /// Create a random PSL generator using atomic propositions from \a ap.
    ///
    /// PSL formulas are built by combining LTL operators, plus
    /// three operators (EConcat, UConcat, Closure) taking a SERE
    /// as parameter.
    ///
    /// The default priorities are defined as follows:
    ///
    /** \verbatim
        ap      n
        false   1
        true    1
        not     1
        F       1
        G       1
        X       1
        Closure 1
        equiv   1
        implies 1
        xor     1
        R       1
        U       1
        W       1
        M       1
        and     1
        or      1
        EConcat 1
        UConcat 1
        \endverbatim */
    ///
    /// Where \c n is the number of atomic propositions in the
    /// set passed to the constructor.
    ///
    /// This means that each operator has equal chance to be
    /// selected.  Also, each atomic proposition has as much chance
    /// as each constant (i.e., true and false) to be picked.
    ///
    /// These priorities can be changed using the parse_options method.
    ///
    /// In addition, you can set the properties of the SERE generator
    /// used to build SERE subformulas using the parse_options method
    /// of the \c rs attribute.
    random_psl(const atomic_prop_set* ap);

    /// The SERE generator used to generate SERE subformulas.
    random_sere rs;
  };

  /// \brief Generator of random LTL/PSL/SERE/Boolean formulas with configurable
  /// options.
  class SPOT_API randltlgenerator
  {
    typedef std::unordered_set<formula> fset_t;


  public:
    /// Output formula type produced by the generator.
    enum output_type { Bool, LTL, SERE, PSL };
    /// Maximum number of attempts to generate a unique formula.
    static constexpr unsigned MAX_TRIALS = 100000U;

    /// \brief Construct with \a aprops_n random atomic propositions.
    randltlgenerator(int aprops_n, const option_map& opts,
                     char* opt_pL = nullptr,
                     char* opt_pS = nullptr,
                     char* opt_pB = nullptr,
                     const atomic_prop_set* subformulas = nullptr,
                     std::function<bool(formula)> is_output = nullptr);

    /// \brief Construct with an explicit set of atomic propositions.
    randltlgenerator(atomic_prop_set aprops, const option_map& opts,
                     char* opt_pL = nullptr,
                     char* opt_pS = nullptr,
                     char* opt_pB = nullptr,
                     const atomic_prop_set* subformulas = nullptr,
                     std::function<bool(formula)> is_output = nullptr);

    ~randltlgenerator();

    /// Generate the next random formula (up to MAX_TRIALS attempts).
    formula next();

    /// Print LTL operator priorities to \a os.
    void dump_ltl_priorities(std::ostream& os);
    /// Print Boolean operator priorities to \a os.
    void dump_bool_priorities(std::ostream& os);
    /// Print PSL operator priorities to \a os.
    void dump_psl_priorities(std::ostream& os);
    /// Print SERE operator priorities to \a os.
    void dump_sere_priorities(std::ostream& os);
    /// Print SERE Boolean operator priorities to \a os.
    void dump_sere_bool_priorities(std::ostream& os);
    /// Remove some propositions from \a s (used for well-formed generation).
    void remove_some_props(atomic_prop_set& s);

    /// Return a GF(p1 & ... & pn) formula over n random propositions.
    formula GF_n();

  private:
    fset_t unique_set_;
    atomic_prop_set aprops_;
    atomic_prop_set aprops_out_;

    int opt_seed_;
    int opt_tree_size_min_;
    int opt_tree_size_max_;
    bool opt_unique_;
    bool opt_wf_;
    int opt_simpl_level_;
    tl_simplifier simpl_;

    int output_;

    random_formula* rf_ = nullptr;
    random_psl* rp_ = nullptr;
    random_sere* rs_ = nullptr;
  };


}
