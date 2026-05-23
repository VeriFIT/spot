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

#include <spot/misc/common.hh>
#include <spot/twa/fwd.hh>
#include <spot/twa/bdddict.hh>

namespace spot
{
  namespace gen
  {
    /// \defgroup gen Hard-coded families of formulas or automata.
    /// @{
    /// \defgroup genaut Hard-coded families of automata.
    /// @{

    /// \brief Identifiers for automaton patterns
    enum aut_pattern_id {
      AUT_BEGIN = 256,
      /// \brief A family of co-Büchi automata.
      ///
      /// Builds a co-Büchi automaton of size 2n+1 that is
      /// good-for-games and that has no equivalent deterministic
      /// co-Büchi automaton with less than 2^n / (2n+1) states.
      /// \cite kuperberg.15.icalp
      ///
      /// Only defined for n>0.
      AUT_KS_NCA = AUT_BEGIN,
      /// \brief Hard-to-complement non-deterministic Büchi automata
      ///
      /// Build a non-deterministic Büchi automaton with 3n+1 states
      /// and whose complementary language requires an automaton with
      /// at least n! states if Streett acceptance is used.
      ///
      /// Only defined for n>0.  The automaton constructed corresponds
      /// to the right part of Fig.1 of \cite loding.99.fstts , except
      /// that only state q_1 is initial.  (The fact that states q_2,
      /// q_3, ..., and q_n are not initial as in the paper does not
      /// change the recognized language.)
      AUT_L_NBA,
      /// \brief DSA hard to convert to DRA.
      ///
      /// Build a deterministic Streett automaton with 4n states, and n
      /// acceptance pairs, such that an equivalent deterministic Rabin
      /// automaton would require at least n! states.
      ///
      /// Only defined for 1<n<=16 because Spot does not support more
      /// than 32 acceptance pairs.
      ///
      /// This automaton corresponds to the right part of Fig.2 of
      /// \cite loding.99.fstts .
      AUT_L_DSA,
      /// \brief An NBA with (n+1) states whose complement needs ≥n! states
      ///
      /// This automaton is usually attributed to Max Michel (1988),
      /// who described it in some unpublished document.  Other
      /// descriptions of this automaton can be found in a number
      /// of papers \cite thomas.97.chapter .
      ///
      /// Our implementation uses ⌈log₂(n+1)⌉ atomic
      /// propositions to encode the $n+1$ letters used in the
      /// original alphabet.
      AUT_M_NBA,
      /// \brief An NBA with (n+2) states derived from a Cyclic test
      /// case.
      ///
      /// This family of automata is derived from a couple of
      /// examples supplied by Reuben Rowe.  The task is to
      /// check that the automaton generated with AUT_CYCLIST_TRACE_NBA
      /// for a given n contain the automaton generated with
      /// AUT_CYCLIST_PROOF_DBA for the same n.
      AUT_CYCLIST_TRACE_NBA,
      /// \brief A DBA with (n+2) states derived from a Cyclic test
      /// case.
      ///
      /// This family of automata is derived from a couple of
      /// examples supplied by Reuben Rowe.  The task is to
      /// check that the automaton generated with AUT_CYCLIST_TRACE_NBA
      /// for a given n contain the automaton generated with
      /// AUT_CYCLIST_PROOF_DBA for the same n.
      AUT_CYCLIST_PROOF_DBA,
      /// \brief cycles of n letters repeated n times
      ///
      /// This is a Büchi automaton with n^2 states, in which each
      /// state i has a true self-loop and a successor labeled by the
      /// (i%n)th letter.  Only the states that are multiple of n have
      /// no self-loop and are accepting.
      ///
      /// This version uses log(n) atomic propositions to
      /// encode the n letters as minterms.
      AUT_CYCLE_LOG_NBA,
      /// \brief cycles of n letters repeated n times
      ///
      /// This is a Büchi automaton with n^2 states, in which each
      /// state i has a true self-loop and a successor labeled by the
      /// (i%n)th letter.  Only the states that are multiple of n have
      /// no self-loop and are accepting.
      ///
      /// This version uses one-hot encoding of letters, i.e., n atomic
      /// propositions are used, but only one is positive (except on
      /// true self-loops).
      AUT_CYCLE_ONEHOT_NBA,
      /// \brief One-state automaton used to benchmark emptiness checks.
      ///
      /// Generates \f$G_{k,N}\f$: a single-state automaton with an
      /// empty alphabet, one unmarked self-loop, and \f$N\f$
      /// self-loops for each color in \f$A = \{0,\ldots,k-1\}\f$.
      /// The acceptance condition is \f$\Psi_A^k = \Phi_A \vee
      /// \mathsf{Inf}(k)\f$, where \f$\Phi_A\f$ is defined
      /// recursively as \f$\Phi_\emptyset = \mathsf{false}\f$ and
      /// \f$\Phi_A = \bigvee_{i\in A}(\mathsf{Fin}(i) \wedge
      /// (\Phi_{A\setminus\{i\}} \vee \mathsf{Inf}(i)))\f$.  Color
      /// \f$k\f$ never appears on any edge, so the automaton is
      /// empty.
      ///
      /// Requires \f$k \geq 1\f$ and \f$N \geq 1\f$.
      AUT_EL_EMPTY,
      AUT_END
    };

    /// \brief generate an automaton from a known pattern
    ///
    /// The pattern is specified using one value from the aut_pattern_id
    /// enum.  See the man page of the `genaut` binary for a
    /// description of those patterns, and bibliographic references.
    ///
    /// In case you want to combine this automaton with other
    /// automata, pass the bdd_dict to use to make sure that all share
    /// the same.
    SPOT_API twa_graph_ptr
    aut_pattern(aut_pattern_id pattern, int n,
                spot::bdd_dict_ptr dict = make_bdd_dict());

    /// \brief generate an automaton from a two-parameter pattern
    ///
    /// Like aut_pattern(pattern, n, dict) but for patterns that take
    /// two integer arguments.  Use aut_pattern_argc() to check whether
    /// a pattern takes one or two arguments.
    SPOT_API twa_graph_ptr
    aut_pattern(aut_pattern_id pattern, int n, int m,
                spot::bdd_dict_ptr dict = make_bdd_dict());

    /// \brief convert an aut_pattern_it value into a name
    ///
    /// The returned name is suitable to be used as an option
    /// key for the genaut binary.
    SPOT_API const char* aut_pattern_name(aut_pattern_id pattern);

    /// \brief return the number of arguments taken by a pattern
    ///
    /// Returns 1 for single-parameter patterns, 2 for two-parameter
    /// patterns.
    SPOT_API int aut_pattern_argc(aut_pattern_id pattern);

    /// \brief return the maximum useful value for a pattern
    ///
    /// Returns 0 when the pattern has no obvious maximum (the user
    /// should always supply an explicit range).
    SPOT_API int aut_pattern_max(aut_pattern_id pattern);

    /// @}
    /// @}
  }
}
