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

#include <spot/twa/twa.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <iosfwd>
#include <spot/misc/formater.hh>

namespace spot
{

  /// \addtogroup twa_misc
  /// @{

  /// \brief Basic statistics (states and edges counts) for a TωA.
  struct SPOT_API twa_statistics
  {
    unsigned edges; ///< Number of edges in the automaton.
    unsigned states; ///< Number of states in the automaton.

    twa_statistics() { edges = 0; states = 0; }
    /// Dump statistics to an output stream.
    std::ostream& dump(std::ostream& out) const;
  };

  /// \brief Extended statistics including transition counts for a TωA.
  struct SPOT_API twa_sub_statistics: public twa_statistics
  {
    unsigned long long transitions; ///< Number of transitions in the automaton.

    twa_sub_statistics() { transitions = 0; }
    /// Dump statistics to an output stream.
    std::ostream& dump(std::ostream& out) const;
  };

  /// \brief Compute statistics for an automaton.
  SPOT_API twa_statistics stats_reachable(const const_twa_ptr& g);
  /// \brief Compute sub statistics for an automaton.
  SPOT_API twa_sub_statistics sub_stats_reachable(const const_twa_ptr& g);

  /// \brief Count all transitions, even unreachable ones.
  SPOT_API unsigned long long
  count_all_transitions(const const_twa_graph_ptr& g);

  /// \brief A printable wrapper for a formula, for use in format strings.
  class SPOT_API printable_formula: public printable_value<formula>
  {
  public:
    /// Assign a new formula value.
    printable_formula&
    operator=(formula new_val)
    {
      val_ = new_val;
      return *this;
    }

    /// Print the formula to an output stream.
    virtual void
    print(std::ostream& os, const char*) const override;
  };

  /// \brief A printable wrapper for an acceptance condition, for use in format
  /// strings.
  class SPOT_API printable_acc_cond final: public spot::printable
  {
    acc_cond val_;
  public:
    /// Assign a new acceptance condition value.
    printable_acc_cond&
    operator=(const acc_cond& new_val)
    {
      val_ = new_val;
      return *this;
    }

    /// Print the acceptance condition to an output stream.
    void print(std::ostream& os, const char* pos) const override;
  };

  /// \brief A printable wrapper for SCC information of an automaton, for use in
  /// format strings.
  class SPOT_API printable_scc_info final:
    public spot::printable
  {
    std::unique_ptr<scc_info> val_;
  public:
    /// Compute SCC information for the given automaton.
    void automaton(const const_twa_graph_ptr& aut)
    {
      val_ = std::make_unique<scc_info>(aut);
    }

    /// Clear the stored SCC information.
    void reset()
    {
      val_ = nullptr;
    }

    /// Print SCC statistics to an output stream.
    void print(std::ostream& os, const char* pos) const override;
  };

  /// \brief A printable wrapper reporting reachable and total state/edge
  /// counts.
  class SPOT_API printable_size final:
    public spot::printable
  {
    unsigned reachable_ = 0;
    unsigned all_ = 0;
  public:
    /// Set the reachable and total counts.
    void set(unsigned reachable, unsigned all)
    {
      reachable_ = reachable;
      all_ = all;
    }

    /// Print the size to an output stream.
    void print(std::ostream& os, const char* pos) const override;
  };

  /// \brief A printable wrapper reporting reachable and total transition counts
  /// as long long.
  class SPOT_API printable_long_size final:
    public spot::printable
  {
    unsigned long long reachable_ = 0;
    unsigned long long all_ = 0;
  public:
    /// Set the reachable and total counts.
    void set(unsigned long long reachable, unsigned long long all)
    {
      reachable_ = reachable;
      all_ = all;
    }

    /// Print the long size to an output stream.
    void print(std::ostream& os, const char* pos) const override;
  };

  /// \brief prints various statistics about a TGBA
  ///
  /// This object can be configured to display various statistics
  /// about a TGBA.  Some %-sequence of characters are interpreted in
  /// the format string, and replaced by the corresponding statistics.
  class SPOT_API stat_printer: protected formater
  {
  public:
    /// Construct with an output stream and a format string.
    stat_printer(std::ostream& os, const char* format);

    /// \brief print the configured statistics.
    ///
    /// The \a f argument is not needed if the Formula does not need
    /// to be output, and so is \a run_time).
    std::ostream&
      print(const const_twa_graph_ptr& aut, formula f = nullptr);

  private:
    const char* format_;

    printable_formula form_;
    printable_size states_;
    printable_size edges_;
    printable_long_size trans_;
    printable_value<unsigned> acc_;
    printable_scc_info scc_;
    printable_value<unsigned> nondetstates_;
    printable_value<unsigned> deterministic_;
    printable_value<unsigned> complete_;
    printable_acc_cond gen_acc_;
  };

  /// @}
}
