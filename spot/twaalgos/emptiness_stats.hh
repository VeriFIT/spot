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
#include <spot/misc/ltstr.hh>
#include <map>

namespace spot
{

  /// \addtogroup emptiness_check_stats
  /// @{

  /// \brief Interface for retrieving unsigned integer statistics from an
  /// emptiness check.
  struct unsigned_statistics
  {
    virtual
    ~unsigned_statistics()
    {
    }

    /// Retrieve a named statistic by its key.
    unsigned
    get(const char* str) const
    {
      auto i = stats.find(str);
      SPOT_ASSERT(i != stats.end());
      return (this->*i->second)();
    }

    /// Function pointer type for unsigned statistics getters.
    typedef unsigned (unsigned_statistics::*unsigned_fun)() const;
    /// Map from statistic names to getter function pointers.
    typedef std::map<const char*, unsigned_fun, char_ptr_less_than> stats_map;
    stats_map stats; ///< Map of available statistics.
  };

  /// \brief Emptiness-check statistics
  ///
  /// Implementations of spot::emptiness_check may also implement
  /// this interface.  Try to dynamic_cast the spot::emptiness_check
  /// pointer to know whether these statistics are available.
  class ec_statistics: public unsigned_statistics
  {
  public :
    ec_statistics()
    : states_(0), transitions_(0), depth_(0), max_depth_(0)
    {
      stats["states"] =
        static_cast<unsigned_statistics::unsigned_fun>(&ec_statistics::states);
      stats["transitions"] =
        static_cast<unsigned_statistics::unsigned_fun>
          (&ec_statistics::transitions);
      stats["max. depth"] =
        static_cast<unsigned_statistics::unsigned_fun>
          (&ec_statistics::max_depth);
    }

    /// Set the number of visited states.
    void
    set_states(unsigned n)
    {
      states_ = n;
    }

    /// Increment the number of visited states.
    void
    inc_states()
    {
      ++states_;
    }

    /// Increment the number of visited transitions.
    void
    inc_transitions()
    {
      ++transitions_;
    }

    /// Increase the current DFS depth by \a n.
    void
    inc_depth(unsigned n = 1)
    {
      depth_ += n;
      if (depth_ > max_depth_)
        max_depth_ = depth_;
    }

    /// Decrease the current DFS depth by \a n.
    void
    dec_depth(unsigned n = 1)
    {
      SPOT_ASSERT(depth_ >= n);
      depth_ -= n;
    }

    /// Return the number of visited states.
    unsigned
    states() const
    {
      return states_;
    }

    /// Return the number of visited transitions.
    unsigned
    transitions() const
    {
      return transitions_;
    }

    /// Return the maximum DFS depth reached.
    unsigned
    max_depth() const
    {
      return max_depth_;
    }

    /// Return the current DFS depth.
    unsigned
    depth() const
    {
      return depth_;
    }

  private :
    unsigned states_;                /// number of distinct visited states
    unsigned transitions_;        /// number of visited transitions
    unsigned depth_;                /// maximal depth of the stack(s)
    unsigned max_depth_;        /// maximal depth of the stack(s)
  };

  /// \brief Accepting Run Search statistics.
  ///
  /// Implementations of spot::emptiness_check_result may also implement
  /// this interface.  Try to dynamic_cast the spot::emptiness_check_result
  /// pointer to know whether these statistics are available.
  class ars_statistics: public unsigned_statistics
  {
  public:
    ars_statistics()
      : prefix_states_(0), cycle_states_(0)
    {
      stats["(non unique) states for prefix"] =
        static_cast<unsigned_statistics::unsigned_fun>
          (&ars_statistics::ars_prefix_states);
      stats["(non unique) states for cycle"] =
        static_cast<unsigned_statistics::unsigned_fun>
          (&ars_statistics::ars_cycle_states);
    }

    /// Increment the count of prefix states visited.
    void
    inc_ars_prefix_states()
    {
      ++prefix_states_;
    }

    /// Return the number of prefix states visited.
    unsigned
    ars_prefix_states() const
    {
      return prefix_states_;
    }

    /// Increment the count of cycle states visited.
    void
    inc_ars_cycle_states()
    {
      ++cycle_states_;
    }

    /// Return the number of cycle states visited.
    unsigned
    ars_cycle_states() const
    {
      return cycle_states_;
    }

  private:
    unsigned prefix_states_;        /// states visited to construct the prefix
    unsigned cycle_states_;        /// states visited to construct the cycle
  };

  /// \brief Accepting Cycle Search Space statistics
  ///
  /// Implementations of spot::emptiness_check_result may also implement
  /// this interface.  Try to dynamic_cast the spot::emptiness_check_result
  /// pointer to know whether these statistics are available.
  class acss_statistics: public ars_statistics
  {
  public:
    acss_statistics()
    {
      stats["search space states"] =
        static_cast<unsigned_statistics::unsigned_fun>
          (&acss_statistics::acss_states);
    }

    virtual
    ~acss_statistics()
    {
    }

    /// Number of states in the search space for the accepting cycle.
    virtual unsigned acss_states() const = 0;
  };
  /// @}
}
