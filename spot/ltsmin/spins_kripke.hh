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

#include <spot/bricks/brick-hash>
#include <spot/bricks/brick-hashset>
#include <spot/kripke/kripke.hh>
#include <spot/ltsmin/spins_interface.hh>
#include <spot/misc/fixpool.hh>
#include <spot/misc/mspool.hh>
#include <spot/misc/intvcomp.hh>
#include <spot/misc/intvcmp2.hh>
#include <spot/twacube/cube.hh>

/// This file aggregates all classes and typedefs necessary
/// to build a kripke that is thread safe.
namespace spot
{
  /// \ingroup ltsmin_interface
  /// @{

  /// \ingroup ltsmin_interface
  /// \brief A Spins state is represented as an array of integer
  /// Note that this array has two reserved slots (position 0 and 1).
  ///
  /// At position 0 we store the hash associated to the state to avoid
  /// multiple computations.
  ///
  /// At position 1 we store the size of the state: keeping this information
  /// allows to compress the state
  typedef int* cspins_state;

  /// \ingroup ltsmin_interface
  /// \brief This class provides the ability to compare two states
  struct cspins_state_equal
  {
    /// \brief Compare two states for equality.
    bool operator()(const cspins_state lhs, const cspins_state rhs) const
    {
      return 0 == memcmp(lhs, rhs, (2+rhs[1])* sizeof(int));
    }
  };

  /// \ingroup ltsmin_interface
  /// \brief This class provides the ability to hash a state
  struct cspins_state_hash
  {
    /// \brief Return the cached hash of a state.
    size_t operator()(const cspins_state that) const
    {
      return that[0];
    }
  };

  /// \ingroup ltsmin_interface
  /// \brief The management of states (i.e. allocation/deallocation) can
  /// be painless since every time we have to consider whether the state will
  /// be compressed or not. This class aims to simplify this management.
  class cspins_state_manager final
  {
  public:
    /// \brief Build a manager for a state of \a state_size variables
    /// and indicate wether compression should be used:
    ///  - 1 for handling large models
    ///  - 2 (faster) assume all values in [0 .. 2^28-1]
    cspins_state_manager(unsigned int state_size, int compress);

    /// \brief Get Rid of the internal representation of the state
    int* unbox_state(cspins_state s) const;

    /// \brief Builder for a state from a raw description given in \a dst
    ///
    /// \a cmp is the area we can use to compute the compressed
    ///    representation of dst.
    /// \a cmpsize the size of the previous area
    cspins_state alloc_setup(int* dst, int* cmp, size_t cmpsize);

    /// \brief Helper to decompress a state
    void decompress(cspins_state s, int* uncompressed, unsigned size) const;

    /// \brief Help the manager to reclaim the memory of a state
    void  dealloc(cspins_state s);

    /// \brief The size of a state
    unsigned int size() const;

  private:
    fixed_size_pool<pool_type::Unsafe> p_;
    multiple_size_pool msp_;
    bool compress_;
    const unsigned int state_size_;
    void (*fn_compress_)(const int*, size_t, int*, size_t&);
    void (*fn_decompress_)(const int*, size_t, int*, size_t);
  };

  /// \brief Parameters passed to callbacks when generating successor
  /// states from the shared library produced by LTSmin.
  struct inner_callback_parameters
  {
    cspins_state_manager* manager;   ///< State manager.
    std::vector<cspins_state>* succ; ///< Successors of a state.
    int* compressed;                ///< Buffer for compressed states.
    int* uncompressed;              ///< Buffer for uncompressed states.
    bool compress;                  ///< Whether compression is used.
    bool selfloopize;               ///< Whether to selfloopize.
  };

  /// \brief This class provides an iterator over the successors of a state.
  /// All successors are computed once when an iterator is recycled or
  /// created.
  ///
  /// Note: Two threads will explore successors with two different orders
  class cspins_iterator final
  {
  public:
    /// \brief Arguments bundle passed to construct or recycle a
    /// cspins_iterator.
    struct cspins_iterator_param
    {
      cspins_state s;               ///< Current state.
      const spot::spins_interface* d; ///< Spins interface.
      cspins_state_manager& manager; ///< State manager.
      inner_callback_parameters& inner; ///< Callback arguments.
      cube cond;                    ///< Current cube condition.
      bool compress;                ///< Whether compression is used.
      bool selfloopize;             ///< Whether to selfloopize.
      spot::cubeset& cubeset;       ///< Cube set.
      int dead_idx;                 ///< Deadlock AP index.
      unsigned tid;                 ///< Thread identifier.
    };

    cspins_iterator(const cspins_iterator&) = delete;
    cspins_iterator(cspins_iterator&) = delete;

    /// \brief Build an iterator from parameters.
    cspins_iterator(cspins_iterator_param& p);
    /// \brief Recycle an iterator from parameters.
    void recycle(cspins_iterator_param& p);
    ~cspins_iterator();

    /// \brief Move to the next successor.
    void next();
    /// \brief Whether all successors were visited.
    bool done() const;
    /// \brief Return the current successor state.
    cspins_state state() const;
    /// \brief Return the current transition condition.
    cube condition() const;

  private:
    /// \brief Compute the real index in the successor vector.
    unsigned compute_index() const;

    inline void setup_iterator(cspins_state s,
                               const spot::spins_interface* d,
                               cspins_state_manager& manager,
                               inner_callback_parameters& inner,
                               cube& cond,
                               bool compress,
                               bool selfloopize,
                               cubeset& cubeset,
                               int dead_idx);

    std::vector<cspins_state> successors_;
    unsigned int current_;
    cube cond_;
    unsigned tid_;
  };


  /// \brief Thread-safe specialization of kripkecube for SpinS states and
  /// iterators.
  template<>
  class kripkecube<cspins_state, cspins_iterator> final
  {
    // Define operators that are available for atomic proposition
     enum class relop
       {
         OP_EQ_VAR,        // 1 == a
         OP_NE_VAR,        // 1 != a
         OP_LT_VAR,        // 1 < a
         OP_GT_VAR,        // 1 > a
         OP_LE_VAR,        // 1 <= a
         OP_GE_VAR,        // 1 >= a
         VAR_OP_EQ,        // a == 1
         VAR_OP_NE,        // a != 1
         VAR_OP_LT,        // a < 1
         VAR_OP_GT,        // a >= 1
         VAR_OP_LE,        // a <= 1
         VAR_OP_GE,        // a >= 1
         VAR_OP_EQ_VAR,    // a == b
         VAR_OP_NE_VAR,    // a != b
         VAR_OP_LT_VAR,    // a < b
         VAR_OP_GT_VAR,    // a > b
         VAR_OP_LE_VAR,    // a <= b
         VAR_OP_GE_VAR,    // a >= b
         VAR_DEAD          // The atomic proposition used to label deadlock
       };

    // Structure for complex atomic proposition
    struct one_prop
    {
      int lval;                 // Index of left variable or raw number
      relop op;                 // The operator
      int rval;                 // Index or right variable or raw number
    };

    // Data structure to store complex atomic propositions
    typedef std::vector<one_prop> prop_set;
    prop_set pset_;

  public:
    /// \brief Build a kripkecube from a Spins interface.
    kripkecube(spins_interface_ptr sip, bool compress,
               std::vector<std::string> visible_aps,
               bool selfloopize, std::string dead_prop,
               unsigned int nb_threads);
    /// \brief Destroy the kripkecube.
    ~kripkecube();
    /// \brief Return the initial state for thread \a tid.
    cspins_state initial(unsigned tid);
    /// \brief Convert a state to a string.
    std::string to_string(const cspins_state s, unsigned tid = 0) const;
    /// \brief Return the iterator for a state.
    cspins_iterator* succ(const cspins_state s, unsigned tid);
    /// \brief Recycle an iterator.
    void recycle(cspins_iterator* it, unsigned tid);

    /// \brief List the atomic propositions used by *this* kripke
    const std::vector<std::string> ap();

    /// \brief The number of thread used by *this* kripke
    unsigned get_threads();

  private:
    /// \brief Parse the set of atomic propositions to have a more
    /// efficient data structure for computation
    void match_aps(std::vector<std::string>& aps, std::string dead_prop);

    /// \brief Compute the cube associated to each state. The cube
    /// will then be given to all iterators.
    void compute_condition(cube c, cspins_state s, unsigned tid = 0);

    spins_interface_ptr sip_;         ///< The interface to the shared library.
    const spot::spins_interface* d_;  ///< Avoid repeated sip_.get() calls.
    cspins_state_manager* manager_;   ///< One manager per thread.
    bool compress_;                   ///< Whether compression is used.

    // One per threads to store no longer used iterators (and save memory)
    std::vector<std::vector<cspins_iterator*>> recycle_;

    inner_callback_parameters* inner_; ///< One callback per thread.
    cubeset cubeset_;                  ///< Cube manipulator.
    bool selfloopize_;                 ///< Whether to selfloopize.
    int dead_idx_;                     ///< Index of the dead AP.
    std::vector<std::string> aps_;     ///< Atomic propositions.
    unsigned int nb_threads_;          ///< Number of threads.
  };

  /// \brief shortcut to manipulate the kripke below
  typedef std::shared_ptr<spot::kripkecube<spot::cspins_state,
                                           spot::cspins_iterator>>
  ltsmin_kripkecube_ptr;

  /// @}
}

#include <spot/ltsmin/spins_kripke.hxx>
