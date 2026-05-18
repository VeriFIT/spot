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

#include <memory>
#include <spot/misc/common.hh>

namespace spot
{
  /// \ingroup ltsmin_interface
  /// @{

  /// \brief Transition information passed to callbacks during state-space
  /// exploration.
  typedef struct transition_info
  {
    int* labels; ///< Edge labels, NULL, or label pointer.
    int  group;  ///< Transition group, or -1 if unknown.
  } transition_info_t;

  /// \brief Callback used by the PINS interface.
  typedef void (*TransitionCB)(void *ctx,
                               transition_info_t *transition_info,
                               int *dst);

  /// \ingroup ltsmin_interface
  /// \brief Implementation of the PINS interface. This class
  /// is a wrapper that, given a file, will compile it w.r.t.
  /// the PINS interface. The class can then be manipulated
  /// transparently, regardless of the input format.
  class SPOT_API spins_interface
  {
  public:
    /// \brief Load a Spins interface from a shared library.
    spins_interface() = default;
    /// \brief Load a Spins interface from \a file_arg.
    spins_interface(const std::string& file_arg);
    ~spins_interface();

    /// Function to get the initial state.
    void (*get_initial_state)(void *to);
    /// Function to check whether properties are available.
    int (*have_property)();
    /// Function to compute successors.
    int (*get_successors)(void* m, int *in, TransitionCB, void *arg);
    /// Function to return the state size.
    int (*get_state_size)();
    /// Function to name a state variable.
    const char* (*get_state_variable_name)(int var);
    /// Function to return a state variable type.
    int (*get_state_variable_type)(int var);
    /// Function to return the number of types.
    int (*get_type_count)();
    /// Function to name a type.
    const char* (*get_type_name)(int type);
    /// Function to count values for a type.
    int (*get_type_value_count)(int type);
    /// Function to name a type value.
    const char* (*get_type_value_name)(int type, int value);

  private:
    // handle to the dynamic library. The variable is of type lt_dlhandle, but
    // we need this trick since we cannot put ltdl.h in public headers
    void* handle; ///< Dynamic library handle.
  };

  /// \brief Shared pointer to a Spins interface.
  typedef std::shared_ptr<const spins_interface> spins_interface_ptr;

  /// @}
}
