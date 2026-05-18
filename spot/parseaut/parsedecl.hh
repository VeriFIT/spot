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

#include <string>
#include "spot/priv/robin_hood.hh"
#include <spot/parseaut/parseaut.hh>
#include <spot/misc/location.hh>

# define YY_DECL \
  int hoayylex(hoayy::parser::semantic_type *yylval, \
               spot::location *yylloc, \
               void* yyscanner, \
               spot::parse_aut_error_list& error_list, \
               robin_hood::unordered_flat_map<std::string, bdd>& fmap)
YY_DECL;

namespace spot
{
  /// \ingroup twa_io
  /// @{

  /// \brief Reset the HOA lexer state.
  void hoayyreset(void* scanner);
  /// \brief Open an HOA file from a path.
  int hoayyopen(const std::string& name, void** scanner);
  /// \brief Open an HOA file from a descriptor.
  int hoayyopen(int fd, void** scanner);
  /// \brief Scan HOA data from a string.
  int hoayystring(const char* data, void** scanner);
  /// \brief Close the HOA lexer.
  void hoayyclose(void* scanner);

  /// \ingroup twa_io
  /// \brief Exception thrown by the HOA lexer upon reading an "--ABORT--"
  /// marker.
  struct hoa_abort
  {
    spot::location pos; ///< Location of the abort marker.
  };

  /// @}
}
