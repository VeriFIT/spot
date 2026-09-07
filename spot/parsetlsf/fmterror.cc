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
#include <spot/parsetlsf/public.hh>
#include <ostream>

namespace spot
{
  bool
  format_tlsf_diagnostics(std::ostream& os,
                          const std::string& filename,
                          const parse_tlsf_error_list& diags)
  {
    bool printed = false;
    for (const auto& err : diags)
      {
        if (!filename.empty() && filename != "-")
          os << filename << ':';
        // spot::location has its own operator<< that prints line:col.
        os << err.first << ": ";
        os << err.second << std::endl;
        printed = true;
      }
    return printed;
  }

  bool
  parsed_tlsf::format_errors(std::ostream& os)
  {
    return format_tlsf_diagnostics(os, filename, errors);
  }

  bool
  parsed_tlsf::format_warnings(std::ostream& os)
  {
    return format_tlsf_diagnostics(os, filename, warnings);
  }
}
