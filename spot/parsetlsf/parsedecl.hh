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

#include <spot/misc/location.hh>
#include <spot/parsetlsf/public.hh>
#include <spot/parsetlsf/parsetlsf.hh>
#include <string>

// Internal header shared between the Flex scanner (scantlsf.ll) and
// the Bison grammar (parsetlsf.yy), mirroring spot/parseaut/parsedecl.hh.
// Both tlsfyy::parser and spot::tlsf_result reach this header
// through the direct include of <spot/parsetlsf/parsetlsf.hh> above.

#define YY_DECL                                                          \
  int tlsfyylex(tlsfyy::parser::semantic_type *yylval,                   \
                spot::location *yylloc,                                  \
                void* yyscanner,                                         \
                spot::tlsf_result& res)
YY_DECL;

namespace spot
{
  /// \brief Open a TLSF scanner on a named file.
  ///
  /// The scanner is wired to the caller-supplied \a res via
  /// yylex_init_extra(): yyextra points to \a res, so both the lexer
  /// and the parser access the same \c spec and \c errors buffers.
  /// \a res must outlive the scanner; in practice, parse_tlsf()
  /// declares \a res on the stack and passes its address here.
  int tlsfyyopen(const std::string& name, void** scanner,
                 tlsf_result& res);

  /// \brief Open a TLSF scanner on an open file descriptor.
  ///
  /// The fd is \c fdopen(3)-ed for reading and is NOT closed by the
  /// scanner; callers retain ownership.
  int tlsfyyopen(int fd, void** scanner, tlsf_result& res);

  /// \brief Open a TLSF scanner on a NUL-terminated string.
  ///
  /// The scanner reads from \a data directly (no copy); \a data must
  /// stay valid until the scanner is closed.
  int tlsfyystring(const char* data, void** scanner,
                   tlsf_result& res);

  /// \brief Close a TLSF scanner.
  ///
  /// Frees only the flex-generated scanner state; \a tlsf_result is
  /// owned by the caller.
  void tlsfyyclose(void* scanner);
}
