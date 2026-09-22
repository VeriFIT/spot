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

#include "common_sys.hh"

#include <iosfwd>
#include <string>
#include <vector>

#include <spot/parsetlsf/public.hh>
#include <spot/tl/formula.hh>

// Helpers used by the tools that accept TLSF specifications
// (ltlsynt, ltlfsynt, ltlf2dfa).  The conversion of a TLSF file to
// LTL or LTLf can be done either by the parser embedded in Spot (the
// default) or by the external syfco tool.  The SPOT_TLSF_PARSER
// environment variable selects the backend: "spot" or "syfco".

// What read_tlsf_file() should extract from the specification.
// The TLSF_IGNORE_* flags only exist to spare the syfco backend
// some process invocations: when set, the corresponding syfco call
// is skipped and the matching field of tlsf_conversion_result is
// left untouched.  They have no effect on the "spot" backend, which
// always fills all fields from a single parse.
enum class tlsf_flags
  {
    // Expect the specification to declare Finite semantics.
    TLSF_EXPECT_FINITE = 1 << 0,
    // Expect the specification to declare infinite semantics (i.e.,
    // it must not declare Finite).
    TLSF_EXPECT_INFINITE = 1 << 1,
    // Do not retrieve the output signals (skips one syfco call).
    TLSF_IGNORE_SIGNALS = 1 << 2,
    // Do not retrieve the target (skips one syfco call).
    TLSF_IGNORE_TARGET = 1 << 3,
  };

// Bitwise operators for tlsf_flags.
inline tlsf_flags
operator|(tlsf_flags a, tlsf_flags b)
{
  return static_cast<tlsf_flags>(static_cast<int>(a)
                                 | static_cast<int>(b));
}

inline tlsf_flags&
operator|=(tlsf_flags& a, tlsf_flags b)
{
  a = a | b;
  return a;
}

inline bool
operator&(tlsf_flags a, tlsf_flags b)
{
  return (static_cast<int>(a) & static_cast<int>(b)) != 0;
}

// The result of converting a TLSF specification.
struct tlsf_conversion_result
{
  // The LTL or LTLf formula.  In the "spot" backend it is produced
  // directly by tlsf_to_ltl(); in the "syfco" backend it is obtained
  // by parsing syfco's output.  Either way the tools get a
  // spot::formula without any intermediate print/parse round-trip.
  spot::formula formula;

  // The flattened list of output signals, in declaration order.
  // The names are taken verbatim from the specification (their case
  // is preserved) when the "spot" backend is used, while the "syfco"
  // backend asks syfco to print them in the "ltlxba" syntax, which
  // currently lower-cases them.  Either way they match the atomic
  // propositions of FORMULA.
  // Unchanged when TLSF_IGNORE_SIGNALS is set.
  std::vector<std::string> outputs;

  // Mealy or Moore semantics.  Unchanged when TLSF_IGNORE_TARGET
  // is set.
  spot::tlsf_target target;
};

// Convert the TLSF specification given by FILENAME to an LTL (or
// LTLf, if FLAGS contains TLSF_EXPECT_FINITE) formula.  FILENAME may
// be followed by "/VAR=VAL[,VAR=VAL...]" to specify values for
// parameters, as in "spec.tlsf/N=3,M=4".  VERBOSE, when non-null,
// receives a trace of the conversion (e.g. the syfco command lines
// when that backend is selected).
//
// FLAGS may contain one of TLSF_EXPECT_FINITE or
// TLSF_EXPECT_INFINITE to require the SEMANTICS declaration of the
// specification to match the requested kind of formula: a
// specification that does not declare Finite semantics is rejected
// if TLSF_EXPECT_FINITE is set, and one that does is rejected if
// TLSF_EXPECT_INFINITE is set (mirroring what "syfco -f ltlxba-fin"
// versus "syfco -f ltlxba" enforce).  If neither is given, both
// kinds are accepted.  Passing both is an error.
//
// TLSF_IGNORE_SIGNALS and TLSF_IGNORE_TARGET leave the `outputs` and
// `target` fields of RES untouched: in the syfco backend this skips
// the corresponding syfco invocations, in the "spot" backend it
// changes nothing (all fields are always filled by the single
// parse).
//
// Returns false, and prints diagnostics on standard error, when the
// specification cannot be parsed or converted.  When the syfco
// backend is selected, a failure to run syfco is fatal, as it was
// before the built-in parser existed.
bool read_tlsf_file(const std::string& filename, tlsf_flags flags,
                    tlsf_conversion_result& res,
                    std::ostream* verbose = nullptr);
