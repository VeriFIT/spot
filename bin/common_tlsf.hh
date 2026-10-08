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
#include "common_finput.hh"

#include <iosfwd>
#include <string>
#include <vector>

#include <spot/parsetlsf/public.hh>
#include <spot/tl/formula.hh>

// Helpers used by the tools that accept TLSF specifications (i.e. all
// the tools that accept LTL or LTLf formulas, through the --tlsf
// option of the shared finput_argp group).  The conversion of a TLSF
// file to LTL or LTLf can be done either by the parser embedded in
// Spot (the default) or by the external syfco tool.  The
// SPOT_TLSF_PARSER environment variable selects the backend: "spot" or
// "syfco".

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

  // The flattened list of input signals, in declaration order.
  //
  // Only the "spot" backend fills this list, since it gets it for
  // free from the single parse it already performs.  The "syfco"
  // backend is never asked for the input signals, as that would cost
  // one more process invocation, and the list is then left empty with
  // inputs_known cleared.
  std::vector<std::string> inputs;

  // False when INPUTS must not be trusted, in which case the caller
  // has to deduce the input signals.  See tlsf_signals below for how
  // the tools do that.
  bool inputs_known = false;

  // Mealy or Moore semantics.  Unchanged when TLSF_IGNORE_TARGET
  // is set.
  spot::tlsf_target target;
};

// Declare the signals of a TLSF specification in the --ins/--outs
// machinery of common_ioap.hh, so that the tools that support
// --relabel=io or --save-part-file can use the partition declared by
// the specification.  If the user already classified some atomic
// propositions from the command-line (with --ins, --outs, or
// --part-file), nothing is declared: the partition the user asked for
// wins.
//
// When CONV.inputs_known, both lists are declared, so that
// find_ap_type() diagnoses any atomic proposition of the formula that
// the specification does not declare.  Otherwise only the outputs are
// declared, and find_ap_type() classifies every other atomic
// proposition of the formula as an input: that is how the inputs are
// deduced when only the syfco backend told us about the outputs.
//
// Pass USABLE=false for a tool that never looks at the partition, so
// that nothing is declared at all.
//
// The previous state is restored when the object is destroyed, so that
// a specification read by --tlsf does not affect the other formulas
// that the tool processes.
class tlsf_signals
{
public:
  explicit tlsf_signals(const tlsf_conversion_result& conv,
                        bool usable = true);
  ~tlsf_signals();
  tlsf_signals(const tlsf_signals&) = delete;
  tlsf_signals& operator=(const tlsf_signals&) = delete;

private:
  // Which of the two lists did we fill?  We only fill them when both
  // were empty, so they only have to be emptied again.
  bool set_inputs_ = false;
  bool set_outputs_ = false;
  // The identifiers this object inserted into the ioap identifier_map,
  // so that we can remove exactly those on destruction (leaving the
  // ones the user provided alone).
  std::vector<std::string> added_inputs_;
  std::vector<std::string> added_outputs_;
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
// parse).  RES.outputs is filled by both backends, but RES.inputs
// and RES.inputs_known are only filled by the "spot" backend: the
// syfco backend is not asked for the input signals, so that
// converting a specification still takes only one syfco invocation
// for the formula, one for the output signals, and one for the
// target.  Callers that need the input signals have to deduce them
// (see tlsf_signals).
//
// Returns false, and prints diagnostics on standard error, when the
// specification cannot be parsed or converted.  When the syfco
// backend is selected, a failure to run syfco is fatal, as it was
// before the built-in parser existed.
bool read_tlsf_file(const std::string& filename, tlsf_flags flags,
                    tlsf_conversion_result& res,
                    std::ostream* verbose = nullptr);
