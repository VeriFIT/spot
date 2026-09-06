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

#include "common_tlsf.hh"
#include "common_sys.hh"
#include "common_ioap.hh"
#include "common_trans.hh"
#include "error.h"

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sys/stat.h>
#include <utility>

#include <spot/parsetlsf/public.hh>
#include <spot/tl/parse.hh>

// Which backend should be used to convert TLSF to LTL?  This is
// controlled by the SPOT_TLSF_PARSER environment variable, whose
// accepted values are "spot" (the default) and "syfco".
static bool
use_builtin_parser()
{
  const char* v = getenv("SPOT_TLSF_PARSER");
  if (!v || !*v || !strcmp(v, "spot"))
    return true;
  if (!strcmp(v, "syfco"))
    return false;
  error(2, 0, "invalid value for SPOT_TLSF_PARSER: '%s' "
        "(expected 'spot' or 'syfco')", v);
  return false;                 // silence compiler warnings
}

// Split a --tlsf argument into the actual file name and a list of
// "VAR=VAL" parameter assignments.  The filename may be followed by
// "/VAR=VAL[,VAR=VAL...]" (e.g. "spec.tlsf/N=3,M=4"): if the whole
// string is not an existing file, the part after the last slash is
// interpreted as assignments.
static void
split_tlsf_argument(const std::string& arg,
                    std::string& filename,
                    std::vector<std::string>& assignments)
{
  filename = arg;
  if (const char* slash = strrchr(arg.c_str(), '/'))
    if (strchr(slash, '='))
      {
        struct stat buf;
        if (stat(arg.c_str(), &buf) != 0)
          {
            filename.assign(arg, 0, slash - arg.c_str());
            const char* p = slash + 1;
            while (*p)
              {
                const char* comma = strchr(p, ',');
                assignments.emplace_back(p,
                                         comma ? comma - p : strlen(p));
                p = comma ? comma + 1 : p + strlen(p);
              }
          }
      }
}

// Convert a TLSF file to LTL using the parser embedded in Spot.
// Note that the TLSF_IGNORE_* flags of FLAGS are irrelevant here:
// the single parse fills all fields of RES anyway.
static bool
read_tlsf_with_spot(const std::string& filename,
                    const std::vector<std::string>& assignments,
                    tlsf_flags flags,
                    tlsf_conversion_result& res)
{
  spot::tlsf_parser_options popts;
  for (const std::string& a: assignments)
    {
      auto eq = a.find('=');
      if (eq == std::string::npos)
        {
          std::cerr << "invalid TLSF parameter assignment: '" << a << "'\n";
          return false;
        }
      char* end = nullptr;
      errno = 0;
      long v = strtol(a.c_str() + eq + 1, &end, 10);
      if (errno || end == a.c_str() + eq + 1 || *end)
        {
          std::cerr << "invalid TLSF parameter assignment: '" << a << "'\n";
          return false;
        }
      popts.overrides.emplace(a.substr(0, eq), v);
    }

  auto parsed = spot::parse_tlsf(filename, popts);
  if (parsed->format_errors(std::cerr))
    return false;

  // The flags may require the SEMANTICS declaration of the
  // specification to be Finite, or to not be Finite.  The syfco
  // backend enforces the same constraint (passing -f ltlxba-fin to a
  // non-finite specification makes syfco fail, and vice-versa), so
  // the two backends behave consistently here.
  bool is_finite =
    parsed->semantics == spot::tlsf_semantics::MealyFinite
    || parsed->semantics == spot::tlsf_semantics::MooreFinite;
  if (flags & tlsf_flags::TLSF_EXPECT_FINITE && !is_finite)
    {
      std::cerr << filename << ": this specification does not declare "
                << "Finite semantics, but an LTLf formula was requested\n";
      return false;
    }
  if (flags & tlsf_flags::TLSF_EXPECT_INFINITE && is_finite)
    {
      std::cerr << filename << ": this specification declares Finite "
                << "semantics, but an LTL formula was requested\n";
      return false;
    }

  spot::parse_tlsf_error_list errors;
  auto conv = spot::tlsf_to_ltl(*parsed, {}, &errors);
  if (!conv.full_formula || !errors.empty())
    {
      for (auto& e: errors)
        std::cerr << e.first << ": " << e.second << '\n';
      return false;
    }

  // Hand the formula to the caller directly: no need to print it
  // and have the tool parse the printed form again.
  res.formula = conv.full_formula;
  res.outputs = std::move(conv.outputs);
  res.target = parsed->target;
  return true;
}

// Run "syfco [-op VAR=VAL]... EXTRA FILENAME" and return its
// standard output.  A failure to run syfco is fatal, as it was
// before the built-in parser existed.  OP_ARGS carries the parameter
// assignments; EXTRA, when non-null, is an additional option such as
// --print-output-signals.
static std::string
run_syfco(std::vector<char*>& command,
          const std::vector<std::string>& op_args,
          const char* extra,
          const std::string& filename,
          std::ostream* verbose)
{
  command.resize(1);            // keep only "syfco"
  for (const std::string& a: op_args)
    {
      static char argop[] = "-op";
      command.push_back(argop);
      command.push_back(const_cast<char*>(a.c_str()));
    }
  if (extra)
    command.push_back(const_cast<char*>(extra));
  command.push_back(const_cast<char*>(filename.c_str()));
  command.push_back(nullptr);
  return read_stdout_of_command(command, verbose);
}

// Convert a TLSF file to LTL by calling the external syfco tool.
// Unlike the "spot" backend, this needs one process invocation per
// requested item, so the TLSF_IGNORE_* flags of FLAGS actually save
// calls.  The semantics expectations are enforced by the formula
// call itself: "syfco -f ltlxba-fin" fails on specifications that do
// not declare Finite semantics, and "syfco -f ltlxba" fails on
// those that do.  When no expectation is given, plain "ltlxba" is
// used and both kinds are accepted.
static bool
read_tlsf_with_syfco(const std::string& filename,
                     const std::vector<std::string>& assignments,
                     tlsf_flags flags,
                     tlsf_conversion_result& res,
                     std::ostream* verbose)
{
  std::vector<char*> command;
  static char arg0[] = "syfco";
  command.push_back(arg0);

  // syfco has to be told which kind of formula to output.  When the
  // caller expresses no expectation (neither TLSF_EXPECT_FINITE nor
  // TLSF_EXPECT_INFINITE), probe the semantics of the specification
  // so that both kinds are accepted, like the "spot" backend does.
  // (The "spot" backend needs no such step: one parse gives
  // everything.)
  bool finite;
  if (flags & tlsf_flags::TLSF_EXPECT_FINITE)
    finite = true;
  else if (flags & tlsf_flags::TLSF_EXPECT_INFINITE)
    finite = false;
  else
    {
      static char arg[] = "--print-semantics";
      std::string sem = run_syfco(command, {}, arg, filename, verbose);
      auto not_space = [](unsigned char c){ return !std::isspace(c); };
      sem.erase(std::find_if(sem.rbegin(), sem.rend(),
                             not_space).base(), sem.end());
      finite = sem.find("Finite") != std::string::npos;
    }

  // The formula itself is always needed.  Pass the parameter
  // assignments as -op VAR=VAL options, like the original code did.
  for (const std::string& a: assignments)
    {
      static char argop[] = "-op";
      command.push_back(argop);
      command.push_back(const_cast<char*>(a.c_str()));
    }
  static char argf[] = "-f";
  static char argm[] = "-m";
  static char argfu[] = "fully";
  command.push_back(argf);
  command.push_back(const_cast<char*>(finite ? "ltlxba-fin" : "ltlxba"));
  command.push_back(argm);
  command.push_back(argfu);
  command.push_back(const_cast<char*>(filename.c_str()));
  command.push_back(nullptr);
  std::string f = read_stdout_of_command(command, verbose);
  // syfco outputs the formula as a string: parse it once here, so
  // that the callers get a spot::formula like with the "spot"
  // backend.
  auto pf = spot::parse_infix_psl(f, spot::default_environment::instance(),
                                  false, false);
  if (!pf.f || !pf.errors.empty())
    {
      pf.format_errors(std::cerr);
      return false;
    }
  res.formula = pf.f;

  if (!(flags & tlsf_flags::TLSF_IGNORE_SIGNALS))
    {
      static char arg[] = "--print-output-signals";
      std::string signals = run_syfco(command, assignments, arg,
                                      filename, verbose);
      split_aps(signals, res.outputs);
    }

  if (!(flags & tlsf_flags::TLSF_IGNORE_TARGET))
    {
      static char arg[] = "--print-target";
      std::string target = run_syfco(command, {}, arg, filename, verbose);
      auto not_space = [](unsigned char c){ return !std::isspace(c); };
      target.erase(std::find_if(target.rbegin(), target.rend(),
                                not_space).base(), target.end());
      if (target == "Moore")
        res.target = spot::tlsf_target::Moore;
      else if (target == "Mealy")
        res.target = spot::tlsf_target::Mealy;
      else
        error(2, 0, "syfco reported an unknown target: '%s'",
              target.c_str());
    }
  return true;
}

bool
read_tlsf_file(const std::string& filename, tlsf_flags flags,
               tlsf_conversion_result& res, std::ostream* verbose)
{
  std::string real_filename;
  std::vector<std::string> assignments;
  split_tlsf_argument(filename, real_filename, assignments);
  if (use_builtin_parser())
    return read_tlsf_with_spot(real_filename, assignments, flags, res);
  else
    return read_tlsf_with_syfco(real_filename, assignments, flags,
                                res, verbose);
}
