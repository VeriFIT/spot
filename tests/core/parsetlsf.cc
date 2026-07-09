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

// A syfco-like TLSF -> LTL converter, used by core/parsetlsf.test.
//
// The parser, the printer, and the translation are all exercised
// on every run: the spec is parsed, translated, printed, the printed
// text is reparsed and printed again (the two prints must coincide),
// and the result is reported on stdout in syfco's style.

#include "config.h"

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include <spot/misc/tmpfile.hh>
#include <spot/parsetlsf/public.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/contains.hh>

static int
syntax(char* prog)
{
  std::cerr << "usage: " << prog << " [OPTIONS] FILE.tlsf\n"
            << "Convert a TLSF specification to an LTL formula.\n\n"
            << "Options:\n"
            << "  -op VAR=VAL             override parameter VAR\n"
            << "  --print-input-signals   print the flattened input APs\n"
            << "  --print-output-signals  print the flattened output APs\n"
            << "  --print-target          print Mealy or Moore\n"
            << "  -e FORMULA              check the translated formula is\n"
            << "                          equivalent to FORMULA\n"
            << "  -q                      do not print the formula\n";
  return 2;
}

static void
print_errors(std::ostream& os, const spot::parse_tlsf_error_list& errors)
{
  for (auto& err: errors)
    os << err.first << ": " << err.second << '\n';
}

static void
print_signals(std::ostream& os, const std::vector<std::string>& signals)
{
  for (unsigned j = 0; j < signals.size(); ++j)
    {
      if (j)
        os << ',';
      os << signals[j];
    }
  os << '\n';
}

static int
convert(const std::string& file, const spot::tlsf_parser_options& popts,
        bool print_formula, bool print_inputs, bool print_outputs,
        bool print_target, const std::string& expected)
{
  auto parsed = spot::parse_tlsf(file, popts);
  if (parsed->format_errors(std::cerr))
    return 1;

  spot::parse_tlsf_error_list errors;
  auto res = spot::tlsf_to_ltl(*parsed, {}, &errors);
  if (!res.full_formula || !errors.empty())
    {
      print_errors(std::cerr, errors);
      if (!res.full_formula)
        std::cerr << "conversion of " << file << " failed\n";
      return 1;
    }

  // Verify that printing the spec, parsing the result, and printing
  // again is stable.  This exercises the printer on every run.
  std::ostringstream printed;
  spot::tlsf_print(printed, *parsed);
  {
    spot::temporary_file* tmp = spot::create_tmpfile("parsetlsf-", ".tlsf");
    {
      std::ofstream out(tmp->name());
      out << printed.str();
    }
    auto reparsed = spot::parse_tlsf(tmp->name());
    delete tmp;
    if (reparsed->format_errors(std::cerr))
      return 1;
    std::ostringstream printed2;
    spot::tlsf_print(printed2, *reparsed);
    if (printed2.str() != printed.str())
      {
        std::cerr << "printer output for " << file << " is not stable\n";
        return 1;
      }
  }

  if (!expected.empty())
    {
      auto pf = spot::parse_infix_psl(expected);
      if (pf.format_errors(std::cerr))
        return 1;
      if (!spot::are_equivalent(res.full_formula, pf.f))
        {
          std::cerr << "translated formula of " << file
                    << " is not equivalent to the expected formula\n";
          return 1;
        }
    }

  // Like syfco, the signal/target selectors replace the formula
  // on stdout; only the requested item is printed.
  bool signals_only = print_inputs || print_outputs || print_target;
  if (print_formula && !signals_only)
    std::cout << spot::str_psl(res.full_formula) << '\n';
  if (print_inputs)
    print_signals(std::cout, res.inputs);
  if (print_outputs)
    print_signals(std::cout, res.outputs);
  if (print_target)
    std::cout << (parsed->target == spot::tlsf_target::Moore
                  ? "Moore\n" : "Mealy\n");
  return 0;
}

int
main(int argc, char** argv)
{
  spot::tlsf_parser_options popts;
  bool print_formula = true;
  bool print_inputs = false;
  bool print_outputs = false;
  bool print_target = false;
  std::string expected;
  std::string file;

  int i = 1;
  while (i < argc)
    {
      const char* arg = argv[i];
      if (!std::strcmp(arg, "--print-input-signals"))
        print_inputs = true;
      else if (!std::strcmp(arg, "--print-output-signals"))
        print_outputs = true;
      else if (!std::strcmp(arg, "--print-target"))
        print_target = true;
      else if (!std::strcmp(arg, "-q"))
        print_formula = false;
      else if (!std::strcmp(arg, "-e"))
        {
          if (++i >= argc)
            return syntax(argv[0]);
          expected = argv[i];
        }
      else if (!std::strcmp(arg, "-op"))
        {
          if (++i >= argc)
            return syntax(argv[0]);
          const char* v = argv[i];
          const char* eq = std::strchr(v, '=');
          if (!eq)
            return syntax(argv[0]);
          std::string name(v, eq - v);
          char* end = nullptr;
          long val = std::strtol(eq + 1, &end, 10);
          if (!end || *end)
            return syntax(argv[0]);
          popts.overrides[name] = val;
        }
      else if (arg[0] == '-' && arg[1])
        return syntax(argv[0]);
      else
        file = arg;
      ++i;
    }

  if (file.empty())
    return syntax(argv[0]);

  int rc = convert(file, popts, print_formula, print_inputs,
                   print_outputs, print_target, expected);
  assert(spot::fnode::instances_check());
  return rc;
}