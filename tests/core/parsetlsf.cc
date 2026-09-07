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
#include <vector>

#include <fcntl.h>
#include <unistd.h>

#include <spot/misc/tmpfile.hh>
#include <spot/parsetlsf/public.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/print.hh>
#include <spot/twaalgos/contains.hh>

static int
syntax(char* prog)
{
  std::cerr << "usage: " << prog << " [OPTIONS] FILE.tlsf [FILE.tlsf ...]\n"
            << "Convert a TLSF specification to an LTL formula.\n\n"
            << "Each FILE.tlsf is converted in turn, and all the options\n"
            << "apply to all of them.  If any conversion fails, the exit\n"
            << "code is 2 and the number of failures is reported.\n\n"
            << "Options:\n"
            << "  -op VAR=VAL             override parameter VAR\n"
            << "  --print-input-signals   print the flattened input APs\n"
            << "  --print-output-signals  print the flattened output APs\n"
            << "  --print-target          print Mealy or Moore\n"
            << "  -R, --raise-errors      raise on parse errors instead\n"
            << "                          of printing them\n"
            << "  --check-info            require the four mandatory INFO\n"
            << "                          items (TITLE, DESCRIPTION,\n"
            << "                          SEMANTICS, TARGET)\n"
            << "  --no-check-info          do not require them (the default\n"
            << "                          of this tool, for the benefit of\n"
            << "                          the regression tests)\n"
            << "  --from-fd N             parse from file descriptor N\n"
            << "                          (-1: open FILE as the fd)\n"
            << "  --tl-empty              call tlsf_to_ltl on a spec whose\n"
            << "                          AST is empty (a failed parse)\n"
            << "  -e FORMULA              check the translated formula is\n"
            << "                          equivalent to FORMULA\n"
            << "  -q                      do not print the formula\n";
  return 2;
}

// Translation-time diagnostics do not record the file they come from, so
// it is passed in and printed with the same format the parser uses.
static void
print_errors(std::ostream& os, const std::string& file,
             const spot::parse_tlsf_error_list& errors)
{
  spot::format_tlsf_diagnostics(os, file, errors);
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
convert(const std::string& file, int fdopt,
        const spot::tlsf_parser_options& popts, bool tl_empty,
        bool print_formula, bool print_inputs, bool print_outputs,
        bool print_target, const std::string& expected, bool multi)
{
  spot::parsed_tlsf_ptr parsed;
  try
    {
      switch (fdopt)
        {
        case -1:
          {
            int fd = ::open(file.c_str(), O_RDONLY);
            if (fd < 0)
              {
                std::cerr << "cannot open " << file << '\n';
                return 2;
              }
            parsed = spot::parse_tlsf(fd, file, popts);
          }
          break;
        case -2:
          parsed = spot::parse_tlsf(file, popts);
          break;
        default:
          parsed = spot::parse_tlsf(fdopt, file, popts);
          break;
        }
    }
  catch (const std::runtime_error& e)
    {
      std::cerr << "caught: " << e.what() << '\n';
      return 2;
    }

  if (tl_empty)
    {
      // A parse that failed to open the file leaves a null AST;
      // tlsf_to_ltl must report that instead of dereferencing it.
      spot::parse_tlsf_error_list errors;
      auto res = spot::tlsf_to_ltl(*parsed, {}, &errors);
      print_errors(std::cerr, file, errors);
      return res.full_formula ? 0 : 2;
    }

  if (parsed->format_errors(std::cerr))
    return 2;
  // Only the main parse reports the warnings: the re-parse below
  // checks the same AST a second time, and reporting there too would
  // duplicate every warning.
  parsed->format_warnings(std::cerr);

  spot::parse_tlsf_error_list errors;
  auto res = spot::tlsf_to_ltl(*parsed, {}, &errors);
  if (!res.full_formula || !errors.empty())
    {
      print_errors(std::cerr, file, errors);
      if (!res.full_formula)
        std::cerr << "conversion of " << file << " failed\n";
      return 2;
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
    // Same INFO requirements as the main parse, but the other
    // options of POPS are the defaults: the printed spec already
    // spells out the overridden parameter values, and a raised
    // exception would escape the diagnostic path of this tool.
    spot::tlsf_parser_options ropts;
    ropts.check_info = popts.check_info;
    auto reparsed = spot::parse_tlsf(tmp->name(), ropts);
    delete tmp;
    if (reparsed->format_errors(std::cerr))
      return 2;
    std::ostringstream printed2;
    spot::tlsf_print(printed2, *reparsed);
    if (printed2.str() != printed.str())
      {
        std::cerr << "printer output for " << file << " is not stable\n";
        return 2;
      }
  }

  if (!expected.empty())
    {
      auto pf = spot::parse_infix_psl(expected);
      if (pf.format_errors(std::cerr))
        return 2;
      if (!spot::are_equivalent(res.full_formula, pf.f))
        {
          std::cerr << "translated formula of " << file
                    << " is not equivalent to the expected formula\n";
          return 2;
        }
    }

  // Like syfco, the signal/target selectors replace the formula
  // on stdout; only the requested item is printed.
  bool signals_only = print_inputs || print_outputs || print_target;
  bool writes_stdout = (print_formula && !signals_only) || signals_only;
  // When several files are converted in one run, their output shares a
  // single stream, so it is labelled: unlike a diagnostic, a formula
  // does not carry the name of the file it came from.
  if (multi && writes_stdout)
    std::cout << "=== " << file << " ===\n";
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
  // The parser requires the four mandatory INFO items by default,
  // but this tool is also used on stripped-down specifications by
  // the regression tests, so the requirement is off unless --check-info
  // asks for it.
  popts.check_info = false;
  bool print_formula = true;
  bool print_inputs = false;
  bool print_outputs = false;
  bool print_target = false;
  int fdopt = -2;  // -2: filename variant; -1: open FILE as an fd.
  bool tl_empty = false;
  std::string expected;
  std::vector<std::string> files;

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
      else if (!std::strcmp(arg, "-R")
               || !std::strcmp(arg, "--raise-errors"))
        popts.raise_errors = true;
      else if (!std::strcmp(arg, "--check-info"))
        popts.check_info = true;
      else if (!std::strcmp(arg, "--no-check-info"))
        popts.check_info = false;
      else if (!std::strcmp(arg, "--tl-empty"))
        tl_empty = true;
      else if (!std::strcmp(arg, "--from-fd"))
        {
          if (++i >= argc)
            return syntax(argv[0]);
          fdopt = std::atoi(argv[i]);
        }
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
        files.push_back(arg);
      ++i;
    }

  if (files.empty())
    return syntax(argv[0]);

  // Several files may be given at once so that a group of related
  // conversions costs a single process startup.  This matters because
  // the `run` helper of tests/core/defs runs the program through
  // valgrind, whose startup costs an order of magnitude more than the
  // conversion itself.  All the options apply to every file.
  bool multi = files.size() > 1;
  unsigned failed = 0;
  for (const auto& file: files)
    if (convert(file, fdopt, popts, tl_empty, print_formula, print_inputs,
                print_outputs, print_target, expected, multi))
      ++failed;

  assert(spot::fnode::instances_check());
  if (failed)
    {
      if (multi)
        std::cerr << failed << " of " << files.size() << " files failed\n";
      return 2;
    }
  return 0;
}
