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

#include <string>
#include <iostream>
#include <climits>
#include <memory>

#include <argp.h>
#include "error.h"

#include "common_setup.hh"
#include "common_hoaread.hh"
#include "common_range.hh"
#include "common_conv.hh"
#include "common_cout.hh"
#include "common_file.hh"

#include <spot/twaalgos/lasso.hh>
#include <spot/twaalgos/word.hh>

static const char argp_program_doc[] = "\
Enumerate lasso-shaped accepted words of ω-automata, printing one word \
per line.\v\
Exit status:\n\
  0  if some words were output\n\
  1  if no words were found (language is empty within the given bounds)\n\
  2  if any error has been reported";

enum {
  OPT_CYCLE = 256,
  OPT_STEM,
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input:", 1 },
    { "file", 'F', "FILENAME", 0,
      "process the automaton in FILENAME", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Lasso-size bounds:", 2 },
    { "stem", OPT_STEM, "RANGE", 0,
      "restrict stem length to RANGE (default: 0..)", 0 },
    { "cycle", OPT_CYCLE, "RANGE", 0,
      "restrict cycle length to RANGE (default: 1..)", 0 },
    /**************************************************/
    RANGE_DOC_FULL,
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output options:", 3 },
    { "count", 'c', nullptr, 0,
      "print only a count of words per automaton (may not terminate "
      "if the size of the words is not restrictued)", 0 },
    { "max-count", 'n', "NUM", 0,
      "stop after outputting NUM words per automaton", 0 },
    { "output", 'o', "FILENAME", 0,
      "write output to FILENAME instead of standard output", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous:", -1 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

static const struct argp_child children[] =
{
  { &hoaread_argp, 0, nullptr, 0 },
  { &misc_argp, 0, nullptr, -1 },
  { nullptr, 0, nullptr, 0 }
};

// Default bounds
static range opt_stem = { 0, std::numeric_limits<int>::max() };
static range opt_cycle = { 1, std::numeric_limits<int>::max() };
static int opt_max_count = -1;
static bool opt_count = false;
static const char* opt_output = nullptr;

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  switch (key)
    {
    case 'c':
      opt_count = true;
      break;
    case 'F':
    case ARGP_KEY_ARG:
      jobs.emplace_back(arg, job_type::AUT_FILENAME);
      break;
    case 'n':
      opt_max_count = to_pos_int(arg, "-n/--max-count");
      break;
    case 'o':
      opt_output = arg;
      break;
    case OPT_CYCLE:
      opt_cycle = parse_range(arg, 1, std::numeric_limits<int>::max());
      break;
    case OPT_STEM:
      opt_stem = parse_range(arg, 0, std::numeric_limits<int>::max());
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  END_EXCEPTION_PROTECT;
  return 0;
}

namespace
{
  class autwords_processor final: public hoa_processor
  {
    std::unique_ptr<output_file> output_;
    std::ostream* out_;
    bool found_any_;

  public:
    autwords_processor(spot::bdd_dict_ptr dict, const char* output_filename)
      : hoa_processor(dict), found_any_(false)
    {
      if (output_filename)
        {
          output_ = std::make_unique<output_file>(output_filename);
          out_ = &output_->ostream();
        }
      else
        {
          out_ = &std::cout;
        }
    }

    ~autwords_processor() override = default;

    bool
    found_any() const
    {
      return found_any_;
    }

    int
    process_automaton(const spot::const_parsed_aut_ptr& haut) override
    {
      // Convert optional int range to unsigned bounds.
      unsigned min_stem = opt_stem.min;
      unsigned max_stem = (opt_stem.max == std::numeric_limits<int>::max())
        ? UINT_MAX : opt_stem.max;
      unsigned min_cycle = opt_cycle.min;
      unsigned max_cycle = (opt_cycle.max == std::numeric_limits<int>::max())
        ? UINT_MAX : opt_cycle.max;

      if (min_cycle < 1)
        error(2, 0, "minimum cycle length must be >= 1");

      auto aut = haut->aut;

      spot::lasso_enumerator enumerator(aut, min_stem, max_stem,
                                          min_cycle, max_cycle);

      unsigned count = 0;
      while (auto word = enumerator.next_word())
        {
          ++count;
          found_any_ = true;

          if (!opt_count)
            {
              *out_ << *word << '\n';
              check_cout();
            }

          if (opt_max_count >= 0
              && static_cast<int>(count) >= opt_max_count)
            break;
        }

      if (opt_count && count > 0)
        {
          *out_ << count << '\n';
          check_cout();
        }
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  return protected_main(argv, [&] {
      const argp ap = { options, parse_opt, "[FILENAME...]",
                        argp_program_doc, children, nullptr, nullptr };

      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      check_no_automaton();

      auto dict = spot::make_bdd_dict();
      autwords_processor processor(dict, opt_output);
      int err = processor.run();
      if (err)
        return 2;
      if (!processor.found_any())
        return 1;
      return 0;
    });
}
