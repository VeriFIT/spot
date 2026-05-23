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

#include "common_sys.hh"

#include <argp.h>
#include "error.h"
#include <vector>
#include <cstring>
#include <cstdlib>
#include <string>

#include "common_setup.hh"
#include "common_aoutput.hh"
#include "common_range.hh"
#include "common_cout.hh"

#include <spot/gen/automata.hh>

using namespace spot;

static const char argp_program_doc[] =
  "Generate ω-automata from predefined patterns.";

static const argp_option options[] =
  {
    /**************************************************/
    // Keep this alphabetically sorted (except for aliases).
    { nullptr, 0, nullptr, 0, "Pattern selection:", 1},
    { "ks-nca", gen::AUT_KS_NCA, "RANGE", 0,
      "A co-Büchi automaton with 2N+1 states for which any equivalent "
      "deterministic co-Büchi automaton has at least 2^N/(2N+1) states.", 0},
    { "l-nba", gen::AUT_L_NBA, "RANGE", 0,
      "A Büchi automaton with 3N+1 states whose complementary Streett "
      "automaton needs at least N! states.", 0},
    { "l-dsa", gen::AUT_L_DSA, "RANGE", 0,
      "A deterministic Streett automaton with 4N states with no "
      "equivalent deterministic Rabin automaton of less than N! states.", 0},
    { "m-nba", gen::AUT_M_NBA, "RANGE", 0,
      "An NBA with N+1 states whose determinization needs at least "
      "N! states.", 0},
    { "cyclist-trace-nba", gen::AUT_CYCLIST_TRACE_NBA, "RANGE", 0,
      "An NBA with N+2 states that should include cyclist-proof-dba=B.", 0},
    { "cyclist-proof-dba", gen::AUT_CYCLIST_PROOF_DBA, "RANGE", 0,
      "A DBA with N+2 states that should be included "
      "in cyclist-trace-nba=B.", 0},
    { "cycle-log-nba", gen::AUT_CYCLE_LOG_NBA, "RANGE", 0,
      "A cyclic NBA with N*N states and log(N) atomic propositions, that "
      "should be simplifiable to a cyclic NBA with N states.", 0 },
    { "cycle-onehot-nba", gen::AUT_CYCLE_ONEHOT_NBA, "RANGE", 0,
      "A cyclic NBA with N*N states and N atomic propositions, that "
      "should be simplifiable to a cyclic NBA with N states.", 0 },
    { "el-empty", gen::AUT_EL_EMPTY, "RANGE[,RANGE]", 0,
      "A one-state automaton G_{k,N} with empty language, used to "
      "benchmark emptiness-checking algorithms.  The first argument is "
      "k (number of colors), the second is N (number of edges per "
      "color).  The acceptance condition uses k+1 colors.", 0 },
    RANGE_DOC,
  /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

struct job
{
  gen::aut_pattern_id pattern;
  struct range range;
  struct range range2;
};

typedef std::vector<job> jobs_t;
static jobs_t jobs;

const struct argp_child children[] =
  {
    { &aoutput_argp, 0, nullptr, 3 },
    { &aoutput_o_format_argp, 0, nullptr, 4 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static void
enqueue_job(int pattern, const char* range_str)
{
  job j;
  j.pattern = static_cast<gen::aut_pattern_id>(pattern);
  j.range2.min = -1;
  j.range2.max = -1;
  if (gen::aut_pattern_argc(j.pattern) == 2)
    {
      const char* comma = strchr(range_str, ',');
      if (!comma)
        {
          j.range2 = j.range = parse_range(range_str);
        }
      else
        {
          std::string range1(range_str, comma);
          j.range = parse_range(range1.c_str());
          j.range2 = parse_range(comma + 1);
        }
    }
  else
    {
      j.range = parse_range(range_str);
    }
  jobs.push_back(j);
}

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  if (key >= gen::AUT_BEGIN && key < gen::AUT_END)
    {
      enqueue_job(key, arg);
      return 0;
    }
  END_EXCEPTION_PROTECT;
  return ARGP_ERR_UNKNOWN;
}

static void
output_pattern(gen::aut_pattern_id pattern, int n, int n2)
{
  process_timer timer;
  timer.start();
  twa_graph_ptr aut = (n2 >= 0)
    ? spot::gen::aut_pattern(pattern, n, n2)
    : spot::gen::aut_pattern(pattern, n);
  timer.stop();
  automaton_printer printer;
  static unsigned serial = 0;
  printer.print(aut, timer, nullptr, aut_pattern_name(pattern), n, serial++);
}

static void
run_jobs()
{
  for (const auto& j: jobs)
    {
      int inc = (j.range.max < j.range.min) ? -1 : 1;
      int n = j.range.min;
      for (;;)
        {
          int inc2 = (j.range2.max < j.range2.min) ? -1 : 1;
          int n2 = j.range2.min;
          for (;;)
            {
              output_pattern(j.pattern, n, n2);
              if (n2 == j.range2.max)
                break;
              n2 += inc2;
            }
          if (n == j.range.max)
            break;
          n += inc;
        }
    }
}


int
main(int argc, char** argv)
{
  return protected_main(argv, [&] {
      strcpy(F_doc, "the name of the pattern");
      strcpy(L_doc, "the argument of the pattern");

      const argp ap = { options, parse_opt, nullptr, argp_program_doc,
                        children, nullptr, nullptr };

      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      if (jobs.empty())
        error(1, 0, "Nothing to do.  Try '%s --help' for more information.",
              program_name);

      run_jobs();
      flush_cout();
      return 0;
    });
}
