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

#include <string>
#include <iostream>
#include <sstream>
#include <sys/wait.h>           // WIFSIGNALED, WIFEXITED, ...

#include "error.h"
#include "argmatch.h"

#include "common_setup.hh"
#include "common_conv.hh"
#include "common_aoutput.hh"
#include "common_hoaread.hh"
#include "common_post.hh"
#include "common_sys.hh"
#include "common_trans.hh"

#include <spot/misc/timer.hh>
#include <spot/parseaut/public.hh>

static const char argp_program_doc[] = "\
Run automata through other programs, performing conversion\n\
of input and output as required.";

enum {
  OPT_ERRORS = 256,
  OPT_FAIL_ON_TIMEOUT,
  OPT_GREATEST,
  OPT_SMALLEST,
};

static const argp_option options[] =
  {
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Input:", 1 },
    { "file", 'F', "FILENAME", 0,
      "process automata from FILENAME", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Error handling:", 4 },
    { "errors", OPT_ERRORS, "abort|warn|ignore", 0,
      "how to deal with tools returning with non-zero exit codes or "
      "automata that autdo cannot parse (default: abort)", 0 },
    { "fail-on-timeout", OPT_FAIL_ON_TIMEOUT, nullptr, 0,
      "consider timeouts as errors", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Output selection:", 5 },
    { "smallest", OPT_SMALLEST, "FORMAT", OPTION_ARG_OPTIONAL,
      "for each automaton select the smallest output automaton given by all "
      "tools, using FORMAT for ordering (default is %s,%e)", 0 },
    { "greatest", OPT_GREATEST, "FORMAT", OPTION_ARG_OPTIONAL,
      "for each automaton select the greatest output automaton given by all "
      "tools, using FORMAT for ordering (default is %s,%e)", 0 },
    { "max-count", 'n', "NUM", 0, "output at most NUM automata", 0 },
    /**************************************************/
    { nullptr, 0, nullptr, 0, "Miscellaneous options:", -1 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };


static const argp_option more_o_format[] =
  {
    { "%#", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "serial number of the input automaton processed", 0 },
    { "%K", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "tool used for processing", 0 },
    { "%<", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the part of the line before the automaton if it "
      "comes from a column extracted from a CSV file", 4 },
    { "%>", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,
      "the part of the line after the automaton if it "
      "comes from a column extracted from a CSV file", 4 },
    { nullptr, 0, nullptr, 0, nullptr, 0 }
  };

// Merge our %-escape documentation into aoutput_io_format_argp.
static const struct argp*
build_percent_list()
{
  const argp_option* iter = aoutput_io_format_argp.options;
  unsigned count = 0;
  while (iter->name || iter->doc)
    {
      ++count;
      ++iter;
    }

  unsigned s = count * sizeof(argp_option);
  argp_option* d =
    static_cast<argp_option*>(malloc(sizeof(more_o_format) + s));
  memcpy(d, aoutput_o_format_argp.options, s);
  memcpy(d + count, more_o_format, sizeof(more_o_format));

  static const struct argp more_o_format_argp =
    { d, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr };
  return &more_o_format_argp;
}

enum errors_type { errors_abort, errors_warn, errors_ignore };
static errors_type errors_opt;
static bool fail_on_timeout = false;
static int best_type = 0;       // -1 smallest, 1 greatest, 0 no selection
static const char* best_format = "%s,%e";
static int opt_max_count = -1;

static char const *const errors_args[] =
{
  "stop", "abort",
  "warn", "print",
  "ignore", "silent", nullptr
};

static errors_type const errors_types[] =
{
  errors_abort, errors_abort,
  errors_warn, errors_warn,
  errors_ignore, errors_ignore
};

ARGMATCH_VERIFY(errors_args, errors_types);

const struct argp_child children[] =
  {
    { &hoaread_argp, 0, "Parsing of automata:", 3 },
    { &autproc_argp, 0, nullptr, 3 },
    { &aoutput_argp, 0, nullptr, 6 },
    { build_percent_list(), 0, nullptr, 7 },
    { &misc_argp, 0, nullptr, -1 },
    { nullptr, 0, nullptr, 0 }
  };

static int
parse_opt(int key, char* arg, struct argp_state*)
{
  // Called from C code, so should not raise any exception.
  BEGIN_EXCEPTION_PROTECT;
  switch (key)
    {
    case OPT_ERRORS:
      errors_opt = XARGMATCH("--errors", arg, errors_args, errors_types);
      break;
    case OPT_FAIL_ON_TIMEOUT:
      fail_on_timeout = true;
      break;
    case OPT_GREATEST:
      best_type = 1;
      if (arg)
        best_format = arg;
      break;
    case OPT_SMALLEST:
      best_type = -1;
      if (arg)
        best_format = arg;
      break;
    case 'F':
      jobs.emplace_back(arg, job_type::AUT_FILENAME);
      break;
    case 'n':
      opt_max_count = to_pos_int(arg, "-n/--max-count");
      break;
    case ARGP_KEY_ARG:
      if (arg[0] == '-' && !arg[1])
        jobs.emplace_back(arg, job_type::AUT_FILENAME);
      else
        tools_push_autproc(arg);
      break;
    default:
      return ARGP_ERR_UNKNOWN;
    }
  END_EXCEPTION_PROTECT;
  return 0;
}

namespace
{
  class xautproc_runner final: public autproc_runner
  {
  public:
    spot::bdd_dict_ptr dict;

    explicit xautproc_runner(spot::bdd_dict_ptr dict)
      : autproc_runner(true), dict(dict)
    {
    }

    spot::twa_graph_ptr
    run_tool(unsigned int tool_num, bool& problem,
             spot::process_timer& timer)
    {
      output.reset(tool_num);

      std::ostringstream command;
      format(command, tools[tool_num].cmd);

      std::string cmd = command.str();
      timer.start();
      int es = exec_with_timeout(cmd.c_str());
      timer.stop();

      spot::twa_graph_ptr res = nullptr;
      problem = false;
      if (timed_out)
        {
          if (fail_on_timeout)
            problem = true;
          else
            ++timeout_count;
          std::cerr << program_name
                    << ": timeout during execution of command \""
                    << cmd << "\"\n";
        }
      else if (WIFSIGNALED(es))
        {
          if (errors_opt != errors_ignore)
            {
              problem = true;
              es = WTERMSIG(es);
              std::cerr << program_name << ": execution of command \"" << cmd
                        << "\" terminated by signal " << es << ".\n";
            }
        }
      else if (WIFEXITED(es) && WEXITSTATUS(es) != 0)
        {
          if (errors_opt != errors_ignore)
            {
              problem = true;
              es = WEXITSTATUS(es);
              std::cerr << program_name << ": execution of command \"" << cmd
                        << "\" returned exit code " << es << ".\n";
            }
        }
      else if (output.val())
        {
          auto aut = spot::parse_aut(output.val()->name(), dict,
                                     spot::default_environment::instance(),
                                     opt_parse);
          if (!aut->errors.empty())
            {
              problem = true;
              if (errors_opt != errors_ignore)
                {
                  std::cerr << program_name
                            << ": failed to parse the automaton "
                    "produced by \"" << cmd << "\".\n";
                  aut->format_errors(std::cerr);
                }
            }
          else if (aut->aborted)
            {
              problem = true;
              if (errors_opt != errors_ignore)
                {
                  std::cerr << program_name << ": command \"" << cmd
                            << "\" aborted its output.\n";
                }
            }
          else
            {
              res = aut->aut;
            }
        }
      // Note that res can stay empty if no automaton was output.

      if (problem && errors_opt == errors_ignore)
        {
          problem = false;
          res = nullptr;
        }
      output.cleanup();
      return res;
    }
  };


  class processor final: public hoa_processor
  {
    xautproc_runner runner;
    automaton_printer printer;
    hoa_stat_printer best_printer;
    std::ostringstream best_stream;
    spot::postprocessor& post;
    spot::printable_value<std::string> cmdname;
    spot::printable_value<unsigned> roundval;

  public:
    explicit processor(spot::postprocessor& post)
      : hoa_processor(spot::make_bdd_dict()),
        runner(dict_),
        printer(aut_input),
        best_printer(best_stream, best_format, aut_input),
        post(post)
    {
      printer.add_stat('K', &cmdname);
      printer.add_stat('#', &roundval);
      best_printer.declare('K', &cmdname);
      best_printer.declare('#', &roundval);
    }

    ~processor() override = default;

    void output_aut(const spot::twa_graph_ptr& aut,
                    spot::process_timer& ptimer,
                    const spot::const_parsed_aut_ptr& haut,
                    const char* csv_prefix, const char* csv_suffix)
    {
      static long int output_count = 0;
      // Pass loc=-1 so the printer falls back to haut->loc
      printer.print(aut, ptimer, nullptr, haut->filename.c_str(),
                    -1, output_count++, haut,
                    csv_prefix, csv_suffix);
      if (opt_max_count >= 0 && output_count >= opt_max_count)
        abort_run = true;
    }

    int
    process_automaton(const spot::const_parsed_aut_ptr& haut) override
    {
      static unsigned round = 1;
      runner.round_automaton(haut->aut, round);

      unsigned ts = tools.size();
      spot::twa_graph_ptr best_aut = nullptr;
      std::string best_stats;
      std::string best_cmdname;
      spot::process_timer best_timer;

      roundval = round;
      for (unsigned t = 0; t < ts; ++t)
        {
          bool problem;
          spot::process_timer timer;
          auto aut = runner.run_tool(t, problem, timer);
          if (problem)
            {
              // An error message already occurred about the problem,
              // but this additional one will print filename &
              // loc, and possibly exit.
              error_at_line(errors_opt == errors_abort ? 2 : 0, 0,
                            haut->filename.c_str(),
                            haut->loc.begin.line,
                            "failed to run `%s'",
                            tools[t].name);
            }
          if (aut)
            {
              cmdname = tools[t].name;
              aut = post.run(aut, nullptr);
              if (best_type)
                {
                  best_printer.print(haut, aut, nullptr,
                                     haut->filename.c_str(), -1, 0,
                                     timer, prefix, suffix);
                  std::string aut_stats = best_stream.str();
                  if (!best_aut ||
                      (strverscmp(best_stats.c_str(), aut_stats.c_str())
                       * best_type) < 0)
                    {
                      best_aut = aut;
                      best_stats = aut_stats;
                      best_cmdname = tools[t].name;
                      best_timer = timer;
                    }
                  best_stream.str("");
                }
              else
                {
                  output_aut(aut, timer, haut, prefix, suffix);
                  if (abort_run)
                    break;
                }
            }
        }
      if (best_aut)
        {
          cmdname = best_cmdname;
          output_aut(best_aut, best_timer, haut, prefix, suffix);
        }

      spot::cleanup_tmpfiles();
      ++round;
      return 0;
    }
  };
}

int
main(int argc, char** argv)
{
  return protected_main(argv, [&] {
      const argp ap = { options, parse_opt, "[COMMANDFMT...]",
                        argp_program_doc, children, nullptr, nullptr };

      // Disable post-processing as much as possible by default.
      level = spot::postprocessor::Low;
      pref = spot::postprocessor::Any;
      type = spot::postprocessor::Generic;
      if (int err = argp_parse(&ap, argc, argv, ARGP_NO_HELP, nullptr, nullptr))
        exit(err);

      check_no_automaton();

      if (tools.empty())
        error(2, 0, "No tool to run?  Run '%s --help' for usage.",
              program_name);

      setup_sig_handler();

      spot::postprocessor post;
      post.set_pref(pref | comp | sbacc | colored);
      post.set_type(type);
      post.set_level(level);

      processor p(post);
      if (p.run())
        return 2;
      return 0;
    });
}
