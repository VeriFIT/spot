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

#include <argp.h>
#include <vector>
#include <spot/tl/parse.hh>

enum class job_type : char { LTL_STRING,
                             LTL_FILENAME,
                             AUT_FILENAME,
                             TLSF_FILENAME };

// What the job_processor should extract from a TLSF specification
// passed via --tlsf.  See read_tlsf_file() in common_tlsf.hh, which
// documents how each of these flags is used.
//
// This enum lives here, rather than in common_tlsf.hh, because it
// describes what a job_type::TLSF_FILENAME job may declare: keeping
// it out of common_tlsf.hh spares spot/parsetlsf/public.hh (which
// pulls spot/parseaut/public.hh) to the few tools that read TLSF.
enum class tlsf_flags
  {
    // Accept both finite and infinite specifications.  This is the
    // value that lets read_tlsf_file() pick the syntax matching the
    // SEMANTICS declared by the specification.
    TLSF_EXPECT_ANY = 0,
    // Expect the specification to declare Finite semantics.
    TLSF_EXPECT_FINITE = 1 << 0,
    // Expect the specification to declare infinite semantics (i.e.,
    // it must not declare Finite).
    TLSF_EXPECT_INFINITE = 1 << 1,
    // The caller will not use the partition of the atomic propositions,
    // so do not retrieve the signals (this skips one syfco call).
    // With the syfco backend this also means that the input signals
    // cannot be deduced; the flag has no effect on the "spot" backend,
    // which fills both lists from a single parse anyway, but
    // job_processor::process_tlsf_file() then skips declaring them as
    // well, so that both backends behave the same way.
    TLSF_IGNORE_SIGNALS = 1 << 2,
    // The caller will not use the TARGET of the specification, so do
    // not retrieve it (this skips one syfco call).
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

struct job
{
  const char* str;
  job_type type;

  job(const char* str, job_type type) noexcept
    : str(str), type(type)
  {
  }
};

typedef std::vector<job> jobs_t;
extern jobs_t jobs;
extern bool lbt_input;
// Set by --tlsf-input: every formula source is a TLSF specification
// file rather than a formula (or a list of formulas).  See
// switch_jobs_to_tlsf() in common_finput.cc.
extern bool tlsf_input;

// The common input options, with their own "Input options:" header.
extern const struct argp finput_argp;
// Same options without that header, for the tools that provide their
// own.  The --tlsf entry advertises LTL, as this variant is for the
// tools that work on LTL (or on both LTL and LTLf).
extern const struct argp finput_argp_headless;
// Same as finput_argp_headless, but with a --tlsf entry that mentions
// LTLf instead of LTL, for tools that only accept LTLf formulas.
extern const struct argp finput_argp_headless_ltlf;

int parse_opt_finput(int key, char* arg, struct argp_state* state);

spot::parsed_formula parse_formula(const std::string& s);

spot::formula parse_formula_arg(const std::string& input);

// The job type to use for a positional argument of the tools whose
// positional arguments are all file names.  With --tlsf-input, the
// argument names a TLSF specification.
inline job_type
positional_filename_job(const char*)
{
  return tlsf_input ? job_type::TLSF_FILENAME : job_type::LTL_FILENAME;
}

// The job type to use for a positional argument of the tools that
// accept both formula strings and file names, "-" standing for the
// standard input.  With --tlsf-input, ARG always names a TLSF
// specification.
//
// The argp option handlers are called once all the options have been
// parsed (getopt permutes the non-option arguments to the end of
// argv), so tlsf_input is always known when this is called.
inline job_type
positional_job(const char* arg)
{
  if (tlsf_input)
    return job_type::TLSF_FILENAME;
  return (*arg == '-' && !arg[1])
         ? job_type::LTL_FILENAME : job_type::LTL_STRING;
}


class job_processor
{
protected:
  bool abort_run = false; // Set to true in process_formula() to abort run().
public:
  job_processor() = default;
  job_processor(const job_processor&) = delete;
  job_processor& operator=(const job_processor&) = delete;

  virtual ~job_processor();

  virtual int
  process_formula(spot::formula f,
                  const char* filename = nullptr, int linenum = 0) = 0;

  virtual int
  process_string(const std::string& str,
                 const char* filename = nullptr, int linenum = 0);
  virtual int
  process_stream(std::istream& is, const char* filename);

  virtual int
  process_ltl_file(const char* filename);

  virtual int
  process_aut_file(const char* filename);

  // Read a TLSF specification and pass the resulting LTL (or LTLf)
  // formula to process_formula().  The default implementation is in
  // common_tlsf.cc; tools that need extra work around it (e.g. to
  // pick the synthesis semantics from the TARGET of the
  // specification) override it and call it explicitly.
  virtual int
  process_tlsf_file(const char* filename);

  virtual int
  run();

  char* real_filename = nullptr;
  long int col_to_read = 0;
  char* prefix = nullptr;
  char* suffix = nullptr;

  // Flags for read_tlsf_file() when reading a file given via --tlsf.
  // Defaults to accepting both finite and infinite specifications;
  // tools that only support one kind of formula should set
  // TLSF_EXPECT_FINITE or TLSF_EXPECT_INFINITE.  A tool that never
  // looks at the partition of the atomic propositions, or never at
  // the TARGET, should say so with TLSF_IGNORE_SIGNALS and
  // TLSF_IGNORE_TARGET respectively, so that the syfco backend is not
  // asked for information that would be discarded.
  tlsf_flags tlsf_read_flags = tlsf_flags::TLSF_EXPECT_ANY;
};

// Report and error message or add a default job depending on whether
// the input is a tty.
void check_no_formula(const char* action = "translate");
void check_no_automaton();
