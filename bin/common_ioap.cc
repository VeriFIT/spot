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

#include "common_ioap.hh"
#include "error.h"
#include <fstream>
#include <unordered_set>

// --ins and --outs, as supplied on the command-line
std::optional<std::vector<std::string>> all_output_aps;
std::optional<std::vector<std::string>> all_input_aps;
std::optional<std::vector<std::string>> all_unobs_aps;

// Store refirst, separate the filters that are regular expressions from
// the others.  Compile the regular expressions while we are at it.
std::vector<std::regex> regex_in;
std::vector<std::regex> regex_unobs;
std::vector<std::regex> regex_out;
// map identifier to input/output (false=input, true=output)
std::unordered_map<std::string, ap_type> identifier_map;

static bool a_part_file_was_read = false;

static std::string
str_tolower(std::string s)
{
  std::transform(s.begin(), s.end(), s.begin(),
                 [](unsigned char c){ return std::tolower(c); });
  return s;
}

void
split_aps(const std::string& arg, std::vector<std::string>& where)
{
  std::istringstream aps(arg);
  std::string ap;
  while (std::getline(aps, ap, ','))
    {
      ap.erase(remove_if(ap.begin(), ap.end(), isspace), ap.end());
      where.push_back(str_tolower(ap));
    }
}

void process_io_options()
{
  // Filter identifiers from regexes.
  if (all_input_aps.has_value())
    for (const std::string& f: *all_input_aps)
      {
        unsigned sz = f.size();
        if (f[0] == '/' && f[sz - 1] == '/')
          regex_in.push_back(std::regex(f.substr(1, sz - 2)));
        else
          identifier_map.emplace(f, ap_type::InputAP);
      }
  if (all_unobs_aps.has_value())
    for (const std::string& f: *all_unobs_aps)
      {
        unsigned sz = f.size();
        if (f[0] == '/' && f[sz - 1] == '/')
          regex_unobs.push_back(std::regex(f.substr(1, sz - 2)));
        else
          // This may overwrite InputAP, but that's OK, an
          // unobservable input is also an input.
          identifier_map.insert_or_assign(f, ap_type::UnobsAP);
      }
  if (all_output_aps.has_value())
    for (const std::string& f: *all_output_aps)
      {
        unsigned sz = f.size();
        if (f[0] == '/' && f[sz - 1] == '/')
          regex_out.push_back(std::regex(f.substr(1, sz - 2)));
        else if (auto [it, is_new] =
                 identifier_map.try_emplace(f, ap_type::OutputAP);
                 !is_new && it->second != ap_type::OutputAP)
          {
            if (it->second == ap_type::InputAP)
              error(2, 0,
                    a_part_file_was_read ?
                    "'%s' appears in both inputs and outputs" :
                    "'%s' appears in both --ins and --outs",
                    f.c_str());
            else // it->second == ap_type::UnobsAP
              error(2, 0,
                    a_part_file_was_read ?
                    "'%s' appears in both unobservables and outputs" :
                    "'%s' appears in both --unobservable-ins and --outs",
                    f.c_str());
          }
      }
}

static std::unordered_set<std::string>
list_aps_in_formula(spot::formula f)
{
  std::unordered_set<std::string> aps;
  f.traverse([&aps](spot::formula s) {
    if (s.is(spot::op::ap))
      aps.emplace(s.ap_name());
    return false;
  });
  return aps;
}


ap_type
find_ap_type(const std::string& a, const char* filename, int linenum)
{
  if (auto it = identifier_map.find(a); it != identifier_map.end())
    return it->second;

  bool found_unobs = false;
  for (const std::regex& r: regex_unobs)
    if (std::regex_search(a, r))
      {
        found_unobs = true;
        break;
      }
  bool found_in = false;
  if (!found_unobs)
    for (const std::regex& r: regex_in)
      if (std::regex_search(a, r))
        {
          found_in = true;
          break;
        }
  bool found_out = false;
  for (const std::regex& r: regex_out)
    if (std::regex_search(a, r))
      {
        found_out = true;
        break;
      }
  bool has_input_specs =
    all_input_aps.has_value() || all_unobs_aps.has_value();
  if (has_input_specs == all_output_aps.has_value())
    {
      if (!has_input_specs)
        {
          // If the atomic proposition hasn't been classified
          // because neither --ins nor --out were specified,
          // attempt to classify automatically using the first
          // letter.
          int fl = a[0];
          if (fl == 'i' || fl == 'I')
            found_in = true;
          else if (fl == 'o' || fl == 'O')
            found_out = true;
          else if (fl == 'u' || fl == 'U')
            found_unobs = true;
        }
      if (found_in && found_out)
        error_at_line(2, 0, filename, linenum,
                      a_part_file_was_read ?
                      "'%s' matches both inputs and outputs" :
                      "'%s' matches both --ins and --outs",
                      a.c_str());
      if (found_unobs && found_out)
        error_at_line(2, 0, filename, linenum,
                      a_part_file_was_read ?
                      "'%s' matches both unobservables and outputs" :
                      "'%s' matches both --unobservable-ins and --outs",
                      a.c_str());
      if (!found_in && !found_out && !found_unobs)
        {
          if (has_input_specs && !all_input_aps.has_value())
            // --outs and --unobs where given, but did not match
            // Since --input was not given, assume it this variable is input.
            found_in = true;
          else if (has_input_specs || all_output_aps.has_value())
              error_at_line(2, 0, filename, linenum,
                            a_part_file_was_read ?
                            "'%s' does not match any input or output" :
                            all_unobs_aps.has_value() ?
                            "one of --ins, --unobservable-ins, or --outs "
                            "should match '%s'" :
                            "one of --ins or --outs should match '%s'",
                            a.c_str());
          else
            error_at_line(2, 0, filename, linenum,
                          "since '%s' does not start with 'i' or 'o', "
                          "it is unclear if it is an input or "
                          "an output;\n    use --ins, --outs, or --part-file",
                          a.c_str());
        }
    }
  else
    {
      // We reach here if we the combination of options given was one
      // of
      // (1) --ins=...
      // (2) --ins=... --unobs=...
      // (3) --unobs=...
      // (4) --outs=...
      //
      // Cases (1),(2),(3) only specify inputs.  Case (4) only specifies
      // output.

      // In case (4), an unclassified AP can be assumed to be input.
      if (all_output_aps.has_value() && !found_out)
        found_in = true;
      // in case (1) and (2), un unclassified AP can be assumed to be output.
      else if (all_input_aps.has_value() && !all_output_aps.has_value()
               && !found_in && !found_unobs)
        found_out = true;
      // else case (3) is really umabiguous
      else if (!found_unobs && !found_in && !found_out)
        {
          assert(all_unobs_aps.has_value());
          error_at_line(2, 0, filename, linenum,
                        a_part_file_was_read ?
                        "'%s' does not match any input or output" :
                        "one of --ins, --unobservable-ins, or --outs "
                        "should match '%s'",
                        a.c_str());
        }
    }
  if (found_unobs)
    return ap_type::UnobsAP;
  if (found_in)
    return ap_type::InputAP;
  if (found_out)
    return ap_type::OutputAP;
  SPOT_UNREACHABLE();
  error(2, 0, "report this bug, please: '%s' was not classified", a.c_str());
  return ap_type::OutputAP;
}

// Takes a set of the atomic propositions appearing in the formula,
// and separate them into two vectors: input APs and output APs.
std::tuple<std::vector<std::string>,
           std::vector<std::string>,
           std::vector<std::string>>
filter_list_of_aps(spot::formula f, const char* filename, int linenum)
{
  std::unordered_set<std::string> aps = list_aps_in_formula(f);
  // now iterate over the list of atomic propositions to filter them
  std::vector<std::string> matched[3];
  for (const std::string& a: aps)
    matched[static_cast<int>(find_ap_type(a, filename, linenum))].push_back(a);
  return {matched[static_cast<int>(ap_type::InputAP)],
          matched[static_cast<int>(ap_type::OutputAP)],
          matched[static_cast<int>(ap_type::UnobsAP)]};
}


spot::formula relabel_io(spot::formula f, spot::relabeling_map& fro,
                         const char* filename, int linenum)
{
  auto [ins, outs, unobs] = filter_list_of_aps(f, filename, linenum);
  // Different implementation of unordered_set, usinged in
  // filter_list_of_aps can cause aps to be output in different order.
  // Let's sort everything for the sake of determinism.
  std::sort(ins.begin(), ins.end());
  std::sort(outs.begin(), outs.end());
  std::sort(unobs.begin(), unobs.end());
  spot::relabeling_map to;
  unsigned ni = 0;
  for (std::string& i: ins)
    {
      std::ostringstream s;
      s << 'i' << ni++;
      spot::formula a1 = spot::formula::ap(i);
      spot::formula a2 = spot::formula::ap(s.str());
      fro[a2] = a1;
      to[a1] = a2;
    }
  unsigned no = 0;
  for (std::string& o: outs)
    {
      std::ostringstream s;
      s << 'o' << no++;
      spot::formula a1 = spot::formula::ap(o);
      spot::formula a2 = spot::formula::ap(s.str());
      fro[a2] = a1;
      to[a1] = a2;
    }
  unsigned nu = 0;
  for (std::string& u: unobs)
    {
      std::ostringstream s;
      s << 'u' << nu++;
      spot::formula a1 = spot::formula::ap(u);
      spot::formula a2 = spot::formula::ap(s.str());
      fro[a2] = a1;
      to[a1] = a2;
    }
  return spot::relabel_apply(f, &to);
}

// Read FILENAME as a ".part" file.   It should
// contains lines of text of the following form:
//
//    .inputs IN1 IN2 IN3...
//    .outputs OUT1 OUT2 OUT3...
//    .unobservables UNOBS1 UNOBS2...
void read_part_file(const char* filename)
{
  std::ifstream in(filename);
  if (!in)
    error(2, errno, "cannot open '%s'", filename);

  // This parsing is inspired from Lily's parser for .part files.  We
  // read words one by one, and change the "mode" if we the word is
  // ".inputs" or ".outputs".  A '#' introduce a comment until the end
  // of the line.
  std::string word;
  enum { Unknown, Input, Output, Unobs } mode = Unknown;
  while (in >> word)
    {
      // The benchmarks for Syft use ".inputs:" instead of ".inputs".
      if (word == ".inputs" || word == ".inputs:")
        {
          mode = Input;
          if (!all_input_aps.has_value())
            all_input_aps.emplace();
        }
      // The benchmarks for Syft use ".outputs:" instead of ".outputs".
      else if (word == ".outputs"  || word == ".outputs:")
        {
          mode = Output;
          if (!all_output_aps.has_value())
            all_output_aps.emplace();
        }
      // Syft with unreliable inputs use ".unobservables:".
      // https://github.com/whitemech/ltlf-synth-unrel-input-aaai2025/tree/main
      else if (word == ".unobservables"  || word == ".unobservables:")
        {
          mode = Unobs;
          if (!all_unobs_aps.has_value())
            all_unobs_aps.emplace();
        }
      else if (word[0] == '#')
        {
          // Skip the rest of the line.
          in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        }
      else if (mode == Unknown)
        {
          error_at_line(2, 0, filename, 0,
                        "expected '.inputs' or '.outputs' instead of '%s'",
                        word.c_str());
        }
      else if (mode == Input)
        {
          all_input_aps->push_back(str_tolower(word));
        }
      else if (mode == Unobs)
        {
          all_unobs_aps->push_back(str_tolower(word));
        }
      else /* mode == Output */
        {
          all_output_aps->push_back(str_tolower(word));
        }
    }
  a_part_file_was_read = true;
}
