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
#include "error.h"
#include "common_r.hh"
#include "argmatch.h"

#include <sstream>

int simplification_level = 0;
spot::tl_simplifier_options simplification_opts(0);

// -- option name → enum index mapping for XARGMATCH --
//
// The names must follow the same order as simplify_opt.  They are
// matched with abbreviation support: e.g. "basi", "cont", "unit" work.
// Named options are applied in the order the user specifies them,
// directly updating simplification_opts.

enum simplify_opt
{
  SO_BASICS,
  SO_SYNT_IMPL,
  SO_EVENT_UNIV,
  SO_CONTAINMENT_CHECKS,
  SO_CONTAINMENT_CHECKS_STRONGER,
  SO_NENOFORM_STOP_ON_BOOLEAN,
  SO_REDUCE_SIZE_STRICTLY,
  SO_BOOLEAN_TO_ISOP,
  SO_FAVOR_EVENT_UNIV,
  SO_KEEP_TOP_XOR,
  SO_UNITPROP,
  SO_LEVEL_0,   // disable all
  SO_LEVEL_1,   // basics, event-univ
  SO_LEVEL_2,   // basics, event-univ, synt-impl
  SO_LEVEL_3,   // basics, event-univ, synt-impl, containment*, stronger
};

static char const *const simplify_option_args[] =
  {
    "basics",
    "synt-impl",
    "event-univ",
    "containment-checks",
    "containment-checks-stronger",
    "nenoform-stop-on-boolean",
    "reduce-size-strictly",
    "boolean-to-isop",
    "favor-event-univ",
    "keep-top-xor",
    "unit-propagation",
    "0",
    "1",
    "2",
    "3",
    nullptr
  };

static simplify_opt const simplify_option_types[] =
  {
    SO_BASICS,
    SO_SYNT_IMPL,
    SO_EVENT_UNIV,
    SO_CONTAINMENT_CHECKS,
    SO_CONTAINMENT_CHECKS_STRONGER,
    SO_NENOFORM_STOP_ON_BOOLEAN,
    SO_REDUCE_SIZE_STRICTLY,
    SO_BOOLEAN_TO_ISOP,
    SO_FAVOR_EVENT_UNIV,
    SO_KEEP_TOP_XOR,
    SO_UNITPROP,
    SO_LEVEL_0,
    SO_LEVEL_1,
    SO_LEVEL_2,
    SO_LEVEL_3,
  };

static void
apply_level(simplify_opt idx)
{
  switch (idx)
    {
    case SO_LEVEL_0:
      simplification_opts = spot::tl_simplifier_options(0);
      simplification_level = 0;
      break;
    case SO_LEVEL_1:
      simplification_opts.reduce_basics = true;
      simplification_opts.event_univ = true;
      simplification_level = 1;
      break;
    case SO_LEVEL_2:
      simplification_opts.reduce_basics = true;
      simplification_opts.event_univ = true;
      simplification_opts.synt_impl = true;
      simplification_level = 2;
      break;
    case SO_LEVEL_3:
      simplification_opts.reduce_basics = true;
      simplification_opts.event_univ = true;
      simplification_opts.synt_impl = true;
      simplification_opts.containment_checks = true;
      simplification_opts.containment_checks_stronger = true;
      simplification_level = 3;
      break;
    default:
      break;
    }
}

void
parse_r(const char* arg)
{
  if (!arg)
    {
      simplification_level = 3;
      simplification_opts = spot::tl_simplifier_options(3);
      return;
    }

  // Split on commas
  ARGMATCH_VERIFY(simplify_option_args, simplify_option_types);
  std::istringstream iss(arg);
  std::string token;
  while (std::getline(iss, token, ','))
    {
      // Trim whitespace
      size_t start = token.find_first_not_of(" \t");
      size_t end = token.find_last_not_of(" \t");
      if (start == std::string::npos)
        continue; // empty token
      std::string t = token.substr(start, end - start + 1);

      // Named option, optionally prefixed with "!" to disable
      bool enable = true;
      if (!t.empty() && t[0] == '!')
        {
          enable = false;
          t = t.substr(1);
          if (t.empty())
            error(2, 0, "empty option name after '!' in --simplify");
        }

      simplify_opt idx = XARGMATCH("--simplify", t.c_str(),
                                   simplify_option_args,
                                   simplify_option_types);

      // Forbid "!" prefix on level digits
      if (!enable && idx >= SO_LEVEL_0)
        error(2, 0,
              "cannot prefix '!' to digit '%s' in --simplify; use '0' "
              "to disable all simplifications", t.c_str());

      // Level shortcuts (0-3) set groups of fields at once.
      if (idx >= SO_LEVEL_0)
        {
          apply_level(idx);
          continue;
        }

      // Named options: set the corresponding field.
      switch (idx)
        {
        case SO_BASICS:
          simplification_opts.reduce_basics = enable;
          break;
        case SO_SYNT_IMPL:
          simplification_opts.synt_impl = enable;
          break;
        case SO_EVENT_UNIV:
          simplification_opts.event_univ = enable;
          break;
        case SO_CONTAINMENT_CHECKS:
          simplification_opts.containment_checks = enable;
          break;
        case SO_CONTAINMENT_CHECKS_STRONGER:
          simplification_opts.containment_checks_stronger = enable;
          break;
        case SO_NENOFORM_STOP_ON_BOOLEAN:
          simplification_opts.nenoform_stop_on_boolean = enable;
          break;
        case SO_REDUCE_SIZE_STRICTLY:
          simplification_opts.reduce_size_strictly = enable;
          break;
        case SO_BOOLEAN_TO_ISOP:
          simplification_opts.boolean_to_isop = enable;
          break;
        case SO_FAVOR_EVENT_UNIV:
          simplification_opts.favor_event_univ = enable;
          break;
        case SO_KEEP_TOP_XOR:
          simplification_opts.keep_top_xor = enable;
          break;
        case SO_UNITPROP:
          simplification_opts.unit_prop = enable;
          break;
        default:
          break;
        }
    }
}

bool
simplification_is_enabled()
{
  return simplification_level > 0
    || simplification_opts.reduce_basics
    || simplification_opts.synt_impl
    || simplification_opts.event_univ
    || simplification_opts.containment_checks
    || simplification_opts.containment_checks_stronger
    || simplification_opts.nenoform_stop_on_boolean
    || simplification_opts.reduce_size_strictly
    || simplification_opts.boolean_to_isop
    || simplification_opts.favor_event_univ
    || simplification_opts.keep_top_xor
    || simplification_opts.unit_prop;
}
