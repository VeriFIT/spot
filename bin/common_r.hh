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
#include <spot/tl/simplify.hh>

#define OPT_R 'r'

#define DECLARE_OPT_R                                                   \
    { "simplify", OPT_R, "OPTIONS[,...]", OPTION_ARG_OPTIONAL,          \
      "simplify formulas according to OPTIONS (see below); defaults to " \
      "3 if omitted.  Options are separated by commas; prefix an "      \
      "option with '!' to disable it.  Use digits 0-3 to set option "   \
      "groups at once.", 0 }

// Documentation entries for the simplification options, for inclusion
// in the argp_options array.  'g' is the group number.
#define SIMPLIFY_OPTION_DOC(g)                                          \
    { nullptr, 0, nullptr, 0,                                           \
      "Simplification options (pass these to -r or --simplify):", g },  \
    { "  basics", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,             \
      "basic rewriting rules", 0 },                                     \
    { "  synt-impl", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,          \
      "syntactic implication rules", 0 },                               \
    { "  event-univ", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,         \
      "eventuality / universality rules", 0 },                          \
    { "  containment-checks", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE, \
      "language containment checks", 0 },                               \
    { "  containment-checks-stronger", 0, nullptr,                      \
      OPTION_DOC | OPTION_NO_USAGE,                                     \
      "stronger containment checks", 0 },                               \
    { "  nenoform-stop-on-boolean", 0, nullptr,                         \
      OPTION_DOC | OPTION_NO_USAGE,                                     \
      "do not push negations into Boolean subformulas", 0 },            \
    { "  reduce-size-strictly", 0, nullptr,                             \
      OPTION_DOC | OPTION_NO_USAGE,                                     \
      "disable rules that increase formula size", 0 },                  \
    { "  boolean-to-isop", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,    \
      "rewrite Boolean subformulas in ISOP form", 0 },                  \
    { "  favor-event-univ", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,   \
      "favor eventuality / universality rules", 0 },                    \
    { "  keep-top-xor", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,       \
      "keep Xor/Equiv at top level", 0 },                               \
    { "  unit-propagation", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,   \
      "unit-propagation-based simplification", 0 },                     \
    { "  0", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                  \
      "disable all simplifications", 0 },                               \
    { "  1", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                  \
      "basics, event-univ", 0 },                                        \
    { "  2", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                  \
      "basics, event-univ, synt-impl", 0 },                             \
    { "  3", 0, nullptr, OPTION_DOC | OPTION_NO_USAGE,                  \
      "basics, event-univ, synt-impl, containment-checks, "             \
      "containment-checks-stronger", 0 }

extern int simplification_level;
extern spot::tl_simplifier_options simplification_opts;

void parse_r(const char* arg);
bool simplification_is_enabled();
