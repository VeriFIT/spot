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

#include <spot/misc/common.hh>
#include <spot/misc/location.hh>
#include <spot/parseaut/public.hh>
#include <spot/tl/formula.hh>
#include <map>
#include <memory>
#include <string>
#include <vector>
#include <iosfwd>

namespace spot
{
  /// \addtogroup tlsf_io
  /// @{

  /// TLSF AST. Forward-declared so callers can hold a pointer to it
  /// (e.g. in a parsed_tlsf) without seeing the field layout. The
  /// definition lives in the private spot/parsetlsf/ast.hh (NOT
  /// installed) together with all the other AST node types.
  struct tlsf_ast;

  /// \brief A diagnostic emitted during parsing or translation.
  typedef parse_aut_error parse_tlsf_error;
  /// \brief A list of diagnostics, as filled by parse_tlsf.
  typedef parse_aut_error_list parse_tlsf_error_list;

  /// \brief Semantics variants recognised in TLSF v1.2.
  enum class tlsf_semantics
  {
    Mealy,
    Moore,
    MealyStrict,
    MooreStrict,
    MealyFinite,
    MooreFinite,
  };

  /// \brief Target (player) variant declared by the spec.
  enum class tlsf_target
  {
    Mealy,
    Moore,
  };

  // Forward declarations used by parsed_tlsf below (and its friends).
  struct parsed_tlsf;
  struct tlsf_parser_options;
  struct tlsf_translator_options;
  struct tlsf_translation_result;
  // The parser-side state of a parse in progress, defined by the
  // generated spot/parsetlsf/parsetlsf.hh.  Only the private
  // parsed_tlsf::finish_parse() below names it, and only in its
  // declaration, so this header does not have to include the
  // generated file.
  struct tlsf_result;

  /// Shared pointer typedefs
  /// @{
  typedef std::shared_ptr<parsed_tlsf> parsed_tlsf_ptr;
  typedef std::shared_ptr<const parsed_tlsf> const_parsed_tlsf_ptr;
  /// @}

  /// \brief Result of parsing a TLSF specification.
  ///
  /// Holds the source metadata extracted during parsing plus an
  /// opaque handle on the private AST.  It does NOT carry a
  /// spot::formula: conversion is a separate step (see
  /// tlsf_to_ltl()).
  ///
  /// The AST is held in a private member whose type is
  /// forward-declared above; its definition (and the definition of
  /// every AST node type) is intentionally not part of the public
  /// ABI.
  struct SPOT_API parsed_tlsf
  {
    /// The semantics declared in the file (carries Finite / Strict).
    tlsf_semantics semantics = tlsf_semantics::Mealy;

    /// The target declared in the file (Mealy or Moore).
    tlsf_target target = tlsf_target::Mealy;

    /// Declared (unflattened) list of input AP names. A bus
    /// declaration like `request[N];` contributes a single string
    /// `"request"`; the size expression `"N"` and the parsed bodies
    /// of every MAIN subsection live inside the opaque AST.
    /// Flattening into individual AP names (`request_0`,
    /// `request_1`, …) happens during translation; see
    /// `tlsf_to_ltl()`.
    std::vector<std::string> inputs;

    /// Declared (unflattened) list of output AP names. See `inputs`.
    std::vector<std::string> outputs;

    /// Title from the INFO section (empty if missing).
    std::string title;

    /// Description from the INFO section (empty if missing).
    std::string description;

    /// Tags from the INFO section (`INFO { TAGS: foo, bar; }`),
    /// in source order.  Empty when TAGS is absent.
    std::vector<std::string> tags;

    /// Parameter overrides applied at parse time, mirrored here for
    /// documentation and round-trip printing.  **Replaces -- does
    /// not merge:** the parser replaces this field with
    /// `tlsf_parser_options::overrides` via std::map copy
    /// assignment, so any pre-existing entries in this map are
    /// discarded on each parse.
    /// **Parser-time only:** this map carries only the
    /// caller-supplied overrides from `tlsf_parser_options::overrides`
    /// (e.g. the `/VAR=VAL` form on `ltlsynt --tlsf`).  Declared
    /// `PARAMETERS` blocks live inside the private AST and are
    /// resolved at translate time via `tlsf_to_ltl`.
    std::map<std::string, int> overrides;

    /// Diagnostics collected during parsing (and translation, when
    /// the caller passes the optional \a errors_out to
    /// tlsf_to_ltl).
    parse_tlsf_error_list errors;

    /// Non-fatal diagnostics collected during parsing.  A
    /// specification that triggers only warnings is still valid:
    /// \c errors stays empty and the caller may go on with the
    /// translation.  Currently used for the `SEMANTICS` / `TARGET`
    /// mismatch of TLSF v1.2 SS1.4, where the specification is
    /// ambiguous rather than invalid.
    parse_tlsf_error_list warnings;

    /// Print collected diagnostics to \a os in Spot's
    /// "filename:line:col: message" format. Returns true iff at least
    /// one diagnostic was emitted.
    bool format_errors(std::ostream& os);

    /// Print the collected warnings to \a os, in the same format as
    /// format_errors.  Returns true iff at least one warning was
    /// emitted.
    bool format_warnings(std::ostream& os);


    /// Constructor: store the source filename for use in error
    /// messages and round-trip printing.
    explicit parsed_tlsf(std::string filename);

    // Default constructor is forbidden: a parsed_tlsf always
    // carries the source filename used in error messages.
    parsed_tlsf() = delete;

    /// Destructor is out-of-line because tlsf_ast is incomplete
    /// in this header.
    ~parsed_tlsf();

    // No copy / move: only shared ownership is meaningful here.
    parsed_tlsf(const parsed_tlsf&) = delete;
    parsed_tlsf(parsed_tlsf&&) = delete;
    parsed_tlsf& operator=(const parsed_tlsf&) = delete;
    parsed_tlsf& operator=(parsed_tlsf&&) = delete;

    /// Source filename used in error messages.
    std::string filename;

    // The parsing, printing, and translation entry points below are
    // the only functions allowed to touch the private AST member;
    // they are declared at the end of this header.
    friend parsed_tlsf_ptr parse_tlsf(const std::string& filename,
                                      const tlsf_parser_options& opts);
    friend parsed_tlsf_ptr parse_tlsf(int fd,
                                      const std::string& filename,
                                      const tlsf_parser_options& opts);
    friend parsed_tlsf_ptr parse_tlsf(const std::string& contents,
                                      const std::string& name,
                                      const tlsf_parser_options& opts);
    friend void tlsf_print(std::ostream& os, const parsed_tlsf& tlsf);
    friend tlsf_translation_result tlsf_to_ltl(
        const parsed_tlsf& tlsf,
        const tlsf_translator_options& opts,
        parse_tlsf_error_list* errors_out);

  private:
    /// The AST built by parse_tlsf, kept opaque. May be null if the
    /// parser could not produce even a partial AST.
    std::shared_ptr<tlsf_ast> ast;

    /// \brief Shared tail of the three parse_tlsf() overloads.
    ///
    /// Runs the cross-section validations of TLSF v1.2 (see
    /// spot/parsetlsf/public.cc) on the AST that \a res holds, moves
    /// its diagnostics onto this object, and turns them into a
    /// std::runtime_error when \a opts asks for it.  A private member
    /// rather than a free function because it is the only place that
    /// fills the private members above.
    void finish_parse(tlsf_result& res,
                      const tlsf_parser_options& opts);
  };

  /// \brief Print \a diags to \a os in Spot's diagnostic format.
  ///
  /// Each diagnostic is written as "filename:line.column: message",
  /// the same format as parsed_tlsf::format_errors() and
  /// parsed_tlsf::format_warnings().  \a filename is the name of the
  /// specification the diagnostics come from; it is suppressed when it
  /// is empty or "-", which is the convention for input read from a
  /// pipe.
  ///
  /// A spot::location does not record a file name (the scanner leaves
  /// position::filename null), so a diagnostic only becomes
  /// attributable once the caller supplies the name.  Use this function
  /// to print the parse_tlsf_error_list returned by tlsf_to_ltl(), so
  /// that translation-time diagnostics are formatted exactly like the
  /// parse-time ones.
  ///
  /// \return true iff at least one diagnostic was printed.
  SPOT_API
  bool format_tlsf_diagnostics(std::ostream& os,
                               const std::string& filename,
                               const parse_tlsf_error_list& diags);

  /// \brief Print a TLSF representation of \a tlsf to \a os.
  ///
  /// Comments, blank lines, and the original indentation are NOT
  /// preserved; the goal is human inspection, not byte-for-byte
  /// round-tripping. Section order, identifiers, and constants
  /// are preserved so the output is itself a valid TLSF spec.
  SPOT_API
  void tlsf_print(std::ostream& os, const parsed_tlsf& tlsf);

  /// \brief Options controlling the TLSF parser.
  struct SPOT_API tlsf_parser_options
  {
    /// Map of PARAM -> integer value, e.g. for the /VAR=VAL syntax
    /// on the command line of `ltlsynt --tlsf`. Used while resolving
    /// bus sizes, n-ary loops, SIZEOF, etc. The applied values are
    /// also recorded in parsed_tlsf::overrides.
    std::map<std::string, int> overrides;

    /// If true, throw std::runtime_error on the first fatal error.
    /// Otherwise (default) the error is appended to parsed_tlsf::errors
    /// and parsing continues.
    bool raise_errors = false;

    /// Report a diagnostic when one of the mandatory INFO items
    /// (TITLE, DESCRIPTION, SEMANTICS, TARGET) is missing.  True by
    /// default: TLSF v1.2 SS1.2 requires all four, and an absent
    /// SEMANTICS is the worst case, because the translation would be
    /// composed as if the file had declared `Mealy`.  Set it to
    /// false to accept a specification whose INFO section is
    /// incomplete or absent -- what tests/core/parsetlsf does, since
    /// its fixtures are about the rest of the language.
    /// Note that a *duplicated* INFO item is always reported, whether
    /// this option is set or not: the second declaration is ignored
    /// rather than overriding the first, so it is never what the
    /// author meant.
    bool check_info = true;

    /// Emit Bison/Flex debug traces (default false).
    bool debug = false;
  };

  /// \brief Options controlling the TLSF -> tlsf_translation_result
  /// conversion.
  struct SPOT_API tlsf_translator_options
  {
    /// Override parameter values without re-parsing the file. Layered
    /// on top of the values already stored in the AST.
    std::map<std::string, int> overrides;

    /// If true, throw std::runtime_error on the first fatal error.
    /// Otherwise the error is appended to *errors_out (when supplied).
    bool raise_errors = false;
  };

  /// \brief Result of converting a parsed TLSF AST to LTL or LTLf.
  ///
  /// Carries the LTL translation of every MAIN subsection plus the
  /// composed `full_formula`, along with the bus-flattened
  /// input/output AP lists. On conversion failure, `full_formula` is
  /// null and any diagnostics are appended to the caller-supplied
  /// `errors_out` (when given); the per-section formulas reflect the
  /// partial progress made up to the failure.
  struct SPOT_API tlsf_translation_result
  {
    /// LTL translation of MAIN { INITIALLY { ... } }: the
    /// conjunction of the section's formulas (tt() when empty).
    formula initially;

    /// LTL translation of MAIN { PRESET { ... } } (same convention).
    formula preset;

    /// LTL translation of MAIN { REQUIRE / REQUIREMENTS { ... } }
    /// (same convention).
    formula require;

    /// LTL translation of MAIN { ASSERT / INVARIANTS { ... } }
    /// (same convention).
    formula assertion;

    /// LTL translation of MAIN { ASSUME / ASSUMPTIONS { ... } }
    /// (same convention).
    formula assume;

    /// LTL translation of MAIN { GUARANTEE / GUARANTEES { ... } }
    /// (same convention).
    formula guarantee;

    /// The composed synthesis formula (the standard or strict
    /// composition described in translate.cc), or a null formula on
    /// failure.
    formula full_formula;

    /// Flattened input AP names (e.g. `request_0`, `request_1` after
    /// expanding `request[N];` with `N = 2`).
    std::vector<std::string> inputs;

    /// Flattened output AP names (same convention as `inputs`).
    std::vector<std::string> outputs;
  };

  /// \brief Parse a TLSF file.
  ///
  /// The returned parsed_tlsf_ptr gives shared ownership over the AST
  /// and metadata, so it can be safely retained for printing or
  /// re-translation with different options.
  ///
  /// Once the whole file has been read, the declarations are checked
  /// against each other (see spot/parsetlsf/public.cc): a name may
  /// be declared only once across PARAMETERS, DEFINITIONS, the
  /// enumerations, INPUTS and OUTPUTS, and the mandatory INFO items
  /// must be present unless opts.check_info is false.  A violation is
  /// appended to \c errors; an ambiguous but usable specification
  /// (a SEMANTICS that does not match the TARGET) only produces a
  /// warning, and is listed in \c warnings.
  ///
  /// The parser does not throw unless opts.raise_errors is true.
  SPOT_API parsed_tlsf_ptr
  parse_tlsf(const std::string& filename,
             const tlsf_parser_options& opts = {});

  /// \brief Parse a TLSF specification from an open file descriptor.
  ///
  /// The fd is NOT closed by the parser. This flavour lets callers
  /// feed the parser from a pipe or a previously opened file.
  SPOT_API parsed_tlsf_ptr
  parse_tlsf(int fd,
             const std::string& filename, // for error messages
             const tlsf_parser_options& opts = {});

  /// \brief Parse a TLSF specification held in memory.
  ///
  /// \a contents must be NUL-terminated (as a `std::string` is);
  /// \a name is only used in error messages. This flavour lets
  /// callers parse a specification that was not stored on disk.
  SPOT_API parsed_tlsf_ptr
  parse_tlsf(const std::string& contents,
             const std::string& name, // for error messages
             const tlsf_parser_options& opts = {});

  /// \brief Convert a parsed TLSF AST to an LTL formula.
  ///
  /// Returns a `tlsf_translation_result`. On conversion failure,
  /// the result's `full_formula` is null and any diagnostics are
  /// appended to \a errors_out (when supplied). The AST is read but
  /// not mutated; the same AST may be re-converted with different
  /// options.
  ///
  /// A specification whose parse reported errors is not converted at
  /// all, even when a partial AST is available: an absent clause reads
  /// as an empty one, so translating such a tree can silently return a
  /// formula that does not correspond to what was written. The
  /// per-diagnostic list stays in `tlsf.errors`, which the caller
  /// already owns; repeating it into \a errors_out would duplicate what
  /// `parsed_tlsf::format_errors()` prints. A file that could not be
  /// opened has no AST at all and is reported as such.
  SPOT_API tlsf_translation_result
  tlsf_to_ltl(const parsed_tlsf& tlsf,
              const tlsf_translator_options& opts = {},
              parse_tlsf_error_list* errors_out = nullptr);

  /// @}
}
