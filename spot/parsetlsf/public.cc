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
#include <spot/parsetlsf/public.hh>
#include "ast.hh"  // private header; the real spot::tlsf_ast definition.
#include "parsedecl.hh"  // private header; tlsfyyopen/close/reset decls.
#include "translate.hh"  // private header; spot::tlsf::translator.
#include <spot/parsetlsf/parsetlsf.hh>  // Bison; declares tlsf_result.
#include <spot/tl/formula.hh>
#include <ostream>
#include <sstream>
#include <utility>
#include <vector>

namespace spot
{
  parsed_tlsf::parsed_tlsf(std::string filename)
    : filename(std::move(filename))
  {
  }

  parsed_tlsf::~parsed_tlsf() = default;

  namespace
  {
    std::string format_semantics(tlsf_semantics s)
    {
      switch (s)
        {
        case tlsf_semantics::Mealy:
          return "Mealy";
        case tlsf_semantics::MealyStrict:
          return "Mealy,Strict";
        case tlsf_semantics::MealyFinite:
          return "Mealy,Finite";
        case tlsf_semantics::Moore:
          return "Moore";
        case tlsf_semantics::MooreStrict:
          return "Moore,Strict";
        case tlsf_semantics::MooreFinite:
          return "Moore,Finite";
        }
      return "Mealy";
    }

    std::string format_target(tlsf_target t)
    {
      return t == tlsf_target::Moore ? "Moore" : "Mealy";
    }

    // Print one ap_decl line.
    void print_ap(std::ostream& os, const spot::tlsf_ap_decl& d)
    {
      os << "    " << d.name;
      if (!d.size.empty())
        os << '[' << d.size << ']';
      os << ";\n";
    }

    // Print a body that may be empty.  An empty body is rendered as
    // `KEY { }`, a non-empty body as `KEY { expr1;\n expr2;\n ... }`.
    // Each formula is deparsed from its AST node via tlsf_print_expr;
    // the deparser honors the .parenthesized flag and inserts
    // precedence-driven parens so the round-trip is stable.
    void print_body(std::ostream& os, const char* keyword,
                    const std::vector<spot::tlsf_expr_ptr>& body)
    {
      if (body.empty())
        {
          os << "  " << keyword << " { }\n";
          return;
        }
      os << "  " << keyword << " {\n";
      for (const auto& e : body)
        {
          spot::tlsf_print_expr(os, *e);
          os << ";\n";
        }
      os << "  }\n";
    }
  }

  // Escape a string for re-emission inside double quotes, using the
  // same convention the lexer and syfco's stringParser understand
  // (see the str start condition in scantlsf.ll): only the double
  // quote is backslash-escaped, because on re-parsing `\"` is the
  // single escape that unescapes to a quote.  A backslash followed
  // by any OTHER character is kept verbatim by the lexer.
  std::string
  escape_info_string(const std::string& in)
  {
    std::string out;
    out.reserve(in.size());
    for (char c : in)
      {
        if (c == '\"')
          out += '\\';
        out += c;
      }
    return out;
  }

  // Print a TLSF dump of the parsed spec.  Comments, blank lines, and
  // the original indentation or section order are NOT preserved; the
  // goal is human inspection, not byte-for-byte round-tripping.
  // The output is itself is meant to be a valid TLSF spec equivalent to
  // the original one.
  void
  tlsf_print(std::ostream& os, const parsed_tlsf& parsed)
  {
    const auto& ast = parsed.ast;
    if (!ast)
      return;

    os << "INFO {\n";
      os << "  TITLE:       \""
         << escape_info_string(ast->title) << "\"\n";
      os << "  DESCRIPTION: \""
         << escape_info_string(ast->description) << "\"\n";
      os << "  SEMANTICS:   " << format_semantics(ast->semantics) << '\n';
      os << "  TARGET:      " << format_target(ast->target) << '\n';
      if (!ast->tags.empty())
        {
          os << "  TAGS:        ";
          for (size_t i = 0; i < ast->tags.size(); ++i)
            {
              if (i)
                os << ", ";
              os << ast->tags[i];
            }
          os << '\n';
        }
    os << "}\n\n";

    os << "GLOBAL {\n";
    if (ast->parameters.empty())
      os << "  PARAMETERS { }\n";
    else
      {
        os << "  PARAMETERS {\n";
        for (const auto& p : ast->parameters)
          os << "    " << p.name << " = " << p.value << ";\n";
        os << "  }\n";
      }      if (ast->definitions.empty() && ast->enumerations.empty())
        os << "  DEFINITIONS { }\n";
      else
        {
          os << "  DEFINITIONS {\n";
          // Enums first: their position relative to regular
          // definitions is not preserved (parsetlsf.yy keeps
          // them in separate vectors, mirroring syfco's
          // `partitionEithers` post-parse split).  Round-trip
          // is byte-stable iff the source ordering is
          // "enums first, then definitions"; re-parsing the
          // canonical form yields the same AST shape.
          for (const auto& e : ast->enumerations)
            {
              os << "    enum " << e.name << " = {";
              for (size_t i = 0; i < e.entries.size(); ++i)
                {
                  if (i)
                    os << ", ";
                  os << e.entries[i].tag << ':'
                     << e.entries[i].bits;
                }
              os << "};\n";
            }
          for (const auto& d : ast->definitions)
            {
              // Bodies are lists of clause AST nodes (no text
              // fallback), so we deparse directly via
              // tlsf_print_expr.  Argument names are COMMA-separated;
              // this must match parsetlsf.yy's `arg_list` rule.  The
              // deparser honors each node's .parenthesized flag and
              // inserts parens for loose-precedence BinaryOp /
              // Quantifier children, so the canonical form
              // round-trips through a fresh parse_tlsf without
              // losing grouping.
              os << "    " << d.name << '(';
              for (size_t i = 0; i < d.args.size(); ++i)
                {
                  if (i)
                    os << ", ";
                  os << d.args[i];
                }
              // Grammar invariant; mirrors translate.cc's assert().
              assert(!d.body.empty());
              if (d.body.size() == 1)
                {
                  // Single-clause bodies (the common macro case)
                  // keep the one-line spelling.
                  os << ") = ";
                  assert(d.body[0]);
                  spot::tlsf_print_expr(os, *d.body[0]);
                  os << ";\n";
                }
              else
                {
                  // Multi-clause (guarded) bodies print one clause
                  // per line; the clauses are juxtaposed maximal
                  // expressions, so the layout re-parses to the
                  // same clause list regardless of line breaks.
                  os << ") =\n";
                  for (size_t i = 0; i < d.body.size(); ++i)
                    {
                      assert(d.body[i]);
                      os << "      ";
                      spot::tlsf_print_expr(os, *d.body[i]);
                      os << (i + 1 == d.body.size() ? ";\n" : "\n");
                    }
                }
            }
          os << "  }\n";
        }
    os << "}\n\n";

    os << "MAIN {\n";
    if (ast->inputs.empty())
      os << "  INPUTS { }\n";
    else
      {
        os << "  INPUTS {\n";
        for (const auto& d : ast->inputs)
          print_ap(os, d);
        os << "  }\n";
      }
    if (ast->outputs.empty())
      os << "  OUTPUTS { }\n";
    else
      {
        os << "  OUTPUTS {\n";
        for (const auto& d : ast->outputs)
          print_ap(os, d);
        os << "  }\n";
      }
    print_body(os, "INITIALLY", ast->initially_body);
    print_body(os, "PRESET", ast->preset_body);
    // ASSUME/ASSUMPTIONS plural-aliases share `assumptions_body`;
    // emit it under the canonical singular keyword.
    print_body(os, "ASSUME", ast->assumptions_body);
    // REQUIRE/REQUIREMENTS share `require_body`; emit the
    // canonical singular.
    print_body(os, "REQUIRE", ast->require_body);
    // ASSERT/INVARIANTS share `assert_body`; emit canonical.
    print_body(os, "ASSERT", ast->assert_body);
    // GUARANTEE/GUARANTEES share `guarantee_body`; emit canonical.
    print_body(os, "GUARANTEE", ast->guarantee_body);
    os << "}\n";
  }

  // Copy the source metadata held in the AST built by the Bison
  // grammar actions onto the public parsed_tlsf so callers can
  // inspect it.  The AST itself (holding parameters, definitions,
  // enumerations, and the parsed MAIN bodies) is attached to out.ast
  // by the parse_tlsf entry points, which are friends of parsed_tlsf.
  // Bus expansion and parameter resolution remain for later phases.
  //
  // The caller-supplied parser-time overrides are mirrored onto
  // out.overrides so parsed_tlsf::overrides reflects the
  // documentation/round-trip contract promised by public.hh
  // (\"mirrored here for documentation and round-trip printing\").
  //
  // Note: the diagnostic list (`res.errors`) is moved out of \a res
  // by the caller (parse_tlsf) BEFORE this function runs, so we
  // only handle the AST-derived fields here.
  static void copy_tlsf_metadata(parsed_tlsf& out,
                                 const spot::tlsf_result& res,
                                 const tlsf_parser_options& opts)
  {
    out.overrides = opts.overrides;
    if (!res.spec)
      return;
    out.title = res.spec->title;
    out.description = res.spec->description;
    out.semantics = res.spec->semantics;
    out.target = res.spec->target;
    out.tags = res.spec->tags;
    out.inputs.reserve(res.spec->inputs.size());
    for (const auto& d : res.spec->inputs)
      out.inputs.push_back(d.name);
    out.outputs.reserve(res.spec->outputs.size());
    for (const auto& d : res.spec->outputs)
      out.outputs.push_back(d.name);
  }

  // Phase-3 implementation: open the scanner, wire the tlsf_result via
  // yylex_init_extra (registring it in tlsfyyopen), run yyparse(),
  // then propagate the diagnostics and the populated AST into the
  // returned parsed_tlsf_ptr.
  parsed_tlsf_ptr
  parse_tlsf(const std::string& filename,
             const tlsf_parser_options& opts)
  {
    auto parsed = std::make_shared<parsed_tlsf>(filename);
    spot::tlsf_result res;
    res.spec = std::make_shared<spot::tlsf_ast>();

    void* scanner = nullptr;
    if (spot::tlsfyyopen(filename, &scanner, res))
      {
        parsed->errors.emplace_back(
          spot::location(),
          "cannot open file: " + filename);
        if (opts.raise_errors)
          {
            std::ostringstream out;
            parsed->format_errors(out);
            throw std::runtime_error(out.str());
          }
        return parsed;
      }

    {
      tlsfyy::parser parser(scanner, res);
      parser.set_debug_level(opts.debug);
      parser.parse();
    }
    spot::tlsfyyclose(scanner);

    // Promote parser diagnostics before testing raise_errors.  The
    // scanner and Bison parser write into res.errors, not into the
    // public result directly.
    parsed->errors = std::move(res.errors);
    parsed->ast = res.spec;
    copy_tlsf_metadata(*parsed, res, opts);
    if (opts.raise_errors && !parsed->errors.empty())
      {
        std::ostringstream out;
        parsed->format_errors(out);
        throw std::runtime_error(out.str());
      }
    return parsed;
  }

  parsed_tlsf_ptr
  parse_tlsf(int fd,
             const std::string& filename,
             const tlsf_parser_options& opts)
  {
    auto parsed = std::make_shared<parsed_tlsf>(filename);
    spot::tlsf_result res;
    res.spec = std::make_shared<spot::tlsf_ast>();

    void* scanner = nullptr;
    if (spot::tlsfyyopen(fd, &scanner, res))
      {
        parsed->errors.emplace_back(
          spot::location(),
          "cannot open descriptor for TLSF parsing");
        if (opts.raise_errors)
          {
            std::ostringstream out;
            parsed->format_errors(out);
            throw std::runtime_error(out.str());
          }
        return parsed;
      }

    {
      tlsfyy::parser parser(scanner, res);
      parser.set_debug_level(opts.debug);
      parser.parse();
    }
    spot::tlsfyyclose(scanner);

    if (opts.raise_errors && !parsed->errors.empty())
      {
        std::ostringstream out;
        if (parsed->format_errors(out))
          throw std::runtime_error(out.str());
      }
    parsed->errors = std::move(res.errors);
    parsed->ast = res.spec;
    copy_tlsf_metadata(*parsed, res, opts);
    return parsed;
  }

  // Walk the AST, evaluate integer contexts, expand buses and ranges,
  // and compose the provisional synthesis formula.  Unsupported
  // language constructs surface as diagnostics (see translate.hh).
  spot::tlsf_translation_result
  tlsf_to_ltl(const parsed_tlsf& tlsf,
              const tlsf_translator_options& opts,
              parse_tlsf_error_list* errors_out)
  {
    if (!tlsf.ast)
      {
        if (errors_out)
          errors_out->emplace_back(spot::location(),
                                   "tlsf_to_ltl: empty AST");
        return spot::tlsf_translation_result{};
      }
    // Parser-time overrides are the defaults for conversion.  A
    // translation-time override has higher precedence and therefore
    // replaces the corresponding parser-time value.
    tlsf_translator_options effective = opts;
    for (const auto& kv : tlsf.overrides)
      if (!effective.overrides.count(kv.first))
        effective.overrides[kv.first] = kv.second;
    spot::tlsf::translator tr(*tlsf.ast, effective, errors_out);
    return tr.run();
  }
}
