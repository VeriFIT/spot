%{/* -*- coding: utf-8 -*- */
/* Copyright (C) by the Spot authors, see the AUTHORS file for details.
 *
 * This file is part of Spot, a model checking library.
 *
 * Spot is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * Spot is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
 * License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * NB: `M` (LTL strong release) is intentionally NOT a reserved
 * keyword here.  Real-world TLSF benchmarks (notably chomp.tlsf
 * in the project root) use single-letter AP / parameter names
 * such as `M`, and reserving the literal in the lexer would
 * surface a spurious "syntax error" on otherwise-valid identifier
 * bindings -- e.g. `M = 3;` would tokenise `M` as `LTL_M` and the
 * `IDENTIFIER EQUAL NUMBER SEMICOLON` rule for `param_decl`
 * would then reject the spec.  The grammar's `LTL_M` token
 * declaration is intentionally retained (matches the spec); a
 * future lexer refactor can reintroduce the keyword alongside its
 * grammar production.
 */
#include "config.h"
#include <spot/misc/location.hh>
#include <spot/parsetlsf/public.hh>
#include <string>
#include "parsedecl.hh"
#include <spot/parsetlsf/parsetlsf.hh>

#define YY_USER_ACTION yylloc->columns(yyleng);

typedef tlsfyy::parser::token token;
%}

%option noyywrap
%option reentrant
%option extra-type="spot::tlsf_result*"
%option prefix="tlsfyy"

%x str

%%

%{
  // Accumulator for the multi-line STRING token (see the str start
  // condition below).  Declared here so it lives in yylex's frame;
  // the whole string is consumed within one yylex() call because
  // every str-state rule except the closing quote falls through, so
  // the per-call initialisation is harmless.  Mirrors the same trick
  // in scanaut.ll (in_STRING).
  std::string s;
%}

[ \t\f]+              yylloc->step();
[\n]+                 yylloc->lines(yyleng); yylloc->step();
[\r\n]+               yylloc->lines(yyleng / 2); yylloc->step();

"//"[^\n]*            yylloc->step();
  /* C-style block comment.  The alternation admits `*` characters
   * inside the comment body (real benchmarks such as
   * full_arbiter_unreal1.tlsf use `*` for bullet-pointed comments),
   * and the closing alternative consumes the first star-slash pair.
   * Indented block comment (not // line comment) per Flex's
   * rules-section convention. */
"/*"([^*]|\*+[^*/])*\*+"/"  yylloc->step();

"INFO"                return token::INFO;
"MAIN"                return token::MAIN;
"GLOBAL"              return token::GLOBAL;

"PARAMETERS"          return token::PARAMETERS;
"DEFINITIONS"         return token::DEFINITIONS;
  /* `enum` keyword (TLSF v1.1) accepted as a def_list item
   * INSIDE the GLOBAL { DEFINITIONS { ... } } block.
   * Format per syfco 1.2.1.2
   * (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs
   * enumParser): `enum X = {Tag0:00, Tag1:01, ...};` -- a
   * comma-separated list of `Tag:bits` pairs.  Each `bits`
   * string is a sequence of 0, 1, and (don't-care) `*`
   * characters; the first value's length sets the enum width.
   * Indented block comment (not // line comment) per
   * Flex's rules-section convention; the leading 2 spaces
   * tell Flex to copy this verbatim into the generated
   * scanner rather than treating it as a pattern.
   * NB: the prior draft of this comment included the literal
   * slash-star, star-slash sequence (used to label the block
   * comment syntax) -- that prematurely closes the enclosing
   * C block comment, so it has been removed here. */
"enum"                return token::ENUM;
"INPUTS"              return token::INPUTS;
"OUTPUTS"             return token::OUTPUTS;

"INITIALLY"           return token::INITIALLY;
"PRESET"              return token::PRESET;
  /* Plural forms for REQUIRE/ASSERT/GUARANTEE/ASSUME recognised
   * by TLSF v1.1 (canonical syfco reference parser):
   * spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Component.hs
   * maps each alias to the same body field.  ASSUME +
   * ASSUMPTIONS introduce a new "assumptions" body that Spot
   * previously had no slot for; both fields are now first-class.
   * Indented block comments here (not // line comments) because
   * Flex does not recognise C++ line comments in its rules
   * section -- they would be parsed as rules and produce an
   * "unrecognized rule" error.  The leading 2-space indent
   * tells Flex the block is C code to copy through, not a
   * pattern.  See scanaut.ll for the same convention. */
"REQUIRE"             return token::REQUIRE;
"REQUIREMENTS"        return token::REQUIREMENTS;
"ASSERT"              return token::ASSERT;
"INVARIANTS"          return token::INVARIANTS;
"GUARANTEE"           return token::GUARANTEE;
"GUARANTEES"          return token::GUARANTEES;
"ASSUME"              return token::ASSUME;
"ASSUMPTIONS"         return token::ASSUMPTIONS;

"TITLE:"              return token::TITLE;
"DESCRIPTION:"        return token::DESCRIPTION;
"SEMANTICS:"          return token::SEMANTICS_KW;
"TARGET:"             return token::TARGET;
"TAGS:"               return token::TAGS;

"Mealy"               return token::MEALY;
"Moore"               return token::MOORE;
"Strict"              return token::STRICT;
"Finite"              return token::FINITE;

"G"                   return token::LTL_G;
"F"                   return token::LTL_F;
"X"                   return token::LTL_X;
"U"                   return token::LTL_U;
"R"                   return token::LTL_R;
"W"                   return token::LTL_W;
"X[!]"                return token::LTL_STRONG_NEXT;

"true"                return token::BOOL_TRUE;
"false"               return token::BOOL_FALSE;
"IN"                  return token::IN;
"NOT"                 return token::KW_NOT;
"AND"                 return token::KW_AND;
"OR"                  return token::KW_OR;
"IMPLIES"             return token::KW_IMPLIES;
"EQUIV"               return token::KW_EQUIV;
"EQ"                  return token::KW_EQ;
"NEQ"                 return token::KW_NEQ;
"LE"                  return token::KW_LE;
"GE"                  return token::KW_GE;
"LEQ"                 return token::KW_LEQ;
"GEQ"                 return token::KW_GEQ;
"ELEM"                return token::KW_ELEM;
"FORALL"              return token::KW_FORALL;
"EXISTS"              return token::KW_EXISTS;
"CUP"                 return token::SET_CUP;
"CAP"                 return token::SET_CAP;
"SETMINUS"            return token::SET_MINUS;
"PLUS"                return token::KW_PLUS;
"MINUS"               return token::KW_MINUS;
"MUL"                 return token::KW_MUL;
"DIV"                 return token::KW_DIV;
"MOD"                 return token::KW_MOD;

"MIN"                 return token::FN_MIN;
"MAX"                 return token::FN_MAX;
"SIZEOF"              return token::FN_SIZEOF;
"SUM"                 return token::FN_SUM;
"PROD"                return token::FN_PROD;

"&&"                  return token::AND;
"||"                  return token::OR;
"->"                  return token::IMPLIES;
"<->"                 return token::EQUIV;
"=="                  return token::EQ;
"!="                  return token::NEQ;
"<="                  return token::LE;
">="                  return token::GE;
"<-"                  return token::IN;
"<"                   return token::LT;
">"                   return token::GT;

"+"                   return token::PLUS;
"-"                   return token::MINUS_;
"*"                   return token::STAR;
"/"                   return token::SLASH;
"%"                   return token::PERCENT;

"!"                   return token::BANG;
".."                  return token::DOTDOT;

"{"                   return token::LBRACE;
"}"                   return token::RBRACE;
";"                   return token::SEMICOLON;
","                   return token::COMMA;
"="                   return token::EQUAL;
":"                   return token::COLON;
"["                   return token::LBRACKET;
"]"                   return token::RBRACKET;
"("                   return token::LPAREN;
")"                   return token::RPAREN;

  /* String literal (INFO TITLE/DESCRIPTION/TAGS).  Mirrors syfco's
   * stringParser (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/
   * Utils.hs): the string may span several lines (real benchmarks
   * such as tictactoe_1.tlsf carry a whole prose paragraph inside
   * DESCRIPTION), `\"` is an escaped quote, any other `\x` is kept
   * verbatim (backslash included), and an unterminated string is
   * diagnosed instead of silently eating the rest of the file.
   * Indented block comment (not // line comment) per Flex's
   * rules-section convention. */
\"                        { BEGIN(str); s.clear(); }
<str>\"                   {
                            BEGIN(INITIAL);
                            yylval->emplace<std::string>(s);
                            return token::STRING;
                          }
<str>\\.                {
                            if (yytext[1] == '\"')
                              s += '\"';
                            else
                              s.append(yytext, yyleng);
                          }
<str>[^\\\"\n\r]+      { s.append(yytext, yyleng); }
<str>\n                   {
                            s += '\n';
                            yylloc->lines(1);
                            yylloc->end.column = 1;
                          }
<str>\r\n                {
                            s.append("\r\n", 2);
                            yylloc->lines(1);
                            yylloc->end.column = 1;
                          }
<str>\r                   {
                            s += '\r';
                            yylloc->lines(1);
                            yylloc->end.column = 1;
                          }
<str><<EOF>>               {
                            yyextra->errors.emplace_back(
                              *yylloc, "unclosed string");
                            BEGIN(INITIAL);
                            yylval->emplace<std::string>(s);
                            return token::STRING;
                          }

  /* Identifier letter class extended to match syfco's
   * (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Data.hs):
   *   identStart     = letter <|> char '_' <|> char '@'
   *   identLetter    = alphaNum <|> char '_' <|> char '@' <|> char '\''
   * The leading char class is [a-zA-Z_@] (apostrophe not allowed
   * to start an identifier); the rest of the identifier can
   * include apostrophes (o'biter, in'bit).  None of Spot's
   * reserved keywords (TITLE:, MAIN, GLOBAL, Mealy, Moore, G,
   * F, X, ...) start with @, so this extension introduces no
   * token-rule conflicts.  See also the lexer header comment
   * above for the M case, which is NOT a token here either for
   * parallel reasons.  Indented block comment (2 spaces)
   * because Flex does not accept // line comments in the rules
   * section. */
[a-zA-Z_@][a-zA-Z0-9_@']* {
                        yylval->emplace<std::string>(yytext, yyleng);
                        return token::IDENTIFIER;
                      }

[0-9]+                {
                        yylval->emplace<std::string>(yytext, yyleng);
                        return token::NUMBER;
                      }

.                     {
                        char buf[2] = { yytext[0], 0 };
                        std::string msg = "unexpected character '";
                        msg += buf;
                        msg += '\'';
                        yyextra->errors.emplace_back(*yylloc, msg);
                      }

%%

namespace spot
{
  int
  tlsfyyopen(const std::string& name, yyscan_t* scanner,
             spot::tlsf_result& res)
  {
    if (yylex_init_extra(&res, scanner))
      return 1;
    yyscan_t yyscanner = *scanner;
    struct yyguts_t* yyg = (struct yyguts_t*)yyscanner;
    BEGIN(INITIAL);
    yyin = fopen(name.c_str(), "r");
    if (!yyin)
      {
        yylex_destroy(yyscanner);
        *scanner = nullptr;
        return 1;
      }
    res.close_yyin = true;
    return 0;
  }

  int
  tlsfyyopen(int fd, yyscan_t* scanner, spot::tlsf_result& res)
  {
    if (yylex_init_extra(&res, scanner))
      return 1;
    yyscan_t yyscanner = *scanner;
    struct yyguts_t* yyg = (struct yyguts_t*)yyscanner;
    BEGIN(INITIAL);
    yyin = fdopen(fd, "r");
    if (!yyin)
      {
        yylex_destroy(yyscanner);
        *scanner = nullptr;
        return 1;
      }
    res.close_yyin = false;
    return 0;
  }

  void
  tlsfyyclose(yyscan_t scanner)
  {
    struct yyguts_t* yyg = (struct yyguts_t*)scanner;
    if (yyin && yyextra->close_yyin)
      {
        fclose(yyin);
        yyin = nullptr;
      }
    yylex_destroy(scanner);
  }

  void
  tlsfyyreset(yyscan_t scanner)
  {
    struct yyguts_t* yyg = (struct yyguts_t*)scanner;
    BEGIN(INITIAL);
  }
}
