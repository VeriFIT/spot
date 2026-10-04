/* -*- coding: utf-8 -*- */
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
 */

%option noyywrap
%option reentrant
%option extra-type="spot::tlsf_result*"
%option prefix="tlsfyy"

%top{
#include "libc-config.h"
/* Flex 2.6.4's test for <inttypes.h> relies on __STDC_VERSION__
   which is undefined in C++.   So without that, it will define
   its own integer types, including a broken SIZE_MAX definition that
   breaks compilation on OpenBSD. So let's define __STDC_VERSION__ to
   make sure <inttypes.h> gets included.  Redefining __STDC_VERSION__
   this way can break all sort of macros defined in <cdefs.h>, so
   we include "libc-config.h" instead of "config.h" above to define
   those macros first. */
#if HAVE_INTTYPES_H && !(defined __STDC_VERSION__)
#  define __STDC_VERSION__ 199901L
#endif
}
%{
#include <spot/misc/location.hh>
#include <spot/parsetlsf/public.hh>
#include <string>
#include "parsedecl.hh"
#include <spot/parsetlsf/parsetlsf.hh>

#define YY_USER_ACTION yylloc->columns(yyleng);

typedef tlsfyy::parser::token token;

/* TLSF's list of words is a scanner convention, not a reservation:
   syfco lets a file call an enumeration `U`, name a tag `U`, or name
   a parameter `U`, and then resolves that word in expressions like any
   other identifier.  So when the file itself declared the current word
   as an enum name, tag, parameter name, definition name, definition
   argument, or input/output signal name, that declaration wins -- but
   only where the word's own syntactic trigger is absent, so that a
   file which both declares a tag named `U` and writes `a U b` keeps
   working.  Words with no trigger a scanner can see (`G`, `F`, `X`,
   `NOT`, `SIZEOF`, `true`, `false`, and the section keywords) are
   never tested and stay reserved; see the declared_words comment in
   spot/parsetlsf/parsetlsf.yy.

   Only a handful of words is ever recorded, and this runs once per
   keyword, so a plain lookup is enough. */
static inline bool
declared_word(const spot::tlsf_result* res, const char* s, size_t n)
{
  return res->declared_words.count(std::string(s, n)) != 0;
}

/* Return \a tok, which cannot end an expression.  Every rule of this
   scanner says which of the two it is, because the ENUM_WORD_INFIX
   guard below needs that one token of left context to tell the infix
   reading of a word this file declared (`a U b`) from its identifier
   reading (`b == U`).  Every rule also clears the `await_decl` flag
   set by the PARAMETERS and DEFINITIONS keyword rules, so that those
   rules cannot latch onto a `{` that is not theirs in a malformed
   file; only whitespace and comments keep the flag across the keyword
   to its brace. */
#define RET(tok)    { yyextra->prev_ends_expr = false;                \
                       yyextra->await_decl = false; return (tok); }

/* Return \a tok, which can end an expression. */
#define RET_EXPR(tok)  { yyextra->prev_ends_expr = true;              \
                         yyextra->await_decl = false; return (tok); }

/* Return a section keyword that the `{` of its section follows.
   Sets the `await_decl` flag to the kind of the following block:
   1 for a PARAMETERS or DEFINITIONS block, whose items are read in the
   declhead condition, and 2 for an INPUTS or OUTPUTS block, whose
   items are read in the signalhead condition.  The `{` rule reads the
   flag and pushes it on `brace_is_decl`.  See RET. */
#define RET_AWAIT(tok) { yyextra->prev_ends_expr = false;             \
                         yyextra->await_decl = 1; return (tok); }

#define RET_AWAIT_SIG(tok) { yyextra->prev_ends_expr = false;         \
                             yyextra->await_decl = 2; return (tok); }

/* A `}` closes the section whose `{` pushed onto `brace_is_decl`, so
   every rule that returns a RBRACE -- the shared one, and the ones of
   the enumdecl, taglist, declhead, and declhead2 start conditions --
   pops the stack, keeping it in step with the block nesting. */
#define POP_BRACE()  if (!yyextra->brace_is_decl.empty())             \
                       yyextra->brace_is_decl.pop_back();

/* The `;` that ends a def_list item delivers the item that follows it,
   so when the item sits in a PARAMETERS or DEFINITIONS block (the
   innermost open brace says so, with kind 1) the scanner is handed to
   the declhead start condition, where the next token is read as the
   name of a parameter or a definition.  The rule that ends an enum
   body is another item end and does the same.  Inside an INPUTS or
   OUTPUTS block (kind 2) the same `;` hands the scanner to the
   signalhead condition, where the next token is read as the name of a
   signal. */
#define AFTER_ITEM_END() \
  if (!yyextra->brace_is_decl.empty())                            \
    {                                                             \
      if (yyextra->brace_is_decl.back() == 1)                     \
        BEGIN(declhead);                                          \
      else if (yyextra->brace_is_decl.back() == 2)                \
        BEGIN(signalhead);                                        \
    }

/* Return IDENTIFIER for a word the file declared, \a tok otherwise.
   Used for a word whose only other reading is a call or a bracket, so
   that a trigger rule has already decided this word is not that.  Each
   arm says whether the token it returns ends an expression: the
   identifier does, and the keyword does not. */
#define ENUM_WORD(tok)                                               \
  if (declared_word(yyextra, yytext, yyleng))                        \
    {                                                               \
      yylval->emplace<std::string>(yytext, yyleng);                 \
      yyextra->prev_ends_expr = true;                                \
      yyextra->await_decl = false;                                   \
      return token::IDENTIFIER;                                      \
    }                                                               \
  else                                                              \
    { yyextra->prev_ends_expr = false; yyextra->await_decl = false;  \
      return (tok); }

/* Same, but only when the word cannot be an infix operator here: when
   the previous token ends an expression, a declared word after it is
   the operator (`a U b` rather than `b == U`). */
#define ENUM_WORD_INFIX(tok)                                          \
  if (declared_word(yyextra, yytext, yyleng)                         \
      && !yyextra->prev_ends_expr)                                   \
    {                                                               \
      yylval->emplace<std::string>(yytext, yyleng);                 \
      yyextra->prev_ends_expr = true;                                \
      yyextra->await_decl = false;                                   \
      return token::IDENTIFIER;                                      \
    }                                                               \
  else                                                              \
    { yyextra->prev_ends_expr = false; yyextra->await_decl = false;  \
      return (tok); }

 /* Same, for a word whose keyword reading also hands the scanner to
  * another start condition: \a state.  Only the `enum` keyword needs
  * this.  */
 #define ENUM_WORD_STATE(tok, state)                                \
  if (declared_word(yyextra, yytext, yyleng))                        \
    {                                                               \
      yylval->emplace<std::string>(yytext, yyleng);                 \
      yyextra->prev_ends_expr = true;                                \
      yyextra->await_decl = false;                                   \
      return token::IDENTIFIER;                                      \
    }                                                               \
  else                                                              \
    { yyextra->prev_ends_expr = false; yyextra->await_decl = false;  \
      BEGIN(state); return (tok); }

 /* Enter a block comment from whichever start condition is current.
  * The body of the comment is scanned by the in_COMMENT state below,
  * which counts the nesting level (TLSF v1.2 SS4.9) and restores
  * `orig_cond` once the outermost comment closes.
  *
  * Neither `await_decl` nor `prev_ends_expr` is touched here, and
  * neither is touched by the rules that skip a comment's contents: a
  * comment is transparent, so it neither separates a section keyword
  * from its brace nor an operand from the operator that follows it.
  * This is also why every rule that opens a comment just calls this
  * macro: the flag that the keyword's trailing context could not set
  * through a comment with nested comments in it is set by the bare
  * keyword rule instead, see ENUM_WORD_AWAIT below.  */
#define BEGIN_COMMENT()                          \
  yyextra->orig_cond = YY_START;                 \
  BEGIN(in_COMMENT);                             \
  yyextra->comment_level = 1;

 /* Same as ENUM_WORD, but the keyword also flags the brace that may
  * follow it, with the kind RET_AWAIT and RET_AWAIT_SIG use.  Only the
  * bare PARAMETERS, DEFINITIONS, INPUTS and OUTPUTS rules need this:
  * they are the rules that fire when the keyword's trailing context
  * did not match, and TLSF_ENUM_SEP being a regular expression, the
  * one separator it cannot express is a comment that nests.  The flag
  * is cleared again by the next token of any kind, exactly as ENUM_WORD
  * clears it, so a keyword that a malformed file leaves unmatched by
  * its brace still cannot latch onto a later one.  */
#define ENUM_WORD_AWAIT(tok, kind)                                    \
  if (declared_word(yyextra, yytext, yyleng))                         \
    {                                                               \
      yylval->emplace<std::string>(yytext, yyleng);                 \
      yyextra->prev_ends_expr = true;                                \
      yyextra->await_decl = false;                                   \
      return token::IDENTIFIER;                                      \
    }                                                               \
  else                                                              \
    { yyextra->prev_ends_expr = false; yyextra->await_decl = (kind);  \
      return (tok); }

%}

%x str
%x in_COMMENT
%x enumname
%x enumdecl
%x taglist
%x semval
%x declhead
%x declhead2
%x arglist
%x signalhead
%x signalafter

  /* What may separate an identifier inside an enum body from the
   * token that tells us whether the identifier belongs to the enum:
   * whitespace and comments, as everywhere else in this scanner.
   *
   * A regular expression cannot count nesting, so the block comment
   * this accepts has to be flat: it is the separator of the section
   * keywords' trailing contexts, and a comment that nests one is
   * simply not part of the trailing context.  Such a keyword still
   * comes back as the keyword, because its bare rule sets the same
   * flag the trailing context rule does; see ENUM_WORD_AWAIT.  */
TLSF_ENUM_SEP  ([ \t\f\r\n]|"//"[^\n]*|"/*"([^*]|\*+[^*/])*\*+"/")*

%%

%{
  // Accumulator for the multi-line STRING token (see the str start
  // condition below).  Declared here so it lives in yylex's frame;
  // the whole string is consumed within one yylex() call because
  // every str-state rule except the closing quote falls through, so
  // the per-call initialisation is harmless.
  std::string s;
%}

[ \t\f]+              yylloc->step();
[\n]+                 yylloc->lines(yyleng); yylloc->step();
[\r\n]+               yylloc->lines(yyleng / 2); yylloc->step();

"//"[^\n]*            yylloc->step();
  /* A C-style block comment, but with proper nesting support.  */
"/*"                  BEGIN_COMMENT();

  /* Section keywords.  A file may still call a signal, a tag, a
   * parameter or a definition by one of these names -- syfco resolves
   * it like any other identifier -- so the `{` that opens the section
   * is what tells the two readings apart.  The trailing context does
   * not consume that brace: flex backs up, so it is returned as a
   * LBRACE of its own, and the rule that returns it still sees the
   * await_decl flag of the keyword.  Any other token clears that flag
   * (see RET), so a keyword that a malformed file leaves unmatched by
   * its brace cannot latch onto a later one, and a name spelled like a
   * keyword is a name everywhere the brace does not follow. */
"INFO"/{TLSF_ENUM_SEP}\{        RET(token::INFO);
"MAIN"/{TLSF_ENUM_SEP}\{        RET(token::MAIN);
"GLOBAL"/{TLSF_ENUM_SEP}\{      RET(token::GLOBAL);
  /* The brace that follows one of these two keywords opens a block of
   * declarations, so the keyword flags it for the `{` rule (RET_AWAIT
   * sets `await_decl`) and the items inside yield their names to the
   * declhead start condition; see the rules at the end of this
   * section. */
"PARAMETERS"/{TLSF_ENUM_SEP}\{  RET_AWAIT(token::PARAMETERS);
"DEFINITIONS"/{TLSF_ENUM_SEP}\{ RET_AWAIT(token::DEFINITIONS);
  /* `enum` keyword accepted as a def_list item
   * INSIDE the GLOBAL { DEFINITIONS { ... } } block.
   * Seeing `enum` switches the lexer to the
   * `enumname` start condition, which recognises the enumeration's
   * name and hands over to the `enumdecl` start condition so tags
   * lex as plain identifiers: a tag spelled like an LTL operator
   * (the `U` in `U: 11*, 1*1, *11` from
   * the TLSF spec itself) must not be mangled into an operator
   * token.  The name and every tag are recorded in `res.declared_words`,
   * so that they are also read as identifiers where they are used
   * outside this declaration, as syfco does.  The keyword has no
   * trigger a scanner could use, so it is one of the two words the
   * declared_word() test of ENUM_WORD_STATE is applied to directly. */
"enum"                ENUM_WORD_STATE(token::ENUM, enumname);
"INPUTS"/{TLSF_ENUM_SEP}\{      RET_AWAIT_SIG(token::INPUTS);
"OUTPUTS"/{TLSF_ENUM_SEP}\{     RET_AWAIT_SIG(token::OUTPUTS);
"INITIALLY"/{TLSF_ENUM_SEP}\{   RET(token::INITIALLY);
"PRESET"/{TLSF_ENUM_SEP}\{      RET(token::PRESET);
  /* Plural forms for REQUIRE/ASSERT/GUARANTEE/ASSUME recognised
   * by TLSF v1.1 as aliases of the singular keywords, mapped to
   * the same body field.  ASSUME + ASSUMPTIONS introduce a new
   * "assumptions" body that Spot previously had no slot for;
   * both fields are now first-class. */
"REQUIRE"/{TLSF_ENUM_SEP}\{      RET(token::REQUIRE);
"REQUIREMENTS"/{TLSF_ENUM_SEP}\{ RET(token::REQUIREMENTS);
"ASSERT"/{TLSF_ENUM_SEP}\{       RET(token::ASSERT);
"INVARIANTS"/{TLSF_ENUM_SEP}\{   RET(token::INVARIANTS);
"GUARANTEE"/{TLSF_ENUM_SEP}\{    RET(token::GUARANTEE);
"GUARANTEES"/{TLSF_ENUM_SEP}\{   RET(token::GUARANTEES);
"ASSUME"/{TLSF_ENUM_SEP}\{       RET(token::ASSUME);
"ASSUMPTIONS"/{TLSF_ENUM_SEP}\{  RET(token::ASSUMPTIONS);
  /* Away from the brace of its section a section keyword is the name
   * the file declares, and the keyword when it declares none: a bare
   * `GLOBAL` is still the keyword, so a malformed file is diagnosed
   * where it was before.
   *
   * The four keywords whose brace opens a block of declarations flag
   * that brace here as well as in the rule above, because this is the
   * rule that fires when a comment with nested comments separated the
   * keyword from its brace, which the trailing context above cannot
   * match.  A comment leaves the flag alone, so it survives the
   * comment; see ENUM_WORD_AWAIT. */
"INFO"               ENUM_WORD(token::INFO);
"MAIN"               ENUM_WORD(token::MAIN);
"GLOBAL"             ENUM_WORD(token::GLOBAL);
"PARAMETERS"         ENUM_WORD_AWAIT(token::PARAMETERS, 1);
"DEFINITIONS"        ENUM_WORD_AWAIT(token::DEFINITIONS, 1);
"INPUTS"             ENUM_WORD_AWAIT(token::INPUTS, 2);
"OUTPUTS"            ENUM_WORD_AWAIT(token::OUTPUTS, 2);
"INITIALLY"          ENUM_WORD(token::INITIALLY);
"PRESET"             ENUM_WORD(token::PRESET);
"REQUIRE"            ENUM_WORD(token::REQUIRE);
"REQUIREMENTS"       ENUM_WORD(token::REQUIREMENTS);
"ASSERT"             ENUM_WORD(token::ASSERT);
"INVARIANTS"         ENUM_WORD(token::INVARIANTS);
"GUARANTEE"          ENUM_WORD(token::GUARANTEE);
"GUARANTEES"         ENUM_WORD(token::GUARANTEES);
"ASSUME"             ENUM_WORD(token::ASSUME);
"ASSUMPTIONS"        ENUM_WORD(token::ASSUMPTIONS);
"TITLE:"              RET(token::TITLE);
"DESCRIPTION:"        RET(token::DESCRIPTION);
  /* The value of a SEMANTICS: or a TARGET: item is one of `Mealy`,
   * `Moore`, `Strict` and `Finite`, but a declared name may be spelled
   * like any of them and nothing here tells the two apart, the value
   * being a bare word.  The keyword that introduces the value does
   * tell them, so the scanner reads the value in the semval start
   * condition, where these four words are the only keywords.  The
   * rules there are what recognize them: elsewhere these are
   * keywords as well, and ENUM_WORD makes them declared names. */
"SEMANTICS:"          { BEGIN(semval); RET(token::SEMANTICS_KW); }
"TARGET:"             { BEGIN(semval); RET(token::TARGET); }
"TAGS:"               { BEGIN(taglist); RET(token::TAGS); }
"Mealy"               ENUM_WORD(token::MEALY);
"Moore"               ENUM_WORD(token::MOORE);
"Strict"              ENUM_WORD(token::STRICT);
"Finite"              ENUM_WORD(token::FINITE);
  /* `G`, `F` and `X` are prefix operators whose operand needs no
   * bracket, so no trigger tells them from an identifier and a tag
   * spelled like one of them stays reserved; `U`, `R` and `W` are
   * purely infix, and the token that precedes one tells the two
   * readings apart. */
"G"                   RET(token::LTL_G);
"F"                   RET(token::LTL_F);
"X"                   RET(token::LTL_X);
"U"                   ENUM_WORD_INFIX(token::LTL_U);
"R"                   ENUM_WORD_INFIX(token::LTL_R);
"W"                   ENUM_WORD_INFIX(token::LTL_W);
"X[!]"                RET(token::LTL_STRONG_NEXT);
  /* `true` and `false` have no trigger either -- syfco keeps them
   * reserved too, so a tag spelled like one of them is unusable. */
"true"                RET_EXPR(token::BOOL_TRUE);
"false"               RET_EXPR(token::BOOL_FALSE);

"IN"                  ENUM_WORD_INFIX(token::IN);
  /* `NOT` is a prefix operator with no trigger, like `G` above. */
"NOT"                 RET(token::KW_NOT);
  /* `AND[i, j] f` and `OR[i, j] f` bind a cardinality, so a declared
   * word followed by `[` is the operator even though it would
   * otherwise read as the infix one.  The trailing context is not
   * consumed: flex backs up so that the `[` is returned as a
   * LBRACKET of its own. */
"AND"/{TLSF_ENUM_SEP}\[  RET(token::KW_AND);
"OR"/{TLSF_ENUM_SEP}\[   RET(token::KW_OR);
"AND"                 ENUM_WORD_INFIX(token::KW_AND);
"OR"                  ENUM_WORD_INFIX(token::KW_OR);
"IMPLIES"             ENUM_WORD_INFIX(token::KW_IMPLIES);
"EQUIV"               ENUM_WORD_INFIX(token::KW_EQUIV);
"EQ"                  ENUM_WORD_INFIX(token::KW_EQ);
"NEQ"                 ENUM_WORD_INFIX(token::KW_NEQ);
"LE"                  ENUM_WORD_INFIX(token::KW_LE);
"GE"                  ENUM_WORD_INFIX(token::KW_GE);
"LEQ"                 ENUM_WORD_INFIX(token::KW_LEQ);
"GEQ"                 ENUM_WORD_INFIX(token::KW_GEQ);
"ELEM"                ENUM_WORD_INFIX(token::KW_ELEM);
  /* `FORALL[i, j]` and `EXISTS[i, j]` are the only reading of these
   * two words, so `[` is their whole trigger. */
"FORALL"/{TLSF_ENUM_SEP}\[  RET(token::KW_FORALL);
"EXISTS"/{TLSF_ENUM_SEP}\[  RET(token::KW_EXISTS);
"FORALL"              ENUM_WORD(token::KW_FORALL);
"EXISTS"              ENUM_WORD(token::KW_EXISTS);
"CUP"/{TLSF_ENUM_SEP}\[  RET(token::SET_CUP);
"CAP"/{TLSF_ENUM_SEP}\[  RET(token::SET_CAP);
"SETMINUS"/{TLSF_ENUM_SEP}\[  RET(token::SET_MINUS);
"CUP"                 ENUM_WORD_INFIX(token::SET_CUP);
"CAP"                 ENUM_WORD_INFIX(token::SET_CAP);
"SETMINUS"            ENUM_WORD_INFIX(token::SET_MINUS);
  /* The set big operators `(+)[b] eSX` and `(*)[b] eSX` (TLSF v1.2
   * Table 1, precedence 5) are parenthesised operator words followed by
   * a binder list, so `[` is their whole trigger.  Without the trigger
   * they would shadow the parenthesised infix forms `(+)` and `(*)`,
   * which the surrounding parentheses already delimit; that is why the
   * `(+) (CAP)` infix spelling is deliberately not matched here.
   * `(-)[b] eSX` is not in TLSF v1.2 -- that table has `(-)`, `(\)`,
   * and `SETMINUS` only as binary right-to-left difference -- but it
   * fits the family and completes it, so it is accepted and documented
   * as a Spot extension. */
"(+)"/{TLSF_ENUM_SEP}\[  RET(token::BIG_SET_UNION);
"(*)"/{TLSF_ENUM_SEP}\[  RET(token::BIG_SET_INTER);
"(-)"/{TLSF_ENUM_SEP}\[  RET(token::BIG_SET_DIFF);
"PLUS"                ENUM_WORD_INFIX(token::KW_PLUS);
"MINUS"               ENUM_WORD_INFIX(token::KW_MINUS);
"MUL"                 ENUM_WORD_INFIX(token::KW_MUL);
"DIV"                 ENUM_WORD_INFIX(token::KW_DIV);
"MOD"                 ENUM_WORD_INFIX(token::KW_MOD);

  /* `MIN(..)` and `MAX(..)` need their parenthesis, so `(` is their
   * whole trigger and they get a token of their own: `MIN`/`MAX` on
   * their own are the prefix operators `MIN eSX` / `MAX eSX`, and a
   * single token cannot be both (otherwise `MIN(1)` would come back
   * through the deparser as the prefix `MIN (1)`, and a print/parse
   * round-trip would no longer be the identity).  `SUM`/`PROD` have no
   * prefix reading, so `(` stays their whole trigger and they need no
   * second token. */
"MIN"/{TLSF_ENUM_SEP}\(  RET(token::FN_MIN_CALL);
"MAX"/{TLSF_ENUM_SEP}\(  RET(token::FN_MAX_CALL);
"SUM"/{TLSF_ENUM_SEP}\(  RET(token::FN_SUM);
"PROD"/{TLSF_ENUM_SEP}\(  RET(token::FN_PROD);
  /* The numeric big operators `+[b] eN` and `*[b] eN` (TLSF v1.2
   * Table 1, precedence 1, the tightest tier) and their `SUM[`/`PROD[`
   * spellings are prefix operators whose argument is a binder list, so
   * `[` is their whole trigger.  `+` and `*` alone keep their infix
   * readings: the `[` has to follow immediately, and an operand cannot
   * start with `[` in TLSF, so `a + b` and `a * b` are unaffected. */
"+"/{TLSF_ENUM_SEP}\[    RET(token::BIG_SUM);
"*"/{TLSF_ENUM_SEP}\[    RET(token::BIG_PROD);
"SUM"/{TLSF_ENUM_SEP}\[  RET(token::BIG_SUM_LONG);
"PROD"/{TLSF_ENUM_SEP}\[ RET(token::BIG_PROD_LONG);
"MIN"                 ENUM_WORD(token::FN_MIN);
"MAX"                 ENUM_WORD(token::FN_MAX);
"SUM"                 ENUM_WORD(token::FN_SUM);
"PROD"                ENUM_WORD(token::FN_PROD);
  /* `SIZEOF` takes a bare expression, so like `NOT` it has no trigger
   * and stays reserved.  `SIZE eSX` does too: syfco reserves both. */
"SIZEOF"              RET(token::FN_SIZEOF);
"SIZE"                RET(token::FN_SIZE);

"&&"                  RET(token::AND);
"||"                  RET(token::OR);
"->"                  RET(token::IMPLIES);
"<->"                 RET(token::EQUIV);
  /* `~` is the pattern-match operator (TLSF v1.2 SS4.6).  It is lexed
   * here like any other binary operator, with no trailing context: a
   * `~` is always the operator, and whether what follows it is a legal
   * pattern is decided by the grammar (see check_pattern). */
"~"                   RET(token::TILDE);
"=="                  RET(token::EQ);
"!="                  RET(token::NEQ);
"<="                  RET(token::LE);
">="                  RET(token::GE);
"<-"                  RET(token::IN);
"<"                   RET(token::LT);
">"                   RET(token::GT);
"+"                   RET(token::PLUS);
"-"                   RET(token::MINUS_);
"*"                   RET(token::STAR);
"/"                   RET(token::SLASH);
"%"                   RET(token::PERCENT);
"!"                   RET(token::BANG);
"|"                   RET(token::BAR);
"[!"                  RET(token::LBRACKET_BANG);
"!]"                  RET_EXPR(token::BANG_RBRACKET);
".."                  RET(token::DOTDOT);
"{"                   {
                        /* A brace opens a block whose kind depends on
                         * the keyword that introduced it: PARAMETERS
                         * and DEFINITIONS set await_decl to 1, INPUTS
                         * and OUTPUTS to 2.  The entry pushed on
                         * brace_is_decl is what the `;` and `}` rules
                         * need to know which blocks contain
                         * declarations, and a nonzero entry means the
                         * next token is a name, read in declhead (say)
                         * or in signalhead. */
                        yyextra->brace_is_decl.push_back(
                          yyextra->await_decl);
                        yyextra->await_decl = 0;
                        if (yyextra->brace_is_decl.back() == 1)
                          BEGIN(declhead);
                        else if (yyextra->brace_is_decl.back() == 2)
                          BEGIN(signalhead);
                        RET(token::LBRACE);
                      }
"}"                   {
                        POP_BRACE();
                        RET_EXPR(token::RBRACE);
                      }
";"                   {
                        AFTER_ITEM_END();
                        RET(token::SEMICOLON);
                      }
","                   RET(token::COMMA);
"="                   RET(token::EQUAL);
":"                   RET(token::COLON);
"["                   RET(token::LBRACKET);
"]"                   RET_EXPR(token::RBRACKET);
"("                   RET(token::LPAREN);
")"                   RET_EXPR(token::RPAREN);

  /* String literal (INFO TITLE/DESCRIPTION/TAGS).  The string may
   * span several lines (real benchmarks such as tictactoe_1.tlsf
   * carry a whole prose paragraph inside DESCRIPTION), `\"` is an
   * escaped quote and `\\` an escaped backslash. */
\"                        { BEGIN(str); s.clear(); }
<str>\"                   {
                            BEGIN(INITIAL);
                            yylval->emplace<std::string>(s);
                            RET_EXPR(token::STRING);
                          }
<str>\\.                {
                            if (yytext[1] == '\"' || yytext[1] == '\\')
                              s += yytext[1];
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
                            RET_EXPR(token::STRING);
                          }

  /* `_` is the pattern wildcard (TLSF v1.2 SS4.6).  It is a reserved
     * word here, as it is in syfco, so the rule has to precede the
     * identifier rule below: flex breaks a tie between two rules of
     * equal length in favour of the earlier one, and `_` matches both of
     * length one.  A name that merely STARTS with an underscore is not
     * affected -- the identifier class matches it in more characters, and
     * flex prefers the longer match -- so `x_1` and `_foo` are still
     * identifiers.
     *
     * The rule is deliberately absent from every start condition that
     * reads a NAME (declhead, declhead2, arglist, signalhead,
     * signalafter, enumname, enumdecl, taglist), each of which spells out
     * its own identifier class: there `_` is still a name, so a
     * parameter, formal argument, signal or enum tag spelled `_` keeps
     * working.  Only the expression position, where this rule is live,
     * reserves the word. */
"_"                   RET_EXPR(token::WILDCARD);

[a-zA-Z_@][a-zA-Z0-9_@']* {
                        yylval->emplace<std::string>(yytext, yyleng);
                        RET_EXPR(token::IDENTIFIER);
                      }

[0-9]+                {
                        yylval->emplace<std::string>(yytext, yyleng);
                        RET_EXPR(token::NUMBER);
                      }

  /* --- enum name (enumname start condition) ---
   * Entered by the `enum` rule above.  Exactly one token belongs to
   * this state: the enumeration's name, an identifier followed by the
   * `=` that introduces the entry list.  */
  <enumname>[ \t\f]+     yylloc->step();
  <enumname>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <enumname>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <enumname>"//"[^\n]*   yylloc->step();
  <enumname>"/*"         BEGIN_COMMENT();
  <enumname>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->declared_words.insert(yylval->as<std::string>());
                          BEGIN(enumdecl);
                          RET(token::IDENTIFIER);
                        }
  <enumname>.            { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- enum-declaration content (enumdecl start condition) ---
   * Entered once the enumeration's name has been scanned, left as
   * soon as the enum body is over.  The rules mirror the shared ones
   * (whitespace, comments, identifiers, comma, colon, equal) with one
   * deliberate difference: NO keyword is recognized, so a tag spelled
   * G, F, U, X, AND, ... lexes as an identifier (the canonical TLSF
   * example even uses a tag named UNDEF).  A tag is returned as
   * ENUM_TAG rather than as an ordinary IDENTIFIER, so that the
   * grammar can tell "another entry of this enum" from "the head of
   * the next def_list item" without a shift/reduce conflict; it is
   * also recorded in `res.declared_words`, so that a tag spelled like a
   * word of the language is usable as an identifier in expressions.
   * Bit patterns are lexed as maximal runs (see the `[01*]+` rule
   * below), and numbers and stars are not tokens of their own here.
   * The body is over at the `;` that terminates the def_list item,
   * at the `}` that closes the enclosing block, and at any identifier
   * that is not a tag (i.e. one that is not followed by the `:` that
   * introduces one); that last case is a syntax error, since the `;`
   * separating two def_list items is mandatory, but the rest of the
   * item is still lexed (and diagnosed) in the normal state. */
  <enumdecl>[ \t\f]+     yylloc->step();
  <enumdecl>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <enumdecl>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <enumdecl>"//"[^\n]*   yylloc->step();
  <enumdecl>"/*"         BEGIN_COMMENT();
  /* disallow "enum" as a tag, to catch two enum declaration not
     separated by ';' */
  <enumdecl>"enum"        { BEGIN(enumname); RET(token::ENUM); }
   /* The `;` of a def_list item and the `}` that closes the
    * enclosing block both end the enum body, and the `;` is optional
    * when the enum is the last item of the block: the enum grammar of
    * TLSF v1.2 SS4.4 has no terminator, and the example of the paper
    * relies on this.   */
  <enumdecl>";"          { BEGIN(INITIAL); AFTER_ITEM_END();
                           RET(token::SEMICOLON); }
  <enumdecl>"}"          { POP_BRACE();
                           BEGIN(INITIAL); RET_EXPR(token::RBRACE); }
  <enumdecl>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->declared_words.insert(yylval->as<std::string>());
                          RET(token::ENUM_TAG);
                        }
  <enumdecl>[01*]+      {
                          yylval->emplace<std::string>(yytext, yyleng);
                          RET(token::BITS);
                        }

  <enumdecl>","          RET(token::COMMA);
  <enumdecl>":"          RET(token::COLON);
  <enumdecl>"="          RET(token::EQUAL);
  <enumdecl>.            {
                           BEGIN(INITIAL);
                           AFTER_ITEM_END();
                           yylloc->columns(-1);
                           yyless(0);
                         }


  /* --- INFO tag list (taglist start condition) ---
   * Entered by `TAGS:` and left as soon as the list is over.  The list
   * is a comma-separated sequence of identifiers without reserved keywords.
   *
   * The `TAGS:` list ends on '}' or on `TITLE: `/` DESCRIPTION:` etc.
   *
   * A second `TAGS:` goes back to the parser as a TAGS token so that
   * note_info_item still diagnoses the duplicate. */
  <taglist>"TITLE:"       { BEGIN(INITIAL); RET(token::TITLE); }
  <taglist>"DESCRIPTION:" { BEGIN(INITIAL); RET(token::DESCRIPTION); }
  <taglist>"SEMANTICS:"   { BEGIN(INITIAL); RET(token::SEMANTICS_KW); }
  <taglist>"TARGET:"      { BEGIN(INITIAL); RET(token::TARGET); }
  <taglist>"TAGS:"        { BEGIN(INITIAL); RET(token::TAGS); }
  <taglist>"}"            { POP_BRACE();
                            BEGIN(INITIAL); RET_EXPR(token::RBRACE); }
  <taglist>[ \t\f]+     yylloc->step();
  <taglist>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <taglist>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <taglist>"//"[^\n]*   yylloc->step();
  <taglist>"/*"         BEGIN_COMMENT();

   /* The tags.  The identifier class is spelled out rather than shared
    * with the INITIAL-state rule above, for the reason given there: a
    * pattern that is used both with and without a trailing context
    * makes flex mis-compile one of the two. */
  <taglist>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          RET_EXPR(token::IDENTIFIER);
                        }

  <taglist>","          RET(token::COMMA);
  <taglist>.            { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- SEMANTICS/TARGET value (semval start condition) ---
   * Entered by the SEMANTICS: and TARGET: rules above, and left as soon
   * as the value is over.  Its whole purpose is to keep the four words
   * a value may be made of out of reach of the names that may precede
   * it: `Mealy` there is the keyword, and a signal, tag or parameter
   * named `Mealy` is that name anywhere else.  Nothing but those four
   * words is a keyword here, and whatever else the value is made of is
   * handed back to the initial condition to be scanned as usual: a
   * `}` closes the INFO block, a `;` ends the item, and a word this
   * file declared is still that word (the catch-all rule below undoes
   * the column advance and pushes the character back, which is what
   * the other start conditions of this scanner do as well). */
  <semval>[ \t\f]+     yylloc->step();
  <semval>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <semval>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <semval>"//"[^\n]*   yylloc->step();
  <semval>"/*"         BEGIN_COMMENT();
  <semval>"Mealy"       { BEGIN(INITIAL); RET(token::MEALY); }
  <semval>"Moore"       { BEGIN(INITIAL); RET(token::MOORE); }
  <semval>"Strict"      { BEGIN(INITIAL); RET(token::STRICT); }
  <semval>"Finite"      { BEGIN(INITIAL); RET(token::FINITE); }
  <semval>.            { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

   /* --- declaration name (declhead start condition) ---
   * Entered by the `{` rule when the brace opens a PARAMETERS or
   * DEFINITIONS block, and by the `;` rule (and the rule that ends an
   * enum body) afterwards, so that the FIRST token of each item of
   * such a block is read here.  That token is the name of a parameter
   * or of a definition, and it is recorded in `res.declared_words`,
   * exactly as the `enumname` and `enumdecl` conditions record enum
   * names and tags, so that a name spelled like any word of the
   * language is usable as an identifier outside its declaration.  No
   * keyword is recognized here, for the same reason: `AND = 2;` names
   * a parameter AND and must not read `AND` as the conjunction word.
   *
   * The name is followed by `=` (a parameter or a parameter-less
   * definition) or by `(` (a definition with arguments); both are
   * handled by the declhead2 condition, which the name rule enters, so
   * no flex trailing context is needed.  The definition arguments are
   * then read by the arglist condition, where they too are recorded
   * (a formal may be spelled like any word of the language).  */
  <declhead>[ \t\f]+     yylloc->step();
  <declhead>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <declhead>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <declhead>"//"[^\n]*   yylloc->step();
  <declhead>"/*"         BEGIN_COMMENT();

  <declhead>"enum"        { BEGIN(enumname); RET(token::ENUM); }

  <declhead>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->declared_words.insert(
                            yylval->as<std::string>());
                          BEGIN(declhead2);
                          RET_EXPR(token::IDENTIFIER);
                        }

  <declhead>"}"           {
                          POP_BRACE();
                          BEGIN(INITIAL); RET_EXPR(token::RBRACE);
                        }
  <declhead>.             { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- declaration name tail ---
   * Entered by the declhead name rule.  The `=` that makes the name a
   * parameter or a parameter-less definition, the `(` that starts a
   * definition's argument list, and the `}` that ends an empty block
   * are the only continuations a declaration allows. */
  <declhead2>[ \t\f]+     yylloc->step();
  <declhead2>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <declhead2>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <declhead2>"//"[^\n]*   yylloc->step();
  <declhead2>"/*"         BEGIN_COMMENT();

  <declhead2>"="        { BEGIN(INITIAL); RET(token::EQUAL); }
  <declhead2>"("        { BEGIN(arglist); RET(token::LPAREN); }

  <declhead2>"}"        {
                          POP_BRACE();
                          BEGIN(INITIAL); RET_EXPR(token::RBRACE);
                        }

  <declhead2>.          { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- definition arguments --- */
  <arglist>[ \t\f]+     yylloc->step();
  <arglist>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <arglist>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <arglist>"//"[^\n]*   yylloc->step();
  <arglist>"/*"         BEGIN_COMMENT();

  <arglist>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->declared_words.insert(
                            yylval->as<std::string>());
                          RET(token::IDENTIFIER);
                        }

  <arglist>","          RET(token::COMMA);
  <arglist>")"          {
                          BEGIN(INITIAL); RET_EXPR(token::RPAREN);
                        }

  <arglist>.            { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- signal name (signalhead & signalafter start conditions) ---
   * Entered by the `{` rule when the brace opens an INPUTS or OUTPUTS
   * block, and by the `;` rule thereafter, so that the FIRST token of
   * each declaration of such a block is read here.  That token is the
   * name of a signal -- an atomic proposition, or a bus whose `[...]`
   * width follows -- or the enumeration type of a typed-bus
   * declaration (`E st;`).  In all three cases it must read as a
   * plain identifier even when it is spelled like a word of the
   * language (the `U` and `AND` of the probes of SPEC rule 18, or a
   * section keyword such as `MAIN`), and the name itself is recorded
   * in `res.declared_words` exactly as the `enumname` and `declhead`
   * conditions record the names they read, so that a signal named
   * `U` or `AND` is usable as an identifier wherever a signal is
   * used.
   *
   * The signalhead condition reads the first identifier, and only the
   * token that follows it decides the identifier's role, so it is
   * handed to the signalafter condition: a `[`, `;` or `}` reveals
   * that it was the name (`U[2]`, `U;`, or a trailing `U` without a
   * `;`), and a second identifier reveals that it was a typed-bus
   * type (`E U;`), in which case THAT second identifier is the name
   * that gets recorded.  The one-token lookahead needs no flex
   * trailing context.  The identifier class is spelled out, as in the
   * declhead condition, for the flex reason given there.
   *
   * The two conditions reproduce the unreservable keyword rules of
   * the initial condition BEFORE their identifier rule, so that a
   * signal list is like any other expression position for those
   * words: `G`, `F`, `X`, `NOT`, `SIZEOF`, `true` and `false` stay
   * their keyword token in a signal list, whether they appear as the
   * type of a typed bus (`INPUTS { G b; }` is a syntax error, as it
   * always was) or as the name itself.  Every other word of the
   * language -- the section keywords, `Mealy`/`Moore`/`Strict`/
   * `Finite`, `enum`, `U`, `AND`, `EQ`, and the rest of the list of
   * SPEC rule 18 -- is read as an identifier by the rules below them,
   * exactly as it would be read in an expression. */
  <signalhead>[ \t\f]+     yylloc->step();
  <signalhead>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <signalhead>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <signalhead>"//"[^\n]*   yylloc->step();
  <signalhead>"/*"         BEGIN_COMMENT();

  <signalhead>"G"           RET(token::LTL_G);
  <signalhead>"F"           RET(token::LTL_F);
  <signalhead>"X"           RET(token::LTL_X);
  <signalhead>"NOT"         RET(token::KW_NOT);
  <signalhead>"SIZEOF"      RET(token::FN_SIZEOF);
  <signalhead>"true"        RET_EXPR(token::BOOL_TRUE);
  <signalhead>"false"       RET_EXPR(token::BOOL_FALSE);

  <signalhead>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->pending_signal.assign(yytext, yyleng);
                          BEGIN(signalafter);
                          RET_EXPR(token::IDENTIFIER);
                        }

  <signalhead>"}"       {
                          POP_BRACE();
                          BEGIN(INITIAL); RET_EXPR(token::RBRACE);
                        }

  <signalhead>.         { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

  /* --- signal name tail (signalafter start condition) ---
   * Entered by the signalhead name rule and left as soon as the
   * identifier's role is decided.  The bus width that follows the `[`
   * is scanned in the normal state, where every word already shadowed
   * by a preceding declaration (a parameter AND used as a width, say)
   * still reads as an identifier; nothing inside the width is recorded
   * here.  The unreservable keywords of the initial condition stay
   * reserved here too, for the same reason as in signalhead; a signal
   * name or a typed-bus name spelled like one of them is a syntax
   * error, exactly as it would be anywhere else. */
  <signalafter>[ \t\f]+     yylloc->step();
  <signalafter>[\n]+        { yylloc->lines(yyleng); yylloc->step(); }
  <signalafter>[\r\n]+      { yylloc->lines(yyleng / 2); yylloc->step(); }
  <signalafter>"//"[^\n]*   yylloc->step();
  <signalafter>"/*"         BEGIN_COMMENT();

  <signalafter>"G"          RET(token::LTL_G);
  <signalafter>"F"          RET(token::LTL_F);
  <signalafter>"X"          RET(token::LTL_X);
  <signalafter>"NOT"        RET(token::KW_NOT);
  <signalafter>"SIZEOF"     RET(token::FN_SIZEOF);
  <signalafter>"true"       RET_EXPR(token::BOOL_TRUE);
  <signalafter>"false"      RET_EXPR(token::BOOL_FALSE);

  <signalafter>"["          {
                          yyextra->declared_words.insert(
                            yyextra->pending_signal);
                          BEGIN(INITIAL); RET(token::LBRACKET);
                        }

  <signalafter>";"          {
                          yyextra->declared_words.insert(
                            yyextra->pending_signal);
                          BEGIN(signalhead); RET(token::SEMICOLON);
                        }

  <signalafter>"}"          {
                          yyextra->declared_words.insert(
                            yyextra->pending_signal);
                          POP_BRACE();
                          BEGIN(INITIAL); RET_EXPR(token::RBRACE);
                        }

  <signalafter>[a-zA-Z_@][a-zA-Z0-9_@']* {
                          // The first identifier was the enum type of a
                          // typed-bus declaration (`E U;`); this one is
                          // the signal name.
                          yylval->emplace<std::string>(yytext, yyleng);
                          yyextra->declared_words.insert(
                            std::string(yytext, yyleng));
                          BEGIN(INITIAL);
                          RET_EXPR(token::IDENTIFIER);
                        }

  <signalafter>.        { BEGIN(INITIAL); yylloc->columns(-1); yyless(0); }

   /* --- block comment (in_COMMENT start condition) ---
   * This implements support for nested comments.  */
  <in_COMMENT>{
  "/*"                  ++yyextra->comment_level;
  [^*/\n\r]*            continue;
  "/"[^*\n\r]*          continue;
  "*"                   continue;
  [\n]+                 yylloc->lines(yyleng);
  [\r\n]+               yylloc->lines(yyleng / 2);
  "*/"                  {
                          if (--yyextra->comment_level == 0)
                            {
                              yylloc->step();
                              const unsigned oc = yyextra->orig_cond;
                              BEGIN(oc);
                            }
                        }
  <<EOF>>               {
                          const unsigned oc = yyextra->orig_cond;
                          BEGIN(oc);
                          yyextra->errors.emplace_back(*yylloc,
                                                       "unclosed comment");
                          return 0;
                        }
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
             tlsf_result& res)
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
  tlsfyyopen(int fd, yyscan_t* scanner, tlsf_result& res)
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

  int
  tlsfyystring(const char* data, yyscan_t* scanner,
               tlsf_result& res)
  {
    if (yylex_init_extra(&res, scanner))
      return 1;
    yyscan_t yyscanner = *scanner;
    struct yyguts_t* yyg = (struct yyguts_t*)yyscanner;
    BEGIN(INITIAL);
    yy_scan_string(data, yyscanner);
    yyin = nullptr;
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
}
