%language "C++"
%defines
%debug
%define parse.error verbose
%define api.value.type variant
%locations
%define api.location.type {spot::location}
%define api.namespace { tlsfyy }
%define api.prefix {tlsfyy}

%parse-param { void* scanner }
%parse-param { spot::tlsf_result& res }
%lex-param { void* scanner } { spot::tlsf_result& res }

%code requires
{
  #include "config.h"
  #include <spot/misc/location.hh>
  #include <spot/parsetlsf/ast.hh>
  #include <spot/parsetlsf/public.hh>
  #include <map>
  #include <memory>
  #include <sstream>
  #include <stdexcept>
  #include <string>
  #include <unordered_set>
  #include <utility>
  #include <vector>

  namespace spot
  {
    /// Per-parse state shared between the lexer and the parser.
    struct tlsf_result
    {
      /// The AST being built.  Always non-null during parsing.
      std::shared_ptr<tlsf_ast> spec;

      /// Diagnostics emitted by both the parser and the lexer.
      parse_tlsf_error_list errors;

      /// Non-fatal diagnostics emitted by the post-parse
      /// validations (see spot/parsetlsf/public.cc).  They are
      /// moved onto parsed_tlsf::warnings by the parse_tlsf()
      /// entry points, so that a valid-but-ambiguous specification
      /// (a SEMANTICS that does not match the TARGET) can be
      /// reported without failing the parse.
      parse_tlsf_error_list warnings;

      /// Whose inputs/outputs the next ap_decl should append to.
      /// Set by mid-rule actions on INPUTS / OUTPUTS and cleared
      /// on the matching RBRACE.
      std::vector<tlsf_ap_decl>* io_target = nullptr;

      /// Current MAIN-subsection body being filled.  Set by
      /// mid-rule actions on INITIALLY / PRESET / REQUIRE / ASSERT /
      /// GUARANTEE / ASSUME.  Cleared on the matching RBRACE.
      std::vector<tlsf_expr_ptr>* current_body = nullptr;

      /// True if yyin was opened with fopen() in tlsfyyopen, so
      /// tlsfyyclose() should fclose() it.  False for the fd
      /// overload (caller retains ownership of the fd and any
      /// wrapper FILE*).
      bool close_yyin = false;

      /// Track the location of each DEFINITION's first occurrence
      /// so a duplicate-name pair can emit BOTH diagnostics -- the
      /// first ("shadowed by later") anchored at the original's
      /// location, and the second ("already defined") anchored at
      /// the new one's location.
      std::map<std::string, location> def_first_loc;

      /// \brief Every enum name and tag this file declares, plus the
      /// name of every parameter, definition, definition argument, and
      /// input/output signal.
      ///
      /// TLSF's list of words is a scanner convention, not a
      /// reservation: syfco lets a file call an enumeration `U`, name
      /// a tag `U`, or name a parameter `U`, and then resolves that
      /// word in expressions like any other identifier.  The scanner
      /// fills this set while it is in the `enumname` and `enumdecl`
      /// start conditions, in the `declhead`, `arglist`, `signalhead`
      /// and `signalafter` ones added for the GLOBAL and MAIN
      /// declarations, and consults it before returning a keyword
      /// token; see ENUM_WORD() in spot/parsetlsf/scantlsf.ll.
      ///
      /// A word whose own syntactic trigger a scanner cannot see
      /// (`G`, `F`, `X`, `NOT`, `SIZEOF`, `true`, `false`, and the
      /// section keywords) is never consulted and stays reserved: a
      /// scanner that has seen nothing but `G` cannot tell `G x` from
      /// a reference to a tag named `G`.
      std::unordered_set<std::string> declared_words;

      /// \brief One entry per open brace: 0 for a block that holds
      /// no declarations, 1 for a `PARAMETERS` or `DEFINITIONS`
      /// block, and 2 for an `INPUTS` or `OUTPUTS` block.
      ///
      /// The `;` that separates two items of such a block is what
      /// hands the scanner to the `declhead` (kind 1) or `signalhead`
      /// (kind 2) start condition: there the next token is the name
      /// of a parameter or a definition, or of an input/output signal.
      std::vector<unsigned char> brace_is_decl;

      /// \brief The kind of block the next `{` opens: 1 for a
      /// `PARAMETERS` or `DEFINITIONS` block, 2 for an `INPUTS` or
      /// `OUTPUTS` one, 0 otherwise.
      ///
      /// Set by the `PARAMETERS` and `DEFINITIONS` keyword rules (and
      /// by `INPUTS`/`OUTPUTS`) and consumed (and cleared) by the
      /// next `{` rule, which uses it to push an entry onto
      /// `brace_is_decl` and to switch the scanner to the matching
      /// name-reading start condition.  Only whitespace and
      /// comments may separate the keyword from its brace in a valid
      /// file, and every other token rule clears the flag, so a
      /// keyword that a malformed file leaves unmatched by its brace
      /// cannot latch onto a later one.
      unsigned char await_decl = 0;

      /// \brief The first identifier of an `INPUTS`/`OUTPUTS`
      /// declaration, as read by the `signalhead` start condition.
      ///
      /// One lookahead decides whether it is a signal name (`U;`,
      /// `U[2];`, `U}`), recorded into `declared_words` by the
      /// `signalafter` rule that sees the `;`/`[`/`}`, or the enum
      /// type of a typed-bus declaration (`E U;`), in which case the
      /// signalafter rule that sees a second identifier records THAT
      /// one instead.  Being the name is the default: a bare
      /// identifier followed by nothing that makes it a type is a
      /// scalar signal.
      std::string pending_signal;

      /// \brief Whether the last token returned can end an expression.
      ///
      /// One token of left context, used to tell the infix reading of a
      /// word this file declared (`a U b`) from its identifier reading
      /// (`b == U`).  Only the rules that can end an expression set it;
      /// it stays false after `{`, `;`, `(`, `,` and after any
      /// operator, which is exactly where a declared word is an
      /// identifier.
      bool prev_ends_expr = false;

      /// \brief Record that the INFO item \a bit was seen at \a loc.
      ///
      /// Returns true the first time an item is seen, and false
      /// afterwards, in which case a "duplicate INFO item" diagnostic
      /// is appended to `errors`.  The caller uses the return value
      /// to decide whether to record the item's value: as for a
      /// re-defined DEFINITION, the first declaration wins and the
      /// later one is only reported.  See tlsf_info_item in
      /// spot/parsetlsf/ast.hh.
      bool note_info_item(unsigned bit, const location& loc,
                          const char* name)
      {
        if (spec->info_seen & bit)
          {
            errors.emplace_back(loc, std::string("duplicate INFO item '")
                                + name + ":'");
            return false;
          }
        spec->info_seen |= bit;
        return true;
      }

      /// \brief Set the SEMANTICS of the spec to \a s.
      ///
      /// The value of an INFO item is parsed by a sub-production of
      /// info_item, so it reduces -- and would assign -- before
      /// note_info_item has a chance to reject a duplicate.  These
      /// two helpers keep the "first declaration wins" rule of
      /// note_info_item: the flag is still clear when the first item
      /// is parsed, and already set for every later one.
      void note_semantics(::spot::tlsf_semantics s)
      {
        if (!(spec->info_seen & ::spot::TLSF_INFO_SEMANTICS))
          spec->semantics = s;
      }

      /// \brief Set the TARGET of the spec to \a t.  See
      /// note_semantics.
      void note_target(::spot::tlsf_target t)
      {
        if (!(spec->info_seen & ::spot::TLSF_INFO_TARGET))
          spec->target = t;
      }
    };
  }
}

%code
{
  #include "parsedecl.hh"

  namespace
  {
    // Reject a binder list holding anything but the two shapes TLSF v1.2
    // SS4.7-4.8 give a binder, `id IN set` and `lo <= id < hi`;
    // tlsf_binder_variable (ast.hh) recognizes exactly those.
    void check_binders(spot::tlsf_result& res,
                       const std::vector<spot::tlsf_expr_ptr>& binders)
    {
      for (const spot::tlsf_expr_ptr& b : binders)
        if (b && !::spot::tlsf_binder_variable(*b))
          res.errors.emplace_back(
            b->loc,
            "invalid binder; a binder must have the form "
            "`id IN set` or `lo <= id < hi`");
    }

    // Recovery from a binder list that does not parse, shared by the
    // `error` production of every head that takes one.
    spot::tlsf_expr_ptr
    recover_binder(spot::tlsf_result& res, const spot::location& loc,
                   spot::tlsf_expr_ptr body)
    {
      res.errors.emplace_back(loc, "malformed binder list");
      return body;
    }
  }
}

%token <std::string> STRING "string"
%token <std::string> IDENTIFIER "identifier"
%token <std::string> NUMBER "number"
// One maximal run of `0`, `1` and `*` characters: a bit pattern of
// an `enum` declaration.  Only the scanner's `enumdecl` state
// returns it; a run outside an enum body is a NUMBER (or a STAR)
// and a juxtaposed run inside one is a syntax error.
%token <std::string> BITS "bit pattern"
// A `Tag` of an `enum` body.  The scanner returns it only from the
// `enumdecl` state, and only for an identifier it has seen followed
// by `:`; a tag is therefore the one identifier that can continue the
// entry list of the enum being declared, which is what keeps the
// grammar free of a shift/reduce conflict on the enum/definition
// boundary (see the %expect block below).
%token <std::string> ENUM_TAG "enum tag"

%token INFO "INFO"
%token MAIN "MAIN"
%token GLOBAL "GLOBAL"
%token SEMICOLON ";"
%token LBRACE "{"
%token RBRACE "}"
%token LBRACKET "["
%token RBRACKET "]"
// Strong (`!`) markers on the stacked next and on the bounded
// temporal operators: `X[!n]`/`X[n!]`, `F[!a:b]`/`F[a:b!]`,
// `G[!a:b]`/`G[a:b!]`.
%token LBRACKET_BANG "[!"
%token BANG_RBRACKET "!]"
%token LPAREN "("
%token RPAREN ")"
%token EQUAL "="
%token COMMA ","
// `:` separator inside `Tag:bits` enum entries.
%token COLON ":"

%token TITLE "TITLE:"
%token DESCRIPTION "DESCRIPTION:"
%token SEMANTICS_KW "SEMANTICS:"
%token TARGET "TARGET:"
%token TAGS "TAGS:"

%token PARAMETERS "PARAMETERS"
%token DEFINITIONS "DEFINITIONS"
%token ENUM "enum"
%token INPUTS "INPUTS"
%token OUTPUTS "OUTPUTS"
%token INITIALLY "INITIALLY"
%token PRESET "PRESET"
// Aliases for the REQUIRE/ASSERT/GUARANTEE/ASSUME
// block keywords, matching TLSF v1.0's old names.
//   REQUIRE     | REQUIREMENTS   -> require_body
//   ASSERT      | INVARIANTS     -> assert_body
//   GUARANTEE   | GUARANTEES     -> guarantee_body
//   ASSUME      | ASSUMPTIONS    -> assumptions_body (new)
%token REQUIRE "REQUIRE"
%token REQUIREMENTS "REQUIREMENTS"
%token ASSERT "ASSERT"
%token INVARIANTS "INVARIANTS"
%token GUARANTEE "GUARANTEE"
%token GUARANTEES "GUARANTEES"
%token ASSUME "ASSUME"
%token ASSUMPTIONS "ASSUMPTIONS"

%token MEALY "Mealy"
%token MOORE "Moore"
%token STRICT "Strict"
%token FINITE "Finite"

// LTL op keywords.
%token LTL_G "G"
%token LTL_F "F"
%token LTL_X "X"
%token LTL_U "U"
%token LTL_R "R"
%token LTL_W "W"
%token LTL_STRONG_NEXT "X[!]"

// Boolean literals and textual operator aliases.  The aliases use
// distinct token kinds so their canonical punctuation counterparts
// remain available in the same grammar.
%token BOOL_TRUE "true"
%token BOOL_FALSE "false"
%token IN "IN"
%token KW_NOT "NOT"
%token KW_AND "AND"
%token KW_OR "OR"
%token KW_IMPLIES "IMPLIES"
%token KW_EQUIV "EQUIV"
%token KW_EQ "EQ"
%token KW_NEQ "NEQ"
%token KW_LE "LE"
%token KW_GE "GE"
%token KW_LEQ "LEQ"
%token KW_GEQ "GEQ"
%token KW_ELEM "ELEM"
%token KW_FORALL "FORALL"
%token KW_EXISTS "EXISTS"
%token SET_CUP "CUP"
%token SET_CAP "CAP"
%token SET_MINUS "SETMINUS"
// Big operators: a prefix head whose argument is a binder list, as in
// `SUM[i IN {0, 1}] eN` or `CUP[i IN {0, 1}] eSX`.  TLSF v1.2 Table 1
// gives the numeric four (`+[`, `*[`, and their `SUM[`/`PROD[`
// spellings) precedence 1 and the set two (`(+)[`, `(*)[`, and their
// `CUP[`/`CAP[` spellings) precedence 5.  `(-)[` and `SETMINUS[` are
// Spot extensions: the table has `(-)`, `(\)`, and `SETMINUS` only as
// binary right-to-left difference.  These heads declare no precedence of
// their own; see the note above the `%precedence NUM_UNARY` line.
%token BIG_SUM "+["
%token BIG_PROD "*["
%token BIG_SUM_LONG "SUM["
%token BIG_PROD_LONG "PROD["
%token BIG_SET_UNION "(+)["
%token BIG_SET_INTER "(*)["
%token BIG_SET_DIFF "(-)["
%token KW_PLUS "PLUS"
%token KW_MINUS "MINUS"
%token KW_MUL "MUL"
%token KW_DIV "DIV"
%token KW_MOD "MOD"

// TLSF built-in functions (phase 4 will fold them; for now they're
// just identifier-shaped apps).  FN_MIN and FN_MAX are the *prefix*
// forms `MIN eSX` / `MAX eSX`; their parenthesised call spellings
// `MIN(..)` / `MAX(..)` are separate tokens, because a single token
// would let `MIN(1)` return from the deparser as the prefix `MIN (1)`
// and break the print/parse round-trip.
%token FN_MIN "MIN"
%token FN_MAX "MAX"
%token FN_MIN_CALL "MIN("
%token FN_MAX_CALL "MAX("
%token FN_SIZEOF "SIZEOF"
%token FN_SIZE "SIZE"
%token FN_SUM "SUM"
%token FN_PROD "PROD"

// Operators (punctuation).
%token AND "&&"
%token OR "||"
%token IMPLIES "->"
%token EQUIV "<->"
%token EQ "=="
%token NEQ "!="
%token LT "<"
%token LE "<="
%token GT ">"
%token GE ">="
%token PLUS "+"
%token MINUS_ "-"
%token STAR "*"
%token SLASH "/"
%token PERCENT "%"
%token BANG "!"
%token DOTDOT ".."
%token BAR "|"

// ---------- Precedence (lowest to highest) -----------------------------
//
// This is the reverse of Table 1 in TLSF v1.2 (Table 1 lists the
// tightest operator first).  Operators on one declaration share both
// precedence and associativity.  NUM_UNARY is a precedence marker only;
// it is never returned by the scanner.
//
// The guard operator `:` (Table 1 row 19) is the loosest of all, even
// looser than R (row 17): in `eB : e` every operator of `eB` and `e`
// binds first.  It is left-associative like every row of the table
// that has no explicit direction.
%left COLON
%left LTL_R
%right LTL_U
%right LTL_W
%right IMPLIES KW_IMPLIES EQUIV KW_EQUIV
%left OR KW_OR
%left AND KW_AND
// Unary LTL operators and quantified conjunction/disjunction share
// Table 1's precedence 11.
%precedence QUANTIFIER
%left IN KW_ELEM
%left EQ KW_EQ NEQ KW_NEQ LT LE KW_LE GT GE KW_GE KW_LEQ KW_GEQ
// Table 1 row 5, the unary-set tier: the set big operators `(+)[b] eSX`,
// `(*)[b] eSX`, and the Spot extension `(-)[b] eSX`.  They bind tighter
// than a comparison but looser than `+`/`-`, which the rows after this one
// give.  This token is never returned by the scanner, exactly like
// QUANTIFIER above: the productions name it with `%prec` only.
%precedence BIG_SET
%left SET_CUP
%left SET_CAP
%right SET_MINUS
%left PLUS KW_PLUS MINUS_ KW_MINUS
%right SLASH KW_DIV PERCENT KW_MOD
%left STAR KW_MUL
%precedence NUM_UNARY
// The big-operator heads take no precedence of their own: each is only
// ever the first token of a production, so no shift/reduce decision ever
// turns on one, and their productions carry `%prec QUANTIFIER` (the
// set ones) or `%prec NUM_UNARY` (the numeric ones) instead.  Bison
// rejects a %precedence for a token it would never consult.

%type <spot::tlsf_ap_decl> ap_decl_body
%type <std::vector<spot::tlsf_expr_ptr>> body
%type <std::vector<std::string>> arg_list
%type <std::vector<std::string>> tag_list
// Enum-related types.  A pattern is the maximal run of `0`, `1` and
// `*` characters that the scanner returns as a single BITS token;
// `enum_patterns` is the comma-separated pattern list of one tag;
// `enum_entry` is the per-tag (tag, patterns) pair; `enum_entries` is
// the whitespace-separated entry list; `enum_decl` is the full
// `enum X = ...;` node.  `def_item` (the parent) discards the
// enum_decl value, so `enum_decl` only side-effects on
// `res.spec->enumerations`.
%type <std::vector<std::string>> enum_patterns
%type <spot::tlsf_definition> def_head
%type <spot::tlsf_enum_value> enum_entry
%type <std::vector<spot::tlsf_enum_value>> enum_entries
%type <spot::tlsf_enum_decl> enum_decl
%type <spot::tlsf_expr_ptr> expr
%type <std::vector<spot::tlsf_expr_ptr>> property_body
%type <std::vector<spot::tlsf_expr_ptr>> arg_expr_list
%type <std::vector<spot::tlsf_expr_ptr>> binder_list
%type <std::vector<spot::tlsf_expr_ptr>> set_elements

%start tlsf

// One shift/reduce conflict, resolved to the shift by Bison's default
// rule (no %prec involved): the shift is always the maximal munch.
// It is inherent to the juxtaposed-clause syntax of TLSF v1.2 SS4.6,
// where `f(x) = a b` is a two-clause body and `a b` is neither a
// definition nor a complete expression.
//
//  A `(` after a bare identifier can be the argument list of a
//  function application or the start of a juxtaposed clause.  A
//  parenthesized expression after an identifier is always a valid
//  application, so maximal munch never splits there.
//
// The companion question -- an identifier after a completed definition
// `body`, which can be a juxtaposed clause extending the SAME
// definition (multi-clause bodies like full_arbiter's mone) or the head
// of a FOLLOWING definition -- is no longer a conflict.  It used to be,
// while `def_list` still had a `def_list -> def_list def_item`
// alternative for a `;`-less item, because that made `identifier` part
// of the lookahead set for reducing the definition and hence offered a
// reduce against the shift.  Splitting the list in two (see the
// `def_list` and `def_items` rules above) leaves a `;`-less item
// followed by `RBRACE` alone, so the only action on `identifier` is the
// shift: it always extends the body, and two juxtaposed definitions
// without a `;` fail at the second one's `=`.
//
// The same question once arose at the end of a brace-less enum
// declaration, where the `;` is optional (TLSF v1.2 SS4.4 has no
// terminator at all): an identifier there could be the tag of a
// further entry or the head of the next def_list item.  That was a
// third conflict, removed earlier by having the scanner return an
// ENUM_TAG for an identifier it has seen followed by `:` and leave the
// `enumdecl` state otherwise (see the `enumdecl` rules of
// scantlsf.ll).  The following item is then rejected by the
// `def_items`/`def_list` split rather than by a conflict, which is what
// syfco does too: its `enumVParserL` cannot end the entry list at an
// identifier that is not a tag either.
//
// The strong `!` markers of SS4.8 (`[!`, `!]`) are a fourth question that
// never became one: the scanner returns each marker glued to its bracket
// as one token, so `F[!a:b]` cannot be confused with the `F[(!a):b]`
// that the plain `!` token would have made of it.  Adding those six
// alternatives therefore leaves this count at 1, and `F[!a:b!]` matches
// none of them and is rejected, as in syfco.
//
// Keep the count in sync if the expression grammar grows new postfix
// forms or the definition/body productions change shape.
%expect 1

%%

tlsf: {
       res.spec = std::make_shared< ::spot::tlsf_ast>();
       res.spec->loc = @$;
     }
     sections
     ;

sections: %empty
        | sections section
        ;

section: INFO
          {
            // Remember where the INFO section starts: the validator
            // anchors a "missing item" diagnostic here, and needs to
            // tell a missing section (line 0) from a present one.
            res.spec->info_loc = @1;
          }
        LBRACE info_items RBRACE
       | GLOBAL LBRACE global_items RBRACE
       | MAIN LBRACE main_items RBRACE
       | error SEMICOLON
       ;

info_items: %empty
          | info_items info_item
          ;

// No trailing `;` after an INFO item: TITLE, DESCRIPTION,
// SEMANTICS, and TARGET are each followed directly by their value.
// TLSF v1.2 SS1.2 requires the first four to be present exactly
// once (and TAGS at most once); note_info_item reports a duplicate
// here, and the validator (spot/parsetlsf/public.cc) reports a
// missing mandatory item.  As with a re-defined DEFINITION, the
// first occurrence wins so a file with a duplicate still translates.
info_item: TITLE STRING
           {
             if (res.note_info_item(::spot::TLSF_INFO_TITLE, @1, "TITLE"))
               res.spec->title = std::move($2);
           }
         | DESCRIPTION STRING
           {
             if (res.note_info_item(::spot::TLSF_INFO_DESCRIPTION, @1,
                                    "DESCRIPTION"))
               res.spec->description = std::move($2);
           }
         | SEMANTICS_KW semantics
           {
             if (res.note_info_item(::spot::TLSF_INFO_SEMANTICS, @1,
                                    "SEMANTICS"))
               res.spec->semantics_loc = @1;
           }
         | TARGET target_kind
           {
             if (res.note_info_item(::spot::TLSF_INFO_TARGET, @1,
                                    "TARGET"))
               res.spec->target_loc = @1;
           }
         | TAGS tag_list
           {
             if (res.note_info_item(::spot::TLSF_INFO_TAGS, @1, "TAGS"))
               res.spec->tags = std::move($2);
           }
         | error RBRACE
         ;

// Comma-separated IDENTIFIER list for optional TAGS.  The list may be
// empty: syfco builds it with `commaSep`, which accepts no element at
// all, so a bare `TAGS:` is valid there.  The `{}` matters -- without
// an action, bison's default for an empty rule is `$$ = $1`, on a rule
// that has no $1; this is the idiom `arg_list` below already uses.
tag_list: %empty {}
        | IDENTIFIER
          {
            $$.push_back(std::move($1));
          }
        | tag_list COMMA IDENTIFIER
          {
            $1.push_back(std::move($3));
            $$ = std::move($1);
          }
        ;

semantics: MEALY
           { res.note_semantics(::spot::tlsf_semantics::Mealy); }
         | MOORE
           { res.note_semantics(::spot::tlsf_semantics::Moore); }
         | MEALY COMMA STRICT
           { res.note_semantics(::spot::tlsf_semantics::MealyStrict); }
         | STRICT COMMA MEALY
           { res.note_semantics(::spot::tlsf_semantics::MealyStrict); }
         | MEALY COMMA FINITE
           { res.note_semantics(::spot::tlsf_semantics::MealyFinite); }
         | FINITE COMMA MEALY
           { res.note_semantics(::spot::tlsf_semantics::MealyFinite); }
         | MOORE COMMA STRICT
           { res.note_semantics(::spot::tlsf_semantics::MooreStrict); }
         | STRICT COMMA MOORE
           { res.note_semantics(::spot::tlsf_semantics::MooreStrict); }
         | MOORE COMMA FINITE
           { res.note_semantics(::spot::tlsf_semantics::MooreFinite); }
         | FINITE COMMA MOORE
           { res.note_semantics(::spot::tlsf_semantics::MooreFinite); }
         ;

target_kind: MEALY { res.note_target(::spot::tlsf_target::Mealy); }
           | MOORE { res.note_target(::spot::tlsf_target::Moore); }
           ;

global_items: %empty
            | global_items global_item
            ;

global_item: PARAMETERS LBRACE param_list RBRACE
           | DEFINITIONS LBRACE def_list RBRACE
           | error SEMICOLON
           ;

param_list: %empty
          | param_list param_decl
          ;

// A PARAMETERS value, like every other integer position, is an
// `expr` AST: the translator's integer evaluator (eval_int) is the
// single arbiter of what an integer expression is, so the grammar
// does not restrict the shape here.
param_decl: IDENTIFIER EQUAL expr SEMICOLON
            {
              res.spec->parameters.push_back(
                ::spot::tlsf_parameter_decl{@1,
                  std::move($1),
                  std::move($3)});
            }
          ;

// A DEFINITIONS block holds zero or more items.  The `;` SEPARATES
// items: it is required between two items but the last one may omit
// it, so all of `A; B;`, `A; B`, `A;`, and a lone `A` are valid.
//
// The two cases are different nonterminals so that a `;`-less item
// cannot be followed by any other item: `def_items` only ever holds
// `;`-terminated ones, and it is not a `def_list`, so the single
// unterminated item that `def_list -> def_items def_item` appends is
// necessarily the last one.  This matters for brace-less enums, whose
// entry list has no terminator (TLSF v1.2 SS4.4) and which are
// therefore ended by the scanner rather than by the grammar: with a
// single `def_list -> def_list def_item` production, two `;`-less
// items would still be derivable, so `enum E = A: 00  F(x) = x;` would
// parse as a def_list of two items.  syfco's `sepBy`
// (Reader/Parser/Global.hs) rejects that input, because its
// `enumVParserL` consumes the following identifier before requiring
// the `:` of a tag, so Parsec cannot end the entry list there; keeping
// the same restriction costs nothing and matches the reference
// implementation.
def_list: def_items
        | def_items def_item
        ;

// The part of a DEFINITIONS block that precedes a last, `;`-less item.
def_items: %empty
         | def_items def_item SEMICOLON
         | def_items error SEMICOLON
         ;

// Each entry in a DEFINITIONS block is either a regular
// function-style definition or an `enum` declaration.
def_item: definition
        | enum_decl
        ;

// The left-hand side of a definition: either a parameterized
// `name(a1, ..., an)` or a bare parameterless `name`
def_head: IDENTIFIER LPAREN arg_list RPAREN
          {
            $$ = ::spot::tlsf_definition{@1,
                  std::move($1),
                  std::move($3),
                  {}};
          }
        | IDENTIFIER
          {
            $$ = ::spot::tlsf_definition{@1,
                  std::move($1),
                  {},
                  {}};
          }
        ;

// No trailing `;`: it belongs to def_list (see above)
definition: def_head EQUAL body
          {
            const std::string& name = $1.name;
            auto ins = res.def_first_loc.emplace(name, $1.loc);
            if (!ins.second)
              {
                // TLSF specifies "one symbol = one definition".
                res.errors.emplace_back(
                  ins.first->second,
                  "definition '" + name
                  + "' is shadowed by a later re-definition");
                res.errors.emplace_back(
                  $1.loc,
                  "definition '" + name
                  + "' is already defined");
              }
            else
              {
                $1.body = std::move($3);
                res.spec->definitions.push_back(std::move($1));
              }
          }
          ;

// `enum` declaration: `enum X = T0:bits0 T1:bits1 ...;` -- the
// trailing `;` belongs to def_list (see above), and the enum
// grammar of TLSF v1.2 SS4.4 has no terminator at all, so the `;`
// may be omitted when the enum is the last item of the block.  The
// action side-effects by appending to `res.spec->enumerations`; the
// `$$ = ...` assignment is then unused by the parent `def_item` rule
// but is kept so the typed value is available to Bison's default
// %type machinery.
enum_decl: ENUM IDENTIFIER EQUAL enum_entries
           {
             // Binding-level validation: (1) uniform width; (2) no
             // overlapping patterns, two DIFFERENT tags must not
             // cover the same concrete valuation.  Overlapping
             // patterns WITHIN one tag are accepted: a tag's pattern
             // list is a deliberate coverage union (the canonical
             // TLSF example `UNDEF: 11*, 1*1, *11` overlaps itself).
             // Spot tests overlap position-wise (no 2^w enumeration)
             // and renders the shared valuation by preferring the
             // concrete bit of either pattern ('0' when both are
             // don't-cares).  Duplicate tags with disjoint patterns
             // are legal.
             const std::string& ename = $2;
             if (!$4.empty())
               {
                 const size_t w = $4[0].patterns[0].size();
                 // Flatten to (entry, pattern) pairs in source
                 // order so within-entry pattern clashes (e.g.
                 // `A: 00, 00`) are checked like cross-tag ones.
                 std::vector<const spot::tlsf_enum_value*> ents;
                 std::vector<const std::string*> pats;
                 for (const auto& e : $4)
                   for (const auto& p : e.patterns)
                     {
                       ents.push_back(&e);
                       pats.push_back(&p);
                     }
                 const size_t n = pats.size();
                 for (size_t i = 0; i < n; ++i)
                   {
                     if (pats[i]->size() != w)
                       {
                         res.errors.emplace_back(
                           ents[i]->loc,
                           "enumeration '" + ename + "': pattern '"
                           + *pats[i] + "' of tag '"
                           + ents[i]->tag + "' has length "
                           + std::to_string(pats[i]->size())
                           + ", but the width is fixed to "
                           + std::to_string(w)
                           + " by the first pattern");
                         // Skip the overlap comparisons: the
                         // position-wise loop below indexes both
                         // patterns up to w-1 and a short pattern
                         // would read past its end.
                         continue;
                       }
                     for (size_t j = 0; j < i; ++j)
                       {
                         if (pats[j]->size() != w)
                           continue;
                         // Position-wise compatibility test.
                         bool overlap = true;
                         std::string shared(w, '0');
                         for (size_t k = 0; k < w && overlap; ++k)
                           {
                             char c1 = (*pats[j])[k];
                             char c2 = (*pats[i])[k];
                             if (c1 != '*' && c2 != '*' && c1 != c2)
                               overlap = false;
                             else if (c1 != '*')
                               shared[k] = c1;
                             else if (c2 != '*')
                               shared[k] = c2;
                           }
                         if (overlap && ents[j]->tag != ents[i]->tag)
                           res.errors.emplace_back(
                             ents[i]->loc,
                             "conflict in enumeration '"
                             + ename + "': tags '"
                             + ents[j]->tag + "' and '"
                             + ents[i]->tag
                             + "' share the same value: "
                             + shared);
                       }
                   }
               }
             ::spot::tlsf_enum_decl decl{ @1 + @4,
                   std::move($2),
                   std::move($4) };
             res.spec->enumerations.push_back(std::move(decl));
           }
           ;

// Whitespace-separated enum_entries list.
// All semantic checks (width, duplicate tags, pattern conflicts) are
// performed once in the `enum_decl` action, where the enum name and
// the complete entry list are available.
enum_entries: enum_entry
              {
                $$.push_back(std::move($1));
              }
            | enum_entries enum_entry
              {
                $1.push_back(std::move($2));
                $$ = std::move($1);
              }
            ;

// One `Tag: patterns...` entry.  The tag is an ENUM_TAG, so a
// following identifier cannot be mistaken for another entry: it
// belongs to the next def_list item, and the enum body is over.
enum_entry: ENUM_TAG COLON enum_patterns
            {
              $$ = ::spot::tlsf_enum_value{ @1 + @3,
                    std::move($1),
                    std::move($3) };
            }
            ;

// Comma-separated bit patterns bound to one tag,
// e.g. `U: 11*, 1*1, *11`.  Each pattern is a single BITS token (one
// maximal run of `0`, `1` and `*` characters, per TLSF v1.2 SS4.4),
// so a run may only follow a `,`.
enum_patterns: BITS
                {
                  $$.push_back(std::move($1));
                }
              | enum_patterns COMMA BITS
                {
                  $1.push_back(std::move($3));
                  $$ = std::move($1);
                }
              | enum_patterns BITS
                {
                  // Two runs with no `,` between them.
                  res.errors.emplace_back(@2,
                    "missing ',' between bit patterns; a pattern is"
                    " one run of '0', '1' and '*' characters");
                  $$ = std::move($1);
                }
              ;

// Right-hand side of a DEFINITION.  TLSF v1.2 SS4.6 allows one or
// more (possibly guarded) clauses `(ec)+` with `ec = e | eB : e |
// eP : e`.
// Both rules carry the loosest precedence (%prec COLON) so that the
// reduce-versus-shift conflicts between "this expression is a complete
// clause" and "this infix operator extends the current expression" are
// resolved by precedence in favor of the shift: an infix operator can
// never start a new clause, so a completed clause followed by one is
// always a longer maximal expression.
body: expr %prec COLON
      {
        // `$$` is default-constructed as an empty vector; pushing
        // keeps the clause list in source order.
        $$.push_back(std::move($1));
      }
    | body expr %prec COLON
      {
        $1.push_back(std::move($2));
        $$ = std::move($1);
      }
    ;

// `arg_list` is the formal-parameter list of a DEFINITION.
arg_list: %empty {}
        | IDENTIFIER
          {
            $$.push_back(std::move($1));
          }
        | arg_list COMMA IDENTIFIER
          {
            $1.push_back(std::move($3));
            $$ = std::move($1);
          }
        ;

main_items: %empty
          | main_items main_item
          ;

main_item: INPUTS LBRACE
            { res.io_target = &res.spec->inputs; }
          ap_list RBRACE
            { res.io_target = nullptr; }
         | OUTPUTS LBRACE
            { res.io_target = &res.spec->outputs; }
          ap_list RBRACE
            { res.io_target = nullptr; }
         | INITIALLY LBRACE
            { res.current_body = &res.spec->initially_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | PRESET LBRACE
            { res.current_body = &res.spec->preset_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | REQUIRE LBRACE
            { res.current_body = &res.spec->require_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | REQUIREMENTS LBRACE
            { res.current_body = &res.spec->require_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | ASSERT LBRACE
            { res.current_body = &res.spec->assert_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | INVARIANTS LBRACE
            { res.current_body = &res.spec->assert_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | GUARANTEE LBRACE
            { res.current_body = &res.spec->guarantee_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | GUARANTEES LBRACE
            { res.current_body = &res.spec->guarantee_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | ASSUME LBRACE
            { res.current_body = &res.spec->assumptions_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | ASSUMPTIONS LBRACE
            { res.current_body = &res.spec->assumptions_body; }
            property_body RBRACE
            { res.current_body = nullptr; }
         | error SEMICOLON
           {
             res.io_target = nullptr;
             res.current_body = nullptr;
           }
         ;

// Declarations separated by `;`; the trailing `;` of the LAST one may
// be omitted (e.g. `HBURST[2]` without `;` in amba_decomposed_decode).
// Like `property_body` above, the split
// between `ap_decls` and a single terminating `ap_decl_nosemi` keeps
// the `;` mandatory between two declarations.
ap_list: ap_decls {}
       | ap_decls ap_decl_nosemi
       ;

ap_decls: %empty {}
        | ap_decls ap_decl
        ;

ap_decl_body: IDENTIFIER
              {
                $$ = ::spot::tlsf_ap_decl{@1, std::move($1),
                  nullptr, std::string()};
              }
            | IDENTIFIER LBRACKET expr RBRACKET
              {
                // A bus width is an integer expression, i.e. any
                // `expr` the translator's integer evaluator accepts
                // (see eval_int in spot/parsetlsf/translate.cc:
                // literals, parameters, loop variables, the
                // builtins, user definitions, and the arithmetic and
                // comparison operators).  Nothing outside that
                // language is rejected here -- it is diagnosed, with
                // a location, at translation time.
                $$ = ::spot::tlsf_ap_decl{@1, std::move($1), std::move($3),
                  std::string()};
              }
            | IDENTIFIER IDENTIFIER
              {
                // Typed-bus declaration `enumType SIGNAL;` (TLSF v1.2
                // SS4.5): SIGNAL is a bus whose width is the bit width
                // of the named enumeration.  The enum existence check
                // happens at translation time, when the GLOBAL section
                // is guaranteed to have been seen (enums may be declared
                // after MAIN lexically, and forward references are
                // accepted).
                $$ = ::spot::tlsf_ap_decl{@1, std::move($2),
                  nullptr, std::move($1)};
              }
            ;

ap_decl: ap_decl_body SEMICOLON
         {
           if (res.io_target)
             res.io_target->push_back(std::move($1));
         }
       ;

ap_decl_nosemi: ap_decl_body
         {
           if (res.io_target)
             res.io_target->push_back(std::move($1));
         }
       ;

// ----- property body (semicolon-separated formulas) ------------------
//
// Statements are separated by `;`.  The semicolon of the LAST
// statement before `}` may be omitted (several benchmarks from the
// wild do so, e.g. amba_decomposed_lock*).  Splitting the list between
// `stmts` (terminated statements) and a trailing `expr` keeps the
// semicolon mandatory between two statements: after `stmts expr` the
// only legal lookahead is `;` (start a new statement) or `}` (reduce the
// trailing expression), so `a b` is still rejected while a lone `a`
// before `}` is accepted.
property_body: stmts {}
            | stmts expr
              {
                if (res.current_body)
                  res.current_body->push_back(std::move($2));
              }
            ;

stmts: %empty {}
     | stmts expr SEMICOLON
       {
         if (res.current_body)
           res.current_body->push_back(std::move($2));
       }
     ;

// ----- expressions ----------------------------------------------------
expr: NUMBER
      {
        long long v = 0;
        try { v = std::stoll($1); }
        catch (const std::out_of_range&)
          {
            // TLSF constants are naturals (grammar `n for n in N`);
            // there is no stated width, but a literal that does not
            // fit in a signed 64-bit integer cannot be represented
            // by the AST.  Record a diagnostic instead of silently
            // truncating to 0.
            res.errors.emplace_back(@1,
              "integer literal is too large");
          }
        $$ = ::spot::tlsf_make_int(@1, v);
      }
    | BOOL_TRUE
      {
        $$ = ::spot::tlsf_make_ident(@1, "true");
      }
    | BOOL_FALSE
      {
        $$ = ::spot::tlsf_make_ident(@1, "false");
      }
    | IDENTIFIER
      {
        $$ = ::spot::tlsf_make_ident(@1, std::move($1));
      }
    | IDENTIFIER LBRACKET expr RBRACKET
      {
        $$ = ::spot::tlsf_make_busref(@1, std::move($1), $3);
      }
    | FN_MIN_CALL LPAREN arg_expr_list RPAREN %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_app(@1, "MIN", std::move($3));
      }
    | FN_MAX_CALL LPAREN arg_expr_list RPAREN %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_app(@1, "MAX", std::move($3));
      }
    | FN_SUM LPAREN arg_expr_list RPAREN %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_app(@1, "SUM", std::move($3));
      }
    | FN_PROD LPAREN arg_expr_list RPAREN %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_app(@1, "PROD", std::move($3));
      }
    // Big operators: a head, a binder list, and a body, folded over
    // the binder with the connective TLSF v1.2 gives the operator
    // (see tlsf_bigop_fold).  `CUP[`/`CAP[`/`SETMINUS[` are the
    // spelled-out forms of `(+)[`/`(*)[`/`(-)[`; they used to head an
    // n-ary list of operands instead, which no longer has a reading.
    | SET_CUP LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigUnion,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    | BIG_SET_UNION LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigUnion,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    | SET_CAP LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigInter,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    | BIG_SET_INTER LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigInter,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    | SET_MINUS LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigDiff,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    | BIG_SET_DIFF LBRACKET binder_list RBRACKET expr %prec BIG_SET
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigDiff,
                                     ::spot::tlsf_bigop_fold::Or,
                                     @1, $3, $5);
      }
    // The numeric big operators share the set ones' shape but fold in
    // integer position, with conjunction as their connective.
    | BIG_SUM LBRACKET binder_list RBRACKET expr %prec NUM_UNARY
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigSum,
                                     ::spot::tlsf_bigop_fold::And,
                                     @1, $3, $5);
      }
    | BIG_SUM_LONG LBRACKET binder_list RBRACKET expr %prec NUM_UNARY
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigSum,
                                     ::spot::tlsf_bigop_fold::And,
                                     @1, $3, $5);
      }
    | BIG_PROD LBRACKET binder_list RBRACKET expr %prec NUM_UNARY
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigProd,
                                     ::spot::tlsf_bigop_fold::And,
                                     @1, $3, $5);
      }
    | BIG_PROD_LONG LBRACKET binder_list RBRACKET expr %prec NUM_UNARY
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_bigop(::spot::tlsf_op::BigProd,
                                     ::spot::tlsf_bigop_fold::And,
                                     @1, $3, $5);
      }
    // `SIZEOF <expr>` -- the canonical TLSF form when the argument is
    // a single token (chomp.tlsf's `(SIZEOF sel)`, for instance).
    // This production subsumes the historical `SIZEOF(arg_list)`
    // form: when written with parens the argument parses as a primary
    // `( ... )` expression inside `expr`.  Unifying on the bare-arg
    // form keeps the parser unambiguous and lets `tlsf_print_expr`
    // round-trip both spellings identically.
    | FN_SIZEOF expr %prec NUM_UNARY
      {
        std::vector< ::spot::tlsf_expr_ptr> args;
        args.push_back(std::move($2));
        $$ = ::spot::tlsf_make_app(@1, "SIZEOF", std::move(args));
      }
    // `|eSX|`, the cardinality of the set expression `eSX`, and `SIZE
    // eSX`, its word spelling.  Both are the same operator, so the AST
    // carries one tag and the two spellings differ only in the first
    // token; the deparser always emits the `|` form.
    | BAR expr BAR %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::SetSize, @1, $2);
      }
    | FN_SIZE expr %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::SetSize, @1, $2);
      }
    | FN_MIN expr %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::SetMin, @1, $2);
      }
    | FN_MAX expr %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::SetMax, @1, $2);
      }
    | IDENTIFIER LPAREN arg_expr_list RPAREN
      {
        $$ = ::spot::tlsf_make_app(@1, std::move($1), std::move($3));
      }
    | LPAREN expr RPAREN
      {
        $2->parenthesized = true;
        $2->loc = @1;
        $$ = std::move($2);
      }
    | expr PLUS expr     %prec PLUS { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Add, @2, $1, $3); }
    | expr KW_PLUS expr  %prec KW_PLUS { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Add, @2, $1, $3); }
    | expr MINUS_ expr   %prec MINUS_ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Sub, @2, $1, $3); }
    | expr KW_MINUS expr %prec KW_MINUS { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Sub, @2, $1, $3); }
    | expr STAR expr     %prec STAR { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Mul, @2, $1, $3); }
    | expr KW_MUL expr   %prec KW_MUL { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Mul, @2, $1, $3); }
    | expr SLASH expr    %prec SLASH { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Div, @2, $1, $3); }
    | expr KW_DIV expr   %prec KW_DIV { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Div, @2, $1, $3); }
    | expr PERCENT expr  %prec PERCENT { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Mod, @2, $1, $3); }
    | expr KW_MOD expr   %prec KW_MOD { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Mod, @2, $1, $3); }
    | expr EQ expr       %prec EQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Eq, @2, $1, $3); }
    | expr KW_EQ expr    %prec KW_EQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Eq, @2, $1, $3); }
    | expr NEQ expr      %prec NEQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Neq, @2, $1, $3); }
    | expr KW_NEQ expr   %prec KW_NEQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Neq, @2, $1, $3); }
    | expr LT expr       %prec LT { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Lt, @2, $1, $3); }
    | expr LE expr       %prec LE { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Le, @2, $1, $3); }
    | expr KW_LE expr    %prec KW_LE { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Lt, @2, $1, $3); }
    | expr GT expr       %prec GT { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Gt, @2, $1, $3); }
    | expr GE expr       %prec GE { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Ge, @2, $1, $3); }
    | expr KW_GE expr    %prec KW_GE { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Gt, @2, $1, $3); }
    | expr KW_LEQ expr   %prec KW_LEQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Le, @2, $1, $3); }
    | expr KW_GEQ expr   %prec KW_GEQ { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Ge, @2, $1, $3); }
    | expr IN expr       %prec IN { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::In, @2, $1, $3); }
    | expr KW_ELEM expr  %prec KW_ELEM { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::In, @2, $1, $3); }
    | expr SET_CUP expr %prec SET_CUP { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::SetUnion, @2, $1, $3); }
    | expr SET_CAP expr %prec SET_CAP { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::SetIntersection, @2, $1, $3); }
    | expr SET_MINUS expr %prec SET_MINUS { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::SetDifference, @2, $1, $3); }
    | expr AND expr      %prec AND { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::And, @2, $1, $3); }
    | expr KW_AND expr   %prec KW_AND { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::And, @2, $1, $3); }
    | expr OR expr       %prec OR { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Or, @2, $1, $3); }
    | expr KW_OR expr    %prec KW_OR { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Or, @2, $1, $3); }
    | expr IMPLIES expr  %prec IMPLIES { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Implies, @2, $1, $3); }
    | expr KW_IMPLIES expr %prec KW_IMPLIES { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Implies, @2, $1, $3); }
    | expr EQUIV expr    %prec EQUIV { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Equiv, @2, $1, $3); }
    | expr KW_EQUIV expr %prec KW_EQUIV { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Equiv, @2, $1, $3); }
    // Guarded clause `eB : e` of a definition body.  COLON is
    // declared with the loosest precedence (see the precedence
    // block), so both the guard and the value keep their natural
    // grouping.  Outside a definition body a top-level guard has no
    // TLSF meaning; the translator diagnoses it when it survives
    // expansion.
    | expr COLON expr %prec COLON
      {
        $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::Guard, @2, $1, $3);
      }
    // The six quantifier heads below all accept a comma-separated binder
    // list, which is shorthand for nested single-binder quantifiers: see
    // tlsf_make_binders().  The fold matches syfco, where `&&[X] e` is
    // literally `forall X. e` and `||[X] e` is `exists X. e`.
    | KW_AND LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::And, @1, $3, $5);
      }
    | KW_OR LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::Or, @1, $3, $5);
      }
    | KW_FORALL LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::And, @1, $3, $5);
      }
    | KW_EXISTS LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::Or, @1, $3, $5);
      }
    | expr LTL_U expr %prec LTL_U
    { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::U, @2, $1, $3); }
    | expr LTL_R expr %prec LTL_R
    { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::R, @2, $1, $3); }
    | expr LTL_W expr %prec LTL_W
    { $$ = ::spot::tlsf_make_binop(::spot::tlsf_op::W, @2, $1, $3); }
    | BANG expr %prec QUANTIFIER
      {
        // Lower the precedence of the child so future parents
        // parenthesise it correctly on deparse.
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::Not, @1, $2);
      }
    | KW_NOT expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::Not, @1, $2);
      }
    | LTL_G expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::G, @1, $2);
      }
    | LTL_F expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::F, @1, $2);
      }
    | LTL_X expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::X, @1, $2);
      }
    | LTL_STRONG_NEXT expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_unop(::spot::tlsf_op::StrongNext, @1, $2);
      }
    // `X[n] phi` (TLSF v1.2 SS4.8): a stack of n next operators, n
    // being an integer expression (possibly a parameter).  Stored as
    // a Quantifier node so the `X[n] phi` spelling round-trips.
    | LTL_X LBRACKET expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::XStack,
               @1, $3, $5);
      }
    // Bounded temporal operators `F[a:b] phi` / `G[a:b] phi`
    | LTL_F LBRACKET expr COLON expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::FBounded,
               @1, $3, $5, $7);
      }
    | LTL_G LBRACKET expr COLON expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::GBounded,
               @1, $3, $5, $7);
      }
    | LTL_X LBRACKET_BANG expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(
               ::spot::tlsf_op::StrongXStack, @1, $3, $5);
      }
    | LTL_X LBRACKET expr BANG_RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(
               ::spot::tlsf_op::StrongXStack, @1, $3, $5);
      }
    | LTL_F LBRACKET_BANG expr COLON expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::StrongFBounded,
               @1, $3, $5, $7);
      }
    | LTL_F LBRACKET expr COLON expr BANG_RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::StrongFBounded,
               @1, $3, $5, $7);
      }
    | LTL_G LBRACKET_BANG expr COLON expr RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::StrongGBounded,
               @1, $3, $5, $7);
      }
    | LTL_G LBRACKET expr COLON expr BANG_RBRACKET expr %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_bounded(::spot::tlsf_op::StrongGBounded,
               @1, $3, $5, $7);
      }
    | AND LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::And, @1, $3, $5);
      }
    | OR LBRACKET binder_list RBRACKET expr  %prec QUANTIFIER
      {
        check_binders(res, $3);
        $$ = ::spot::tlsf_make_binders(::spot::tlsf_op::Or, @1, $3, $5);
      }
    // Error recovery for a malformed binder list: swallow the
    // `[...]` region, drop the operator, and resume parsing on the
    // body.  One rule per head, because the head token and its
    // precedence differ; they all share recover_binder()'s message so
    // that a change to it cannot leave one head behind.
    | AND LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | OR LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | KW_AND LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | KW_OR LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | KW_FORALL LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | KW_EXISTS LBRACKET error RBRACKET expr  %prec QUANTIFIER
      { $$ = recover_binder(res, @1, $5); }
    | SET_CUP LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | BIG_SET_UNION LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | SET_CAP LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | BIG_SET_INTER LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | SET_MINUS LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | BIG_SET_DIFF LBRACKET error RBRACKET expr  %prec BIG_SET
      { $$ = recover_binder(res, @1, $5); }
    | BIG_SUM LBRACKET error RBRACKET expr  %prec NUM_UNARY
      { $$ = recover_binder(res, @1, $5); }
    | BIG_SUM_LONG LBRACKET error RBRACKET expr  %prec NUM_UNARY
      { $$ = recover_binder(res, @1, $5); }
    | BIG_PROD LBRACKET error RBRACKET expr  %prec NUM_UNARY
      { $$ = recover_binder(res, @1, $5); }
    | BIG_PROD_LONG LBRACKET error RBRACKET expr  %prec NUM_UNARY
      { $$ = recover_binder(res, @1, $5); }
    | LBRACE set_elements RBRACE
      {
        $$ = ::spot::tlsf_make_set_explicit(@1, std::move($2));
      }
    | LBRACE expr DOTDOT expr RBRACE
      {
        $$ = ::spot::tlsf_make_set_range(@1, $2, $4);
      }
    ;

arg_expr_list: %empty {}
             | expr
               {
                 $$.push_back(std::move($1));
               }
             | arg_expr_list COMMA expr
               {
                 $1.push_back(std::move($3));
                 $$ = std::move($1);
               }
             ;

set_elements: %empty {}
            | expr
              {
                $$.push_back(std::move($1));
              }
            | set_elements COMMA expr
              {
                $1.push_back(std::move($3));
                $$ = std::move($1);
              }
            ;

// The comma-separated binder list of a big operator, e.g. the `i, j`
// of `&&[i, j] phi`.  It is not an argument list: unlike `arg_expr_list`
// it is never empty and never accepts a trailing comma.  Whether each
// element really is a binder is checked by the head production, which
// sees the list only once it is complete.
binder_list: expr
              {
                $$.push_back(std::move($1));
              }
            | binder_list COMMA expr
              {
                $1.push_back(std::move($3));
                $$ = std::move($1);
              }
            ;

%%

void
tlsfyy::parser::error(const location_type& loc,
                     const std::string& msg)
{
  res.errors.emplace_back(loc, msg);
}

// Local Variables:
// mode: C++
// End:
