%language "C++"
%defines
%debug
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

      /// Whose inputs/outputs the next ap_decl should append to.
      /// Set by mid-rule actions on INPUTS / OUTPUTS and cleared
      /// on the matching RBRACE.
      std::vector<tlsf_ap_decl>* io_target = nullptr;

      /// Current MAIN-subsection body being filled.  Set by
      /// mid-rule actions on INITIALLY / PRESET / REQUIRE / ASSERT /
      /// GUARANTEE / ASSUME.  The vector is owned by
      /// `spec->{initially_body,...}`; `stmt` productions append
      /// to it.  Cleared (set to nullptr) on the matching RBRACE.
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
      /// the new one's location -- in O(log n) instead of an O(n^2)
      /// scan of `spec->definitions`.
      std::map<std::string, spot::location> def_first_loc;
    };
  }
}

%code
{
  #include "parsedecl.hh"
}

%token <std::string> STRING "string"
%token <std::string> IDENTIFIER "identifier"
%token <std::string> NUMBER "number"

%token INFO "INFO"
%token MAIN "MAIN"
%token GLOBAL "GLOBAL"
%token SEMICOLON ";"
%token LBRACE "{"
%token RBRACE "}"
%token LBRACKET "["
%token RBRACKET "]"
%token LPAREN "("
%token RPAREN ")"
%token EQUAL "="
%token COMMA ","
// `:` separator inside `Tag:bits` enum entries.  Reserved
// only at the enum_entry position; otherwise `:` is not a
// Spot syntax token (the LTL `X[!]` operator uses `[`, `!`,
// `]` characters, not `:`).
%token COLON ":"

%token TITLE "TITLE:"
%token DESCRIPTION "DESCRIPTION:"
%token SEMANTICS_KW "SEMANTICS:"
%token TARGET "TARGET:"
// `TAGS:` keyword, accepted as the INFO TAGS section opener.
// Format per syfco (refs/.../Reader/Parser/Info.hs tagsParser):
// comma-separated IDENTIFIER list.  TAGS is OPTIONAL -- a spec
// with no TAGS line is still valid.
%token TAGS "TAGS:"

%token PARAMETERS "PARAMETERS"
%token DEFINITIONS "DEFINITIONS"
// `enum` keyword, accepted as a def_list item INSIDE
// GLOBAL { DEFINITIONS { ... } } (NOT a top-level global_item
// -- syfco's Reader/Parser/Global.hs dispatch on
// `globalContentParser` only takes `}`, `PARAMETERS`,
// `DEFINITIONS` as top-level alternatives; enums are mixed
// in with regular defs, separated by `;`).  Format per
// syfco: `enum X = {V0:00, V1:01, ...};` -- a
// comma-separated list of `Tag:bits` pairs.  The bits width
// is the length of the first entry's bits string; subsequent
// entries must match (syfco enforces this via
// `valueParserL n = count n bitParser`).
%token ENUM "enum"
%token INPUTS "INPUTS"
%token OUTPUTS "OUTPUTS"
%token INITIALLY "INITIALLY"
%token PRESET "PRESET"
// Plural aliases for the REQUIRE/ASSERT/GUARANTEE/ASSUME
// block keywords, matching TLSF v1.1's MAIN section vocabulary
// in syfco's Reader/Parser/Component.hs (sectionParser lines map
// every alias to the same body field):
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
// `M` (LTL strong release) is intentionally NOT a reserved
// keyword at either the lexer or grammar level here -- see
// spot/parsetlsf/scantlsf.ll for the rationale (real-world
// TLSF benchmarks, notably chomp.tlsf, use single-letter
// parameter/AP names like `M`, and reserving it would
// surface a spurious "syntax error" on otherwise-valid
// specs).  Strong Release can be reintroduced by adding
// BOTH a `%token LTL_M "M"` here AND a `"M" return
// token::LTL_M;` line in scantlsf.ll.  The AST also needs a
// matching operator entry -- none currently exists in
// spot/parsetlsf/ast.hh -- so introduce that first or
// alongside the keyword so the parser has a target for the
// new token.
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
%token KW_PLUS "PLUS"
%token KW_MINUS "MINUS"
%token KW_MUL "MUL"
%token KW_DIV "DIV"
%token KW_MOD "MOD"

// TLSF built-in functions (phase 4 will fold them; for now they're
// just identifier-shaped apps).
%token FN_MIN "MIN"
%token FN_MAX "MAX"
%token FN_SIZEOF "SIZEOF"
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
%left SET_CUP
%left SET_CAP
%right SET_MINUS
%left PLUS KW_PLUS MINUS_ KW_MINUS
%right SLASH KW_DIV PERCENT KW_MOD
%left STAR KW_MUL
%precedence NUM_UNARY

%type <std::string> size
%type <std::vector<spot::tlsf_expr_ptr>> body
%type <std::vector<std::string>> arg_list
%type <std::vector<std::string>> tag_list
// Enum-related types.  `bits` is a string accumulator
// (built from `0`/`1`/`*` characters); `enum_entry` is the
// per-tag pair; `enum_entries` is the comma-separated list;
// `enum_decl` is the full `enum X = { ... };` node.
%type <std::string> bits
%type <spot::tlsf_enum_value> enum_entry
%type <std::vector<spot::tlsf_enum_value>> enum_entries
%type <spot::tlsf_enum_decl> enum_decl
%type <spot::tlsf_expr_ptr> expr
%type <std::vector<spot::tlsf_expr_ptr>> property_body
%type <std::vector<spot::tlsf_expr_ptr>> arg_expr_list
%type <std::vector<spot::tlsf_expr_ptr>> set_elements

%start tlsf

// Two shift/reduce conflicts, both resolved to the shift by Bison's
// default rule (no %prec involved), and both matching the syfco
// reference parser's maximal munch (`many1 exprParser`):
//
//  1. A `(` after a bare identifier can be the argument list of a
//     function application or the start of a juxtaposed clause.  A
//     parenthesized expression after an identifier is always a valid
//     application, so maximal munch never splits there.
//  2. An identifier after a completed definition `body` can be a
//     juxtaposed clause extending the SAME definition (multi-clause
//     bodies like full_arbiter's mone) or the head of a FOLLOWING
//     `;`-less definition.  The shift extends the body -- the
//     correct maximal munch: two juxtaposed definitions without a
//     `;` then fail at the second one's `=`, exactly where syfco
//     fails (see the def_list comment).  The semicolon separator
//     itself introduces no conflict because `def_list` is only ever
//     followed by `RBRACE`, so after an item only `;` may be shifted
//     and only `}` may reduce.
//
// Keep the count in sync if the expression grammar grows new postfix
// forms or the definition/body productions change.
%expect 2

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

section: INFO LBRACE info_items RBRACE
       | GLOBAL LBRACE global_items RBRACE
       | MAIN LBRACE main_items RBRACE
       | error SEMICOLON
       ;

info_items: %empty
          | info_items info_item
          ;

// No trailing `;` after an INFO item: the canonical reference
// parser syfco (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Info.hs,
// `infoContentParser`) treats `;` after TITLE/DESCRIPTION/SEMANTICS/
// TARGET as a SYNTAX ERROR.  Spot matches syfco exactly here, so a
// `;` in the INFO block will surface as a parse error just as it
// would in syfco.  Real-world TLSF corpora (tests/core/syfco.dir/
// chomp.tlsf, SPIReadManag.tlsf, tictactoe.tlsf, ...) match this.
info_item: TITLE STRING
           {
             res.spec->title = std::move($2);
           }
         | DESCRIPTION STRING
           {
             res.spec->description = std::move($2);
           }
         | SEMANTICS_KW semantics
         | TARGET target_kind
         | TAGS tag_list
           {
             res.spec->tags = std::move($2);
           }
         // `;` is no longer a valid INFO token (the `info_item`
         // productions above never produce a `;`), so the error
         // recovery sync token switches from SEMICOLON to RBRACE
         // here.  Falling back to `error SEMICOLON` would have
         // Bison scan past the closing `}` of the INFO block
         // searching for a `;` that cannot appear.
         | error RBRACE
         ;

// Comma-separated IDENTIFIER list for INFO TAGS.  Matches syfco's
// `commaSep tokenparser (identifier (~~))` in
// refs/.../Reader/Parser/Info.hs (tagsParser).  TAGS is OPTIONAL
// in the spec; rule-list size is "one or more" since `TAGS:` with
// no identifier would be a typo, but the source grammar still
// accepts it as a degenerate empty list (the parser would
// recover on the next expected token).
tag_list: IDENTIFIER
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
           { res.spec->semantics = ::spot::tlsf_semantics::Mealy; }
         | MOORE
           { res.spec->semantics = ::spot::tlsf_semantics::Moore; }
         | MEALY COMMA STRICT
           { res.spec->semantics = ::spot::tlsf_semantics::MealyStrict; }
         | STRICT COMMA MEALY
           { res.spec->semantics = ::spot::tlsf_semantics::MealyStrict; }
         | MEALY COMMA FINITE
           { res.spec->semantics = ::spot::tlsf_semantics::MealyFinite; }
         | FINITE COMMA MEALY
           { res.spec->semantics = ::spot::tlsf_semantics::MealyFinite; }
         | MOORE COMMA STRICT
           { res.spec->semantics = ::spot::tlsf_semantics::MooreStrict; }
         | STRICT COMMA MOORE
           { res.spec->semantics = ::spot::tlsf_semantics::MooreStrict; }
         | MOORE COMMA FINITE
           { res.spec->semantics = ::spot::tlsf_semantics::MooreFinite; }
         | FINITE COMMA MOORE
           { res.spec->semantics = ::spot::tlsf_semantics::MooreFinite; }
         ;

target_kind: MEALY { res.spec->target = ::spot::tlsf_target::Mealy; }
           | MOORE { res.spec->target = ::spot::tlsf_target::Moore; }
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

param_decl: IDENTIFIER EQUAL size SEMICOLON
            {
              res.spec->parameters.push_back(
                ::spot::tlsf_parameter_decl{@1,
                  std::move($1),
                  std::move($3)});
            }
          ;

// A DEFINITIONS block holds zero or more items.  Mirroring syfco's
// `sepBy assignmentParser (rOp ";")` (spot/parsetlsf/refs/syfco/src/
// lib/Reader/Parser/Global.hs), the `;` SEPARATES items: it is
// required between two items but the last one may omit it, so all of
// `A; B;`, `A; B`, `A;`, and a lone `A` are valid (real benchmarks
// such as M.tlsf in the project root end their last definition
// without `;`).  The `;` is therefore NOT part of `definition` /
// `enum_decl`; those rules end at their `body` / `RBRACE` and the
// optional trailing `;` is handled here.  Two items juxtaposed with
// no `;` at all are NOT a valid two-item list: the second item's
// head is munched into the first item's `body` as another clause
// (maximal munch, matching syfco's `many1 exprParser`), and the
// parse fails at the second item's `=` -- exactly where syfco fails.
def_list: %empty
        | def_list def_item
        | def_list def_item SEMICOLON
        ;

// Each entry in a DEFINITIONS block is either a regular
// function-style definition or an `enum` declaration.  The
// two are disambiguated by the leading token: definition
// starts with IDENTIFIER (followed by `(` or `=`), enum_decl
// starts with the `enum` keyword.  No LALR(1) conflict
// because IDENTIFIER and ENUM are distinct terminals.
def_item: definition
        | enum_decl
        ;

// No trailing `;`: it belongs to def_list (see above).  The last
// grammar symbol is `body` (position 6), so the def's location span
// is @1 + @6 (IDENTIFIER through the last body clause).
definition: IDENTIFIER LPAREN arg_list RPAREN EQUAL body
          {
            // TLSF specifies "one symbol = one definition" (see the
            // arXiv v1.1 paper on TLSF and the canonical
            // syfco parser's tArgs map keyed by symbol name:
            // spot/parsetlsf/refs/syfco/src/lib/Reader/Bindings.hs).
            // We enforce that here: a second DEFINITION with the
            // same name -- regardless of arity -- emits BOTH
            // diagnostics (one at the FIRST definition's location
            // warning of the shadow, one at the SECOND location
            // reporting the duplicate) and the second definition
            // is dropped.  The first one survives so any later
            // calls still expand to a real body.
            //
            // Looking up via `def_first_loc` is O(log n) in the
            // number of definitions (vs. an O(n^2) linear scan of
            // `spec->definitions`); the map also gives us the
            // original location so the shadow-warning can point
            // precisely at the FIRST occurrence.
            const std::string& name = $1;
            // Track only the LHS (the IDENTIFIER token's span, `@1`)
            // for the duplicate-detection shadow warning, so the two
            // diagnostics fire at consistent anchors: both callouts
            // point at the IDENTIFIER itself, not at one end's
            // full-LHS-to-EQUAL span.  The def's own `loc` field
            // keeps the broader `@1 + @6` span -- useful for any
            // future caller that wants a whole-def range rather
            // than just the LHS token.
            auto ins = res.def_first_loc.emplace(name, @1);
            if (!ins.second)
              {
                res.errors.emplace_back(
                  ins.first->second,
                  "definition '" + name
                  + "' is shadowed by a later re-definition");
                res.errors.emplace_back(
                  @1,
                  "definition '" + name
                  + "' is already defined");
              }
            else
              {
                // $6 carries the parsed clause list for `body` (one
                // vector slot per `(ec)` clause, possibly guarded).
                // Expansion uses clone-and-substitute
                // (translator::subst_arg) plus guarded-clause
                // selection (translator::select_def_clause).
                res.spec->definitions.push_back(
                  ::spot::tlsf_definition{@1 + @6,
                    std::move($1),
                    std::move($3),
                    std::move($6)});
              }
          }
          ;

// `enum` declaration: `enum X = { V0:bits0, V1:bits1, ... };` -- the
// trailing `;` belongs to def_list (see above), so the last grammar
// symbol is `RBRACE` (position 6) and the location span is @1+@6
// (ENUM through the closing brace).  Symbol positions:
// 1=ENUM, 2=IDENTIFIER(name), 3=EQUAL, 4=LBRACE, 5=enum_entries,
// 6=RBRACE.  $2 carries the name (typed), $5 carries the entries
// (typed).  The action side-effects by appending to
// `res.spec->enumerations` (mirroring the `definition:` rule's
// pattern of pushing onto `res.spec->definitions`); the
// `$$ = ...` assignment is then unused by the parent
// `def_item` rule but is kept so the typed value is available
// to Bison's default %type machinery.
enum_decl: ENUM IDENTIFIER EQUAL LBRACE enum_entries RBRACE
           {
             ::spot::tlsf_enum_decl decl{ @1 + @6,
                   std::move($2),
                   std::move($5) };
             res.spec->enumerations.push_back(std::move(decl));
             $$ = ::spot::tlsf_enum_decl{ @1 + @6, "", {} };
           }
           ;

// Comma-separated enum_entries list.  Mirrors the structure
// of `arg_list` (commas between entries, no leading/trailing
// comma tolerated).  Syfco allows an empty enum
// (`enum X = {};`); we mirror with `enum_entries: %empty` in
// a follow-up.  For now, an empty enum is rejected -- the
// grammar matches one or more entries.
enum_entries: enum_entry
              {
                $$.push_back(std::move($1));
              }
            | enum_entries COMMA enum_entry
              {
                $1.push_back(std::move($3));
                $$ = std::move($1);
              }
            ;

// One `Tag:bits` pair.  Symbol positions: 1=IDENTIFIER(tag),
// 2=COLON, 3=bits.  $1=tag, $3=bits.  Location @1+@3
// covers the entry.
enum_entry: IDENTIFIER COLON bits
            {
              $$ = ::spot::tlsf_enum_value{ @1 + @3,
                    std::move($1),
                    std::move($3) };
            }
            ;

// `bits` is a sequence of `0`, `1`, and `*` characters,
// accumulated into a std::string.  Reuses the existing
// NUMBER token (which matches `[0-9]+` -- e.g. `0`, `1`,
// `00`, `01`, etc.) and the existing STAR token (the
// multiplication operator).  No new lexer token needed;
// this keeps single-bit numbers in expressions (`0`, `1`)
// tokenising as NUMBER rather than introducing an enum-
// context-specific lexer.  The recursive accumulation
// requires the parser to shift on NUMBER/STAR after `bits`,
// which Bison resolves by default (shift over reduce).
bits: NUMBER       { $$ = std::move($1); }
    | STAR         { $$ = "*"; }
    | bits NUMBER  { $$ = $1 + $2; }
    | bits STAR    { $$ = $1 + "*"; }
    ;

// Right-hand side of a DEFINITION.  TLSF v1.2 SS4.6 allows one or
// more (possibly guarded) clauses `(ec)+` with `ec = e | eB : e |
// eP : e`; the canonical syfco reference parser
// (spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs
// `reminderParser`) parses the body with `many1 exprParser`, i.e.
// the clauses are juxtaposed maximal expressions.  The `body` rule
// below mirrors that list shape: each clause is a full `expr` (a
// guarded clause is an `expr COLON expr`, see the Guard production
// in the expression rules), and consecutive clauses are simply
// juxtaposed.  The translator keeps one clause per `tlsf_definition`
// body slot and selects the first whose guard holds at expansion
// time (translator::select_def_clause in translate.cc).
//
// Quoted-string RHS is NOT accepted here; the STRING token remains
// in the grammar only for `INFO { TITLE: "..."; DESCRIPTION:
// "..."; }`.
// Both rules carry the loosest precedence (%prec COLON) so that the
// reduce-versus-shift conflicts between "this expression is a complete
// clause" and "this infix operator extends the current expression" are
// resolved by precedence in favor of the shift: an infix operator can
// never start a new clause, so a completed clause followed by one is
// always a longer maximal expression (matching syfco's many1
// exprParser).  See the %expect note above for the one conflict that
// precedence cannot resolve.
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

// `arg_list` is the formal-parameter list of a DEFINITION.  TLSF
// uses comma separation here, matching `arg_expr_list` (the actual
// argument list at App call sites) and syfco's `commaSep tokenparser`
// combinator in spot/parsetlsf/refs/syfco/src/lib/Reader/Parser/Global.hs.
// Whitespace alone is NOT a separator: `Pos(grid i j)` would be
// rejected by every other TLSF tool.
arg_list: %empty {}
        | IDENTIFIER
          {
            // Push directly into `$$` (default-constructed by Bison
            // as an empty std::vector) rather than build a stack
            // local first and move it in: the local-and-double-move
            // pattern can leave Bison's variant in a partially
            // populated state on some compilers, and using `$$`
            // directly matches the working `arg_list COMMA IDENTIFIER`
            // pattern below.
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

ap_list: %empty
       | ap_list ap_decl
       ;

ap_decl: IDENTIFIER SEMICOLON
         {
           if (res.io_target)
             res.io_target->push_back(
               ::spot::tlsf_ap_decl{@1, std::move($1), std::string()});
         }
       | IDENTIFIER LBRACKET size RBRACKET SEMICOLON
         {
           if (res.io_target)
             res.io_target->push_back(
               ::spot::tlsf_ap_decl{@1, std::move($1), std::move($3)});
         }
       ;

// `size` is the bus-size expression in `name[size]`.  TLSF permits
// integer literals AND parameter names AND arithmetic
// combinations thereof -- chomp.tlsf has `os[N*M]`, for instance.
// Pure arithmetic -- arithmetic ops and parens -- so the size
// cannot accidentally swallow a boolean subterm.  Left-assoc;
// the existing `%left "+" "-"` / `%left "*" "/" "%"`
// declarations carry over because precedence is keyed on
// tokens.
//
// TODO(limitation): the `size` non-terminal stringifies
// without tracking explicit grouping heuristics, so a source
// like `os[(N+1)*M]` (user parens around N+1 to force
// `(N+1)*M` precedence) round-trips through parse-deparse
// as `os[N+1*M]` and re-parses with left-assoc as
// `N + (1*M)`, changing semantics.  chomp.tlsf's bus-sizes
// are all bare arithmetic (`os[N*M]`), so the round-trip is
// value-preserving on that corpus.  Future work: replace the
// string-based size with a small AST node carrying a
// `parenthesized` flag, so any user-supplied grouping is
// preserved verbatim through deparse.  Until then, prefer
// rewriting user-supplied grouped sizes to bare arithmetic
// before testing against the deparser.
size: NUMBER      { $$ = std::move($1); }
    | IDENTIFIER  { $$ = std::move($1); }
    | LPAREN size RPAREN { $$ = "(" + $2 + ")"; }
    | size PLUS size     %prec PLUS { $$ = $1 + " + " + $3; }
    | size KW_PLUS size  %prec KW_PLUS { $$ = $1 + " + " + $3; }
    | size MINUS_ size   %prec MINUS_ { $$ = $1 + " - " + $3; }
    | size KW_MINUS size %prec KW_MINUS { $$ = $1 + " - " + $3; }
    | size STAR size     %prec STAR { $$ = $1 + " * " + $3; }
    | size KW_MUL size   %prec KW_MUL { $$ = $1 + " * " + $3; }
    | size SLASH size    %prec SLASH { $$ = $1 + " / " + $3; }
    | size KW_DIV size   %prec KW_DIV { $$ = $1 + " / " + $3; }
    | size PERCENT size  %prec PERCENT { $$ = $1 + " % " + $3; }
    | size KW_MOD size   %prec KW_MOD { $$ = $1 + " % " + $3; }
    ;

// ----- property body (semicolon-terminated formulas) -----------------
property_body: %empty {}
            | property_body stmt
            ;

stmt: expr SEMICOLON
     {
       if (res.current_body)
         res.current_body->push_back(std::move($1));
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
            // truncating to 0 (SyFCo's `read` throws here too).
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
    | FN_MIN LPAREN arg_expr_list RPAREN %prec NUM_UNARY
      {
        $$ = ::spot::tlsf_make_app(@1, "MIN", std::move($3));
      }
    | FN_MAX LPAREN arg_expr_list RPAREN %prec NUM_UNARY
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
    | SET_CUP LBRACKET arg_expr_list RBRACKET
      {
        $$ = ::spot::tlsf_make_nary_setop(
          ::spot::tlsf_op::SetUnion, @1, std::move($3));
      }
    | SET_CAP LBRACKET arg_expr_list RBRACKET
      {
        $$ = ::spot::tlsf_make_nary_setop(
          ::spot::tlsf_op::SetIntersection, @1, std::move($3));
      }
    | SET_MINUS LBRACKET arg_expr_list RBRACKET
      {
        $$ = ::spot::tlsf_make_nary_setop(
          ::spot::tlsf_op::SetDifference, @1, std::move($3));
      }
    // `SIZEOF <expr>` -- the canonical TLSF form when the argument
    // is a single token (chomp.tlsf's `(SIZEOF sel)`, for
    // instance).  This production subsumes the historical
    // `SIZEOF(arg_list)` form: when written with parens the
    // argument parses as a primary `( ... )` expression inside
    // `expr`, so a separate parenthesised production would
    // collide with this one (LALR(1) shift/reduce on `RPAREN`
    // between `arg_expr_list` and `(...)`).  Unifying on the
    // bare-arg form keeps the parser unambiguous and lets
    // `tlsf_print_expr` round-trip both spellings identically.
    // Precedence ties to BANG so `SIZEOF !x` parses as
    // `SIZEOF(!x)` rather than `(SIZEOF! x)`.
    | FN_SIZEOF expr %prec NUM_UNARY
      {
        std::vector< ::spot::tlsf_expr_ptr> args;
        args.push_back(std::move($2));
        $$ = ::spot::tlsf_make_app(@1, "SIZEOF", std::move(args));
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
    | KW_AND LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::And, @1, $3, $5);
      }
    | KW_OR LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::Or, @1, $3, $5);
      }
    | KW_FORALL LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::And, @1, $3, $5);
      }
    | KW_EXISTS LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::Or, @1, $3, $5);
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
    | AND LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::And, @1, $3, $5);
      }
    | OR LBRACKET expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::Or, @1, $3, $5);
      }
    // Quantifier range `&&[lo..hi] body` / `||[lo..hi] body`:
    // un-braced form not yet supported by Spot's `expr`
    // grammar (DOTDOT is only valid inside `{...}` set ranges);
    // adding parallel productions here lets a bare range flow
    // directly into the quantifier bound.  We synthesise a
    // SetRange AST node ($3..$4) so the body's quantifier slot
    // gets the SAME shape a `{lo..hi}` SetExplicit would, and
    // the deparser emits `&&[{lo..hi}] body` (round-trip
    // idempotent because `expr: {expr DOTDOT expr}` parses
    // that exactly).  No LALR(1) conflict: after `expr`,
    // `LBRACKET` is the existing reduction choice in the
    // quantifier context, `DOTDOT` is the new one -- distinct
    // terminals.
    | AND LBRACKET expr DOTDOT expr RBRACKET expr  %prec QUANTIFIER
      {
        // Symbol positions: 1=AND, 2=LBRACKET, 3=lo expr,
        // 4=DOTDOT, 5=hi expr, 6=RBRACKET, 7=body expr.  $4/$6
        // refer to the untyped DOTDOT/RBRACKET punctuation tokens,
        // so they cannot be used as semantic values; lo=$3, hi=$5,
        // body=$7 here.
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::And, @1,
               ::spot::tlsf_make_set_range(@3 + @5, $3, $5), $7);
      }
    | OR LBRACKET expr DOTDOT expr RBRACKET expr  %prec QUANTIFIER
      {
        $$ = ::spot::tlsf_make_quantifier(::spot::tlsf_op::Or, @1,
               ::spot::tlsf_make_set_range(@3 + @5, $3, $5), $7);
      }
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
