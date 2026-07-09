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
#include "translate.hh"
#include <spot/tl/formula.hh>
#include <spot/tl/apcollect.hh>
#include <algorithm>
#include <cctype>
#include <cstdint>
#include <limits>
#include <sstream>
#include <utility>

namespace spot
{
  namespace tlsf
  {
    namespace
    {
      unsigned long long integer_range_span(long long lower,
                                            long long upper)
      {
        assert(lower <= upper);
        if (lower < 0 && upper >= 0)
          {
            const auto negative_magnitude =
              static_cast<unsigned long long>(-(lower + 1)) + 1;
            return negative_magnitude
              + static_cast<unsigned long long>(upper);
          }
        return static_cast<unsigned long long>(upper - lower);
      }

      // Return the iteration variable introduced by a quantifier bound,
      // or an empty string when the bound introduces none.  TLSF v1.2
      // requires an explicit variable, so the recognized shapes are the
      // comparison chain `lo <= i < hi` (parsed as `(lo <= i) < hi`)
      // and the membership `i in set`; variable-less bounds are
      // diagnosed at translation, and this helper only feeds the
      // shadowing used by substitution to keep such variables local.
      std::string quantifier_loop_var(const tlsf_expr& bound)
      {
        if (bound.type == tlsf_expr_type::BinaryOp
            && (bound.op == tlsf_op::Lt || bound.op == tlsf_op::Le)
            && bound.children.size() >= 2
            && bound.children[0]
            && bound.children[0]->type == tlsf_expr_type::BinaryOp
            && (bound.children[0]->op == tlsf_op::Lt
                || bound.children[0]->op == tlsf_op::Le)
            && bound.children[0]->children.size() >= 2
            && bound.children[0]->children[1]
            && bound.children[0]->children[1]->type
               == tlsf_expr_type::Identifier)
          return bound.children[0]->children[1]->name;
        if (bound.type == tlsf_expr_type::BinaryOp
            && bound.op == tlsf_op::In
            && bound.children.size() >= 2
            && bound.children[0]
            && bound.children[0]->type == tlsf_expr_type::Identifier)
          return bound.children[0]->name;
        return "";
      }

      // Safety valve for guarded recursive expansion.  The
      // translate_expr App case increments expansion_depth_ for the
      // duration of each definition application and diagnoses a
      // definition whose application depth exceeds this bound: a
      // genuinely cyclic or non-terminating body (e.g. `f(x) =
      // f(x);`) would otherwise recurse until the C++ stack
      // overflows.  Legitimate guarded recursion over shrinking
      // constant arguments (full_arbiter's `mone` halves its index
      // range at each level) stays a few dozen frames deep no
      // matter how large the parameters are, so this bound cannot
      // be hit by terminating real-world definitions.  It must stay
      // low enough that a runaway body cannot overflow the C++ call
      // stack before the diagnostic fires: each nested application
      // costs several translate_expr / subst_arg frames, several KB
      // each, so 256 levels is already well past any realistic
      // guard-selected recursion depth while staying comfortably
      // inside the default stack size.
      constexpr unsigned max_def_depth = 256;

      // Total number of definition applications allowed in one
      // translation run.  A non-terminating recursion whose tree
      // grows exponentially (e.g. an unguarded `mone(bus,i,j) =
      // ... mone(bus,i,j) ...`) would blow up in size long before
      // hitting max_def_depth; this budget stops it at a bounded
      // amount of work (a few seconds of translation).
      // Terminating guarded recursion and plain macro expansion
      // use a handful of applications per use site, so the limit
      // is unreachable on real inputs.
      constexpr unsigned max_def_expansions_total = 100000;

      bool checked_add(long long lhs, long long rhs, long long& result)
      {
        if ((rhs > 0 && lhs > (std::numeric_limits<long long>::max)() - rhs)
            || (rhs < 0
                && lhs < (std::numeric_limits<long long>::min)() - rhs))
          return false;
        result = lhs + rhs;
        return true;
      }

      bool checked_sub(long long lhs, long long rhs, long long& result)
      {
        if ((rhs > 0
             && lhs < (std::numeric_limits<long long>::min)() + rhs)
            || (rhs < 0
                && lhs > (std::numeric_limits<long long>::max)() + rhs))
          return false;
        result = lhs - rhs;
        return true;
      }

      bool checked_mul(long long lhs, long long rhs, long long& result)
      {
        if (lhs == 0 || rhs == 0)
          {
            result = 0;
            return true;
          }
        if (lhs == -1)
          {
            if (rhs == (std::numeric_limits<long long>::min)())
              return false;
            result = -rhs;
            return true;
          }
        if (rhs == -1)
          {
            if (lhs == (std::numeric_limits<long long>::min)())
              return false;
            result = -lhs;
            return true;
          }
        if (lhs > 0)
          {
            if (rhs > 0)
              {
                if (lhs > (std::numeric_limits<long long>::max)() / rhs)
                  return false;
              }
            else if (lhs > (std::numeric_limits<long long>::min)() / rhs)
              return false;
          }
        else if (rhs > 0)
          {
            if (lhs < (std::numeric_limits<long long>::min)() / rhs)
              return false;
          }
        else if (lhs < (std::numeric_limits<long long>::max)() / rhs)
          return false;
        result = lhs * rhs;
        return true;
      }
    }


    translator::translator(const tlsf_ast& ast,
                           const tlsf_translator_options& opts,
                           parse_tlsf_error_list* errors)
      : ast_(ast), opts_(opts), errors_(errors)
    {
    }

    translator::~translator() = default;

    void translator::diag(const spot::location& loc,
                          const std::string& msg)
    {
      if (diags_quiet_)
        return;
      failed_ = true;
      if (!errors_)
        return;
      errors_->emplace_back(loc, msg);
    }

    void translator::diag(const tlsf_expr& e, const std::string& msg)
    {
      diag(e.loc, msg);
    }

    tlsf_expr_ptr
    translator::subst_arg(const tlsf_expr_ptr& body,
                          const std::string& arg_name,
                          const tlsf_expr_ptr& replacement,
                          const std::set<std::string>& shadowed)
    {
      if (!body)
        return nullptr;
      // Free identifier matching the formal arg => splice in the
      // actual argument tree.  Identifiers in `shadowed` (e.g. a
      // quantifier's loop variable) are skipped so a body containing
      // its own quantifier remains intact.
      if (body->type == tlsf_expr_type::Identifier
          && body->name == arg_name
          && !shadowed.count(arg_name))
        return replacement;

      auto clone = std::make_shared<tlsf_expr>();
      if (body->type == tlsf_expr_type::BusRef
          && body->name == arg_name
          && !shadowed.count(arg_name)
          && replacement->type == tlsf_expr_type::Identifier)
        clone->name = replacement->name;
      std::set<std::string> child_shadowed = shadowed;
      if (body->type == tlsf_expr_type::Quantifier
          && body->children.size() >= 2 && body->children[0])
        {
          // A quantified identifier is local to both its bound and
          // body, so substitution must leave it intact.  Variable-less
          // bounds are diagnosed at translation and introduce nothing
          // to shadow.
          const std::string var = quantifier_loop_var(*body->children[0]);
          if (!var.empty())
            child_shadowed.insert(var);
        }
      clone->loc = body->loc;
      clone->type = body->type;
      // Only copy the payload-bearing field for this node kind.
      // Copying all three unconditionally (val, name, op) bled
      // stale data across kinds when the body was reused across
      // substitutions; switching here guarantees a clone carries
      // exactly what is meaningful for its tag.
      switch (body->type)
        {
        case tlsf_expr_type::LiteralInt:
          clone->val = body->val;
          break;
        case tlsf_expr_type::Identifier:
        case tlsf_expr_type::BusRef:
        case tlsf_expr_type::App:
          if (!(body->type == tlsf_expr_type::BusRef
                && body->name == arg_name
                && !shadowed.count(arg_name)
                && replacement->type == tlsf_expr_type::Identifier))
            clone->name = body->name;
          break;
        case tlsf_expr_type::UnaryOp:
        case tlsf_expr_type::BinaryOp:
        case tlsf_expr_type::Quantifier:
          clone->op = body->op;
          break;
        case tlsf_expr_type::SetExplicit:
        case tlsf_expr_type::SetRange:
          // No extra payload: only the children vector is
          // meaningful, and it is filled in below.
          break;
        }
      clone->parenthesized = body->parenthesized;
      // A Quantifier keeps exactly its [bound, body] children here;
      // both are substituted like any other child.
      for (size_t i = 0; i < body->children.size(); ++i)
        clone->children.push_back(
          subst_arg(body->children[i], arg_name, replacement,
                    child_shadowed));
      return clone;
    }

    bool translator::eval_int_string(const std::string& s,
                                     long long& out)
    {
      class parser
      {
      public:
        explicit parser(const std::string& text)
          : text_(text)
        {
        }

        tlsf_expr_ptr parse()
        {
          auto result = parse_additive();
          skip_space();
          if (!result || pos_ != text_.size())
            return nullptr;
          return result;
        }

      private:
        void skip_space()
        {
          while (pos_ < text_.size()
                 && std::isspace(static_cast<unsigned char>(text_[pos_])))
            ++pos_;
        }

        bool take(char c)
        {
          skip_space();
          if (pos_ >= text_.size() || text_[pos_] != c)
            return false;
          ++pos_;
          return true;
        }

        tlsf_expr_ptr parse_additive()
        {
          auto result = parse_multiplicative();
          while (result)
            {
              skip_space();
              if (pos_ >= text_.size()
                  || (text_[pos_] != '+' && text_[pos_] != '-'))
                break;
              char op = text_[pos_++];
              auto rhs = parse_multiplicative();
              if (!rhs)
                return nullptr;
              result = tlsf_make_binop(
                op == '+' ? tlsf_op::Add : tlsf_op::Sub,
                spot::location(), result, rhs);
            }
          return result;
        }

        tlsf_expr_ptr parse_multiplicative()
        {
          auto result = parse_unary();
          while (result)
            {
              skip_space();
              if (pos_ >= text_.size()
                  || (text_[pos_] != '*' && text_[pos_] != '/'
                      && text_[pos_] != '%'))
                break;
              char op = text_[pos_++];
              auto rhs = parse_unary();
              if (!rhs)
                return nullptr;
              tlsf_op tag = op == '*' ? tlsf_op::Mul
                : op == '/' ? tlsf_op::Div : tlsf_op::Mod;
              result = tlsf_make_binop(tag, spot::location(), result, rhs);
            }
          return result;
        }

        tlsf_expr_ptr parse_unary()
        {
          skip_space();
          if (pos_ < text_.size()
              && (text_[pos_] == '+' || text_[pos_] == '-'))
            {
              char op = text_[pos_++];
              auto child = parse_unary();
              if (!child)
                return nullptr;
              if (op == '+')
                return child;
              return tlsf_make_binop(tlsf_op::Sub, spot::location(),
                                     tlsf_make_int(spot::location(), 0),
                                     child);
            }
          return parse_primary();
        }

        tlsf_expr_ptr parse_primary()
        {
          skip_space();
          if (pos_ >= text_.size())
            return nullptr;
          if (take('('))
            {
              auto result = parse_additive();
              if (!result || !take(')'))
                return nullptr;
              result->parenthesized = true;
              return result;
            }
          if (std::isdigit(static_cast<unsigned char>(text_[pos_])))
            {
              size_t begin = pos_++;
              while (pos_ < text_.size()
                     && std::isdigit(static_cast<unsigned char>(text_[pos_])))
                ++pos_;
              try
                {
                  return tlsf_make_int(spot::location(),
                                       std::stoll(text_.substr(
                                         begin, pos_ - begin)));
                }
              catch (...)
                {
                  return nullptr;
                }
            }
          if (std::isalpha(static_cast<unsigned char>(text_[pos_]))
              || text_[pos_] == '_' || text_[pos_] == '@')
            {
              size_t begin = pos_++;
              while (pos_ < text_.size()
                     && (std::isalnum(static_cast<unsigned char>(text_[pos_]))
                         || text_[pos_] == '_' || text_[pos_] == '@'
                         || text_[pos_] == '\''))
                ++pos_;
              return tlsf_make_ident(spot::location(),
                                     text_.substr(begin, pos_ - begin));
            }
          return nullptr;
        }

        const std::string& text_;
        size_t pos_ = 0;
      };

      auto parsed = parser(s).parse();
      if (!parsed)
        return false;
      return eval_int(*parsed, out);
    }

    tlsf_expr_ptr
    translator::expand_ast(const tlsf_expr_ptr& e)
    {
      if (!e)
        return nullptr;

      // App: only flatten user-defined def chains.  Built-in
      // helpers and unknown names pass through unchanged --
      // they are evaluated downstream in integer or domain-
      // specific positions (eval_int for MIN/MAX/SUM/PROD/
      // SIZEOF, the translate_expr App case for unknown
      // names), not at AST-shape time.
      if (e->type == tlsf_expr_type::App)
        {
          if (e->name == "MIN" || e->name == "MAX"
              || e->name == "SUM" || e->name == "PROD"
              || e->name == "SIZEOF")
            return e;
          const tlsf_definition* def = nullptr;
          for (const auto& d : ast_.definitions)
            if (d.name == e->name)
              {
                def = &d;
                break;
              }
          if (!def)
            return e;
          // Arity mismatch and unknowns are surfaced later by
          // the outer translate_expr App case via diag; here
          // we just pass the AST through unchanged.
          if (def->args.size() != e->children.size())
            return e;
          // This pass only flattens plain macro definitions: a
          // single, unguarded clause.  A guarded or multi-clause
          // body (and a recursive definition) needs the
          // guard-selecting evaluation of the translate_expr App
          // case, which may legitimately re-enter the same symbol;
          // leave the call in place for it.  translate_expr is
          // called on every definition use, so guarded defs are
          // still expanded there even when they appear nested
          // inside an actual.
          if (def->body.size() != 1)
            return e;
          const tlsf_expr_ptr& only = def->body[0];
          if (only && only->type == tlsf_expr_type::BinaryOp
              && only->op == tlsf_op::Guard)
            return e;
          // Cycle detection: a def whose body calls itself
          // (directly or transitively) trips the active_defs_
          // check.  Insert fails; we return the AST unchanged
          // so the outer translate_expr path handles the call
          // (its expansion counter diagnoses true cycles)
          // instead of recursing forever here.  Note that
          // compositional patterns like
          // `MultiUse(MyDef(a))` no longer false-trip here:
          // the OUTER App case has already expanded each
          // actual via expand_ast, so the inner MyDef(a)
          // call is flattened to its body (G a) BEFORE the
          // App case inserts MyDef into active_defs_.
          if (!active_defs_.insert(e->name).second)
            return e;
          // Eager: each actual is itself flattened first, so
          // the splice below never has to chase a nested App
          // call at subst_arg time.  Constant actuals (literals
          // and arithmetic over them) are folded to a single
          // LiteralInt first, mirroring the translate_expr App
          // case, so a constant argument tree is never re-cloned
          // on every substitution pass.
          std::vector<tlsf_expr_ptr> actuals;
          actuals.reserve(e->children.size());
          for (const auto& c : e->children)
            {
              long long v;
              if (eval_int_quiet(*c, v))
                {
                  actuals.push_back(tlsf_make_int(c->loc, v));
                  continue;
                }
              actuals.push_back(expand_ast(c));
            }
          // Substitute formals -> expanded actuals into the
          // single body clause.  Use a fresh shadowed set so we
          // don't trample on the caller's
          // quantifier-loop-var binding.
          std::set<std::string> shadowed;
          auto expanded = only;
          for (size_t i = 0; i < def->args.size(); ++i)
            expanded = subst_arg(expanded,
                                 def->args[i],
                                 actuals[i],
                                 shadowed);
          // Flatten any App calls surfaced inside the
          // substituted body (e.g., MultiUse's body has 5
          // MyDef(x) leaves) so translate_expr never has to
          // re-fire the App case on them.
          expanded = expand_ast(expanded);
          active_defs_.erase(e->name);
          return expanded;
        }

      // All other node types -- Identifier, BusRef, UnaryOp,
      // BinaryOp, Quantifier, SetExplicit, SetRange,
      // LiteralInt -- are cloned structurally with expand_ast
      // applied to children, so any nested App call also gets
      // flattened.  BusRef indices and Quantifier bounds pass
      // through unchanged at this layer: their integer
      // evaluation happens later by translate_expr via
      // eval_int.
      auto clone = std::make_shared<tlsf_expr>();
      clone->loc = e->loc;
      clone->type = e->type;
      switch (e->type)
        {
        case tlsf_expr_type::LiteralInt:
          clone->val = e->val;
          break;
        case tlsf_expr_type::Identifier:
        case tlsf_expr_type::BusRef:
        case tlsf_expr_type::App:
          clone->name = e->name;
          break;
        case tlsf_expr_type::UnaryOp:
        case tlsf_expr_type::BinaryOp:
        case tlsf_expr_type::Quantifier:
          clone->op = e->op;
          break;
        case tlsf_expr_type::SetExplicit:
        case tlsf_expr_type::SetRange:
          // No extra payload: only the children vector is
          // meaningful, and it is filled in below.
          break;
        }
      clone->parenthesized = e->parenthesized;
      for (size_t i = 0; i < e->children.size(); ++i)
        clone->children.push_back(expand_ast(e->children[i]));
      return clone;
    }

    const tlsf_ap_decl*
    translator::find_decl(const std::string& name) const
    {
      for (const auto& d : ast_.inputs)
        if (d.name == name)
          return &d;
      for (const auto& d : ast_.outputs)
        if (d.name == name)
          return &d;
      return nullptr;
    }

    bool translator::base_is_output(const std::string& name) const
    {
      for (const auto& d : ast_.outputs)
        if (d.name == name)
          return true;
      return false;
    }

    bool translator::eval_set(const tlsf_expr& e,
                              std::vector<long long>& out)
    {
      if (e.type == tlsf_expr_type::SetExplicit)
        {
          for (const auto& child : e.children)
            {
              if (!child)
                {
                  diag(e, "null element in integer set");
                  return false;
                }
              long long value;
              if (!eval_int(*child, value))
                return false;
              if (std::find(out.begin(), out.end(), value) == out.end())
                out.push_back(value);
            }
          return true;
        }
      if (e.type == tlsf_expr_type::SetRange
          && e.children.size() >= 2 && e.children[0]
          && e.children[1])
        {
          long long lower;
          long long upper;
          if (!eval_int(*e.children[0], lower)
              || !eval_int(*e.children[1], upper))
            return false;
          if (lower > upper)
            return true;
          const auto span = integer_range_span(lower, upper);
          if (span >= 1000000)
            {
              diag(e, "integer set range is too large");
              return false;
            }
          long long value = lower;
          while (true)
            {
              out.push_back(value);
              if (value == upper)
                break;
              ++value;
            }
          return true;
        }
      if (e.type == tlsf_expr_type::BinaryOp
          && (e.op == tlsf_op::SetUnion
              || e.op == tlsf_op::SetIntersection
              || e.op == tlsf_op::SetDifference)
          && e.children.size() >= 2)
        {
          std::vector<long long> lhs;
          std::vector<long long> rhs;
          if (!eval_set(*e.children[0], lhs)
              || !eval_set(*e.children[1], rhs))
            return false;
          if (e.op == tlsf_op::SetUnion)
            {
              out = lhs;
              for (long long value : rhs)
                if (std::find(out.begin(), out.end(), value) == out.end())
                  out.push_back(value);
            }
          else if (e.op == tlsf_op::SetIntersection)
            {
              for (long long value : lhs)
                if (std::find(rhs.begin(), rhs.end(), value) != rhs.end())
                  out.push_back(value);
            }
          else
            {
              for (long long value : lhs)
                if (std::find(rhs.begin(), rhs.end(), value) == rhs.end())
                  out.push_back(value);
            }
          return true;
        }
      diag(e, "expected an integer set");
      return false;
    }

    bool translator::eval_int_quiet(const tlsf_expr& e, long long& out)
    {
      const bool saved = diags_quiet_;
      diags_quiet_ = true;
      const bool ok = eval_int(e, out);
      diags_quiet_ = saved;
      return ok;
    }

    bool translator::eval_set_quiet(const tlsf_expr& e,
                                    std::vector<long long>& out)
    {
      const bool saved = diags_quiet_;
      diags_quiet_ = true;
      const bool ok = eval_set(e, out);
      diags_quiet_ = saved;
      return ok;
    }

    int translator::eval_guard_bool(const tlsf_expr& g)
    {
      switch (g.type)
        {
        case tlsf_expr_type::LiteralInt:
          // Guards are Boolean expressions; a bare literal is only
          // meaningful as 0/1.  Anything else is treated as true so
          // the comparison stays total.
          return g.val != 0;
        case tlsf_expr_type::Identifier:
          if (g.name == "true")
            return 1;
          if (g.name == "false")
            return 0;
          // An identifier bound to an integer (parameter, loop
          // variable) may be used as a guard; a bound value of 0 is
          // the only "false" case.
          {
            long long v;
            if (eval_int_quiet(g, v))
              return v != 0;
          }
          return -1;
        case tlsf_expr_type::UnaryOp:
          if (g.op == tlsf_op::Not && !g.children.empty()
              && g.children[0])
            {
              int c = eval_guard_bool(*g.children[0]);
              return c < 0 ? -1 : !c;
            }
          return -1;
        case tlsf_expr_type::BinaryOp:
          if (g.children.size() < 2 || !g.children[0]
              || !g.children[1])
            return -1;
          switch (g.op)
            {
            case tlsf_op::And:
              {
                int l = eval_guard_bool(*g.children[0]);
                int r = eval_guard_bool(*g.children[1]);
                if (l == 0 || r == 0)
                  return 0;
                if (l < 0 || r < 0)
                  return -1;
                return 1;
              }
            case tlsf_op::Or:
              {
                int l = eval_guard_bool(*g.children[0]);
                int r = eval_guard_bool(*g.children[1]);
                if (l == 1 || r == 1)
                  return 1;
                if (l < 0 || r < 0)
                  return -1;
                return 0;
              }
            case tlsf_op::Eq:
            case tlsf_op::Neq:
            case tlsf_op::Lt:
            case tlsf_op::Le:
            case tlsf_op::Gt:
            case tlsf_op::Ge:
              {
                long long l;
                long long r;
                if (!eval_int_quiet(*g.children[0], l)
                    || !eval_int_quiet(*g.children[1], r))
                  return -1;
                switch (g.op)
                  {
                  case tlsf_op::Eq:
                    return l == r;
                  case tlsf_op::Neq:
                    return l != r;
                  case tlsf_op::Lt:
                    return l < r;
                  case tlsf_op::Le:
                    return l <= r;
                  case tlsf_op::Gt:
                    return l > r;
                  default:
                    return l >= r;
                  }
              }
            case tlsf_op::In:
              {
                long long v;
                std::vector<long long> values;
                if (!eval_int_quiet(*g.children[0], v)
                    || !eval_set_quiet(*g.children[1], values))
                  return -1;
                return std::find(values.begin(), values.end(), v)
                  != values.end();
              }
            default:
              return -1;
            }
        default:
          return -1;
        }
    }

    tlsf_expr_ptr translator::select_def_clause(
      const tlsf_definition& def,
      const std::vector<tlsf_expr_ptr>& actuals,
      const tlsf_expr& call)
    {
      // Grammar invariant: a definition accepted by the parser
      // carries at least one body clause.
      assert(!def.body.empty());
      std::set<std::string> shadowed;
      for (const tlsf_expr_ptr& raw_clause : def.body)
        {
          // Substitute the (pre-expanded) actuals into this clause
          // before inspecting its guard, so guards over formal
          // integer arguments become constant comparisons.
          tlsf_expr_ptr clause = raw_clause;
          for (size_t i = 0; i < def.args.size(); ++i)
            clause = subst_arg(clause, def.args[i], actuals[i],
                               shadowed);
          if (clause->type == tlsf_expr_type::BinaryOp
              && clause->op == tlsf_op::Guard
              && clause->children.size() >= 2 && clause->children[0]
              && clause->children[1])
            {
              const tlsf_expr_ptr& body = clause->children[1];
              const tlsf_expr& guard = *clause->children[0];
              // `otherwise` is the catch-all guard: it holds iff
              // every earlier clause's guard was false, which is
              // exactly the situation when the scan reaches it.
              if (guard.type == tlsf_expr_type::Identifier
                  && guard.name == "otherwise")
                return body;
              const int v = eval_guard_bool(guard);
              if (v < 0)
                {
                  diag(guard, "definition '" + def.name
                         + "' guard is not statically decidable; "
                         "guards must be comparisons, memberships,"
                         " or boolean combinations thereof over "
                         "constant arguments, parameters, and loop "
                         "variables");
                  return nullptr;
                }
              if (v != 0)
                return body;
              continue;                 // guard false: next clause
            }
          // Unguarded clause: implicitly guarded by true.
          return clause;
        }
      diag(call, "no guard of definition '" + def.name
             + "' holds for the given arguments");
      return nullptr;
    }

    bool translator::eval_int(const tlsf_expr& e, long long& out)
    {
      switch (e.type)
        {
        case tlsf_expr_type::LiteralInt:
          out = e.val;
          return true;
        case tlsf_expr_type::Identifier:
          {
            auto lv = loop_vars_.find(e.name);
            if (lv != loop_vars_.end())
              {
                out = lv->second;
                return true;
              }
            auto pv = params_.find(e.name);
            if (pv != params_.end())
              {
                out = pv->second;
                return true;
              }
            auto pe = param_exprs_.find(e.name);
            if (pe != param_exprs_.end())
              {
                if (!active_params_.insert(e.name).second)
                  {
                    diag(e, "cyclic parameter definition involving '"
                           + e.name + "'");
                    return false;
                  }
                long long value = 0;
                bool ok = eval_int_string(pe->second, value);
                active_params_.erase(e.name);
                if (ok)
                  {
                    params_[e.name] = value;
                    out = value;
                    return true;
                  }
                diag(e, "could not evaluate parameter '" + e.name
                       + "' expression '" + pe->second + "'");
                return false;
              }
            diag(e, "expected an integer; identifier '"
                   + e.name + "' has no integer binding");
            return false;
          }
        case tlsf_expr_type::BusRef:
          diag(e, "BusRef in integer position (only loop variables, "
                 "parameters, and integer literals are valid here)");
          return false;
        case tlsf_expr_type::App:
          // TLSF built-in helpers:
          //   MIN(a,b,...)   -> min of evaluated args
          //   MAX(a,b,...)   -> max of evaluated args
          //   SUM(...)       -> sum
          //   PROD(...)      -> product
          //   SIZEOF(ap)     -> declared bus size, evaluated
          //     (for SIZEOF we treat the argument's name as a bus base)
          if (e.name == "MIN" || e.name == "MAX" || e.name == "SUM"
              || e.name == "PROD")
            {
              if (e.children.empty())
                {
                  diag(e, e.name + "() requires at least one argument");
                  return false;
                }
              long long acc = 0;
              bool first = true;
              for (const auto& c : e.children)
                {
                  long long v;
                  if (!eval_int(*c, v))
                    return false;
                  if (first)
                    {
                      acc = v;
                      first = false;
                    }
                  else
                    {
                      if (e.name == "MIN")
                        acc = std::min(acc, v);
                      else if (e.name == "MAX")
                        acc = std::max(acc, v);
                      else if (e.name == "SUM")
                        {
                          if (!checked_add(acc, v, acc))
                            {
                              diag(e, "integer overflow in SUM");
                              return false;
                            }
                        }
                      else if (e.name == "PROD")
                        {
                          if (!checked_mul(acc, v, acc))
                            {
                              diag(e, "integer overflow in PROD");
                              return false;
                            }
                        }
                    }
                }
              out = acc;
              return true;
            }
          if (e.name == "SIZEOF")
            {
              if (e.children.size() != 1)
                {
                  diag(e, "SIZEOF expects exactly one argument");
                  return false;
                }
              const auto& arg = *e.children[0];
              if (arg.type != tlsf_expr_type::Identifier)
                {
                  diag(e, "SIZEOF argument must be a bus name");
                  return false;
                }
              // Search inputs and outputs for a matching bus decl.
              for (const auto& d : ast_.inputs)
                if (d.name == arg.name)
                  {
                    if (d.size.empty())
                      {
                        diag(e, "SIZEOF of scalar AP '" + arg.name + "'");
                        return false;
                      }
                    return eval_int_string(d.size, out);
                  }
              for (const auto& d : ast_.outputs)
                if (d.name == arg.name)
                  {
                    if (d.size.empty())
                      {
                        diag(e, "SIZEOF of scalar AP '" + arg.name + "'");
                        return false;
                      }
                    return eval_int_string(d.size, out);
                  }
              diag(e, "SIZEOF: unknown bus '" + arg.name + "'");
              return false;
            }
          diag(e, "function call '" + e.name + "' is not supported "
                 "in integer position");
          return false;
        case tlsf_expr_type::UnaryOp:
          if (e.children.empty())
            {
              diag(e, "unary op with no operand");
              return false;
            }
          if (e.op == tlsf_op::Not)
            {
              // The parser does not produce unary minus/plus; we
              // neither expect nor need them here.  For symmetry we
              // map "Not" to a logical-not on the integer 0/1.
              long long v;
              if (!eval_int(*e.children[0], v))
                return false;
              out = v ? 0 : 1;
              return true;
            }
          diag(e, "unary op '" + tlsf_format_op(e.op)
                 + "' is not supported in integer position");
          return false;
        case tlsf_expr_type::BinaryOp:
          if (e.children.size() < 2)
            {
              diag(e, "binary op with fewer than two operands");
              return false;
            }
          {
            long long l;
            if (!eval_int(*e.children[0], l))
              return false;
            if (e.op == tlsf_op::In)
              {
                std::vector<long long> values;
                if (!eval_set(*e.children[1], values))
                  return false;
                out = std::find(values.begin(), values.end(), l)
                  != values.end() ? 1 : 0;
                return true;
              }
            long long r;
            if (!eval_int(*e.children[1], r))
              return false;
            switch (e.op)
              {
              case tlsf_op::Add:
                if (!checked_add(l, r, out))
                  {
                    diag(e, "integer overflow in addition");
                    return false;
                  }
                return true;
              case tlsf_op::Sub:
                if (!checked_sub(l, r, out))
                  {
                    diag(e, "integer overflow in subtraction");
                    return false;
                  }
                return true;
              case tlsf_op::Mul:
                if (!checked_mul(l, r, out))
                  {
                    diag(e, "integer overflow in multiplication");
                    return false;
                  }
                return true;
              case tlsf_op::Div:
                if (r == 0)
                  {
                    diag(e, "division by zero");
                    return false;
                  }
                if (l == (std::numeric_limits<long long>::min)() && r == -1)
                  {
                    diag(e, "integer overflow in division");
                    return false;
                  }
                out = l / r;
                return true;
              case tlsf_op::Mod:
                if (r == 0)
                  {
                    diag(e, "modulo by zero");
                    return false;
                  }
                if (l == (std::numeric_limits<long long>::min)() && r == -1)
                  {
                    diag(e, "integer overflow in modulo");
                    return false;
                  }
                out = l % r;
                return true;
              case tlsf_op::Lt:
                out = l < r ? 1 : 0;
                return true;
              case tlsf_op::Le:
                out = l <= r ? 1 : 0;
                return true;
              case tlsf_op::Gt:
                out = l > r ? 1 : 0;
                return true;
              case tlsf_op::Ge:
                out = l >= r ? 1 : 0;
                return true;
              case tlsf_op::Eq:
                out = l == r ? 1 : 0;
                return true;
              case tlsf_op::Neq:
                out = l != r ? 1 : 0;
                return true;
              default:
                diag(e, "binary op '" + tlsf_format_op(e.op)
                       + "' is not supported in integer position");
                return false;
              }
          }
        case tlsf_expr_type::Quantifier:
          diag(e, "quantifier is not an integer expression");
          return false;
        case tlsf_expr_type::SetExplicit:
        case tlsf_expr_type::SetRange:
          diag(e, "set is not an integer expression");
          return false;
        }
      diag(e, "internal: unknown tlsf_expr_type");
      return false;
    }

    spot::formula translator::translate_expr(const tlsf_expr& e)
    {
      switch (e.type)
        {
        case tlsf_expr_type::LiteralInt:
          diag(e, "integer literal in LTL position");
          return spot::formula::ff();
        case tlsf_expr_type::Identifier:
          {
            if (e.name == "true")
              return spot::formula::tt();
            if (e.name == "false")
              return spot::formula::ff();
            // Loop variables and parameters are integer-valued only;
            // they have no Boolean meaning on their own.
            if (loop_vars_.count(e.name))
              {
                diag(e, "loop variable '" + e.name
                       + "' used in LTL position");
                return spot::formula::ff();
              }
            if (params_.count(e.name))
              {
                diag(e, "parameter '" + e.name
                       + "' used in LTL position");
                return spot::formula::ff();
              }
            // A declared SCALAR AP used here is recorded in
            // first-use order in inputs_/outputs_ (mirroring the
            // BusRef case below): specs like tictactoe_1.tlsf
            // declare each signal flat (`cross_0;`) rather than as
            // a bus (`ix[N];`) and reference it as a plain
            // identifier.  A declared BUS base, by contrast, is not
            // an AP -- only its flattened `base_index` references
            // are -- so it is left for the BusRef case to record.
            // Undeclared identifiers currently pass through as
            // fresh APs without being recorded (see the roadmap on
            // the handling of undeclared identifiers).
            const std::string& base = e.name;
            const tlsf_ap_decl* decl = find_decl(base);
            if (decl && decl->size.empty())
              {
                bool is_out = base_is_output(base);
                if (is_out)
                  {
                    if (seen_outputs_.insert(base).second)
                      outputs_.push_back(base);
                  }
                else if (seen_inputs_.insert(base).second)
                  inputs_.push_back(base);
              }
            return spot::formula::ap(base);
          }
        case tlsf_expr_type::BusRef:
          {
            // Flatten bus[i] to "base_index" and emit as AP.
            if (e.children.empty())
              {
                diag(e, "bus reference '"
                       + e.name + "' missing its index expression");
                return spot::formula::ff();
              }
            long long idx;
            if (!eval_int(*e.children[0], idx))
              return spot::formula::ff();
            const tlsf_ap_decl* decl = find_decl(e.name);
            if (!decl)
              {
                diag(e, "indexed reference uses undeclared bus '"
                       + e.name + "'");
                return spot::formula::ff();
              }
            if (decl->size.empty())
              {
                diag(e, "indexed reference uses scalar AP '"
                       + e.name + "'");
                return spot::formula::ff();
              }
            long long size;
            if (!eval_int_string(decl->size, size))
              {
                diag(e, "could not evaluate size of bus '" + e.name
                       + "'");
                return spot::formula::ff();
              }
            if (size <= 0)
              {
                diag(e, "bus '" + e.name + "' has non-positive size");
                return spot::formula::ff();
              }
            if (idx < 0 || idx >= size)
              {
                diag(e, "index " + std::to_string(idx)
                       + " is outside bus '" + e.name + "' of size "
                       + std::to_string(size));
                return spot::formula::ff();
              }
            bool out = base_is_output(e.name);
            std::ostringstream flat;
            flat << e.name << '_' << idx;
            std::string name = flat.str();
            if (out)
              {
                if (seen_outputs_.insert(name).second)
                  outputs_.push_back(name);
              }
            else
              {
                if (seen_inputs_.insert(name).second)
                  inputs_.push_back(name);
              }
            return spot::formula::ap(name);
          }
        case tlsf_expr_type::App:
          {
            // Built-in helpers (MIN/MAX/SUM/PROD/SIZEOF) are folded
            // by eval_int when they appear in an integer position.
            // Here we see App in LTL position; expand a user-defined
            // definition by substituting the actual arguments into
            // its clauses and translating the body of the first
            // clause whose guard holds (see select_def_clause).
            // Unknown names surface as a diagnostic so the partial
            // result still flows through.
            //
            // TLSF enforces "one symbol = one definition" (see
            // spot/parsetlsf/parsetlsf.yy: definition semantic action
            // and the syfco tArgs map keyed by symbol name in
            // spot/parsetlsf/refs/syfco/src/lib/Reader/Bindings.hs),
            // so the lookup is by name alone.  An arity mismatch
            // gets a dedicated diagnostic that explains BOTH the
            // declared arity and the call-site arity, so the user
            // can fix the call without grepping the DEFINITIONS
            // block.
            const tlsf_definition* def = nullptr;
            for (const auto& d : ast_.definitions)
              if (d.name == e.name)
                {
                  def = &d;
                  break;
                }
            if (!def)
              {
                diag(e, "definition '" + e.name + "' is not defined");
                return spot::formula::ff();
              }
            if (def->args.size() != e.children.size())
              {
                diag(e, "definition '" + e.name
                       + "' expects "
                       + std::to_string(def->args.size())
                       + " argument(s); called with "
                       + std::to_string(e.children.size()));
                return spot::formula::ff();
              }
            // Recursion is legitimate in TLSF: a guarded definition
            // may call itself while its constant arguments shrink
            // toward the base case selected by the guards (e.g.
            // full_arbiter.tlsf's `mone` halves its index range at
            // every level).  We therefore do NOT reject re-entry
            // into a definition that is already being expanded;
            // expansion_depth_ below bounds the recursion depth and
            // expansion_total_ bounds the total work, so bodies that
            // never reach a base case get diagnosed instead of
            // hanging.  Once either bound trips, expansion_exhausted_
            // goes sticky: every later definition application returns
            // ff() silently and only the first overflow is reported,
            // so a non-terminating spec yields one diagnostic rather
            // than one per call site.
            if (expansion_exhausted_)
              return spot::formula::ff();
            // The depth limit trips on whichever App happens to
            // overflow -- for a recursive definition that is often a
            // LEAF call inside the cyclic def's own clause (e.g. the
            // `none` calls inside full_arbiter's recursive `mone`),
            // which would misattribute the cycle.  Record the name of
            // the def that STARTED the current expansion chain (the
            // first App seen at depth 0) and report that one.
            if (expansion_depth_ == 0)
              expansion_root_name_ = e.name;
            if (++expansion_depth_ > max_def_depth
                || ++expansion_total_ > max_def_expansions_total)
              {
                expansion_exhausted_ = true;
                diag(e, "definition expansion limit exceeded; "
                        "the expansion of definition '"
                        + expansion_root_name_ + "' is cyclic or "
                        "does not reach a base case");
                --expansion_depth_;
                return spot::formula::ff();
              }
            // Fold constant actuals (literals, parameters, loop
            // variables, and arithmetic over them -- e.g. the
            // `(i+j)/2+1` arguments of full_arbiter.tlsf's
            // recursive mone calls) to a single LiteralInt BEFORE
            // splicing them into the next clause.  Without this,
            // every recursion level would wrap the previous
            // argument tree in one more layer of arithmetic:
            // subst_arg embeds the actual into the substituted
            // clause, so the argument trees form a chain as deep
            // as the recursion, and every subsequent substitution,
            // clone, and destruction re-walks it -- turning
            // terminating recursion into O(depth^2) work with
            // unbounded stack depth.  Folding keeps the substituted
            // clauses constant-sized: guarded recursion (e.g.
            // full_arbiter's mone) costs O(1) per level, and
            // unguarded self-calls trip the depth/total budgets
            // immediately instead of grinding through ever-deeper
            // trees.
            //
            // Non-constant actuals fall through to the eager
            // expansion below (the same `expand_ast` the App case
            // performs); compositional patterns like
            // `MultiUse(MyDef(a))` depend on it so the substituted
            // clause never carries a nested App that would trip
            // `active_defs_` in expand_ast.  expand_ast returns
            // non-App expressions unchanged (Identifier, BusRef,
            // App to builtins, etc.), so this is a safe no-op when
            // the actual is a leaf.
            std::vector<tlsf_expr_ptr> actuals;
            actuals.reserve(e.children.size());
            for (const auto& c : e.children)
              {
                long long v;
                if (eval_int_quiet(*c, v))
                  {
                    actuals.push_back(tlsf_make_int(c->loc, v));
                    continue;
                  }
                actuals.push_back(expand_ast(c));
              }
            // Select the first clause whose guard holds for these
            // actuals and translate its value (recursive calls
            // re-enter this App case, bounded by the expansion
            // depth and total-work budgets).
            tlsf_expr_ptr chosen =
              select_def_clause(*def, actuals, e);
            if (!chosen)
              {
                --expansion_depth_;
                return spot::formula::ff();
              }
            // Translate the selected clause while this application
            // is still on the expansion stack, so nested calls to
            // the same (or any) definition accumulate depth.
            spot::formula res = translate_expr(*chosen);
            --expansion_depth_;
            return res;
          }
        case tlsf_expr_type::UnaryOp:
          {
            if (e.children.empty())
              {
                diag(e, "unary op with no operand");
                return spot::formula::ff();
              }
            spot::formula c = translate_expr(*e.children[0]);
            switch (e.op)
              {
              case tlsf_op::Not:
                return spot::formula::Not(c);
              case tlsf_op::G:
                return spot::formula::G(c);
              case tlsf_op::F:
                return spot::formula::F(c);
              case tlsf_op::X:
                return spot::formula::X(c);
              case tlsf_op::StrongNext:
                if (ast_.semantics != tlsf_semantics::MealyFinite
                    && ast_.semantics != tlsf_semantics::MooreFinite)
                  {
                    diag(e, "strong next X[!] requires finite semantics");
                    return spot::formula::ff();
                  }
                return spot::formula::strong_X(c);
              default:
                diag(e, "unary op '" + tlsf_format_op(e.op)
                       + "' is not supported in LTL position");
                return spot::formula::ff();
              }
          }
        case tlsf_expr_type::BinaryOp:
          {
            if (e.children.size() < 2)
              {
                diag(e, "binary op with fewer than two operands");
                return spot::formula::ff();
              }
            // Comparison and arithmetic operators decide based on
            // context.  Spot has no Eq/Lt/etc. operators, so anything
            // not collapsible to a Boolean subterm gets a diagnostic.
            switch (e.op)
              {
              case tlsf_op::And:
              case tlsf_op::Or:
              case tlsf_op::Implies:
              case tlsf_op::Equiv:
              case tlsf_op::U:
              case tlsf_op::R:
              case tlsf_op::W:
                {
                  spot::formula l = translate_expr(*e.children[0]);
                  spot::formula r = translate_expr(*e.children[1]);
                  switch (e.op)
                    {
                    case tlsf_op::And:
                      return spot::formula::And({l, r});
                    case tlsf_op::Or:
                      return spot::formula::Or({l, r});
                    case tlsf_op::Implies:
                      return spot::formula::Implies(l, r);
                    case tlsf_op::Equiv:
                      return spot::formula::Equiv(l, r);
                    case tlsf_op::U:
                      return spot::formula::U(l, r);
                    case tlsf_op::R:
                      return spot::formula::R(l, r);
                    case tlsf_op::W:
                      return spot::formula::W(l, r);
                    default:
                      SPOT_UNREACHABLE();
                    }
                }
              case tlsf_op::Add:
              case tlsf_op::Sub:
              case tlsf_op::Mul:
              case tlsf_op::Div:
              case tlsf_op::Mod:
              case tlsf_op::Eq:
              case tlsf_op::Neq:
              case tlsf_op::Lt:
              case tlsf_op::Le:
              case tlsf_op::Gt:
              case tlsf_op::Ge:
                diag(e, "arithmetic/comparison op '"
                       + tlsf_format_op(e.op)
                       + "' is not supported in LTL position");
                return spot::formula::ff();
              case tlsf_op::In:
                {
                  long long value;
                  std::vector<long long> values;
                  if (!eval_int(*e.children[0], value)
                      || !eval_set(*e.children[1], values))
                    return spot::formula::ff();
                  return std::find(values.begin(), values.end(), value)
                    != values.end() ? spot::formula::tt()
                    : spot::formula::ff();
                }
              case tlsf_op::Guard:
                // A guard clause `eB : e` is meaningful only as a
                // clause of a DEFINITION body, where select_def_clause
                // strips it before translating the selected value.  A
                // survivor here means the clause escaped expansion
                // (e.g. written directly in a MAIN subsection).
                diag(e, "guard clause ':' is only meaningful inside "
                        "a definition body");
                return spot::formula::ff();
              default:
                diag(e, "unknown binary op");
                return spot::formula::ff();
              }
          }
        case tlsf_expr_type::Quantifier:
          {
            if (e.children.size() < 2 || !e.children[0]
                || !e.children[1])
              {
                diag(e, "quantifier with fewer than two operands");
                return spot::formula::ff();
              }

            // `X[n] phi` (TLSF v1.2 SS4.8): unfold the stack of n
            // next operators.  n is an integer expression evaluated
            // with the current parameter bindings.
            if (e.op == tlsf_op::XStack)
              {
                long long n;
                if (!eval_int(*e.children[0], n))
                  return spot::formula::ff();
                if (n < 0)
                  {
                    diag(e, "X[...] requires a non-negative number "
                            "of next steps");
                    return spot::formula::ff();
                  }
                spot::formula f = translate_expr(*e.children[1]);
                for (long long i = 0; i < n; ++i)
                  f = spot::formula::X(f);
                return f;
              }

            // TLSF v1.2 requires every quantifier to introduce an
            // explicit iteration variable.  The bound is kept verbatim
            // in children[0], and its two valid shapes are recognized
            // here, at translation time:
            //   * comparison chain `lo <= i < hi` (parsed as
            //     `(lo <= i) < hi`, with `<=`/`<` in any combination);
            //   * membership `i in set`, where the set is a literal,
            //     a range, or a CUP/CAP/SETMINUS combination.
            // The legacy variable-less bounds (`&&[N]`, `&&[lo..hi]`,
            // `&&[{...}]`) are not valid TLSF and are diagnosed here
            // rather than silently iterating over an implicit `i`.
            const auto& bound = *e.children[0];
            std::string variable;
            std::vector<long long> values;

            if (bound.type == tlsf_expr_type::BinaryOp
                && (bound.op == tlsf_op::Lt || bound.op == tlsf_op::Le)
                && bound.children.size() >= 2
                && bound.children[0]
                && bound.children[0]->type == tlsf_expr_type::BinaryOp
                && (bound.children[0]->op == tlsf_op::Lt
                    || bound.children[0]->op == tlsf_op::Le)
                && bound.children[0]->children.size() >= 2
                && bound.children[0]->children[1]
                && bound.children[0]->children[1]->type
                   == tlsf_expr_type::Identifier)
              {
                // Comparison chain: the variable sits on the RHS of the
                // inner comparison, and the inclusivity of each bound
                // is given by the `<=` vs `<` spellings.
                const auto& lower_cmp = *bound.children[0];
                variable = lower_cmp.children[1]->name;
                const bool lower_inclusive =
                  lower_cmp.op == tlsf_op::Le;
                const bool upper_inclusive = bound.op == tlsf_op::Le;
                long long lower;
                long long upper;
                if (!eval_int(*lower_cmp.children[0], lower)
                    || !eval_int(*bound.children[1], upper))
                  return e.op == tlsf_op::And
                    ? spot::formula::tt() : spot::formula::ff();
                if (lower <= upper)
                  {
                    const auto span = integer_range_span(lower, upper);
                    if (span >= 1000000)
                      {
                        diag(e, "quantifier range is too large");
                        return e.op == tlsf_op::And
                          ? spot::formula::tt() : spot::formula::ff();
                      }
                    values.reserve(static_cast<size_t>(span + 1));
                    long long value = lower;
                    while (true)
                      {
                        if ((lower_inclusive || value != lower)
                            && (upper_inclusive || value != upper))
                          values.push_back(value);
                        if (value == upper)
                          break;
                        ++value;
                      }
                  }
              }
            else if (bound.type == tlsf_expr_type::BinaryOp
                     && bound.op == tlsf_op::In
                     && bound.children.size() >= 2
                     && bound.children[0]
                     && bound.children[0]->type
                        == tlsf_expr_type::Identifier)
              {
                // Membership: the variable is the element expression on
                // the left of `IN`; the iteration values come from
                // evaluating the set on the right.
                variable = bound.children[0]->name;
                if (!eval_set(*bound.children[1], values))
                  return e.op == tlsf_op::And
                    ? spot::formula::tt() : spot::formula::ff();
              }
            else
              {
                diag(e, "quantifier bound must introduce an iteration "
                        "variable (e.g. `&&[0 <= i < N]` or "
                        "`&&[i IN {0, 1}]`)");
                return e.op == tlsf_op::And
                  ? spot::formula::tt() : spot::formula::ff();
              }

            auto previous = loop_vars_.find(variable);
            bool had_previous = previous != loop_vars_.end();
            long long previous_value = had_previous ? previous->second : 0;
            std::vector<spot::formula> parts;
            parts.reserve(values.size());
            for (long long value : values)
              {
                loop_vars_[variable] = value;
                parts.push_back(translate_expr(*e.children[1]));
              }
            if (had_previous)
              loop_vars_[variable] = previous_value;
            else
              loop_vars_.erase(variable);

            if (e.op == tlsf_op::And)
              return spot::formula::And(parts);
            if (e.op == tlsf_op::Or)
              return spot::formula::Or(parts);
            diag(e, "unsupported quantifier op");
            return spot::formula::ff();
          }
        case tlsf_expr_type::SetExplicit:
          diag(e, "set literal in LTL position");
          return spot::formula::ff();
        case tlsf_expr_type::SetRange:
          diag(e, "set range in LTL position");
          return spot::formula::ff();
        }
      diag(e, "internal: unhandled tlsf_expr_type");
      return spot::formula::ff();
    }

    tlsf_translation_result translator::run()
    {
      tlsf_translation_result result;

      // 1. Resolve parameters. Keep source expressions until all
      // declarations are known, so a parameter may refer to one that
      // appears later in the PARAMETERS block. Overrides take
      // precedence over declared expressions.
      for (const auto& p : ast_.parameters)
        param_exprs_[p.name] = p.value;
      for (const auto& kv : opts_.overrides)
        params_[kv.first] = kv.second;
      for (const auto& p : ast_.parameters)
        {
          if (params_.count(p.name))
            continue;
          long long value = 0;
          if (!eval_int_string(p.value, value))
            diag(p.loc, "could not evaluate parameter '" + p.name
                   + "' expression '" + p.value + "'");
          else
            params_[p.name] = value;
        }

      if (opts_.raise_errors && failed_)
        throw std::runtime_error("tlsf translator: parameter parsing "
                                 "failed");

      // 2. Translate each MAIN subsection as the conjunction of its
      //    body.  An empty body folds to tt(); a singleton body is
      //    returned as-is when wrapping in tt()∧x would just simplify
      //    to x anyway.
      auto conjunction =
        [&](const std::vector<tlsf_expr_ptr>& body) -> spot::formula
        {
          if (body.empty())
            return spot::formula::tt();
          std::vector<spot::formula> parts;
          parts.reserve(body.size());
          for (const auto& e : body)
            parts.push_back(translate_expr(*e));
          return spot::formula::And(parts);
        };

      spot::formula initially = conjunction(ast_.initially_body);
      spot::formula preset    = conjunction(ast_.preset_body);
      spot::formula require   = conjunction(ast_.require_body);
      spot::formula assumptions = conjunction(ast_.assumptions_body);
      spot::formula assertion = conjunction(ast_.assert_body);
      spot::formula guarantee = conjunction(ast_.guarantee_body);

      // Expose each subsection's translation on the result so
      // callers can inspect the individual pieces of the composed
      // formula below.
      result.initially = initially;
      result.preset = preset;
      result.require = require;
      result.assume = assumptions;
      result.assertion = assertion;
      result.guarantee = guarantee;

      if (opts_.raise_errors && failed_)
        throw std::runtime_error("tlsf translator: section "
                                 "translation failed");

      // 4. Compose the formula.
      //    REQUIRE and ASSUME form the environment side; ASSERT and
      //    GUARANTEE form the system side.  PRESET and INITIALLY are
      //    handled as the outer conditional layers.  Empty sections
      //    are represented by tt() and normalized by the formula
      //    constructors below.
      //
      //  Standard semantics:
      //  INITIALLY → (PRESET
      //                ∧ ((G(REQUIRE) ∧ ASSUME) → (G(ASSERT) ∧ GUARANTEE)))
      //
      //  Strict semantics:
      //  INITIALLY → (PRESET
      //                ∧ (G(REQUIRE) ∧ ASSUME) → GUARANTEE)
      //                ∧ (ASSERT W ¬REQUIRE))

      spot::formula environment =
        spot::formula::And({spot::formula::G(require), assumptions});

      const bool strict =
        ast_.semantics == tlsf_semantics::MealyStrict
        || ast_.semantics == tlsf_semantics::MooreStrict;

      spot::formula system = strict
        ? guarantee
        : spot::formula::And({spot::formula::G(assertion), guarantee});
      spot::formula conditional =
        spot::formula::Implies(environment, system);

      spot::formula core;
      if (strict)
        {
          spot::formula w =
            spot::formula::W(assertion, spot::formula::Not(require));
          core = spot::formula::And({preset, conditional, w});
        }
      else
        {
          core = spot::formula::And({preset, conditional});
        }

      result.full_formula = spot::formula::Implies(initially, core);
      result.full_formula = failed_ ? spot::formula(nullptr)
                                    : result.full_formula;
      result.inputs = std::move(inputs_);
      result.outputs = std::move(outputs_);
      inputs_.clear();
      outputs_.clear();
      seen_inputs_.clear();
      seen_outputs_.clear();
      return result;
    }
  }
}
