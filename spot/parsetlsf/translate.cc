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
      // or an empty string when the bound introduces none.  The two
      // shapes tlsf_binder_variable recognizes are the whole of TLSF
      // v1.2 SS4.7-4.8; the parser has already rejected everything else,
      // so the empty string is a safety net for an AST built by hand
      // rather than by the parser.  This helper only feeds the
      // shadowing used by substitution to keep such variables local.
      std::string quantifier_loop_var(const tlsf_expr& bound)
      {
        const std::string* var = tlsf_binder_variable(bound);
        return var ? *var : std::string();
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

      // Evaluate a comparison operator on two already-computed
      // integers.  \a op must be one of Eq, Neq, Lt, Le, Gt, Ge;
      // this is the integer semantics of the comparison operators,
      // shared by eval_int (which returns 0/1) and by the LTL-position
      // fold of translate_expr (which returns tt/ff).
      bool compare_ints(tlsf_op op, long long lhs, long long rhs)
      {
        switch (op)
          {
          case tlsf_op::Eq:
            return lhs == rhs;
          case tlsf_op::Neq:
            return lhs != rhs;
          case tlsf_op::Lt:
            return lhs < rhs;
          case tlsf_op::Le:
            return lhs <= rhs;
          case tlsf_op::Gt:
            return lhs > rhs;
          case tlsf_op::Ge:
            return lhs >= rhs;
          default:
            SPOT_UNREACHABLE();
          }
      }

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
      // Build the name indexes once.  Inputs are inserted before
      // outputs so find_decl keeps resolving a name declared on
      // both sides to the input, as the former two-loop scan did.
      decls_.reserve(ast_.inputs.size() + ast_.outputs.size());
      for (const auto& d : ast_.inputs)
        decls_.emplace(d.name, &d);
      for (const auto& d : ast_.outputs)
        {
          decls_.emplace(d.name, &d);
          output_bases_.insert(d.name);
        }
      defs_.reserve(ast_.definitions.size());
      for (const auto& d : ast_.definitions)
        defs_.emplace(d.name, &d);
      enums_.reserve(ast_.enumerations.size());
      for (const auto& e : ast_.enumerations)
        enums_.emplace(e.name, &e);
    }

    translator::~translator() = default;

    void translator::diag(const location& loc,
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

    bool translator::require_finite_semantics(const tlsf_expr& e)
    {
      if (ast_.semantics == tlsf_semantics::MealyFinite
          || ast_.semantics == tlsf_semantics::MooreFinite)
        return true;
      diag(e, "strong next requires finite semantics");
      return false;
    }

    size_t translator::lookup_scope(
      const std::vector<subst_binding>& scopes,
      const std::string& name)
    {
      for (size_t i = scopes.size(); i-- > 0; )
        if (scopes[i].name == name)
          return i;
      return scopes.size();
    }

    // Widest conjunction or disjunction spot will accept in one node:
    // fnode::nary throws beyond UINT16_MAX children.  Any fold that
    // could exceed this many terms (a wide binder, the per-bus enum
    // coverage constraints) must be folded pairwise instead.
    constexpr long long max_formula_children = 65535;

    tlsf_expr_ptr
    translator::subst_scoped(const tlsf_expr_ptr& body,
                             const std::vector<subst_binding>& env,
                             const std::vector<subst_binding>& scopes)
    {
      if (!body)
        return nullptr;
      // A subtree holding no Identifier, BusRef or Quantifier cannot
      // reference a binding, so the walk would only rebuild an
      // identical tree.  The assert re-derives the flag from the
      // tree: a clone that dropped has_binding_target would
      // otherwise silently skip substitution here and produce a
      // wrong formula with no diagnostic.
      if (!body->has_binding_target)
        {
          assert(!tlsf_subtree_has_binding_target(*body));
          return body;
        }
      // Nothing was truncated: walk with the full environment.
      if (scopes.size() == env.size())
        return subst_expr(body, env);
      // A quantifier above us re-bound at least one name, so
      // `scopes` is a proper subset of `env` holding the bindings
      // that are still visible here.  Walk with exactly that set: the
      // shadowed formals must not be substituted inside the
      // quantifier, while every unrelated formal stays in scope.
      return subst_expr(body, scopes);
    }

    tlsf_expr_ptr
    translator::subst_expr(const tlsf_expr_ptr& body,
                           const std::vector<subst_binding>& env)
    {
      if (!body)
        return nullptr;

      // Fast path: with an empty environment there is nothing to
      // substitute, and a subtree holding no Identifier, BusRef or
      // Quantifier cannot reference a formal anyway.  Returning the
      // node untouched is what keeps this pass linear in the number
      // of names instead of the number of body nodes.
      if (env.empty() && !body->has_binding_target)
        return body;
      if (!env.empty() && !body->has_binding_target)
        {
          assert(!tlsf_subtree_has_binding_target(*body));
          return body;
        }

      // Resolve the free occurrence of \a name, if any.  Sets
      // \a kind to the matching binding's kind so the caller knows
      // whether the actual must itself be substituted.
      const auto lookup = [&](const std::string& name,
                              subst_binding::kind& kind)
        -> tlsf_expr_ptr
        {
          const size_t i = lookup_scope(env, name);
          if (i == env.size())
            return nullptr;
          kind = env[i].k;
          return env[i].expr;
        };

      // Non-null when this node itself resolves to a binding.
      tlsf_expr_ptr resolved;
      subst_binding::kind kind = subst_binding::kind::splice;
      if (body->type == tlsf_expr_type::Identifier
          || body->type == tlsf_expr_type::BusRef)
        resolved = lookup(body->name, kind);

      // A BusRef index (`a[i]`) is always resolved later through
      // eval_int, never by this pass, so a bound BusRef base can only
      // be renamed.  Splicing a non-Identifier actual would leave a
      // BusRef with no base, so such a match is dropped and the
      // original node is kept.
      if (resolved && body->type == tlsf_expr_type::BusRef
          && resolved->type != tlsf_expr_type::Identifier)
        resolved = nullptr;

      if (resolved)
        {
          if (body->type == tlsf_expr_type::BusRef)
            {
              // Keep the BusRef and its index children, pointing the
              // base at the actual's name.
              auto ren = std::make_shared<tlsf_expr>();
              ren->loc = body->loc;
              ren->type = body->type;
              ren->parenthesized = body->parenthesized;
              ren->name = resolved->name;
              for (size_t i = 0; i < body->children.size(); ++i)
                ren->children.push_back(subst_scoped(body->children[i], env,
                                                    env));
              tlsf_update_flags(ren);
              return ren;
            }
          // A splice carries an already-expanded actual: return it
          // verbatim so this pass cannot expand it a second time.  A
          // shadow binding still has to be substituted by the
          // definitions outside its own scope, which is what the
          // old outermost-first `shadowed` set emulated.
          if (kind == subst_binding::kind::splice)
            return resolved;
          return subst_scoped(resolved, env, env);
        }

      // No binding matched: rebuild the node structurally so that its
      // children are substituted in turn.
      auto clone = std::make_shared<tlsf_expr>();
      clone->loc = body->loc;
      clone->type = body->type;
      clone->parenthesized = body->parenthesized;
      // Only copy the payload-bearing field for this node kind;
      // copying val, name and op unconditionally bleeds stale data
      // across kinds.
      switch (body->type)
        {
        case tlsf_expr_type::LiteralInt:
          clone->val = body->val;
          break;
        case tlsf_expr_type::Identifier:
        case tlsf_expr_type::BusRef:
        case tlsf_expr_type::App:
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

      // A quantified identifier is local to both its bound and its
      // body, so an outer definition formal of the same name must
      // neither capture it nor be renamed by it.  Drop the bindings
      // that name from the environment for this subtree only.
      std::vector<subst_binding> inner(env);
      if (body->type == tlsf_expr_type::Quantifier
          && body->children.size() >= 2 && body->children[0])
        {
          // A bound with no iteration variable contributes nothing
          // to shadow; the parser rejects those, so this only guards
          // a hand-built AST.
          const std::string var = quantifier_loop_var(*body->children[0]);
          if (!var.empty())
            inner.erase(std::remove_if(inner.begin(), inner.end(),
                                       [&](const subst_binding& b)
                                       { return b.name == var; }),
                        inner.end());
        }

      // A Quantifier keeps exactly its [bound, body] children here;
      // both are substituted like any other child.
      for (size_t i = 0; i < body->children.size(); ++i)
        clone->children.push_back(
          subst_scoped(body->children[i], env, inner));
      tlsf_update_flags(clone);
      return clone;
    }

    tlsf_expr_ptr
    translator::subst_clause(const tlsf_expr_ptr& clause,
                             const tlsf_definition& def,
                             const std::vector<tlsf_expr_ptr>& actuals,
                             bool actuals_expanded)
    {
      // Both callers hand over actuals that expand_ast has already
      // expanded, and both therefore ask for `splice` bindings: the
      // actual is substituted verbatim and is not expanded a second
      // time here.  Shadowing is applied to both kinds alike, so a
      // quantifier inside the body still captures a formal of the same
      // name.
      //
      // `shadow` is the other kind, for an actual that must be
      // rewritten by the bindings enclosing this definition.  It is not
      // reachable from here: its actual is re-substituted under the
      // same environment, and an expanded actual still mentions the
      // identifiers the caller substituted for its own formals, so the
      // two rewrite each other and the recursion never terminates.
      std::vector<subst_binding> env;
      env.reserve(def.args.size());
      for (size_t i = 0; i < def.args.size(); ++i)
        env.push_back({actuals_expanded ? subst_binding::kind::splice
                                         : subst_binding::kind::shadow,
                       def.args[i], actuals[i]});
      return subst_expr(clause, env);
    }

    tlsf_expr_ptr
    translator::expand_ast(const tlsf_expr_ptr& e)
    {
      if (!e)
        return nullptr;

      // Fast path: a subtree with no App node contains no
      // user-defined call, so this pass has nothing to flatten
      // and cannot change it.  Return the node as is instead of
      // rebuilding an identical tree.  The clone below is purely
      // structural, so sharing the original is safe: neither this
      // pass nor its callers mutate the tree they are handed.
      if (!e->has_app)
        {
          assert(!tlsf_subtree_has_app(*e));
          return e;
        }

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
          const tlsf_definition* def = find_def(e->name);
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
          // single body clause.  The actuals were pre-expanded
          // above, so every binding splices verbatim and this
          // pass cannot re-expand them; the caller's
          // quantifier-loop-var binding is untouched because a
          // quantifier inside the body truncates the scope chain
          // locally.
          tlsf_expr_ptr expanded =
            subst_clause(only, *def, actuals, true);
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
      tlsf_update_flags(clone);
      return clone;
    }

    const tlsf_ap_decl*
    translator::find_decl(const std::string& name) const
    {
      auto it = decls_.find(name);
      return it == decls_.end() ? nullptr : it->second;
    }

    bool translator::base_is_output(const std::string& name) const
    {
      return output_bases_.count(name) != 0;
    }

    const tlsf_definition*
    translator::find_def(const std::string& name) const
    {
      auto it = defs_.find(name);
      return it == defs_.end() ? nullptr : it->second;
    }

    const tlsf_enum_decl*
    translator::find_enum(const std::string& name) const
    {
      auto it = enums_.find(name);
      return it == enums_.end() ? nullptr : it->second;
    }

    bool
    translator::eval_ap_width(const tlsf_ap_decl& d, long long& out)
    {
      if (!d.enum_type.empty())
        {
          const tlsf_enum_decl* en = find_enum(d.enum_type);
          if (!en)
            {
              diag(d.loc, "typed bus '" + d.name + "' uses enum '"
                   + d.enum_type + "' which is not declared");
              return false;
            }
          // Parser invariant: every accepted enum entry carries at
          // least one pattern, and all patterns share the first
          // one's width.
          assert(!en->entries.empty());
          assert(!en->entries[0].patterns.empty());
          out = static_cast<long long>(en->entries[0].patterns[0].size());
          return out > 0;
        }
      // Every caller (register_decl, BusRef, SIZEOF, and the enum
      // comparison / missing-valuation paths) filters scalar APs out
      // before asking for a width, so a size-less declaration cannot
      // reach this point.
      assert(d.size);
      return eval_int(*d.size, out);
    }

    formula
    translator::translate_enum_cmp(const tlsf_expr& e,
                                   const tlsf_ap_decl& bus,
                                   bool equal)
    {
      // Shape (see the BinaryOp Eq/Neq case in translate_expr):
      // children[0] is the typed-bus base identifier, children[1]
      // the enum-constant identifier.
      const tlsf_enum_decl* en = find_enum(bus.enum_type);
      if (!en)
        {
          diag(e, "typed bus '" + bus.name + "' uses enum '"
                 + bus.enum_type + "' which is not declared");
          return formula::ff();
        }
      assert(!e.children.empty() && e.children[1]);
      const std::string& tag = e.children[1]->name;
      const tlsf_enum_value* val = nullptr;
      for (const auto& v : en->entries)
        if (v.tag == tag)
          {
            val = &v;
            break;
          }
      if (!val)
        {
          diag(e, "enum '" + en->name + "' has no value named '"
                 + tag + "'");
          return formula::ff();
        }
      // Width of the bus (== width of the enum).
      long long width;
      // The enum was found above, so eval_ap_width cannot fail here.
      if (!eval_ap_width(bus, width))
        SPOT_UNREACHABLE();
      // run()'s register_decl pass (see run()) records every bit of
      // every declared bus before any translation, so the flattened
      // names below are guaranteed to already be registered (in
      // seen_outputs_ or seen_inputs_ depending on the direction of
      // the bus).
      assert([&] {
          bool out = base_is_output(bus.name);
          for (long long i = 0; i < width; ++i)
            {
              const std::string name = bus.name + '_' + std::to_string(i);
              if (out ? !seen_outputs_.count(name)
                      : !seen_inputs_.count(name))
                return false;
            }
          return true;
        }());
      // Build the OR of the per-pattern conjunctions; bit k of a
      // pattern constrains AP `bus.name_k` ('1' positive, '0'
      // negated, '*' omitted).
      std::vector<formula> alts;
      alts.reserve(val->patterns.size());
      for (const std::string& pat : val->patterns)
        {
          std::vector<formula> bits;
          for (size_t k = 0; k < pat.size() && k < static_cast<size_t>(width);
               ++k)
            {
              if (pat[k] == '*')
                continue;
              formula ap = formula::ap(
                bus.name + '_' + std::to_string(k));
              bits.push_back(pat[k] == '1' ? ap
                             : formula::Not(ap));
            }
          alts.push_back(bits.empty()
                         ? formula::tt()
                         : formula::And(bits));
        }
      formula res = alts.empty()
        ? formula::ff()
        : (alts.size() == 1
           ? alts[0] : formula::Or(alts));
      return equal ? res : formula::Not(res);
    }

    // Shared budget check for one user-definition application.
    // Used by the translate_expr App case (LTL position) and by
    // eval_def_int (integer position, i.e. eval_int's Identifier
    // and App cases for zero-argument and arity-matching
    // definitions).
    //
    // \a depth is the caller's current recursion depth: the LTL
    // path passes expansion_depth_, the integer path passes
    // int_def_depth_.  Depth 0 means the call starts a fresh
    // expansion chain, so expansion_root_name_ is (re)anchored to
    // it: the depth limit trips on whichever App happens to
    // overflow -- for a recursive definition that is often a LEAF
    // call inside the cyclic def's own clause (e.g. the `none`
    // calls inside full_arbiter's recursive `mone`) -- and this
    // anchor makes the diagnostic blame the def that STARTED the
    // chain instead.
    //
    // Returns true when the application may proceed; false means
    // the caller must fold the call to ff() (LTL) or report
    // failure (integer) without further expansion.  Once either
    // budget trips, expansion_exhausted_ goes sticky and every
    // later application is refused silently, so a non-terminating
    // spec yields exactly one diagnostic.  A true return has
    // pushed one frame onto expansion_depth_; the caller must pop
    // it (--expansion_depth_) once its expansion is done.
    bool
    translator::def_app_budget(const std::string& name,
                               const tlsf_expr& call, unsigned depth)
    {
      if (expansion_exhausted_)
        return false;
      if (depth == 0)
        expansion_root_name_ = name;
      if (++expansion_depth_ > max_def_depth
          || ++expansion_total_ > max_def_expansions_total)
        {
          expansion_exhausted_ = true;
          diag(call,
               "definition expansion limit exceeded; "
               "the expansion of definition '"
               + expansion_root_name_ + "' is cyclic or "
               "does not reach a base case");
          --expansion_depth_;
          return false;
        }
      return true;
    }

    bool
    translator::eval_def_int(const tlsf_definition& def,
                             const std::vector<tlsf_expr_ptr>& actuals,
                             const tlsf_expr& call,
                             long long& out)
    {
      // The callers evaluate each actual to a LiteralInt (or pass
      // no actuals at all) before coming here, so the
      // guard-selection substitution below sees constant
      // arguments.
      assert(actuals.size() == def.args.size());
      if (!def_app_budget(def.name, call, int_def_depth_))
        return false;
      // Keep both depth counters incremented while the clause body
      // is evaluated: nested definition calls inside the body (or
      // inside a guard, via eval_guard_bool -> eval_int_quiet) must
      // see the enlarged depth for the budgets to bound the chain.
      ++int_def_depth_;
      tlsf_expr_ptr clause = select_def_clause(def, actuals, call);
      bool ok = false;
      if (clause)
        ok = eval_int(*clause, out);
      --int_def_depth_;
      --expansion_depth_;
      return ok;
    }

    bool translator::eval_set(const tlsf_expr& e,
                              std::vector<long long>& out)
    {
      if (e.type == tlsf_expr_type::SetExplicit)
        {
          for (const auto& child : e.children)
            {
              assert(child);
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
      // `(+)[b] eSX` / `(*)[b] eSX` (also spelled `CUP[` / `CAP[`), and the
      // Spot extension `(-)[b] eSX` (`SETMINUS[`): the union,
      // intersection, and difference of eSX over every combination the
      // binder list b ranges over.  The argument is the quantifier run
      // the list desugars to, exactly as for the numeric big operators.
      if (e.type == tlsf_expr_type::UnaryOp
          && (e.op == tlsf_op::BigUnion || e.op == tlsf_op::BigInter
              || e.op == tlsf_op::BigDiff)
          && e.children.size() >= 1 && e.children[0])
        return eval_set_binder_run(*e.children[0], e.op, out);
      diag(e, "expected an integer set");
      return false;
    }

    namespace
    {
      /// \brief Is \a e a binder of a binder run, i.e. one of the nodes
      /// \ref spot::tlsf_make_binders nests?
      ///
      /// The run built by \ref spot::tlsf_make_binders and \ref
      /// spot::tlsf_make_bigop is a chain of two-child Quantifier nodes
      /// tagged \c And or \c Or.  The bounded temporal quantifiers
      /// (`X[lo:hi]`, `F[lo:hi]`, `G[lo:hi]` and the strong variants)
      /// are Quantifier nodes too, but they carry three children, so
      /// they must never be mistaken for a binder to enumerate: a body
      /// like `&&[0 <= i < N] X[i] e` would otherwise have `i` bound
      /// twice and lose its own `lo`/`hi` children.
      bool is_binder_run_node(const tlsf_expr& e)
      {
        return e.type == tlsf_expr_type::Quantifier
          && (e.op == tlsf_op::And || e.op == tlsf_op::Or)
          && e.children.size() == 2 && e.children[0] && e.children[1];
      }
    }

    bool translator::push_binder(const tlsf_expr& q, std::string& var,
                                 std::vector<long long>& values)
    {
      // Only the two-child nodes of tlsf_make_binders reach here, and
      // only when they are well formed: translate_expr's Quantifier
      // case checks the child count, and the big operators build their
      // runs through tlsf_make_binders.
      assert(is_binder_run_node(q));
      assert(q.children.size() >= 2 && q.children[0]);
      const auto& bound = *q.children[0];

      if (!tlsf_binder_variable(bound))
        {
          // The parser rejects a bound that is neither a membership nor
          // a comparison chain (see tlsf_binder_variable), so this only
          // fires on an AST that did not come from the parser: a
          // hand-built one, or a caller of the public tlsf_to_ltl()
          // that ignored the parse diagnostics.
          diag(q, "quantifier bound must introduce an iteration "
                  "variable (e.g. `&&[0 <= i < N]` or "
                  "`&&[i IN {0, 1}]`)");
          return false;
        }

      if (bound.op == tlsf_op::In)
        {
          // Membership: the variable is the element expression on the
          // left of `IN`; the iteration values come from evaluating
          // the set on the right.
          var = bound.children[0]->name;
          return eval_set(*bound.children[1], values);
        }

      // Comparison chain: the variable sits on the RHS of the inner
      // comparison, and the inclusivity of each end of the range is
      // given by the `<=` vs `<` spelling of its own operator.
      const auto& lower_cmp = *bound.children[0];
      var = lower_cmp.children[1]->name;
      const bool lower_inclusive = lower_cmp.op == tlsf_op::Le;
      const bool upper_inclusive = bound.op == tlsf_op::Le;
      long long lower;
      long long upper;
      if (!eval_int(*lower_cmp.children[0], lower)
          || !eval_int(*bound.children[1], upper))
        return false;
      if (lower <= upper)
        {
          const auto span = integer_range_span(lower, upper);
          if (span >= 1000000)
            {
              diag(q, "quantifier range is too large");
              var.clear();
              return false;
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
      return true;
    }

    bool translator::for_each_instantiation(
      const tlsf_expr& q,
      const std::function<bool(const tlsf_expr&)>& emit)
    {
      std::string var;
      std::vector<long long> values;
      if (!push_binder(q, var, values))
        return false;
      // A run this wide cannot be folded into one formula node, and
      // there is no way to build it: spot's fnode layer caps a node at
      // max_formula_children operands, and both fnode::multop and
      // multop_build_and_or inline a child that already carries the
      // same operator, so a balanced tree of Ands is flattened back
      // into the one over-wide node (spot/tl/formula.cc).  Catching
      // that throw instead is not free either: it unwinds past the
      // half-built node and leaks the formulas the run had already
      // interned.  So refuse the run, here, before any body is
      // translated.  loop_vars_ is populated for the enclosing binders
      // at this point, so the bound evaluates in the right scope.
      if (SPOT_UNLIKELY(values.size() > static_cast<size_t>(
                                        max_formula_children)))
        {
          diag(q, "quantifier instantiation count exceeds the formula "
                  "child limit of "
                  + std::to_string(max_formula_children));
          return false;
        }
      assert(q.children.size() >= 2 && q.children[1]);
      const tlsf_expr& rest = *q.children[1];

      bool ok = true;
      for (long long value : values)
        {
          auto previous = loop_vars_.find(var);
          const bool had_previous = previous != loop_vars_.end();
          const long long previous_value =
            had_previous ? previous->second : 0;
          loop_vars_[var] = value;
          // A nested run continues the enumeration; its bindings stay
          // in effect for the body it eventually reaches.
          if (is_binder_run_node(rest))
            ok = for_each_instantiation(rest, emit);
          else
            ok = emit(rest);
          // Restore as we unwind, so no binding escapes its binder.
          if (had_previous)
            loop_vars_[var] = previous_value;
          else
            loop_vars_.erase(var);
          if (!ok)
            break;
        }
      return ok;
    }

    bool translator::translate_binder_run(const tlsf_expr& e, formula& out)
    {
      // for_each_instantiation() refuses a binder wider than a single
      // formula node can hold, before translating any body, so the fold
      // below is always within the child limit of spot's fnode layer.
      std::vector<formula> parts;
      const bool ok = for_each_instantiation(
        e, [&](const tlsf_expr& body)
        {
          parts.push_back(translate_expr(body));
          return true;
        });
      if (!ok)
        {
          // A bad binder or bound was already reported; fall back to a
          // constant of the right polarity so the caller has something
          // to return.
          out = e.op == tlsf_op::And ? formula::tt() : formula::ff();
          return false;
        }
      // A fold over no value is the neutral element, and
      // formula::And/Or of an empty vector already spell `true` and
      // `false`.
      out = e.op == tlsf_op::And
        ? formula::And(parts) : formula::Or(parts);
      return true;
    }

    bool translator::eval_int_binder_run(const tlsf_expr& e, tlsf_op op,
                                         long long& out)
    {
      // A fold over no value is the operation's neutral element: 0 for
      // a sum, 1 for a product.  (The Boolean folds over no value are
      // `true` and `false`, which formula::And/Or of an empty vector
      // already give.)  Any first value then replaces that element.
      const bool is_prod = op == tlsf_op::BigProd;
      long long acc = is_prod ? 1 : 0;
      bool first = true;
      const bool ok = for_each_instantiation(
        e, [&](const tlsf_expr& body)
        {
          long long value;
          if (!eval_int(body, value))
            return false;
          if (first)
            {
              acc = value;
              first = false;
              return true;
            }
          const bool fits = is_prod
            ? checked_mul(acc, value, acc) : checked_add(acc, value, acc);
          if (!fits)
            {
              diag(e, std::string("integer overflow in ")
                   + tlsf_format_op(op) + " big operator");
              return false;
            }
          return true;
        });
      if (!ok)
        return false;
      // `first` still set means the binder domain was empty, in which
      // case `acc` still holds the neutral element computed above.
      out = acc;
      return true;
    }

    bool translator::eval_set_binder_run(const tlsf_expr& e, tlsf_op op,
                                         std::vector<long long>& out)
    {
      const bool is_union = op == tlsf_op::BigUnion;
      const bool is_inter = op == tlsf_op::BigInter;
      assert(is_union || is_inter || op == tlsf_op::BigDiff);
      bool any = false;
      const bool ok = for_each_instantiation(
        e, [&](const tlsf_expr& body)
        {
          std::vector<long long> values;
          if (!eval_set(body, values))
            return false;
          if (!any)
            {
              // The first instantiation is the fold's initial value.
              out = std::move(values);
              any = true;
              return true;
            }
          // Each further instantiation folds in from the left, so the
          // accumulator is always kept in the order the binder
          // enumerates it.
          std::vector<long long> acc;
          if (is_union)
            {
              acc = out;
              for (long long v : values)
                if (std::find(acc.begin(), acc.end(), v) == acc.end())
                  acc.push_back(v);
            }
          else if (is_inter)
            {
              for (long long v : out)
                if (std::find(values.begin(), values.end(), v)
                    != values.end())
                  acc.push_back(v);
            }
          else
            {
              // Left fold of difference, matching the right-to-left
              // associativity TLSF gives the binary `(-)`: each
              // instantiation removes from what the earlier ones
              // accumulated.
              for (long long v : out)
                if (std::find(values.begin(), values.end(), v)
                    == values.end())
                  acc.push_back(v);
            }
          out = std::move(acc);
          return true;
        });
      if (!ok)
        return false;
      if (!any)
        {
          // Only the union has a representable identity (the empty
          // set): the intersection's is the universal set and the
          // left fold's is the first operand, neither of which exists
          // when there is no operand.
          if (is_union)
            {
              out.clear();
              return true;
            }
          diag(e, std::string(is_inter ? "intersection" : "difference")
                 + " over an empty binder domain has no value; "
                   "the domain must be nonempty");
          return false;
        }
      return true;
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
      for (const tlsf_expr_ptr& raw_clause : def.body)
        {
          // Substitute the (pre-expanded) actuals into this clause
          // before inspecting its guard, so guards over formal
          // integer arguments become constant comparisons.  The
          // actuals are spliced verbatim: they were already
          // expanded by the caller and carry no formal name, and a
          // quantifier inside the clause must not capture a formal
          // (it never did here, the scan having used an empty
          // shadow set).
          tlsf_expr_ptr clause =
            subst_clause(raw_clause, def, actuals, true);
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
                // The parameter's value is a parsed AST (the
                // PARAMETERS block uses the same expression nodes as
                // everything else); evaluate it with the current
                // bindings so a parameter may reference another one.
                long long value = 0;
                bool ok = pe->second && eval_int(*pe->second, value);
                active_params_.erase(e.name);
                if (ok)
                  {
                    params_[e.name] = value;
                    out = value;
                    return true;
                  }
                diag(e, "could not evaluate parameter '" + e.name
                       + "'");
                return false;
              }
            // A zero-argument definition (`m = log2(n);`) used as a
            // bare identifier in integer position: expand it now
            // (amba_case_study's `HMASTER[m]` bus size).  Callers
            // that need a *name* in this position (SIZEOF, ap
            // registration) look up declarations before reaching
            // this fallback.
            if (const tlsf_definition* def = find_def(e.name))
              {
                if (def->args.empty())
                  {
                    std::vector<tlsf_expr_ptr> no_args;
                    return eval_def_int(*def, no_args, e, out);
                  }
                diag(e, "definition '" + e.name + "' expects "
                       + std::to_string(def->args.size())
                       + " argument(s); used with none");
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
              assert(e.children.size() == 1);
              const auto& arg = *e.children[0];
              if (arg.type != tlsf_expr_type::Identifier)
                {
                  diag(e, "SIZEOF argument must be a bus name");
                  return false;
                }
              // Search inputs and outputs for a matching bus decl.
              // A typed bus (`hburst HBURST;`) has an empty `size`
              // but is a real bus: its width comes from the enum.
              if (const tlsf_ap_decl* d = find_decl(arg.name))
                {
                  if (!d->size && d->enum_type.empty())
                    {
                      diag(e, "SIZEOF of scalar AP '" + arg.name + "'");
                      return false;
                    }
                  return eval_ap_width(*d, out);
                }
              diag(e, "SIZEOF: unknown bus '" + arg.name + "'");
              return false;
            }
          // A user-defined definition with an arity-matching call
          // can be evaluated in integer position too (e.g. amba's
          // `bit(v,i)` feeding `value'`'s guard arithmetic).  Each
          // actual is folded to a LiteralInt first (same policy as
          // the translate_expr App case) so the guard-selection
          // substitution sees constant arguments; a non-constant
          // actual cannot appear here because integer-position
          // expressions only contain literals, parameters, loop
          // variables, builtins, and other definitions -- all of
          // which fold.
          if (const tlsf_definition* def = find_def(e.name))
            {
              if (def->args.size() != e.children.size())
                {
                  diag(e, "definition '" + e.name + "' expects "
                         + std::to_string(def->args.size())
                         + " argument(s); called with "
                         + std::to_string(e.children.size()));
                  return false;
                }
              std::vector<tlsf_expr_ptr> actuals;
              actuals.reserve(e.children.size());
              for (const auto& c : e.children)
                {
                  long long v;
                  if (!eval_int(*c, v))
                    return false;
                  actuals.push_back(tlsf_make_int(c->loc, v));
                }
              return eval_def_int(*def, actuals, e, out);
            }
          diag(e, "function call '" + e.name + "' is not supported "
                 "in integer position");
          return false;
        case tlsf_expr_type::UnaryOp:
          assert(e.children.size() == 1);
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
          // `+[b] eN` / `*[b] eN` (also spelled `SUM[` / `PROD[`):
          // the sum and the product of eN over every combination the
          // binder list b ranges over.  The big operator's argument is
          // the quantifier run that list desugars to, so the fold
          // walks the same enumeration the Boolean quantifiers do.
          if (e.op == tlsf_op::BigSum || e.op == tlsf_op::BigProd)
            return eval_int_binder_run(*e.children[0], e.op, out);
          // `|eSX|` (also spelled `SIZE eSX`): the number of elements of
          // the set.  `MIN eSX` / `MAX eSX`: its smallest / largest
          // element.  All three take a set in a set position, so they
          // are evaluated here rather than by eval_set, which only
          // ever yields integer sets.
          if (e.op == tlsf_op::SetSize || e.op == tlsf_op::SetMin
              || e.op == tlsf_op::SetMax)
            {
              std::vector<long long> values;
              if (!eval_set(*e.children[0], values))
                return false;
              if (e.op == tlsf_op::SetSize)
                {
                  // size() cannot overflow: the set was built from at
                  // most that many evaluated integers.
                  out = static_cast<long long>(values.size());
                  return true;
                }
              if (values.empty())
                {
                  diag(e, std::string(tlsf_format_op(e.op))
                         + " of an empty set has no value");
                  return false;
                }
              const long long m = *std::min_element(values.begin(),
                                                    values.end());
              const long long M = *std::max_element(values.begin(),
                                                    values.end());
              out = e.op == tlsf_op::SetMin ? m : M;
              return true;
            }
          diag(e, "unary op '" + tlsf_format_op(e.op)
                 + "' is not supported in integer position");
          return false;
        case tlsf_expr_type::BinaryOp:
          {
            assert(e.children.size() == 2);
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
              case tlsf_op::Le:
              case tlsf_op::Gt:
              case tlsf_op::Ge:
              case tlsf_op::Eq:
              case tlsf_op::Neq:
                out = compare_ints(e.op, l, r) ? 1 : 0;
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
      // All nine tlsf_expr_type values have a case in this switch.
      SPOT_UNREACHABLE();
    }

    formula translator::translate_expr(const tlsf_expr& e)
    {
      switch (e.type)
        {
        case tlsf_expr_type::LiteralInt:
          diag(e, "integer literal in LTL position");
          return formula::ff();
        case tlsf_expr_type::Identifier:
          {
            if (e.name == "true")
              return formula::tt();
            if (e.name == "false")
              return formula::ff();
            // Loop variables and parameters are integer-valued only;
            // they have no Boolean meaning on their own.
            if (loop_vars_.count(e.name))
              {
                diag(e, "loop variable '" + e.name
                       + "' used in LTL position");
                return formula::ff();
              }
            if (params_.count(e.name))
              {
                diag(e, "parameter '" + e.name
                       + "' used in LTL position");
                return formula::ff();
              }
            // A zero-argument macro definition used as a bare
            // identifier in LTL position: expand it via the same
            // eager-flattening machinery the App case uses, so a
            // plain-macro def behaves identically spelled `f` or
            // `f()`.  A guarded or multi-clause body needs the
            // guard-selecting App path; diagnose it (a bare
            // identifier cannot carry actuals for guard selection).
            if (const tlsf_definition* def = find_def(e.name))
              {
                if (def->args.empty() && def->body.size() == 1
                    && def->body[0]
                    && !(def->body[0]->type == tlsf_expr_type::BinaryOp
                         && def->body[0]->op == tlsf_op::Guard))
                  return translate_expr(
                    *expand_ast(tlsf_make_app(e.loc, e.name, {})));
                diag(e, "definition '" + e.name
                       + (def->args.empty()
                          ? "' has a guarded or multi-clause body; "
                            "call it as '"
                          : "' expects "
                          + std::to_string(def->args.size())
                          + " argument(s); called as '")
                       + e.name + "()' to expand it");
                return formula::ff();
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
            // A typed bus is never a Boolean AP by itself: it must
            // be indexed (BusRef) or compared against an enum value
            // (Eq/Neq below).
            if (decl && !decl->enum_type.empty())
              {
                diag(e, "typed bus '" + base
                       + "' used without an index; compare it against "
                         "an enum value or index it");
                return formula::ff();
              }
            // A declared scalar AP was always already registered (under
            // its bare name) by run()'s register_decl pass.
            assert(!decl || decl->size || [&] {
                bool is_out = base_is_output(base);
                return is_out ? seen_outputs_.count(base) != 0
                              : seen_inputs_.count(base) != 0;
              }());
            return formula::ap(base);
          }
        case tlsf_expr_type::BusRef:
          {
            assert(e.children.size() == 1);
            long long idx;
            if (!eval_int(*e.children[0], idx))
              return formula::ff();
            const tlsf_ap_decl* decl = find_decl(e.name);
            if (!decl)
              {
                diag(e, "indexed reference uses undeclared bus '"
                       + e.name + "'");
                return formula::ff();
              }
            if (!decl->size && decl->enum_type.empty())
              {
                diag(e, "indexed reference uses scalar AP '"
                       + e.name + "'");
                return formula::ff();
              }
            long long size;
            if (!eval_ap_width(*decl, size))
              {
                diag(e, "could not evaluate size of bus '" + e.name
                       + "'");
                return formula::ff();
              }
            if (size <= 0)
              {
                diag(e, "bus '" + e.name + "' has non-positive size");
                return formula::ff();
              }
            if (idx < 0 || idx >= size)
              {
                diag(e, "index " + std::to_string(idx)
                       + " is outside bus '" + e.name + "' of size "
                       + std::to_string(size));
                return formula::ff();
              }
            // A declared bus bit was always already registered (under its
            // flattened name) by run()'s register_decl pass.
            std::ostringstream flat;
            flat << e.name << '_' << idx;
            const std::string name = flat.str();
            assert(base_is_output(e.name)
                   ? seen_outputs_.count(name) != 0
                   : seen_inputs_.count(name) != 0);
            return formula::ap(name);
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
            // spot/parsetlsf/parsetlsf.yy: definition semantic
            // action), so the lookup is by name alone.  An arity
            // mismatch
            // gets a dedicated diagnostic that explains BOTH the
            // declared arity and the call-site arity, so the user
            // can fix the call without grepping the DEFINITIONS
            // block.
            const tlsf_definition* def = find_def(e.name);
            if (!def)
              {
                diag(e, "definition '" + e.name + "' is not defined");
                return formula::ff();
              }
            if (def->args.size() != e.children.size())
              {
                diag(e, "definition '" + e.name
                       + "' expects "
                       + std::to_string(def->args.size())
                       + " argument(s); called with "
                       + std::to_string(e.children.size()));
                return formula::ff();
              }
            // Recursion is legitimate in TLSF: a guarded definition
            // may call itself while its constant arguments shrink
            // toward the base case selected by the guards (e.g.
            // full_arbiter.tlsf's `mone` halves its index range at
            // every level).  We therefore do NOT reject re-entry
            // into a definition that is already being expanded;
            // def_app_budget below bounds the recursion depth and
            // total work, so bodies that never reach a base case
            // get diagnosed instead of hanging.  Once either bound
            // trips, expansion_exhausted_ goes sticky: every later
            // definition application returns ff() silently and only
            // the first overflow is reported, so a non-terminating
            // spec yields one diagnostic rather than one per call
            // site.  depth==0 re-anchors expansion_root_name_ to
            // this call; a LEAF call overflowing the depth limit
            // (e.g. the `none` calls inside full_arbiter's recursive
            // `mone`) is then not misattributed.
            if (!def_app_budget(e.name, e, expansion_depth_))
              return formula::ff();
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
                return formula::ff();
              }
            // Translate the selected clause while this application
            // is still on the expansion stack, so nested calls to
            // the same (or any) definition accumulate depth.
            formula res = translate_expr(*chosen);
            --expansion_depth_;
            return res;
          }
        case tlsf_expr_type::UnaryOp:
          {
            // The parser always attaches exactly one operand.
            assert(e.children.size() == 1);
            // The big operators and the integer-valued set operators
            // have no LTL counterpart.  Report them before translating
            // the operand, so the diagnostic names the operator that
            // cannot appear in LTL position rather than something
            // buried in its body -- and so a big operator's nested
            // quantifiers are not expanded pointlessly first.
            if (e.op == tlsf_op::SetSize || e.op == tlsf_op::SetMin
                || e.op == tlsf_op::SetMax || e.op == tlsf_op::BigSum
                || e.op == tlsf_op::BigProd || e.op == tlsf_op::BigUnion
                || e.op == tlsf_op::BigInter || e.op == tlsf_op::BigDiff)
              {
                diag(e, "operator '" + tlsf_format_op(e.op)
                       + "' is not supported in LTL position");
                return formula::ff();
              }
            formula c = translate_expr(*e.children[0]);
            switch (e.op)
              {
              case tlsf_op::Not:
                return formula::Not(c);
              case tlsf_op::G:
                return formula::G(c);
              case tlsf_op::F:
                return formula::F(c);
              case tlsf_op::X:
                return formula::X(c);
              case tlsf_op::StrongNext:
                if (!require_finite_semantics(e))
                  return formula::ff();
                return formula::strong_X(c);
              default:
                // The parser only produces Not/G/F/X/X[!] unary ops;
                // any other op in LTL position reaches the notifier.
                SPOT_UNREACHABLE();
              }
          }
        case tlsf_expr_type::BinaryOp:
          {
            assert(e.children.size() == 2);
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
                  formula l = translate_expr(*e.children[0]);
                  formula r = translate_expr(*e.children[1]);
                  switch (e.op)
                    {
                    case tlsf_op::And:
                      return formula::And({l, r});
                    case tlsf_op::Or:
                      return formula::Or({l, r});
                    case tlsf_op::Implies:
                      return formula::Implies(l, r);
                    case tlsf_op::Equiv:
                      return formula::Equiv(l, r);
                    case tlsf_op::U:
                      return formula::U(l, r);
                    case tlsf_op::R:
                      return formula::R(l, r);
                    case tlsf_op::W:
                      return formula::W(l, r);
                    default:
                      SPOT_UNREACHABLE();
                    }
                }
              case tlsf_op::Eq:
              case tlsf_op::Neq:
                // Enum comparison over a typed bus: `HBURST == INCR`
                // folds to the OR of the value's bit patterns over
                // the expanded bus APs (translate_enum_cmp); `!=` is
                // its negation.  Both sides may be swapped.
                if (!e.children.empty() && e.children[0]
                    && e.children[0]->type == tlsf_expr_type::Identifier
                    && e.children[1]
                    && e.children[1]->type == tlsf_expr_type::Identifier)
                  {
                    const tlsf_ap_decl* lhs = find_decl(
                      e.children[0]->name);
                    const tlsf_ap_decl* rhs = find_decl(
                      e.children[1]->name);
                    if (lhs && !lhs->enum_type.empty())
                      return translate_enum_cmp(e, *lhs,
                                                e.op == tlsf_op::Eq);
                    if (rhs && !rhs->enum_type.empty())
                      return translate_enum_cmp(e, *rhs,
                                                e.op == tlsf_op::Eq);
                  }
                [[fallthrough]];
              case tlsf_op::Lt:
              case tlsf_op::Le:
              case tlsf_op::Gt:
              case tlsf_op::Ge:
                // A comparison of two integer expressions is a
                // constant.  Section 4.3 makes an LTL expression a
                // boolean expression plus signals and temporal
                // operators, and a boolean expression may compare two
                // integer expressions, so `(SIZEOF b) == 4`,
                // `N >= 4`, or `m(2) == 2` are valid LTL expressions
                // even though the comparison operators have no LTL
                // counterpart.  Fold them like the `In` case below.
                // This also covers a definition whose body is a
                // comparison of two integer expressions (amba's
                // `bit(v,i) = ... : v % 2`), once the actual arguments
                // have been substituted and the body reaches this
                // point.
                //
                // The evaluation is quiet: a non-constant operand
                // (a signal, a bus) simply fails here and is
                // rejected below with the dedicated diagnostic.
                {
                  long long l;
                  long long r;
                  if (eval_int_quiet(*e.children[0], l)
                      && eval_int_quiet(*e.children[1], r))
                    return compare_ints(e.op, l, r)
                           ? formula::tt() : formula::ff();
                }
                // Not constant, so at least one operand is a signal,
                // a bus, or something built from one.  Re-evaluate
                // the operands that are not plain leaves so a
                // mistake inside one of them is reported where it
                // happens ("function call 'SIZE' is not supported in
                // integer position" for an unknown function, "SIZEOF
                // of scalar AP 's'" for a non-bus, ...) instead of
                // being hidden behind the rejection of the enclosing
                // comparison.  A leaf is understood already: a
                // signal or a bus has no integer value, and a literal
                // always has one.
                for (const auto& c : e.children)
                  if (c && c->type != tlsf_expr_type::Identifier
                      && c->type != tlsf_expr_type::BusRef
                      && c->type != tlsf_expr_type::LiteralInt)
                    {
                      long long v;
                      eval_int(*c, v);
                    }
                diag(e, "arithmetic/comparison op '"
                       + tlsf_format_op(e.op)
                       + "' is not supported in LTL position");
                return formula::ff();
              case tlsf_op::Add:
              case tlsf_op::Sub:
              case tlsf_op::Mul:
              case tlsf_op::Div:
              case tlsf_op::Mod:
                diag(e, "arithmetic/comparison op '"
                       + tlsf_format_op(e.op)
                       + "' is not supported in LTL position");
                return formula::ff();
              case tlsf_op::In:
                {
                  long long value;
                  std::vector<long long> values;
                  if (!eval_int(*e.children[0], value)
                      || !eval_set(*e.children[1], values))
                    return formula::ff();
                  return std::find(values.begin(), values.end(), value)
                    != values.end() ? formula::tt()
                    : formula::ff();
                }
              case tlsf_op::Guard:
                // A guard clause `eB : e` is meaningful only as a
                // clause of a DEFINITION body, where select_def_clause
                // strips it before translating the selected value.  A
                // survivor here means the clause escaped expansion
                // (e.g. written directly in a MAIN subsection).
                diag(e, "guard clause ':' is only meaningful inside "
                        "a definition body");
                return formula::ff();
              default:
                diag(e, "unknown binary op");
                return formula::ff();
              }
          }
        case tlsf_expr_type::Quantifier:
          {
            // `X[n] phi`: unfold the stack of n next operators.  n is
            // an integer expression evaluated with the current
            // parameter bindings.  The strong (LTLf) flavour
            // `X[!n] phi`/`X[n!] phi` unfolds strong next instead.
            if (e.op == tlsf_op::XStack || e.op == tlsf_op::StrongXStack)
              {
                if (e.op == tlsf_op::StrongXStack
                    && !require_finite_semantics(e))
                  return formula::ff();
                assert(e.children.size() == 2
                       && e.children[0] && e.children[1]);
                long long n;
                if (!eval_int(*e.children[0], n))
                  return formula::ff();
                if (n < 0)
                  {
                    diag(e, "X[...] requires a non-negative number "
                            "of next steps");
                    return formula::ff();
                  }
                if (static_cast<unsigned long long>(n)
                    >= formula::unbounded())
                  {
                    diag(e, "X[...] bound exceeds the maximum supported"
                            " repetition");
                    return formula::ff();
                  }
                formula body = translate_expr(*e.children[1]);
                unsigned steps = static_cast<unsigned>(n);
                if (e.op == tlsf_op::StrongXStack)
                  return formula::strong_X(steps, body);
                return formula::X(steps, body);
              }

            // Bounded temporal operators `F[a:b] phi` / `G[a:b] phi`
            // children = [lower, upper, body].  The strong (LTLf)
            // flavour `F[!a:b] phi`/`F[a:b!] phi` (and likewise for G)
            // is the same operator built on strong next, so its
            // expansion differs only in the operator each repeated
            // step is combined with: `formula::nested_unop_range` on
            // op::strong_X with op::Or (resp. op::And) yields exactly
            // what syfco prints for `F[!a:b]` (resp. `G[!a:b]`).
            if (e.op == tlsf_op::FBounded || e.op == tlsf_op::GBounded
                || e.op == tlsf_op::StrongFBounded
                || e.op == tlsf_op::StrongGBounded)
              {
                const bool strong = e.op == tlsf_op::StrongFBounded
                                    || e.op == tlsf_op::StrongGBounded;
                if (strong && !require_finite_semantics(e))
                  return formula::ff();
                // F[a:b]/G[a:b] always carry [lower, upper, body].
                assert(e.children.size() == 3 && e.children[2]);
                long long lo;
                long long hi;
                if (!eval_int(*e.children[0], lo)
                    || !eval_int(*e.children[1], hi))
                  return formula::ff();
                if (lo < 0 || hi < 0)
                  {
                    diag(e, "temporal bound must be non-negative");
                    return formula::ff();
                  }
                // An inverted bound (a > b) makes the operator
                // vacuous: `F[a:b]`/`G[a:b]` is then `true`.  This
                // test has to precede the nested_unop_range() calls
                // below, which would silently swap the two bounds.
                if (lo > hi)
                  return formula::tt();
                if (static_cast<unsigned long long>(hi)
                    >= formula::unbounded())
                  {
                    diag(e, "temporal bound exceeds the maximum supported"
                            " repetition");
                    return formula::ff();
                  }
                formula body = translate_expr(*e.children[2]);
                unsigned min = static_cast<unsigned>(lo);
                unsigned max = static_cast<unsigned>(hi);
                if (e.op == tlsf_op::FBounded
                    || e.op == tlsf_op::StrongFBounded)
                  {
                    if (strong)
                      return formula::nested_unop_range(op::strong_X, op::Or,
                                                        min, max, body);
                    return formula::F(min, max, body);
                  }
                if (strong)
                  return formula::nested_unop_range(op::strong_X, op::And,
                                                    min, max, body);
                return formula::G(min, max, body);
              }

            // The And/Or runs are translated by the shared binder
            // machinery, which the big operators use too.  XStack,
            // FBounded, GBounded and their strong flavours returned
            // above.
            if (!is_binder_run_node(e))
              {
                // Parser recovery can leave a binder without its bound
                // or its body; the run helpers assert on a well-formed
                // node, so report it the way an operand-less
                // quantifier always was.
                diag(e, "quantifier with fewer than two operands");
                return e.op == tlsf_op::And
                  ? formula::tt() : formula::ff();
              }
            formula result;
            if (!translate_binder_run(e, result))
              return e.op == tlsf_op::And
                ? formula::tt() : formula::ff();
            return result;
          }
        case tlsf_expr_type::SetExplicit:
          diag(e, "set literal in LTL position");
          return formula::ff();
        case tlsf_expr_type::SetRange:
          diag(e, "set range in LTL position");
          return formula::ff();
        }
      // All nine tlsf_expr_type values have a case in this switch.
      SPOT_UNREACHABLE();
    }

    tlsf_translation_result translator::run()
    {
      tlsf_translation_result result;

      // 1. Resolve parameters. Keep source expressions (as parsed
      // ASTs) until all declarations are known, so a parameter may
      // refer to one that appears later in the PARAMETERS block.
      // Overrides take precedence over declared expressions.
      for (const auto& p : ast_.parameters)
        param_exprs_[p.name] = p.value;
      for (const auto& kv : opts_.overrides)
        params_[kv.first] = kv.second;
      for (const auto& p : ast_.parameters)
        {
          if (params_.count(p.name))
            continue;
          long long value = 0;
          if (!p.value || !eval_int(*p.value, value))
            diag(p.loc, "could not evaluate parameter '" + p.name
                   + "'");
          else
            params_[p.name] = value;
        }

      if (opts_.raise_errors && failed_)
        throw std::runtime_error("tlsf translator: parameter parsing "
                                 "failed");

      // 1b. Register every declared signal eagerly, in declaration
      // order.  This makes a bad bus size or an unknown enum type a
      // declaration error even when the bus is never referenced.  A
      // zero size is silently empty.  The seen_* sets make this a
      // no-op for signals that first-use registration already
      // handled (first-use order still wins for anything used before
      // this pass would run -- but this pass runs first, so it fully
      // determines the order).
      auto register_decl = [&](const tlsf_ap_decl& d)
        {
          // A scalar AP is registered under its bare name; a bus
          // (sized or typed) contributes name_0..name_{w-1}.  The
          // seen_* sets make this a no-op if a first-use registration
          // already handled the signal (first-use order still wins
          // for anything recorded before this pass).
          if (!d.size && d.enum_type.empty())
            {
              if (base_is_output(d.name))
                {
                  if (seen_outputs_.insert(d.name).second)
                    outputs_.push_back(d.name);
                }
              else if (seen_inputs_.insert(d.name).second)
                inputs_.push_back(d.name);
              return;
            }
          long long w;
          if (!eval_ap_width(d, w))
            return;           // diagnosed by eval_ap_width
          for (long long i = 0; i < w; ++i)
            {
              std::string name = d.name + '_' + std::to_string(i);
              if (base_is_output(d.name))
                {
                  if (seen_outputs_.insert(name).second)
                    outputs_.push_back(name);
                }
              else if (seen_inputs_.insert(name).second)
                inputs_.push_back(name);
            }
        };
      for (const auto& d : ast_.inputs)
        register_decl(d);
      for (const auto& d : ast_.outputs)
        register_decl(d);

      // 2. Translate each MAIN subsection as the conjunction of its
      //    body.  An empty body folds to tt(); a singleton body is
      //    returned as-is when wrapping in tt()∧x would just simplify
      //    to x anyway.
      auto conjunction =
        [&](const std::vector<tlsf_expr_ptr>& body) -> formula
        {
          if (body.empty())
            return formula::tt();
          std::vector<formula> parts;
          parts.reserve(body.size());
          for (const auto& e : body)
            parts.push_back(translate_expr(*e));
          return formula::And(parts);
        };

      formula initially = conjunction(ast_.initially_body);
      formula preset    = conjunction(ast_.preset_body);
      formula require   = conjunction(ast_.require_body);
      formula assumptions = conjunction(ast_.assumptions_body);
      formula assertion = conjunction(ast_.assert_body);
      formula guarantee = conjunction(ast_.guarantee_body);

      // 2b. Coverage constraints of typed buses.
      //
      // A typed bus may only carry a valuation that one of its enum
      // tags covers; this keeps the environment from driving an
      // uninterpreted pattern.  Two exact encodings of that set are
      // available and the smaller one is used.
      //
      //  * The factored coverage formula: the disjunction over tags
      //    of the conjunction over the tag's patterns of the
      //    conjunction over each pattern's pinned bits.  Its size is
      //    bounded by the source text, because a pattern with k stars
      //    contributes the bits it pins, not the 2^k valuations it
      //    covers.  It is therefore always available.
      //
      //  * Its complement: one disjunct ("some bit differs") per
      //    valuation that no tag covers.  More compact when the enum
      //    covers most of the space, but 2^w terms wide.
      //
      // The complement used to be the only encoding, which built a
      // 65535-term formula for a 16-bit bus and overflowed
      // formula::nary's child limit for anything wider; that overflow
      // is signalled by an exception the translator did not catch, so
      // a perfectly ordinary 17-bit enum aborted the process.
      //
      // Input buses contribute to REQUIRE, output buses to ASSERT.
      // Widest bus for which the covered valuations are enumerated to
      // compare the two encodings.  Above it the factored form is
      // used without looking, since 2^w valuations cannot be walked
      // anyway and the factored form is a sound, compact answer.
      static constexpr long long max_scan_width = 20;

      auto enum_coverage =
        [&](const std::vector<tlsf_ap_decl>& decls) -> formula
        {
          std::vector<formula> parts;
          for (const auto& d : decls)
            {
              if (d.enum_type.empty())
                continue;
              const tlsf_enum_decl* en = find_enum(d.enum_type);
              if (!en)
                continue;   // already diagnosed by eval_ap_width
              long long w;
              if (!eval_ap_width(d, w) || w <= 0)
                continue;   // diagnosed, or a zero-width bus
              // The bus bits are APs registered by run()'s
              // register_decl pass (see run()) before any section is
              // translated.  Build each of them once per bus: the name
              // is a string concatenation, and the loops below ask for
              // the same bit over and over.
              std::vector<formula> bits;
              bits.reserve(static_cast<size_t>(w));
              for (long long i = 0; i < w; ++i)
                bits.push_back(formula::ap(d.name + '_' + std::to_string(i)));
              auto bit_ap = [&](long long i) -> const formula&
                {
                  return bits[static_cast<size_t>(i)];
                };
              // A pattern covers v iff every non-star bit of p equals
              // the corresponding bit of v, so the conjunction over p's
              // fixed bits denotes exactly the valuations p covers.
              // Pattern position k is significance order, i.e. bit
              // w-1-k of the valuation.
              std::vector<formula> tag_terms;
              // Sum over the patterns of 2^(number of stars): an
              // upper bound on the number of covered valuations, used
              // below to pick the encoding without enumerating.  It
              // saturates so a wide bus cannot overflow the shift.
              long long span_bound = 0;
              for (const auto& entry : en->entries)
                {
                  std::vector<formula> pattern_terms;
                  for (const auto& pat : entry.patterns)
                    {
                      if (pat.size() != static_cast<size_t>(w))
                        continue;   // diagnosed by the parser
                      std::vector<formula> lits;
                      unsigned stars = 0;
                      for (long long k = 0; k < w; ++k)
                        {
                          const char c =
                            pat[static_cast<size_t>(w - 1 - k)];
                          if (c == '*')
                            {
                              ++stars;
                              continue;
                            }
                          lits.push_back(c == '1'
                                         ? bit_ap(k)
                                         : formula::Not(bit_ap(k)));
                        }
                      // An all-star pattern pins nothing, and covers
                      // every valuation.
                      pattern_terms.push_back(lits.empty()
                                              ? formula::tt()
                                              : formula::And(lits));
                      span_bound = stars < 31
                        ? span_bound + (1LL << stars) : (1LL << 31);
                    }
                  // A tag's pattern list is a union of alternatives,
                  // as in the canonical `UNDEF: 11*, 1*1, *11`.
                  if (!pattern_terms.empty())
                    tag_terms.push_back(formula::Or(pattern_terms));
                }
              if (tag_terms.empty())
                continue;   // no usable pattern, nothing to constrain
              const formula factored = formula::Or(tag_terms);
              // The factored form is the smaller one as soon as the
              // tags pin at most half of the space; that bound needs
              // no enumeration and settles the common case.
              if (w > max_scan_width || span_bound <= (1LL << (w - 1)))
                {
                  parts.push_back(factored);
                  continue;
                }
              // Otherwise count the covered valuations exactly and
              // build the complement.  A bitmap indexed by the
              // valuation records coverage, so the patterns are
              // expanded once (work follows the number of stars) and
              // the complement is then a bit scan rather than a
              // sort plus a search over a sorted vector.  The bitmap
              // is capped so a wide bus cannot allocate wildly: past
              // the cap the factored form is kept, which the test
              // below detects without allocating.
              const unsigned long long space = 1ULL << w;
              std::vector<bool> covered;
              if (w < 24)
                covered.assign(static_cast<size_t>(space), false);
              long long ncovered = 0;
              bool overflowed = false;
              for (const auto& entry : en->entries)
                for (const auto& pat : entry.patterns)
                  {
                    if (pat.size() != static_cast<size_t>(w))
                      continue;   // diagnosed by the parser
                    long long base = 0;
                    std::vector<long long> free_pos;
                    for (long long k = 0; k < w; ++k)
                      {
                        const char c =
                          pat[static_cast<size_t>(w - 1 - k)];
                        if (c == '*')
                          free_pos.push_back(k);
                        else if (c == '1')
                          base |= 1LL << k;
                      }
                    const bool track = !covered.empty();
                    for (long long sub = 0, span = 1LL << free_pos.size();
                         sub < span; ++sub)
                      {
                        long long v = base;
                        for (size_t b = 0; b < free_pos.size(); ++b)
                          if ((sub >> b) & 1)
                            v |= 1LL << free_pos[b];
                        if (!track)
                          continue;
                        if (!covered[static_cast<size_t>(v)])
                          {
                            covered[static_cast<size_t>(v)] = true;
                            ++ncovered;
                          }
                      }
                    // Every valuation is covered: the complement is
                    // empty and the factored form already says so.
                    if (ncovered == static_cast<long long>(space))
                      {
                        overflowed = true;
                        break;
                      }
                  }
              const long long nmissing =
                static_cast<long long>(space) - ncovered;
              // Take the complement only when it is both smaller than
              // the factored form and small enough to fit in a
              // formula; otherwise keep the factored form.
              if (overflowed || covered.empty()
                  || nmissing > max_formula_children
                  || nmissing >= ncovered)
                {
                  parts.push_back(factored);
                  continue;
                }
              std::vector<formula> disjoint;
              disjoint.reserve(static_cast<size_t>(nmissing));
              for (long long v = 0; v < static_cast<long long>(space);
                   ++v)
                {
                  if (covered[static_cast<size_t>(v)])
                    continue;
                  // Or_i (bit i of the bus differs from bit i of v)
                  std::vector<formula> differs;
                  differs.reserve(static_cast<size_t>(w));
                  for (long long i = 0; i < w; ++i)
                    differs.push_back(((v >> i) & 1)
                                      ? formula::Not(bit_ap(i))
                                      : bit_ap(i));
                  disjoint.push_back(formula::Or(differs));
                }
              parts.push_back(formula::And(disjoint));
            }
          if (parts.empty())
            return formula::tt();
          while (parts.size() > static_cast<size_t>(max_formula_children))
            {
              // A pathological number of typed buses: fold the
              // collected constraints pairwise, so that no single
              // conjunction exceeds the child limit of formula::nary.
              std::vector<formula> folded;
              folded.reserve((parts.size() + 1) / 2);
              for (size_t i = 0; i < parts.size(); i += 2)
                folded.push_back(i + 1 < parts.size()
                                 ? formula::And({parts[i],
                                                       parts[i + 1]})
                                 : parts[i]);
              parts.swap(folded);
            }
          return formula::And(parts);
        };
      formula covered_in = enum_coverage(ast_.inputs);
      formula covered_out = enum_coverage(ast_.outputs);
      require = formula::And({require, covered_in});
      assertion = formula::And({assertion, covered_out});

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

      formula environment =
        formula::And({formula::G(require), assumptions});

      const bool strict =
        ast_.semantics == tlsf_semantics::MealyStrict
        || ast_.semantics == tlsf_semantics::MooreStrict;

      formula system = strict
        ? guarantee
        : formula::And({formula::G(assertion), guarantee});
      formula conditional =
        formula::Implies(environment, system);

      formula core;
      if (strict)
        {
          formula w =
            formula::W(assertion, formula::Not(require));
          core = formula::And({preset, conditional, w});
        }
      else
        {
          core = formula::And({preset, conditional});
        }

      result.full_formula = formula::Implies(initially, core);
      result.full_formula = failed_ ? formula(nullptr)
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
