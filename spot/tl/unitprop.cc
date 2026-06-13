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
#include <spot/tl/unitprop.hh>
#include <spot/priv/robin_hood.hh>
#include <vector>

namespace spot
{
  namespace
  {
    // A fact map counts how many different children contributed a
    // given formula to the fact set.  Using a count instead of a
    // simple set allows the exclusion mechanism to work correctly:
    // when we exclude the facts contributed by child i (to avoid
    // simplifying the source of a fact using that same fact), we
    // decrement their counts, and only actually remove a fact when
    // its count reaches 0 (i.e., no other child provides the same
    // fact).
    using fmap = robin_hood::unordered_map<formula, int>;

    // A contribution records which facts a child adds to each of the
    // four fact sets (true global, true local, false global, false
    // local).  Each entry is a (formula, is_global) pair.
    using fvec = std::vector<std::pair<formula, bool>>;
    struct contribution
    {
      fvec true_facts;
      fvec false_facts;
    };

    // Propagation context holding the four fact sets.
    struct up_ctx
    {
      fmap true_G;   // globally true formulas (persist across temporal ops)
      fmap true_L;   // locally true formulas (dropped at X/G/F/U/W/R/M)
      fmap false_G;  // globally false formulas
      fmap false_L;  // locally false formulas

      bool is_true(formula f) const
      {
        return true_G.contains(f) || true_L.contains(f);
      }

      bool is_false(formula f) const
      {
        return false_G.contains(f) || false_L.contains(f);
      }
    };

    void add_map(fmap& m, formula f, int delta)
    {
      int& v = m[f];
      v += delta;
      if (v == 0)
        m.erase(f);
    }

    // Apply a single (formula, is_global) pair to the TRUE fact sets.
    // If f = Not(g), also update the FALSE fact sets symmetrically.
    void apply_true(up_ctx& ctx, formula f, bool global, int delta)
    {
      add_map(global ? ctx.true_G : ctx.true_L, f, delta);
      if (f.is(op::Not))
        add_map(global ? ctx.false_G : ctx.false_L, f[0], delta);
    }

    // Dual: apply to the FALSE fact sets.
    void apply_false(up_ctx& ctx, formula f, bool global, int delta)
    {
      add_map(global ? ctx.false_G : ctx.false_L, f, delta);
      if (f.is(op::Not))
        add_map(global ? ctx.true_G : ctx.true_L, f[0], delta);
    }

    // Apply a whole contribution (all true and false facts) to ctx.
    void apply(const contribution& c, up_ctx& ctx, int delta)
    {
      for (auto [f, global]: c.true_facts)
        apply_true(ctx, f, global, delta);
      for (auto [f, global]: c.false_facts)
        apply_false(ctx, f, global, delta);
    }

    // Forward declarations for mutual recursion.
    void add_true(contribution& c, formula f, bool global);
    void add_false(contribution& c, formula f, bool global);

    // Record a true fact in a contribution.
    // The fact f is recorded as-is; composites are also broken down:
    //   - Not(g): g is recursively recorded as a false fact.
    //   - And(…): each child is recursively added with the same locality,
    //     because if f is true all its conjuncts are true.
    //   - G(φ):   φ is added as a globally true fact, because G entails
    //     φ at every step.
    //   - R(α,β), M(α,β): β is added as a true fact (same locality),
    //     because (α R β) ≡ β ∧ (α ∨ X(α R β)) and
    //     (α M β) ≡ β ∧ (α ∧ X(α M β)).
    void add_true(contribution& c, formula f, bool global)
    {
      if (f.is_tt() || f.is_ff())
        return;
      c.true_facts.emplace_back(f, global);
      if (f.is(op::Not))
        add_false(c, f[0], global);
      else if (f.is(op::And))
        for (const formula& child: f)
          add_true(c, child, global);
      else if (f.is(op::G))
        add_true(c, f[0], true);
      else if (f.is(op::R) || f.is(op::M))
        add_true(c, f[1], global);
    }

    // Dual: record a false fact.
    //   - Not(g): g is recursively recorded as a true fact.
    //   - Or(…): each child is recursively added with the same locality,
    //     because if f is false all its disjuncts are false.
    //   - F(φ):  φ is added as a globally false fact, because F entails
    //     φ never holds at any step.
    //   - U(α,β), W(α,β): β is added as a false fact (same locality),
    //     because (α U β) ≡ β ∨ (α ∧ X(α U β)) and
    //     (α W β) ≡ β ∨ (α ∧ X(α W β)).
    void add_false(contribution& c, formula f, bool global)
    {
      if (f.is_tt() || f.is_ff())
        return;
      c.false_facts.emplace_back(f, global);
      if (f.is(op::Not))
        add_true(c, f[0], global);
      else if (f.is(op::Or))
        for (const formula& child: f)
          add_false(c, child, global);
      else if (f.is(op::F))
        add_false(c, f[0], true);
      else if (f.is(op::U) || f.is(op::W))
        add_false(c, f[1], global);
    }

    // Forward declaration.
    formula up_rec(formula f, up_ctx& ctx);

    // Collect true facts from the antecedent of an Implies.
    // The And/G breakdown in add_true handles everything recursively.
    void implies_true_contrib_from(contribution& c, formula alpha)
    {
      add_true(c, alpha, false);
    }

    // Collect false facts from the consequent of an Implies into a
    // contribution.  If β holds then the implication is trivially
    // true, so assuming β is false is the interesting case for
    // simplifying the antecedent.
    // The Or/F breakdown in add_false handles everything recursively.
    void implies_false_contrib_from(contribution& c, formula beta)
    {
      add_false(c, beta, false);
    }

    // Process an And or Or node with the current context.
    formula process_and_or(formula f, bool is_and, up_ctx& ctx)
    {
      unsigned n = f.size();

      // Collect the contribution of every child and apply them all to
      // the context so that siblings can see each other's facts.
      std::vector<contribution> contribs;
      contribs.reserve(n);
      for (unsigned i = 0; i < n; ++i)
        {
          contribution& c = contribs.emplace_back();
          if (is_and)
            add_true(c, f[i], false);
          else
            add_false(c, f[i], false);
          apply(c, ctx, +1);
        }

      // Simplify each child with its OWN contribution temporarily
      // removed, so that a formula cannot simplify itself (DAG
      // sharing: the same pointer may appear elsewhere in the tree).
      //
      // When a child is dropped (simplifies to tt in And, or ff in
      // Or), its contribution is NOT re-applied.  This prevents the
      // dropped child's facts from being used to over-simplify its
      // siblings: if child A drops itself using child B's local fact,
      // child B must not then use A's global facts for further
      // simplification, since A is no longer in the formula.
      std::vector<formula> result;
      result.reserve(n);
      bool changed = false;

      // still_applied[i]: true iff contribution i is currently in ctx.
      std::vector<bool> still_applied(n, true);

      for (unsigned i = 0; i < n; ++i)
        {
          apply(contribs[i], ctx, -1);
          still_applied[i] = false;

          formula s = up_rec(f[i], ctx);

          const bool drop = is_and ? s.is_tt() : s.is_ff();
          const bool abort = is_and ? s.is_ff() : s.is_tt();

          if (drop)
            {
              // Permanently exclude: do NOT re-apply.
              changed = true;
            }
          else if (abort)
            {
              // Short-circuit result.  Remove all remaining
              // contributions from the context.
              for (unsigned j = 0; j < n; ++j)
                if (still_applied[j])
                  apply(contribs[j], ctx, -1);
              return is_and ? formula::ff() : formula::tt();
            }
          else
            {
              // Keep this child: re-apply its contribution.
              apply(contribs[i], ctx, +1);
              still_applied[i] = true;
              if (s != f[i])
                changed = true;
              result.push_back(s);
            }
        }

      // Remove all contributions still in the context.
      for (unsigned i = 0; i < n; ++i)
        if (still_applied[i])
          apply(contribs[i], ctx, -1);

      if (!changed)
        return f;
      if (result.empty())
        return is_and ? formula::tt() : formula::ff();
      if (result.size() == 1)
        return result[0];
      return formula::multop(is_and ? op::And : op::Or,
                             std::move(result));
    }

    formula up_rec(formula f, up_ctx& ctx)
    {
      if (f.is_tt() || f.is_ff())
        return f;

      // If f is already a known fact, replace it with a constant.
      if (ctx.is_true(f))
        return formula::tt();
      if (ctx.is_false(f))
        return formula::ff();

      switch (f.kind())
        {
        case op::tt:
        case op::ff:
        case op::ap:
          return f;

        case op::Not:
          {
            formula child = up_rec(f[0], ctx);
            if (child == f[0])
              return f;
            return formula::Not(child);
          }

        case op::And:
          return process_and_or(f, true, ctx);

        case op::Or:
          return process_and_or(f, false, ctx);

        case op::X:
        case op::strong_X:
          {
            // Drop local facts at a Next operator.
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula child = up_rec(f[0], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (child == f[0])
              return f;
            return f.is(op::X) ? formula::X(child)
                                : formula::strong_X(child);
          }

        case op::G:
          {
            // If child is known false (locally or globally),
            // G(child) = ff.
            if (ctx.is_false(f[0]))
              return formula::ff();
            // G(child) = tt when child is globally true is handled
            // automatically by the recursion: the top-level check in
            // up_rec() will replace the child by 1, and the formula
            // constructor handles G(1) = 1.
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula child = up_rec(f[0], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (child == f[0])
              return f;
            return formula::G(child);
          }

        case op::F:
          {
            // If child is known true (locally or globally),
            // F(child) = tt, because "now" counts as "eventually".
            if (ctx.is_true(f[0]))
              return formula::tt();
            // F(child) = ff when child is globally false is handled
            // automatically by the recursion: the top-level check in
            // up_rec() will replace the child by 0, and the formula
            // constructor handles F(0) = 0.
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula child = up_rec(f[0], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (child == f[0])
              return f;
            return formula::F(child);
          }

        case op::U:
        case op::W:
          {
            // If the right operand is known true (locally or globally),
            // (α U β) ≡ tt and (α W β) ≡ tt, since β holds now.
            if (ctx.is_true(f[1]))
              return formula::tt();
            // For U: if the right operand is globally false, it can
            // never hold, so (α U β) ≡ ff.  This shortcut is not
            // superfluous: it avoids recursively simplifying the
            // left operand α when β is already known to be impossible.
            if (f.is(op::U) && ctx.false_G.contains(f[1]))
              return formula::ff();
            // For W: if the left operand is globally true, then G α
            // holds, so (α W β) ≡ (α U β) ∨ G α ≡ tt.  This shortcut
            // avoids recursively simplifying the right operand β.
            if (f.is(op::W) && ctx.true_G.contains(f[0]))
              return formula::tt();
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula left = up_rec(f[0], ctx);
            formula right = up_rec(f[1], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (left == f[0] && right == f[1])
              return f;
            return formula::binop(f.kind(), left, right);
          }

        case op::R:
        case op::M:
          {
            // If the right operand is known false (locally or globally),
            // (α R β) ≡ ff and (α M β) ≡ ff, since β fails now.
            if (ctx.is_false(f[1]))
              return formula::ff();
            // For R: if the right operand is globally true, then
            // G β holds, so (α R β) ≡ tt.  This shortcut is not
            // superfluous: it avoids recursively simplifying the
            // left operand α when β is already known to hold forever.
            if (f.is(op::R) && ctx.true_G.contains(f[1]))
              return formula::tt();
            // For M: if the left operand is globally false, then
            // F α ≡ ff, so (α M β) ≡ (α R β) ∧ F α ≡ ff.  This
            // shortcut avoids recursively simplifying the right
            // operand β when α is already known to be impossible.
            if (f.is(op::M) && ctx.false_G.contains(f[0]))
              return formula::ff();
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula left = up_rec(f[0], ctx);
            formula right = up_rec(f[1], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (left == f[0] && right == f[1])
              return f;
            return formula::binop(f.kind(), left, right);
          }

        case op::Implies:
          {
            formula alpha = f[0];
            formula beta = f[1];

            // Collect false facts from β: if β were true the
            // implication would be trivial, so assuming β false is
            // the interesting case when simplifying α.
            contribution beta_c;
            implies_false_contrib_from(beta_c, beta);

            // Simplify α assuming β is false.
            apply(beta_c, ctx, +1);
            formula new_alpha = up_rec(alpha, ctx);
            apply(beta_c, ctx, -1);

            // Collect true facts from the SIMPLIFIED α to use when
            // simplifying β.  Using new_alpha (not the original α)
            // ensures that the two simplifications are sequential and
            // sound: first alpha is simplified to new_alpha, then
            // beta is simplified assuming new_alpha holds.
            contribution new_alpha_c;
            implies_true_contrib_from(new_alpha_c, new_alpha);

            // Simplify β assuming (simplified) α is true.
            apply(new_alpha_c, ctx, +1);
            formula new_beta = up_rec(beta, ctx);
            apply(new_alpha_c, ctx, -1);

            if (new_alpha == alpha && new_beta == beta)
              return f;
            return formula::Implies(new_alpha, new_beta);
          }

        case op::Equiv:
        case op::Xor:
          {
            // These operators mix polarities; drop local facts to be
            // conservative and only keep global ones.
            fmap saved_tl = std::move(ctx.true_L);
            fmap saved_fl = std::move(ctx.false_L);
            ctx.true_L = {};
            ctx.false_L = {};
            formula left = up_rec(f[0], ctx);
            formula right = up_rec(f[1], ctx);
            ctx.true_L = std::move(saved_tl);
            ctx.false_L = std::move(saved_fl);
            if (left == f[0] && right == f[1])
              return f;
            return formula::binop(f.kind(), left, right);
          }

        default:
          // PSL operators and other constructs: do not propagate.
          return f;
        }
    }
  } // anonymous namespace

  formula unit_propagate(formula f)
  {
    up_ctx ctx;
    return up_rec(f, ctx);
  }
}
