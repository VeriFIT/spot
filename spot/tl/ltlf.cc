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
#include <spot/tl/ltlf.hh>
#include <spot/priv/robin_hood.hh>
#include <iostream>

namespace spot
{
  namespace
  {
    formula from_ltlf_aux(formula f, formula alive)
    {
      auto t = [&alive] (formula f) { return from_ltlf_aux(f, alive); };
      switch (auto o = f.kind())
        {
        case op::strong_X:
          o = op::X;
          SPOT_FALLTHROUGH;
        case op::F:
          return formula::unop(o, formula::And(alive, t(f[0])));
        case op::X:             // weak
        case op::G:
          {
            formula dead = formula::Not(alive);
            return formula::unop(o, formula::Or(dead, t(f[0])));
            // Note that the t() function given in the proof of Theorem 1 of
            // the IJCAI'13 paper by De Giacomo & Vardi has a typo.
            //  t(a U b) should be equal to t(a) U t(b & alive).
            // This typo is fixed in the Memocode'14 paper by Dutta & Vardi.
            //
            // (However beware that the translation given in the
            // Memocode'14 paper forgets to ensure that alive holds
            // initially, as required in the IJCAI'13 paper.)
          }
        case op::U:
          {
            formula t0 = t(f[0]);
            return formula::U(t0, formula::And(alive, t(f[1])));
          }
        case op::R:
          {
            formula t0 = t(f[0]);
            formula dead = formula::Not(alive);
            return formula::R(t0, formula::Or(dead, t(f[1])));
          }
        case op::M:
          {
            formula t0 = formula::And(alive, t(f[0]));
            return formula::M(t0, t(f[1]));
          }
        case op::W:
          {
            formula dead = formula::Not(alive);
            formula t0 = formula::Or(dead, t(f[0]));
            return formula::W(t0, t(f[1]));
          }
        default:
          return f.map(t);
        }
    }
  }

  formula from_ltlf(formula f, const char* alive)
  {
    if (!f.is_ltl_formula())
      throw std::runtime_error("from_ltlf() only supports LTL formulas");
    auto al = ((*alive == '!')
               ? formula::Not(formula::ap(alive + 1))
               : formula::ap(alive));
    return formula::And({from_ltlf_aux(f, al), al,
                         formula::U(al, formula::G(formula::Not(al)))});
  }


  typedef robin_hood::unordered_map<formula, formula> formula_cache;

  static formula
  ltlf_one_step_sat_rewrite_cached(formula f, formula_cache* c)
  {
    if (f.is_boolean())
      return f;
    if (auto it = c->find(f); it != c->end())
      return it->second;
    formula g = f;
    switch (f.kind())
      {
      case op::ap:
      case op::tt:
      case op::ff:
        SPOT_UNREACHABLE();
        break;
      case op::X:
        f = formula::tt();
        break;
      case op::strong_X:
        f = formula::ff();
        break;
      case op::G:
      case op::F:
        f = ltlf_one_step_sat_rewrite_cached(f[0], c);
        break;
      case op::R:
      case op::U:
        f = ltlf_one_step_sat_rewrite_cached(f[1], c);
        break;
      case op::W:
        {
          formula f0 = ltlf_one_step_sat_rewrite_cached(f[0], c);
          f = formula::Or(f0, ltlf_one_step_sat_rewrite_cached(f[1], c));
          break;
        }
      case op::M:
        {
          formula f0 = ltlf_one_step_sat_rewrite_cached(f[0], c);
          f = formula::And(f0, ltlf_one_step_sat_rewrite_cached(f[1], c));
          break;
        }
      case op::And:
      case op::Or:
      case op::Not:
      case op::Xor:
      case op::Equiv:
      case op::Implies:
        f = f.map(ltlf_one_step_sat_rewrite_cached, c);
        break;
      case op::eword:
      case op::AndNLM:
      case op::AndRat:
      case op::Closure:
      case op::Concat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::first_match:
      case op::FStar:
      case op::Fusion:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::OrRat:
      case op::Star:
      case op::UConcat:
        formula::report_message("ltlf_one_step_sat_rewrite(): "
                                "unsupported operator");
      case op::exists:
      case op::forall:
        formula::report_message("ltlf_one_step_sat_rewrite(): "
                                "quantification unsupported");
      }
    c->emplace(g, f);
    return f;
  }

  formula ltlf_one_step_sat_rewrite(formula f)
  {
    formula_cache c;
    return ltlf_one_step_sat_rewrite_cached(f, &c);
  }

  ltlf_one_step_sat_rewrite_with_cache::ltlf_one_step_sat_rewrite_with_cache()
  {
    cache_ = new formula_cache;
  }

  ltlf_one_step_sat_rewrite_with_cache::~ltlf_one_step_sat_rewrite_with_cache()
  {
    delete static_cast<formula_cache*>(cache_);
  }

  formula ltlf_one_step_sat_rewrite_with_cache::rewrite(formula f)
  {
    return
      ltlf_one_step_sat_rewrite_cached(f, static_cast<formula_cache*>(cache_));
  }

  static formula
  ltlf_one_step_unsat_rewrite_cached(formula f, bool negate,
                                     formula_cache* c)
  {
    if (f.is_boolean())
      return negate ? formula::Not(f) : f;

    formula_cache& cc = c[negate];
    if (auto it = cc.find(f); it != cc.end())
      return it->second;
    formula g = f;
    switch (op o = f.kind())
      {
      case op::Not:
        f = ltlf_one_step_unsat_rewrite_cached(f[0], !negate, c);
        break;
      case op::ap:
      case op::tt:
      case op::ff:
        SPOT_UNREACHABLE();
        break;
      case op::X:
      case op::strong_X:
        f = formula::tt();
        break;
      case op::F:
        if (negate)           // G
          f = ltlf_one_step_unsat_rewrite_cached(f[0], true, c);
        else
          f = formula::tt();
        break;
      case op::G:
        if (negate)           // F
          f = formula::tt();
        else
          f = ltlf_one_step_unsat_rewrite_cached(f[0], false, c);
        break;
      case op::R:
      case op::M:
        if (negate)           // U, W
          {
            formula f0 = ltlf_one_step_unsat_rewrite_cached(f[0], true, c);
            f = formula::Or(f0,
                            ltlf_one_step_unsat_rewrite_cached(f[1], true, c));
          }
        else
          {
            f = ltlf_one_step_unsat_rewrite_cached(f[1], false, c);
          }
        break;
      case op::U:
      case op::W:
        if (negate)         // R, M
          {
            f = ltlf_one_step_unsat_rewrite_cached(f[1], true, c);
          }
        else
          {
            formula f0 = ltlf_one_step_unsat_rewrite_cached(f[0], false, c);
            f = formula::Or(f0,
                            ltlf_one_step_unsat_rewrite_cached(f[1], false, c));
          }
        break;
      case op::Implies:
        if (negate)
          // !(a => b) == a & !b
          {
            formula f2 = ltlf_one_step_unsat_rewrite_cached(f[1], true, c);
            f = formula::And(ltlf_one_step_unsat_rewrite_cached(f[0], false, c),
                             f2);
          }
        else // a => b == !a | b
          {
            formula f2 = ltlf_one_step_unsat_rewrite_cached(f[1], false, c);
            f = formula::Or(ltlf_one_step_unsat_rewrite_cached(f[0], true, c),
                            f2);
          }
        break;
      case op::Xor:
      case op::Equiv:
        {
          formula a = ltlf_one_step_unsat_rewrite_cached(f[0], false, c);
          formula b = ltlf_one_step_unsat_rewrite_cached(f[1], false, c);
          formula na = ltlf_one_step_unsat_rewrite_cached(f[0], true, c);
          formula nb = ltlf_one_step_unsat_rewrite_cached(f[1], true, c);
          if ((o == op::Xor) == negate) // equiv
            {
              formula f1 = formula::And(a, b);
              formula f2 = formula::And(na, nb);
              f = formula::Or(f1, f2);
            }
          else
            {
              formula f1 = formula::And(a, nb);
              formula f2 = formula::And(na, b);
              f = formula::Or(f1, f2);
            }
          break;
        }
      case op::And:
      case op::Or:
        {
          unsigned mos = f.size();
          std::vector<formula> v;
          formula abs =
            ((o == op::Or) == negate) ? formula::ff() : formula::tt();
          for (unsigned i = 0; i < mos; ++i)
            {
              formula g = ltlf_one_step_unsat_rewrite_cached(f[i], negate, c);
              if (g == abs)     // abort early on absorbent element
                {
                  f = abs;
                  goto done;
                }
              v.emplace_back(g);
            }
          op on = o;
          if (negate)
            on = o == op::Or ? op::And : op::Or;
          f = formula::multop(on, v);
          break;
        }
      case op::eword:
      case op::AndNLM:
      case op::AndRat:
      case op::Closure:
      case op::Concat:
      case op::EConcat:
      case op::EConcatMarked:
      case op::first_match:
      case op::FStar:
      case op::Fusion:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::OrRat:
      case op::Star:
      case op::UConcat:
        formula::report_message("ltlf_one_step_unsat_rewrite(): "
                                "unsupported operator");
      case op::exists:
      case op::forall:
        formula::report_message("ltlf_one_step_unsat_rewrite(): "
                                "quantification unsupported");
      }
  done:
    cc.emplace(g, f);
    return f;
  }

  formula ltlf_one_step_unsat_rewrite(formula f, bool negated)
  {
    formula_cache c[2];
    return ltlf_one_step_unsat_rewrite_cached(f, negated, c);
  }

  ltlf_one_step_unsat_rewrite_with_cache::
  ltlf_one_step_unsat_rewrite_with_cache()
  {
    cache_ = new formula_cache[2];
  }

  ltlf_one_step_unsat_rewrite_with_cache::
  ~ltlf_one_step_unsat_rewrite_with_cache()
  {
    delete[] static_cast<formula_cache*>(cache_);
  }

  formula ltlf_one_step_unsat_rewrite_with_cache::rewrite(formula f)
  {
    return ltlf_one_step_unsat_rewrite_cached
      (f, false, static_cast<formula_cache*>(cache_));
  }


  class ltlf_simplifier::cache
  {
  public:
    robin_hood::unordered_map<formula, formula> pos;
    robin_hood::unordered_map<formula, formula> neg;
  };

  ltlf_simplifier::ltlf_simplifier()
  {
    cache_ = new cache;
  }

  ltlf_simplifier::~ltlf_simplifier()
  {
    delete cache_;
  }

  formula ltlf_simplifier::simplify(formula f, bool negated)
  {
    if (negated)
      {
        auto it = cache_->neg.find(f);
        if (it != cache_->neg.end())
          return it->second;
        return cache_->neg[f] = simplify_aux(f, true);
      }
    else
      {
        auto it = cache_->pos.find(f);
        if (it != cache_->pos.end())
          return it->second;
        return cache_->pos[f] = simplify_aux(f, false);
      }
  }

  // if vec = [Xa, Fb, Fc, Gd, e], match = F, combine = &
  // this returns [Xa, F(b & c), Gd, e]
  static std::vector<formula>
  group_op(std::vector<formula>&& vec, op match, op combine)
  {
    std::vector<formula> matched;
    matched.reserve(vec.size());
    for (formula f: vec)
      if (f.kind() == match)
        matched.push_back(f[0]);
    if (matched.empty())
      return vec;
    formula f = formula::unop(match, formula::multop(combine, matched));
    matched.clear();
    matched.push_back(f);
    for (formula f: vec)
      if (f.kind() != match)
        matched.push_back(f);
    return matched;
  }


  formula ltlf_simplifier::simplify_aux(formula f, bool negated)
  {
    switch (op o = f.kind())
      {
      case op::eword:
      case op::Closure:
      case op::NegClosure:
      case op::NegClosureMarked:
      case op::EConcat:
      case op::EConcatMarked:
      case op::UConcat:
      case op::OrRat:
      case op::AndRat:
      case op::AndNLM:
      case op::Concat:
      case op::Fusion:
      case op::Star:
      case op::FStar:
      case op::first_match:
        SPOT_UNREACHABLE();
        return f;
      case op::ff:
        return negated ? formula::tt() : f;
      case op::tt:
        return negated ? formula::ff() : f;
      case op::ap:
        return negated ? formula::Not(f) : f;
      case op::Not:
        return simplify(f[0], !negated);
      case op::X:
      case op::strong_X:
        {
          formula res = simplify(f[0], negated);
          if (negated == (o == op::X))
            return formula::strong_X(res);
          else
            return formula::X(res);
        }
      case op::F:
      case op::G:
        {
          formula res = simplify(f[0], negated);
          // FG or GF ?
          if (res.is(op::F, op::G) && f.kind() != res.kind())
            return formula::G(formula::F(ltlf_one_step_sat_rewrite(res[0])));

          if (negated == (o == op::F))
            return formula::G(res);
          else
            return formula::F(res);
        }
      case op::U:
      case op::R:
        {
          formula res1 = simplify(f[0], negated);
          formula res2 = simplify(f[1], negated);
          if (negated == (o == op::U))
            return formula::R(res1, res2);
          else
            return formula::U(res1, res2);
        }
      case op::W:
      case op::M:
        {
          formula res1 = simplify(f[0], negated);
          formula res2 = simplify(f[1], negated);
          if (negated == (o == op::W))
            return formula::M(res1, res2);
          else
            return formula::W(res1, res2);
        }
      case op::Xor:
      case op::Equiv:
        {
          formula left = f[0];
          if (left.is(op::Not))
            {
              left = left[0];
              negated = !negated;
            }
          formula right = f[1];
          if (right.is(op::Not))
            {
              right = right[0];
              negated = !negated;
            }
          formula res1 = simplify(left, false);
          formula res2 = simplify(right, false);
          if (negated == (o == op::Xor))
            return formula::Equiv(res1, res2);
          else
            return formula::Xor(res1, res2);
        }
      case op::Implies:
        if (negated) // !(a -> b)  =  s(a) & s(!b)
          {
            formula left = simplify(f[0], false);
            formula right = simplify(f[1], true);
            return formula::And(left, right);
          }
        // !a -> b  =  s(a) | s(b)
        if (f[0].is(op::Not))
          {
            formula left = simplify(f[0][0], false);
            formula right = simplify(f[1], false);
            return formula::Or(left, right);
          }
        // bool1 -> bool2  =  s(!bool1) | s(bool2)
        if (f[0].is_boolean() || f[1].is_boolean())
          {
            formula left = simplify(f[0], true);
            formula right = simplify(f[1], false);
            return formula::Or(left, right);
          }
        // a -> b  =  s(a) -> s(b)
        {
          formula left = simplify(f[0], false);
          formula right = simplify(f[1], false);
          return formula::Implies(left, right);
        }
      case op::Or:
      case op::And:
        {
          std::vector<formula> res;
          for (const formula& sub : f)
            res.push_back(simplify(sub, negated));

          op opos = o;
          op oneg = opos == op::Or ? op::And : op::Or;
          if (negated)
            std::swap(opos, oneg);

          if (opos == op::And)
            {
              // (a -> b1) & (a -> b2) & rest  =  (a -> (b1 & b2)) & rest
              // G(a) & G(b) & GF(c) & GF(d) & rest = G(a & b & F(c & d)) & rest
              robin_hood::unordered_map<formula, std::vector<formula>> map;
              std::vector<formula> inG;
              std::vector<formula> rest;
              std::vector<formula> inXw;
              std::vector<formula> inXs;
              bool found = false;
              for (const formula& sub: res)
                if (sub.is(op::Implies))
                  {
                    auto& bs = map[sub[0]];
                    bs.push_back(sub[1]);
                    if (bs.size() == 2)
                      found = true;
                  }
                else if (sub.is(op::G))
                  {
                    inG.push_back(sub[0]);
                    if (inG.size() == 2)
                      found = true;
                  }
                else if (sub.is(op::strong_X))
                  {
                    inXs.push_back(sub[0]);
                    if (inXs.size() == 2)
                      found = true;
                  }
                else if (sub.is(op::X))
                  {
                    inXw.push_back(sub[0]);
                    if (inXw.size() == 2)
                      found = true;
                  }
                else
                  {
                    rest.push_back(sub);
                  }
              if (found)
                {
                  res.clear();
                  for (const auto& [a, bs]: map)
                    res.push_back(formula::Implies(a, formula::And(bs)));
                  if (!inG.empty())
                    {
                      inG = group_op(std::move(inG), op::F, op::And);
                      res.push_back(formula::G(formula::And(inG)));
                    }
                  if (!inXs.empty())
                    res.push_back(formula::strong_X(formula::And(inXs)));
                  if (!inXw.empty())
                    res.push_back(formula::X(formula::And(inXw)));
                  res.insert(res.end(), rest.begin(), rest.end());
                  formula g = formula::And(res);
                  if (g != f)
                    return simplify(g);
                }
            }
          else if (opos == op::Or)
            {
              // (a1 -> b) | (a2 -> b) | rest  =  !a1 | !a2 | b | rest
              // F(a) | F(b) | rest  =  F(a | b) | rest
              std::vector<formula> inF;
              std::vector<formula> rest;
              std::vector<formula> inXw;
              std::vector<formula> inXs;
              bool found = false;
              for (const formula& sub: res)
                if (sub.is(op::Implies))
                  {
                    found = true;
                    rest.push_back(formula::Not(sub[0]));
                    rest.push_back(sub[1]);
                  }
                else if (sub.is(op::F))
                  {
                    inF.push_back(sub[0]);
                    if (inF.size() == 2)
                      found = true;
                  }
                else if (sub.is(op::strong_X))
                  {
                    inXs.push_back(sub[0]);
                    if (inXs.size() == 2)
                      found = true;
                  }
                else if (sub.is(op::X))
                  {
                    inXw.push_back(sub[0]);
                    if (inXw.size() == 2)
                      found = true;
                  }
                else
                  {
                    rest.push_back(sub);
                  }
              if (found)
                {
                  res.clear();
                  if (!inF.empty())
                    {
                      inF = group_op(std::move(inF), op::G, op::Or);
                      res.push_back(formula::F(formula::Or(inF)));
                    }
                  if (!inXs.empty())
                    res.push_back(formula::strong_X(formula::Or(inXs)));
                  if (!inXw.empty())
                    res.push_back(formula::X(formula::Or(inXw)));
                  res.insert(res.end(), rest.begin(), rest.end());
                  formula g = formula::Or(res);
                  if (g != f)
                    return simplify(g);
                }
            }

          // return formula::multop(opos, res);

          // Scan s for children that use the other operator.
          // The plan is to lift subformulas that can be lifted
          // in the AST as in:
          //
          // (a & b) | (a & c) | rest  =  (a & (b | c)) | rest
          // (a | b) & (a | c) & rest  =  (a | (b & c)) | rest
          //
          // To do so, we'll first count the subformulas
          // that are shared between the children of s.
          robin_hood::unordered_map<formula, unsigned> count;
          unsigned largest = 0;
          formula largest_sub = nullptr;
          auto remember = [&] (const formula& sub) {
            if (sub.is_boolean())
              return;
            if (unsigned c = ++count[sub]; c > largest)
              {
                largest = c;
                largest_sub = sub;
              }
          };
          for (const formula& sub: res)
            if (sub.is(oneg))
              for (const formula& subsub : sub)
                remember(subsub);
            else
              remember(sub);

          // no shared sub formula
          if (largest < 2)
            return formula::multop(opos, res);

          // shared subformula found
          std::vector<formula> simplified_clauses;
          std::vector<formula> unmodified_clauses;
          for (const formula& sub: res)
            if (sub.is(oneg))
              {
                // check if sub contains largest_sub
                bool found = false;
                for (const formula& subsub: sub)
                  if (subsub == largest_sub)
                    {
                      found = true;
                      break;
                    }
                if (!found)
                  {
                    unmodified_clauses.push_back(sub);
                    continue;
                  }
                std::vector<formula> subsubs;
                for (const formula& subsub: sub)
                  if (subsub != largest_sub)
                    subsubs.push_back(subsub);
                simplified_clauses.push_back(formula::multop(oneg, subsubs));
              }
            else if (sub == largest_sub)
              simplified_clauses.push_back(opos == op::Or ?
                                          formula::tt() : formula::ff());
            else
              unmodified_clauses.push_back(sub);

          formula simp = simplify(formula::multop(opos, simplified_clauses));
          formula rest = simplify(formula::multop(opos, unmodified_clauses));
          formula simp2 = formula::multop(oneg, largest_sub, simp);
          return formula::multop(opos, simp2, rest);
        }
      case op::exists:
      case op::forall:
        {
          std::vector<formula> tmp;
          unsigned sz = f.size();
          tmp.reserve(sz - 1);
          for (unsigned i = 0; i < sz - 1; ++i)
            tmp.push_back(f[i]);
          formula c = f[sz - 1];
          formula d = simplify(c, negated);
          if (d == c)
            return f;
          return formula::quantify(o, tmp, d);
        }
      }
    SPOT_UNREACHABLE();
    return f;
  }




}
