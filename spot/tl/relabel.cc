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
#include <spot/misc/bitvect.hh>
#include <spot/tl/relabel.hh>
#include <spot/tl/simplify.hh>
#include <algorithm>
#include <memory>
#include <sstream>
#include <map>
#include <set>
#include <unordered_set>
#include <vector>

namespace spot
{
  //////////////////////////////////////////////////////////////////////
  // Basic relabeler
  //////////////////////////////////////////////////////////////////////

  namespace
  {
    struct ap_generator
    {
      virtual formula next() = 0;
      virtual ~ap_generator() {}
    };

    struct pnn_generator final: ap_generator
    {
      unsigned nn;
      pnn_generator()
        : nn(0)
        {
        }

      virtual formula next() override
      {
        std::ostringstream s;
        s << 'p' << nn++;
        return formula::ap(s.str());
      }
    };

    struct abc_generator final: ap_generator
    {
    public:
      abc_generator()
        : nn(0)
        {
        }

      unsigned nn;

      virtual formula next() override
      {
        std::string s;
        unsigned n = nn++;
        do
          {
            s.push_back('a' + (n % 26));
            n /= 26;
          }
        while (n);
        return formula::ap(s);
      }
    };

    // if subexp == false, matches APs
    // if subexp == true, matches boolean subexps
    template <bool subexp, bool use_bdd = false>
    class relabeler
    {
    public:
      typedef std::unordered_map<formula, formula> map;
      map newname;
      ap_generator* gen;
      relabeling_map* oldnames;
      tl_simplifier tl;

      relabeler(ap_generator* gen, relabeling_map* m)
        : gen(gen), oldnames(m)
      {
      }

      ~relabeler()
      {
        delete gen;
      }

      formula rename(formula old)
      {
        if constexpr (subexp)
          {
            // have we given a name to the negation of this formula?
            auto neg = newname.find(formula::Not(old));
            if (neg != newname.end())
              return formula::Not(neg->second);
          }

        auto r = newname.emplace(old, nullptr);
        if (!r.second)
          return r.first->second;

        if constexpr (use_bdd)
          if (!old.is(op::ap))
            {
              bdd b = tl.as_bdd(old);
              if (b == bddtrue)
                return r.first->second = formula::tt();
              if (b == bddfalse)
                return r.first->second = formula::ff();
            }

        formula res = gen->next();
        r.first->second = res;
        if (oldnames)
          (*oldnames)[res] = old;
        return res;
      }

      formula
      visit(formula f)
      {
        if ((!subexp && f.is(op::ap))
            || (subexp && f.is_boolean()))
          {
            return rename(f);
          }
        if (subexp && f.is(op::Or, op::And) && f[0].is_boolean())
          {
            // Boolean terms are always beginning of And and Or, so
            // the above test capture Or/And that some Boolean arguments
            // and some non-Boolean arguments.
            unsigned i = 0;
            formula b = f.boolean_operands(&i);
            unsigned sz = f.size();
            std::vector<formula> res;
            res.reserve(sz - i + 1);
            res.emplace_back(visit(b));
            for (; i < sz; ++i)
              res.emplace_back(visit(f[i]));
            return formula::multop(f.kind(), res);
          }
        else
          {
            return f.map([this](formula f)
            {
              return this->visit(f);
            });
          }
      }

    };

    template<bool subexp>
    formula
    relabel_do(formula f, relabeling_style style, relabeling_map* m)
    {
      ap_generator* gen = nullptr;
      switch (style)
        {
        case Pnn:
          gen = new pnn_generator;
          break;
        case Abc:
          gen = new abc_generator;
          break;
        }

      relabeler<subexp> r(gen, m);
      return r.visit(f);
    }
  }

  formula
  relabel(formula f, relabeling_style style, relabeling_map* m)
  {
    return relabel_do<false>(f, style, m);
  }

  formula
  relabel_overlapping_bse(formula f, relabeling_style style, relabeling_map* m)
  {
    return relabel_do<true>(f, style, m);
  }

  //////////////////////////////////////////////////////////////////////
  // Boolean-subexpression relabeler
  //////////////////////////////////////////////////////////////////////

  // Here we want to rewrite a formula such as
  //   "a & b & X(c & d) & GF(c & d)" into "p0 & Xp1 & GFp1"
  // where Boolean subexpressions are replaced by fresh propositions.
  //
  // Let us say that a Boolean subformula is "closed" if all the
  // occurrences of all its atomic propositions are inside that
  // subformula.  Replacing a closed subformula by a fresh proposition
  // preserves the semantics: the new proposition is equivalent to the
  // subformula, and since the atomic propositions of the subformula
  // appear nowhere else, no correlation with the rest of the formula
  // is lost.
  //
  // Replacing a subformula that is not closed would be wrong: for
  // instance in "(a & b) U (a & !b)", relabeling both "a & b" and
  // "a & !b" as p0 and p1 would hide the fact that both depend on "a".
  // Instead only the atomic propositions may be renamed, giving
  // "(p0 & p1) U (p0 & !p1)".
  //
  // Distinct closed subformulas may still share atomic propositions
  // when one is nested in the other (e.g., "a & b" and "!(a & b)").
  // Only one of them can be renamed, so we greedily select the
  // subformulas that hide the largest number of atomic propositions,
  // making sure that no two selected subformulas share an atomic
  // proposition.  This is the minimal renaming we are looking for:
  // every selected subformula replaces at least two atomic
  // propositions by a single one.
  //
  // Detecting closed subformulas is cheap: for each subformula we
  // compute the set of atomic propositions it uses, and the set of
  // atomic propositions that occur outside of it; the subformula is
  // closed iff the second set is empty.  The first set is computed
  // bottom-up and the second top-down, in two traversals of the syntax
  // DAG.  Atomic propositions are identified by their index and sets
  // of indices are stored as bit-vectors, so unions and intersections
  // are a few machine-word operations.
  //
  // Renaming must remain cheap, so no BDD is involved in detecting
  // closed subformulas.  A BDD is needed only for the subformulas
  // that are actually renamed: replacing an unsatisfiable (or
  // tautological) subformula by a fresh proposition would be wrong,
  // so such a subformula must be replaced by "false" (or "true")
  // instead, and that can only be decided semantically.  This check
  // (as_bdd()) is therefore restricted to the selected subformulas,
  // and it is skipped for those in which each atomic proposition
  // occurs at most once: such "read-once" formulas are never
  // equivalent to true or false.  That property is tested locally, in
  // rename(), on the subformula being renamed: the subformula is
  // scanned as a tree (not as a DAG) and its atomic propositions are
  // marked in a bit-vector, the second occurrence of any of them
  // aborting the scan.
  //
  // One subtlety remains.  Because And and Or are n-ary, a formula
  // such as "(a & b & c) U X(a & b)" would not relabel "a & b": "a"
  // and "b" occur outside of that node (as operands of the first "&").
  // However, since "&" is associative and commutative, "(a & b & c)"
  // may be regrouped as "((a & b) & c)", making the shared "a & b"
  // explicit; after that regrouping, all the occurrences of "a" and
  // "b" are inside "a & b", which therefore becomes closed.  So we
  // regroup the operands of n-ary And/Or nodes using the Boolean
  // subformulas that already exist elsewhere in the formula.  This
  // regrouping only affects the analysis graph: the output formula
  // stays flat.
  //
  // Finally, in an n-ary node, all Boolean operands whose atomic
  // propositions never occur elsewhere may be grouped in a single
  // subformula, so that "a & b & Xc" is relabeled as "p0 & Xp1" (with
  // p0 = a & b) instead of "p0 & p1 & Xp2".
  namespace
  {
    typedef std::vector<formula> fvec;
    typedef std::vector<unsigned> uvec;

    // Disjoint-set structure, used to group the operands of n-ary
    // operators that share atomic propositions.
    class union_find
    {
    public:
      union_find(unsigned n = 0)
      {
        reset(n);
      }

      // Reuse an existing union-find structure for n elements.
      void reset(unsigned n)
      {
        parent_.resize(n);
        for (unsigned i = 0; i != n; ++i)
          parent_[i] = i;
      }

      unsigned find(unsigned i)
      {
        while (parent_[i] != i)
          i = parent_[i] = parent_[parent_[i]];
        return i;
      }

      void unite(unsigned i, unsigned j)
      {
        i = find(i);
        j = find(j);
        if (i != j)
          parent_[j] = i;
      }

    private:
      std::vector<unsigned> parent_;
    };

    // The subformulas of the formula to relabel, organized as a graph.
    //
    // This is the syntax DAG of the formula, except that the operands
    // of n-ary And/Or nodes may be regrouped: if all the operands of an
    // existing Boolean subformula m are operands of an And/Or node f,
    // then m can be used as an operand of f instead of its own
    // operands.  Since And and Or are associative, this does not change
    // the formula, but it makes the shared use of m explicit, so that
    // the atomic propositions of m can be hidden behind a single
    // proposition even if they also occur in f.
    //
    // Every subformula (and every atomic proposition) is given a dense
    // index by scan().  All the tables below are indexed by that
    // number, and the operands of a node are stored as indices, so the
    // algorithms never have to hash a formula, except in scan().
    class subformula_graph
    {
    public:
      std::vector<formula> node;                  // index -> formula
      std::vector<uvec> children_;                // index -> operand indices
      std::vector<int> ap_bit;                    // index -> AP bit or -1
      std::vector<unsigned> order;                // indices, topologically
      std::unordered_map<formula, unsigned> idx;  // formula -> index
      unsigned nap = 0;                           // number of APs

      // The operand indices of a node, after regrouping.
      const uvec& children(unsigned id) const
      {
        return children_[id];
      }

      unsigned root() const
      {
        return root_;
      }

      // The atomic propositions of a node, and those used outside of
      // it.  Both tables are allocated by allocate_sets().
      const bitvect& aps(unsigned id) const
      {
        return aps_->at(id);
      }

      bitvect& aps(unsigned id)
      {
        return aps_->at(id);
      }

      const bitvect& esc(unsigned id) const
      {
        return esc_->at(id);
      }

      bitvect& esc(unsigned id)
      {
        return esc_->at(id);
      }

      // Allocate the AP sets now that the number of nodes and the
      // number of atomic propositions are known.  Storing all the sets
      // in a single bitvect_array avoids one allocation per node.
      void allocate_sets()
      {
        aps_.reset(make_bitvect_array(nap, node.size()));
        esc_.reset(make_bitvect_array(nap, node.size()));
        before_ = bitvect(nap);
        after_ = bitvect(nap);
      }

      // Record all the subformulas of f.
      void scan(formula f)
      {
        auto p = idx.emplace(f, node.size());
        if (!p.second)
          return;
        unsigned id = node.size();
        node.push_back(f);
        children_.emplace_back();
        ap_bit.push_back(-1);
        if (parents_.size() < node.size())
          parents_.resize(node.size());
        if (f.is(op::ap))
          {
            ap_bit[id] = nap++;
            return;
          }
        unsigned sz = f.size();
        for (unsigned i = 0; i != sz; ++i)
          scan(f[i]);
        // The recursion above may have reallocated children_, so index
        // it again now that it is over.
        uvec& ch = children_[id];
        ch.reserve(sz);
        bool andor = sz > 1 && f.is(op::And, op::Or);
        for (unsigned i = 0; i != sz; ++i)
          {
            unsigned cid = idx.at(f[i]);
            ch.push_back(cid);
            if (andor)
              parents_[cid].push_back(id);
          }
      }

      // Regroup the operands of n-ary And/Or nodes, as explained above.
      void regroup()
      {
        for (unsigned id = 0; id != node.size(); ++id)
          {
            uvec& ch = children_[id];
            if (ch.size() < 2 || !node[id].is(op::And, op::Or))
              continue;
            formula f = node[id];
            std::unordered_set<unsigned> bops;  // Boolean operands of f
            for (unsigned c : ch)
              if (node[c].is_boolean())
                bops.insert(c);
            if (bops.empty())
              continue;
            // Existing Boolean nodes of the same kind whose operands
            // are all Boolean operands of f are candidate groups.
            uvec cand;
            std::unordered_set<unsigned> seen;
            for (unsigned c : bops)
              for (unsigned pid : parents_[c])
                {
                  if (pid == id || !seen.insert(pid).second
                      || node[pid].kind() != f.kind()
                      || node[pid].size() < 2)
                    continue;
                  bool subset = true;
                  for (unsigned c2 : children_[pid])
                    if (!bops.count(c2))
                      {
                        subset = false;
                        break;
                      }
                  if (subset)
                    cand.push_back(pid);
                }
            if (cand.empty())
              continue;
            // Prefer the largest groups, and keep them disjoint.
            std::sort(cand.begin(), cand.end(),
                      [this](unsigned a, unsigned b)
                      {
                        if (node[a].size() != node[b].size())
                          return node[a].size() > node[b].size();
                        return node[a] < node[b];
                      });
            std::unordered_set<unsigned> used;
            uvec groups;
            for (unsigned m : cand)
              {
                bool ok = true;
                for (unsigned c : children_[m])
                  if (used.count(c))
                    {
                      ok = false;
                      break;
                    }
                if (!ok)
                  continue;
                groups.push_back(m);
                for (unsigned c : children_[m])
                  used.insert(c);
              }
            if (groups.empty())
              continue;
            // Replace each grouped operand by its group, keeping the
            // group at the position of its first operand.
            std::unordered_map<unsigned, unsigned> pos;
            for (unsigned i = 0; i != ch.size(); ++i)
              pos.emplace(ch[i], i);
            std::unordered_map<unsigned, unsigned> group_of;
            std::unordered_map<unsigned, unsigned> first_pos;
            for (unsigned m : groups)
              for (unsigned c : children_[m])
                {
                  group_of.emplace(c, m);
                  unsigned p = pos.at(c);
                  auto it = first_pos.find(m);
                  if (it == first_pos.end())
                    first_pos.emplace(m, p);
                  else if (p < it->second)
                    it->second = p;
                }
            uvec res;
            res.reserve(ch.size());
            for (unsigned i = 0; i != ch.size(); ++i)
              {
                unsigned c = ch[i];
                auto it = group_of.find(c);
                if (it == group_of.end())
                  res.push_back(c);
                else if (first_pos.at(it->second) == i)
                  res.push_back(it->second);
              }
            ch = std::move(res);
          }
      }

      // Compute a topological order of the (regrouped) graph.
      void sort(formula f)
      {
        root_ = idx.at(f);
        order.clear();
        seen_.assign(node.size(), 0);
        stamp_.assign(node.size(), 0);
        generation_ = 0;
        order.reserve(node.size());
        topo(root_);
      }

      // Return true iff all the occurrences of all the atomic
      // propositions of n are inside n.
      //
      // This is decided exactly by checking which atomic propositions
      // can be reached from the root without going through n.  The esc
      // sets computed by compute_esc() over-approximate this: when two
      // distinct siblings share a descendant (like "F(x)" and "G(x)"
      // in "GF(x) & FG(x)"), the APs of one sibling are considered to
      // occur outside the other, even though those occurrences are in
      // fact inside it.
      //
      // The traversal ignores any subtree that cannot reach an atomic
      // proposition of n, and uses a generation stamp instead of a hash
      // set of formulas, so that it stays cheap even when called for
      // many candidates.
      bool exactly_closed(unsigned nid) const
      {
        const bitvect& target = aps(nid);
        if (++generation_ == 0)
          {
            std::fill(stamp_.begin(), stamp_.end(), 0);
            generation_ = 1;
          }
        stack_.clear();
        stack_.push_back(root_);
        while (!stack_.empty())
          {
            unsigned id = stack_.back();
            stack_.pop_back();
            if (id == nid || stamp_[id] == generation_)
              continue;
            stamp_[id] = generation_;
            if (ap_bit[id] >= 0)
              {
                if (target.get(ap_bit[id]))
                  return false;
                continue;
              }
            for (unsigned cid : children_[id])
              if (aps(cid).intersects(target))
                stack_.push_back(cid);
          }
        return true;
      }

      void compute_aps()
      {
        for (unsigned id : order)         // operands are visited first
          {
            bitvect& v = aps(id);
            if (ap_bit[id] >= 0)
              {
                v.set(ap_bit[id]);
                continue;
              }
            for (unsigned cid : children_[id])
              v |= aps(cid);
          }
      }

      // Compute, for each subformula, the atomic propositions that
      // occur outside of it.
      void compute_esc()
      {
        // order is a post-order: iterate in reverse so that parents are
        // processed before their operands.
        for (auto it = order.rbegin(); it != order.rend(); ++it)
          {
            unsigned id = *it;
            const uvec& ch = children_[id];
            unsigned sz = ch.size();
            if (sz == 0)
              continue;
            // esc(ch[i]) contains esc(n) and the APs of all the other
            // operands of n: those before ch[i] in a first pass, and
            // those after it in a second pass.
            before_.clear_all();
            for (unsigned i = 0; i != sz; ++i)
              {
                esc(ch[i]) |= esc(id);
                esc(ch[i]) |= before_;
                before_ |= aps(ch[i]);
              }
            after_.clear_all();
            for (unsigned i = sz; i != 0; --i)
              {
                esc(ch[i - 1]) |= esc(id);
                esc(ch[i - 1]) |= after_;
                after_ |= aps(ch[i - 1]);
              }
          }
      }

    private:
      unsigned root_ = 0;
      std::vector<uvec> parents_;       // And/Or parents
      std::vector<char> seen_;
      std::unique_ptr<bitvect_array> aps_;
      std::unique_ptr<bitvect_array> esc_;
      // Scratch space reused by compute_esc().
      bitvect before_;
      bitvect after_;
      // Scratch space for exactly_closed(), see there.
      mutable std::vector<unsigned> stack_;
      mutable std::vector<unsigned> stamp_;
      mutable unsigned generation_ = 0;

      void topo(unsigned id)
      {
        if (seen_[id])
          return;
        seen_[id] = 1;
        for (unsigned cid : children_[id])
          topo(cid);
        order.push_back(id);
      }
    };

    class bse_relabeler
    {
      // An operand of an n-ary node, after grouping.
      struct piece
      {
        formula f;    // the subformula to use as operand
        unsigned id;  // its node index, unless whole
        bool whole;   // whether f must be relabeled as a whole
      };

    public:
      // Renaming an unsatisfiable (or tautological) piece would hide
      // its nature: the fresh proposition could be satisfied freely,
      // so we keep false/true for those.  This semantic check is done
      // only on the pieces that are renamed, and it is skipped for
      // read-once pieces, as decided by read_once().
      tl_simplifier tl;

      bse_relabeler(ap_generator* gen, relabeling_map* m,
                    const subformula_graph& g,
                    const std::vector<char>& selected)
        : gen_(gen), oldnames_(m), g_(g), selected_(selected),
          read_marks_(g.nap), visit_(g.node.size(), 0),
          memo_(g.node.size())
      {
        owner_.assign(g.nap, ~0u);
      }

      ~bse_relabeler()
      {
        delete gen_;
      }

      // Return true iff each atomic proposition occurs at most once in
      // f expanded as a tree.  A formula that contains a constant, or
      // no atomic proposition at all, is not read-once, so a positive
      // answer guarantees that f is neither true nor false.
      bool read_once(formula f)
      {
        read_marks_.clear_all();
        read_count_ = 0;
        return read_once_tree(f) && read_count_ != 0;
      }

      bool read_once_tree(formula f)
      {
        if (f.is_constant())
          return false;
        if (f.is(op::ap))
          {
            unsigned bit = g_.ap_bit[g_.idx.at(f)];
            if (read_marks_.get(bit))
              return false;
            read_marks_.set(bit);
            ++read_count_;
            return true;
          }
        unsigned sz = f.size();
        for (unsigned i = 0; i != sz; ++i)
          if (!read_once_tree(f[i]))
            return false;
        return true;
      }

      formula rename(formula old)
      {
        if (!old.is(op::ap))
          {
            // A group built by partition() may coincide with an
            // existing node that was already visited: keep that
            // expansion instead of hiding the node behind a name.
            auto it = g_.idx.find(old);
            if (it != g_.idx.end() && visit_[it->second])
              return memo_[it->second];
          }
        auto r = renamed_.emplace(old, nullptr);
        if (!r.second)
          return r.first->second;
        // A read-once formula, in which each atomic proposition
        // occurs at most once, is neither true nor false, so the BDD
        // check is useless for it.
        if (!read_once(old))
          {
            bdd b = tl.as_bdd(old);
            if (b == bddtrue)
              return r.first->second = formula::tt();
            if (b == bddfalse)
              return r.first->second = formula::ff();
          }
        formula res = gen_->next();
        if (oldnames_)
          (*oldnames_)[res] = old;
        r.first->second = res;
        return res;
      }

      formula visit(unsigned id)
      {
        formula f = g_.node[id];
        if (g_.ap_bit[id] >= 0 || selected_[id])
          return rename(f);
        if (visit_[id])
          return memo_[id];
        if (f.is_boolean())
          {
            // As in rename(): a group of partition() can be equal to
            // an existing Boolean node that was already visited.
            auto it = renamed_.find(f);
            if (it != renamed_.end())
              return it->second;
          }
        formula res;
        if (f.size() > 1 && f.is(op::And, op::Or))
          {
            fvec operands;
            operands.reserve(f.size());
            for (const piece& p : partition(id))
              operands.push_back(p.whole ? rename(p.f) : visit(p.id));
            res = formula::multop(f.kind(), std::move(operands));
          }
        else
          {
            // Compute the relabeled operands first, then let map()
            // rebuild the node without looking any of them up.
            fvec operands;
            operands.reserve(f.size());
            for (unsigned cid : g_.children(id))
              operands.push_back(visit(cid));
            unsigned k = 0;
            res = f.map([&k, &operands](formula)
                        {
                          return operands[k++];
                        });
          }
        visit_[id] = 1;
        memo_[id] = res;
        return res;
      }

      formula visit(formula f)
      {
        return visit(g_.idx.at(f));
      }

    private:
      // Split the operands of the n-ary node f into pieces.  Boolean
      // operands whose atomic propositions do not occur elsewhere are
      // grouped in a single piece that is relabeled as a whole.
      std::vector<piece> partition(unsigned id)
      {
        formula f = g_.node[id];
        const uvec& ch = g_.children(id);
        unsigned sz = ch.size();
        // APs that will stay visible whatever grouping we choose.
        bitvect& out = out_;
        out = g_.esc(id);
        for (unsigned i = 0; i != sz; ++i)
          if (!g_.node[ch[i]].is_boolean())
            out |= g_.aps(ch[i]);
        // Group Boolean operands that share atomic propositions.
        uf_.reset(sz);
        opnd_.assign(sz, false);
        touched_.clear();
        for (unsigned i = 0; i != sz; ++i)
          if ((opnd_[i] = g_.node[ch[i]].is_boolean()))
            g_.aps(ch[i]).foreach_set_index(
              [&](unsigned a)
              {
                unsigned& o = owner_[a];
                if (o == ~0u)
                  {
                    o = i;
                    touched_.push_back(a);
                  }
                else
                  uf_.unite(i, o);
              });
        // Give each component of the union-find a dense index.
        comp_.assign(sz, ~0u);
        unsigned ncomp = 0;
        for (unsigned i = 0; i != sz; ++i)
          if (opnd_[i])
            {
              unsigned r = uf_.find(i);
              if (comp_[r] == ~0u)
                comp_[r] = ncomp++;
              comp_[i] = comp_[r];
            }
        // An operand cannot be grouped if its component contains an
        // operand of the same kind (formula::multop() would flatten
        // it) or an atomic proposition that stays visible.
        flat_.assign(ncomp, false);
        visible_.assign(ncomp, false);
        for (unsigned i = 0; i != sz; ++i)
          if (opnd_[i])
            {
              if (g_.node[ch[i]].kind() == f.kind())
                flat_[comp_[i]] = true;
              if (g_.aps(ch[i]).intersects(out))
                visible_[comp_[i]] = true;
            }
        // Group the operands that can be.
        groupable_.assign(sz, false);
        merged_.clear();
        unsigned first_merged = sz;
        for (unsigned i = 0; i != sz; ++i)
          if (opnd_[i] && !flat_[comp_[i]] && !visible_[comp_[i]])
            {
              groupable_[i] = true;
              merged_.push_back(g_.node[ch[i]]);
              if (i < first_merged)
                first_merged = i;
            }
        bool whole = merged_.size() > 1;
        formula grp = nullptr;
        unsigned grp_id = ~0u;
        if (!merged_.empty())
          {
            if (whole)
              grp = formula::multop(f.kind(), merged_);
            else
              {
                grp = merged_.front();
                grp_id = ch[first_merged];
              }
          }
        std::vector<piece> res;
        res.reserve(sz - merged_.size() + (merged_.empty() ? 0 : 1));
        for (unsigned i = 0; i != sz; ++i)
          {
            if (i == first_merged)
              res.push_back(piece{grp, grp_id, whole});
            if (!groupable_[i])
              res.push_back(piece{g_.node[ch[i]], ch[i], false});
          }
        for (unsigned a : touched_)
          owner_[a] = ~0u;
        touched_.clear();
        return res;
      }

      ap_generator* gen_;
      relabeling_map* oldnames_;
      const subformula_graph& g_;
      const std::vector<char>& selected_;
      std::vector<unsigned> owner_;    // AP -> first operand index
      std::vector<unsigned> touched_;  // APs set in owner_
      bitvect out_;                    // scratch space for partition()
      bitvect read_marks_;             // APs seen by read_once()
      unsigned read_count_ = 0;        // APs seen by read_once()
      // Scratch space reused by partition().
      union_find uf_;
      std::vector<char> opnd_;
      std::vector<unsigned> comp_;
      std::vector<char> flat_;
      std::vector<char> visible_;
      std::vector<char> groupable_;
      fvec merged_;
      std::vector<char> visit_;        // node has been visited
      std::vector<formula> memo_;      // result for a visited node
      std::unordered_map<formula, formula> renamed_;
    };
  }

  formula
  relabel_bse(formula f, relabeling_style style, relabeling_map* m)
  {
    subformula_graph g;
    g.scan(f);
    g.regroup();
    g.sort(f);
    g.allocate_sets();
    g.compute_aps();
    g.compute_esc();

    // Select the subformulas to relabel: those that are closed and
    // hide the most atomic propositions, while never sharing an atomic
    // proposition with another selected subformula.
    struct candidate
    {
      unsigned id;
      unsigned index;
      unsigned count;   // number of APs, cached for the sort
    };
    std::vector<candidate> cand;
    for (unsigned i = 0; i != g.order.size(); ++i)
      {
        unsigned id = g.order[i];
        formula n = g.node[id];
        if (!n.is_boolean() || g.ap_bit[id] >= 0)
          continue;
        unsigned count = g.aps(id).count();
        if (count < 2)
          continue;
        // Disjointness of aps(n) and esc(n) is a cheap sufficient
        // condition for n being closed.
        if (g.aps(id).intersects(g.esc(id)) && !g.exactly_closed(id))
          continue;
        cand.push_back({id, i, count});
      }
    std::sort(cand.begin(), cand.end(),
              [](const candidate& a, const candidate& b)
              {
                if (a.count != b.count)
                  return a.count > b.count;
                return a.index < b.index;
              });
    std::vector<char> selected(g.node.size(), 0);
    bitvect hidden(g.nap);
    for (const candidate& c : cand)
      if (!g.aps(c.id).intersects(hidden))
        {
          selected[c.id] = 1;
          hidden |= g.aps(c.id);
        }

    ap_generator* gen = nullptr;
    switch (style)
      {
      case Pnn:
        gen = new pnn_generator;
        break;
      case Abc:
        gen = new abc_generator;
        break;
      }
    bse_relabeler rel(gen, m, g, selected);
    return rel.visit(f);
  }

  formula
  relabel_apply(formula f, relabeling_map* m)
  {
    if (f.is(op::ap))
      {
        auto i = m->find(f);
        if (i != m->end())
          return i->second;
      }
    // For quantifiers, allow AP-to-AP relabeling of bound variables.
    // If a bound variable is replaced by something that is not an AP
    // (e.g., a constant like tt() or ff()), drop it from the quantifier
    // list.  If the quantifier becomes empty, return the body directly.
    if (f.is(op::exists, op::forall))
      {
        unsigned last = f.size() - 1;
        bool changed = false;
        std::vector<formula> qvars;
        qvars.reserve(last);
        for (unsigned i = 0; i < last; ++i)
          {
            formula var = f[i];
            auto j = m->find(var);
            if (j != m->end())
              {
                formula repl = j->second;
                if (repl && repl.is(op::ap))
                  {
                    if (repl != var)
                      changed = true;
                    qvars.push_back(repl);
                  }
                else
                  {
                    // Non-AP replacement: drop this variable.
                    changed = true;
                  }
              }
            else
              {
                qvars.push_back(var);
              }
          }
        formula newbody = relabel_apply(f[last], m);
        if (!changed && newbody == f[last])
          return f;
        if (qvars.empty())
          return newbody;
        return formula::quantify(f.is(op::exists) ? op::exists
                                                  : op::forall,
                                 std::move(qvars), newbody);
      }
    // Since relabel_apply is overloaded, we should help the compiler
    // to understand we are talking about the current function...
    return f.map(static_cast<formula(*)(formula,
                                        relabeling_map*)>(&relabel_apply), m);
  }

  formula
  relabel_apply(formula f, const std::vector<formula>& m)
  {
    if (f.is(op::ap))
      {
        unsigned id = f.apid();
        if (SPOT_UNLIKELY(id >= m.size()))
          return f;
        formula g = m[id];
        return g ? g : f;
      }
    // For quantifiers, allow AP-to-AP relabeling of bound variables.
    // If a bound variable is replaced by something that is not an AP
    // (e.g., a constant like tt() or ff()), drop it from the quantifier
    // list.  If the quantifier becomes empty, return the body directly.
    if (f.is(op::exists, op::forall))
      {
        unsigned last = f.size() - 1;
        bool changed = false;
        std::vector<formula> qvars;
        qvars.reserve(last);
        for (unsigned i = 0; i < last; ++i)
          {
            formula var = f[i];
            unsigned id = var.apid();
            formula repl = (id < m.size()) ? m[id] : formula{};
            if (repl && repl.is(op::ap))
              {
                if (repl != var)
                  changed = true;
                qvars.push_back(repl);
              }
            else
              {
                // Not replaced, or replaced by a non-AP.
                // Only keep the variable if it's not replaced.
                if (!repl)
                  qvars.push_back(var);
                else
                  changed = true;  // non-AP: drop this variable
              }
          }
        formula newbody = relabel_apply(f[last], m);
        if (!changed && newbody == f[last])
          return f;
        if (qvars.empty())
          return newbody;
        return formula::quantify(f.is(op::exists) ? op::exists
                                                  : op::forall,
                                 std::move(qvars), newbody);
      }
    // Since relabel_apply is overloaded, we should help the compiler
    // to understand we are talking about the current function...
    return f.map(static_cast<formula(*)(formula,
                                        const std::vector<formula>& m)>
                 (&relabel_apply), m);
  }

}
