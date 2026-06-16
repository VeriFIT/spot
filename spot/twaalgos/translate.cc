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
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/ltl2tgba_fm.hh>
#include <spot/twaalgos/complement.hh>
#include <spot/twaalgos/compsusp.hh>
#include <spot/misc/optionmap.hh>
#include <spot/tl/relabel.hh>
#include <spot/tl/ltlf.hh>
#include <spot/twaalgos/relabel.hh>
#include <spot/twaalgos/remprop.hh>
#include <spot/twaalgos/gfguarantee.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/twaalgos/dbranch.hh>
#include <spot/twaalgos/mtdswa.hh>
#include <spot/twaalgos/stripacc.hh>
#include <spot/twaalgos/hoa.hh>

#define OBLIGATION_ (pref_ & Obligation)

namespace spot
{

  void translator::setup_opt(const option_map* opt)
  {
    comp_susp_ = early_susp_ = skel_wdba_ = skel_simul_ = 0;
    relabel_bool_ = 4;
    relabel_overlap_ = 8;
    tls_impl_ = -1;
    ltl_split_ = true;
    exprop_ = -1;

    opt_ = opt;
    if (!opt)
      return;

    relabel_bool_ = opt->get("relabel-bool", 4);
    relabel_overlap_ = opt->get("relabel-overlap", 8);
    comp_susp_ = opt->get("comp-susp", 0);
    if (comp_susp_ == 1)
      {
        early_susp_ = opt->get("early-susp", 0);
        skel_wdba_ = opt->get("skel-wdba", -1);
        skel_simul_ = opt->get("skel-simul", 1);
      }
    tls_impl_ = opt->get("tls-impl", -1);
    int gfg = opt->get("gf-guarantee", -1);
    if (gfg >= 0)
      {
        gf_guarantee_ = !!gfg;
        gf_guarantee_set_ = true;
      }
    ltl_split_ = opt->get("ltl-split", 1);
    tls_max_states_ = std::max(0, opt->get("tls-max-states", 64));
    tls_max_ops_ = std::max(0, opt->get("tls-max-ops", 16));
    exprop_ = opt->get("exprop", -1);
    branchpost_ = opt->get("branch-post", -1);
    new_oblig_ = opt->get("new-oblig", -1);
  }

  void translator::build_simplifier(const bdd_dict_ptr& dict)
  {
    tl_simplifier_options options(false, false, false);
    options.containment_max_states = tls_max_states_;
    options.containment_max_ops = tls_max_ops_;
    switch (level_)
      {
      case High:
        options.containment_checks = true;
        options.containment_checks_stronger = true;
        SPOT_FALLTHROUGH;
      case Medium:
        options.synt_impl = true;
        SPOT_FALLTHROUGH;
      case Low:
        options.reduce_basics = true;
        options.event_univ = true;
      }
    // User-supplied fine-tuning?
    if (tls_impl_ >= 0)
      switch (tls_impl_)
        {
        case 0:
          options.synt_impl = false;
          options.containment_checks = false;
          options.containment_checks_stronger = false;
          break;
        case 1:
          options.synt_impl = true;
          options.containment_checks = false;
          options.containment_checks_stronger = false;
          break;
        case 2:
          options.synt_impl = true;
          options.containment_checks = true;
          options.containment_checks_stronger = false;
          break;
        case 3:
          options.synt_impl = true;
          options.containment_checks = true;
          options.containment_checks_stronger = true;
          break;
        default:
          throw std::runtime_error
            ("tls-impl should take a value between 0 and 3");
        }
    simpl_owned_ = simpl_ = new tl_simplifier(options, dict);
  }


  twa_graph_ptr translator::run_aux(formula r)
  {
#define PREF_ (pref_ & (Small | Deterministic))

    bool unambiguous = (pref_ & Unambiguous);
    if (unambiguous && type_ == Monitor)
      {
        // Deterministic monitor are unambiguous, so the unambiguous
        // option is not really relevant for monitors.
        unambiguous = false;
        pref_ |= postprocessor::Deterministic;
      }

    if (new_oblig_ < 0)
      new_oblig_ = !!(pref_ & postprocessor::Deterministic);

    // This helps ltl_to_tgba_fm() to order BDD variables in a more
    // natural way (improving the degeneralization).
    simpl_->clear_as_bdd_cache();

    twa_graph_ptr aut;
    twa_graph_ptr aut2 = nullptr;

    // Handle quantified formulas.
    if (r.is_quantified())
      {
        // gf_guarantee_to_ba_maybe and compsusp are skipped for
        // quantified formulas.
        bool det = unambiguous || (pref_ & postprocessor::Deterministic);
        if (det && new_oblig_ == 1
            && r.is_syntactic_obligation()
            && r.is_ltl_formula())
          {
            mtdswa_ptr mtdwa = obligation_to_mtdswa(r, simpl_->get_dict());
            return finish_obligation_mtdswa(r, mtdwa);
          }

        aut = run_q(r);
        aut = this->postprocessor::run(aut, r);
        return aut;
      }

    bool split_hard =
      type_ == Generic || (type_ & Parity) || type_ == GeneralizedBuchi;

    bool postprocess_was_done = false;

    // It would make sense to split, even in the presence of multiple
    // obligations.
    if (ltl_split_ && !r.is_syntactic_obligation() /* && !OBLIGATION_ */)
      {
        formula r2 = r;
        unsigned leading_x = 0;
        while (r2.is(op::X))
          {
            r2 = r2[0];
            ++leading_x;
          }
        if (split_hard)
          {
            // F(q|u|f) = q|F(u)|F(f)  disabled for GeneralizedBuchi
            // G(q&e&f) = q&G(e)&G(f)
            bool want_u = r2.is({op::F, op::Or}) && (type_ != GeneralizedBuchi);
            if (want_u || r2.is({op::G, op::And}))
              {
                std::vector<formula> susp;
                std::vector<formula> rest;
                auto op1 = r2.kind();
                auto op2 = r2[0].kind();
                for (formula child: r2[0])
                  {
                    bool u = child.is_universal();
                    bool e = child.is_eventual();
                    if (u && e)
                      susp.push_back(child);
                    else if ((want_u && u) || (!want_u && e))
                      susp.push_back(formula::unop(op1, child));
                    else
                      rest.push_back(child);
                  }
                susp.push_back(formula::unop(op1, formula::multop(op2, rest)));
                r2 = formula::multop(op2, susp);
              }
          }
        if (r2.is_syntactic_obligation() || !r2.is(op::And, op::Or,
                                                   op::Xor, op::Equiv) ||
            // For TGBA/BA we only do conjunction.  There is nothing wrong
            // with disjunction, but it seems to generate larger automata
            // in many cases and it needs to be further investigated.  Maybe
            // this could be relaxed in the case of deterministic output.
            (!r2.is(op::And) && (type_ == GeneralizedBuchi
                                 || (type_ & (Buchi | Finite)))))
          goto nosplit;

        op topop = r2.kind();
        // Let's classify subformulas.
        std::vector<formula> oblg;
        std::vector<formula> susp;
        std::vector<formula> rest;
        bool want_g = type_ == GeneralizedBuchi || type_ == Buchi;
        for (formula child: r2)
          {
            if (child.is_syntactic_obligation())
              oblg.push_back(child);
            else if (child.is_eventual() && child.is_universal()
                     && (!want_g || child.is(op::G)))
              susp.push_back(child);
            else
              rest.push_back(child);
          }

        // Safety formulas are quite easy to translate since they do
        // not introduce marks.  If rest is non-empty, it seems
        // preferable to translate the safety inside rest, as this may
        // constrain the translation.
        if (!rest.empty() && !oblg.empty())
          {
            auto safety = [](formula f)
            {
              // Prevent gcc 12.2.0 from warning us that f could be a
              // nullptr formula.
              SPOT_ASSUME(f != nullptr);
              return f.is_syntactic_safety();
            };
            auto i = std::remove_if(oblg.begin(), oblg.end(), safety);
            rest.insert(rest.end(), i, oblg.end());
            oblg.erase(i, oblg.end());
          }

        // The only cases where we accept susp and rest to be both
        // non-empty is when doing Generic/Parity/TGBA
        if (!susp.empty())
          {
            if (!rest.empty() && !split_hard)
              {
                rest.insert(rest.end(), susp.begin(), susp.end());
                susp.clear();
              }
            // For Parity, we want to translate all suspendable
            // formulas at once.
            //if (rest.empty() && type_ & Parity)
            //  susp = { formula::multop(r2.kind(), susp) };
          }
        // For TGBA and BA, we only split if there is something to
        // suspend.
        if (susp.empty() && (type_ == GeneralizedBuchi || type_ == Buchi))
          goto nosplit;

        option_map om_wos;
        option_map om_ws;
        if (opt_)
          om_ws = *opt_;
        // Don't blindingly apply reduce_parity() in the
        // generic case, for issue #402.
        om_ws.set("gen-reduce-parity", 0);
        translator translate_with_split(simpl_, &om_ws);
        // Translation with split is performed on sub-formulas
        // that have been separated from the main one.
        //
        // Never force colored automata at intermediate steps.  This
        // is best added at the very end.
        translate_with_split.set_pref(pref_ & ~Colored);
        translate_with_split.set_level(level_);
        translate_with_split.set_type(type_ == postprocessor::Finite ?
                                      postprocessor::Buchi : type_);
        // "Translation without split" is used when the split failed
        // and the input formula is still whole.  In that case we can
        // disable LTL simplification (already performed), and
        // postprocessings (because those will be performed again on the
        // result of that translation).
        om_wos = om_ws;
        om_wos.set("ltl-split", 0);
        om_wos.set("tls-impl", 0); // input already simplified
        translator translate_without_split(simpl_, &om_wos);
        translate_without_split.set_pref(pref_ & ~Colored);
        translate_without_split.set_level(level_);
        translate_without_split.set_type(type_ == postprocessor::Finite ?
                                         postprocessor::Buchi : type_);
        auto transrun = [&](formula f)
          {
            if (f == r2)
              {
                postprocess_was_done = true;
                return translate_without_split.run(f);
              }
            else
              return translate_with_split.run(f);
          };

        // std::cerr << "splitting\n";
        aut = nullptr;
        // All obligations can be converted into a minimal WDBA.
        if (!oblg.empty())
          {
            formula oblg_f = formula::multop(r2.kind(), oblg);
            //std::cerr << "oblg: " << oblg_f << '\n';
            aut = transrun(oblg_f);
          }
        if (!rest.empty())
          {
            formula rest_f = formula::multop(r2.kind(), rest);
            //std::cerr << "rest: " << rest_f << '\n';
            twa_graph_ptr rest_aut = transrun(rest_f);
            if (aut == nullptr)
              aut = rest_aut;
            else if (topop == op::And)
              aut = product(aut, rest_aut);
            else if (topop == op::Or)
              aut = product_or(aut, rest_aut);
            else if (topop == op::Xor)
              aut = product_xor(aut, rest_aut);
            else if (topop == op::Equiv)
              aut = product_xnor(aut, rest_aut);
            else
              SPOT_UNREACHABLE();
          }
        if (!susp.empty())
          {
            twa_graph_ptr susp_aut = nullptr;
            // Each suspendable formula separately
            for (formula f: susp)
              {
                //std::cerr << "susp: " << f << '\n';
                twa_graph_ptr one = transrun(f);
                if (!susp_aut)
                  susp_aut = one;
                else if (topop == op::And)
                  susp_aut = product(susp_aut, one);
                else if (topop == op::Or)
                  susp_aut = product_or(susp_aut, one);
                else if (topop == op::Xor)
                  susp_aut = product_xor(susp_aut, one);
                else if (topop == op::Equiv)
                  susp_aut = product_xnor(susp_aut, one);
                else
                  SPOT_UNREACHABLE();
              }
            if (susp_aut->prop_universal().is_true())
              {
                // In a deterministic and suspendable automaton, all
                // state recognize the same language, so we can move
                // the initial state into a bottom accepting SCC.
                scc_info si(susp_aut, scc_info_options::NONE);
                if (si.is_trivial(si.scc_of(susp_aut->get_init_state_number())))
                  {
                    unsigned st = si.one_state_of(0);
                    // The bottom SCC can actually be trivial if it
                    // has no successor because the formula is
                    // equivalent to false.
                    assert(!si.is_trivial(0) ||
                           susp_aut->out(st).begin()
                           == susp_aut->out(st).end());
                    susp_aut->set_init_state(st);
                    susp_aut->purge_unreachable_states();
                  }
              }
            if (aut == nullptr)
              aut = susp_aut;
            else if (topop == op::And)
              aut = product_susp(aut, susp_aut);
            else if (topop == op::Or)
              aut = product_or_susp(aut, susp_aut);
            else if (topop == op::Xor) // No suspension here
              aut = product_xor(aut, susp_aut);
            else if (topop == op::Equiv) // No suspension here
              aut = product_xnor(aut, susp_aut);
            //if (aut && susp_aut)
            //  {
            //    print_hoa(std::cerr << "AUT\n", aut) << '\n';
            //    print_hoa(std::cerr << "SUSPAUT\n", susp_aut) << '\n';
            //  }
          }
        if (leading_x > 0)
          add_leading_x(aut, leading_x);
      }
    else
      {
      nosplit:
        if (comp_susp_ > 0)
          {
            // FIXME: Handle unambiguous_ automata?
            int skel_wdba = skel_wdba_;
            if (skel_wdba < 0)
              skel_wdba = (pref_ & postprocessor::Deterministic) ? 1 : 2;

            aut = compsusp(r, simpl_->get_dict(), skel_wdba == 0,
                           skel_simul_ == 0, early_susp_ != 0,
                           comp_susp_ == 2, skel_wdba == 2, false);
          }
        else
          {
            if (gf_guarantee_ && PREF_ != Any)
              {
                bool det = unambiguous || (PREF_ == Deterministic);
                if ((type_ & (Buchi | Parity))
                     || type_ == Generic
                     || type_ == GeneralizedBuchi)
                  aut2 = gf_guarantee_to_ba_maybe(r, simpl_->get_dict(),
                                                  det, state_based_);
                acd_was_used_ = false;
                if (aut2 && (pref_ & Deterministic))
                  return finalize(aut2);
                if (!aut2 && (type_ == Generic
                              || type_ & (Parity | CoBuchi)))
                  {
                    aut2 = fg_safety_to_dca_maybe(r, simpl_->get_dict(),
                                                  state_based_);
                    if (aut2 && (pref_ & Deterministic))
                      return finalize(aut2);
                  }
              }
          }
        if (new_oblig_ == 1
            && r.is_syntactic_obligation()
            && r.is_ltl_formula()) // does not support PSL at that point
          {
            mtdswa_ptr mtdwa = obligation_to_mtdswa(r, simpl_->get_dict());
            return finish_obligation_mtdswa(r, mtdwa);
          }
        else
          {
            aut = translate_via_fm(r, unambiguous);
          }
      }
    if (!postprocess_was_done)
      aut = this->postprocessor::run(aut, r);
    if (aut2)
      {
        aut2 = this->postprocessor::run(aut2, r);
        unsigned s2 = aut2->num_states();
        unsigned s1 = aut->num_states();
        bool d2_more_det = !is_deterministic(aut) && is_deterministic(aut2);
        if (((PREF_ == Deterministic) && d2_more_det)
            || (s2 < s1)
            || (s2 == s1
                && ((aut2->num_sets() < aut->num_sets()) || d2_more_det)))
          aut = std::move(aut2);
      }

    return aut;
  }

  twa_graph_ptr translator::run_q(formula f)
  {
    // Base case: no quantifier.
    // We don't force unambiguous output for intermediate translations;
    // postprocessing at the end will take care of that if requested.
    if (!f.is(op::exists, op::forall))
      return translate_via_fm(f, false);

    op qtype = f.kind();
    unsigned sz = f.size();
    formula body = f[sz - 1];

    // Collect quantified APs.
    std::vector<formula> qaps;
    for (unsigned i = 0; i < sz - 1; ++i)
      qaps.push_back(f[i]);

    bool nested = body.is(op::exists, op::forall);

    if (nested)
      {
        // Recursively translate the body.
        auto aut = run_q(body);

        // Apply the current quantifier on top.
        remove_ap ra;
        for (auto& ap: qaps)
          ra.add_ap(ap);

        if (qtype == op::exists)
          return ra.strip(aut);
        else
          {
            aut = complement(aut);
            if (SPOT_UNLIKELY(!aut))
              throw std::runtime_error(
                "run_q(): complementation failed for nested forall");
            aut = ra.strip(aut);
            auto result = complement(aut);
            if (SPOT_UNLIKELY(!result))
              throw std::runtime_error(
                "run_q(): second complementation failed for nested forall");
            return result;
          }
      }

    // Single quantifier: body has no quantifiers.
    // Try restricted splitting.
    op split_op = (qtype == op::exists) ? op::Or : op::And;
    bool split_hard = type_ == Generic || (type_ & Parity)
                      || type_ == GeneralizedBuchi;

    // Remember the original formula in case splitting is skipped.
    formula orig_f = f;

    if (ltl_split_ && !body.is_syntactic_obligation())
      {
        formula r2 = body;
        unsigned leading_x = 0;
        while (r2.is(op::X))
          {
            r2 = r2[0];
            ++leading_x;
          }

        // Handle F(Or) / G(And) patterns based on quantifier type.
        if (split_hard)
          {
            bool want_pattern = false;
            if (qtype == op::exists)
              want_pattern = r2.is({op::F, op::Or})
                             && type_ != GeneralizedBuchi;
            else
              want_pattern = r2.is({op::G, op::And});

            if (want_pattern)
              {
                std::vector<formula> susp;
                std::vector<formula> rest;
                auto op1 = r2.kind();
                auto op2 = r2[0].kind();
                bool want_u = (qtype == op::exists);

                for (formula child: r2[0])
                  {
                    bool u = child.is_universal();
                    bool e = child.is_eventual();
                    if (u && e)
                      susp.push_back(child);
                    else if ((want_u && u) || (!want_u && e))
                      susp.push_back(formula::unop(op1, child));
                    else
                      rest.push_back(child);
                  }
                susp.push_back(formula::unop(op1,
                               formula::multop(op2, rest)));
                r2 = formula::multop(op2, susp);
                // Update orig_f to use the transformed body.
                orig_f = formula::quantify(qtype, qaps, r2);
              }
          }

        // Top-level splitting on the allowed operator.
        if (!r2.is_syntactic_obligation() && r2.is(split_op))
          {
            op topop = r2.kind();
            std::vector<formula> oblg;
            std::vector<formula> susp;
            std::vector<formula> rest;
            bool want_g = type_ == GeneralizedBuchi || type_ == Buchi;
            for (formula child: r2)
              {
                if (child.is_syntactic_obligation())
                  oblg.push_back(child);
                else if (child.is_eventual() && child.is_universal()
                         && (!want_g || child.is(op::G)))
                  susp.push_back(child);
                else
                  rest.push_back(child);
              }

            if (!rest.empty() && !oblg.empty())
              {
                auto safety = [](formula g)
                  {
                    SPOT_ASSUME(g != nullptr);
                    return g.is_syntactic_safety();
                  };
                auto i = std::remove_if(oblg.begin(), oblg.end(), safety);
                rest.insert(rest.end(), i, oblg.end());
                oblg.erase(i, oblg.end());
              }

            if (!susp.empty())
              {
                if (!rest.empty() && !split_hard)
                  {
                    rest.insert(rest.end(), susp.begin(), susp.end());
                    susp.clear();
                  }
              }

            if (susp.empty()
                && (type_ == GeneralizedBuchi || type_ == Buchi))
              goto no_split_q;

            // Translate each piece re-wrapped with the quantifier.
            auto transrun = [&](formula g)
              {
                return run_q(formula::quantify(qtype, qaps, g));
              };

            twa_graph_ptr aut = nullptr;

            if (!oblg.empty())
              {
                formula oblg_f = formula::multop(r2.kind(), oblg);
                aut = transrun(oblg_f);
              }
            if (!rest.empty())
              {
                formula rest_f = formula::multop(r2.kind(), rest);
                twa_graph_ptr rest_aut = transrun(rest_f);
                if (aut == nullptr)
                  aut = rest_aut;
                else if (topop == op::And)
                  aut = product(aut, rest_aut);
                else // Or
                  aut = product_or(aut, rest_aut);
              }
            if (!susp.empty())
              {
                twa_graph_ptr susp_aut = nullptr;
                for (formula g: susp)
                  {
                    twa_graph_ptr one = transrun(g);
                    if (!susp_aut)
                      susp_aut = one;
                    else if (topop == op::And)
                      susp_aut = product(susp_aut, one);
                    else
                      susp_aut = product_or(susp_aut, one);
                  }
                if (susp_aut->prop_universal().is_true())
                  {
                    scc_info si(susp_aut, scc_info_options::NONE);
                    if (si.is_trivial(
                          si.scc_of(susp_aut->get_init_state_number())))
                      {
                        unsigned st = si.one_state_of(0);
                        assert(!si.is_trivial(0) ||
                               susp_aut->out(st).begin()
                               == susp_aut->out(st).end());
                        susp_aut->set_init_state(st);
                        susp_aut->purge_unreachable_states();
                      }
                  }
                if (aut == nullptr)
                  aut = susp_aut;
                else if (topop == op::And)
                  aut = product_susp(aut, susp_aut);
                else
                  aut = product_or_susp(aut, susp_aut);
              }

            if (leading_x > 0)
              add_leading_x(aut, leading_x);

            return aut;
          }
      }

  no_split_q:
    if (qtype == op::exists)
      return translate_via_fm(orig_f, false);
    else
      {
        // forall: translate exists(aps, Not(body)) then complement.
        formula b = orig_f[orig_f.size() - 1];
        formula neg_body = formula::Not(b);
        formula ef = formula::quantify(op::exists, qaps, neg_body);
        auto aut = translate_via_fm(ef, false);
        auto result = complement(aut);
        if (SPOT_UNLIKELY(!result))
          throw std::runtime_error(
            "run_q(): complementation failed during forall translation");
        return result;
      }
  }

  twa_graph_ptr translator::finish_obligation_mtdswa(formula f,
                                                      mtdswa_ptr mtdwa)
  {
    if (wdba_minimize_ != 0)
      {
        mtdwa->sinks_as_states();
        std::vector<unsigned> part = loding_weak_ranking(mtdwa, true);
        mtdwa = minimize_mtdswa(mtdwa, part);
      }
    // The output of obligation_to_mtdswa is always B\u00fcchi.
    // Since the automaton is complete and weak, we can obtain
    // CoB\u00fcchi simply by flipping the colors.
    if (type_ == CoBuchi)
      {
        acc_cond::mark_t good = {};
        acc_cond::mark_t bad = {0};
        for (auto& c: mtdwa->colors)
          c = mtdwa->acc.accepting(c) ? good : bad;
        mtdwa->acc = acc_cond(1, acc_cond::acc_code::cobuchi());
      }
    bool want_complete = pref_ & Complete;
    auto aut = mtdwa->as_twa(true, false, want_complete);
    aut->prop_weak(true);

    if (f.is_syntactic_stutter_invariant())
      aut->prop_stutter_invariant(true);

    // Unless we need a B\u00fcchi or colored automaton, if the
    // weak automaton has all its edges marked as accepting,
    // we can reduce the acceptance to t.
    if (type_ != Buchi && type_ != CoBuchi && aut->num_sets() > 0)
      {
        acc_cond::mark_t c = {};
        // If the automaton has no edge, we are good to reduce
        // the acceptance to t.
        bool good = true;
        for (auto& e: aut->edges())
          {
            c = e.acc;
            good = false;
            break;
          }
        if (aut->acc().accepting(c))
          {
            good = true;
            for (auto& e: aut->edges())
              if (e.acc != c)
                {
                  good = false;
                  break;
                }
          }
        if (good)
          strip_acceptance_here(aut);
      }
    return finalize(aut);
  }

  twa_graph_ptr translator::translate_via_fm(formula f, bool unambiguous)
  {
    bool exprop = unambiguous
      || (level_ == postprocessor::High && exprop_ != 0)
      || exprop_ > 0;
    bool bpost = branchpost_ == 1;
    auto a = ltl_to_tgba_fm(f, simpl_->get_dict(), exprop,
                            true, bpost, false, nullptr, nullptr,
                            unambiguous,
                            nullptr, false, type_ == Finite);
    if (!bpost && branchpost_ != 0 && delay_branching_here(a))
      {
        a->purge_unreachable_states();
        a->merge_edges();
      }
    return a;
  }

  void translator::add_leading_x(twa_graph_ptr& aut, unsigned n)
  {
    unsigned init = aut->get_init_state_number();
    do
      {
        unsigned tmp = aut->new_state();
        aut->new_edge(tmp, init, bddtrue);
        init = tmp;
      }
    while (--n);
    aut->set_init_state(init);
    // Adding initial edges is very likely to kill stutter
    // invariance (and it certainly cannot fix it).
    if (aut->prop_stutter_invariant().is_true())
      aut->prop_stutter_invariant(trival::maybe());
  }

  twa_graph_ptr translator::run(formula* f)
  {
    if (type_ == BA)
      {
        pref_ |= SBAcc;
        type_ = Buchi;
      }
    if (pref_ & SBAcc)
      state_based_ = true;
    else if (state_based_)
      pref_ |= SBAcc;

    formula to_work_on = *f;
    std::string alive_ap;
    if (type_ == Finite)        // LTLf semantics
      {
        pref_ |= Obligation;
        // translating LTLf via LTL requires adding some atomic
        // proposition to keep track of when the formula is actually
        // "alive".  We just have to make sure that AP isn't already
        // used in the formula.
        atomic_prop_set apset;
        atomic_prop_collect(to_work_on, &apset);
        alive_ap = "alive";

        while (apset.contains(formula::ap(alive_ap)))
          alive_ap.push_back('$');

        to_work_on = from_ltlf(to_work_on, alive_ap.c_str());
      }

    if (simpl_owned_)
      {
        // Modify the options according to set_pref() and set_type().
        // We do it for all translations, but really only the first one
        // matters.
        auto& opt = simpl_owned_->options();
        if (comp_susp_ > 0 || (ltl_split_ && type_ == Generic))
          opt.favor_event_univ = true;
        if (type_ == Generic && ltl_split_ && (pref_ & Deterministic))
          opt.keep_top_xor = true;
      }

    // Do we want to relabel Boolean subformulas?
    // If we have a huge formula such as
    //  (a1 & a2 & ... & an) U (b1 | b2 | ... | bm)
    // then it is more efficient to translate
    //  a U b
    // and then fix the automaton.  We use relabel_bse() to find
    // sub-formulas that are Boolean but do not have common terms.
    //
    // This rewriting is enabled only if the formula
    //  1) has more than relabel_bool_ atomic propositions (the default
    //     is 4, but this can be changed)
    //  2) has some Boolean subformula
    //  3) relabel_bse() actually reduces the number of atomic
    //     propositions.
    //
    // If the formula still has more than relabel_overlap_ APs after
    // the above, we try the more aggressive relabel_overlapping_bse()
    // function.  However after applying this function, we might have
    // false edges.
    relabeling_map m;
    if (relabel_bool_ > 0 || relabel_overlap_ > 0)
      {
        std::set<formula> aps;
        atomic_prop_collect(to_work_on, &aps);
        unsigned atomic_props = aps.size();

        if ((relabel_bool_
             && atomic_props >= (unsigned) relabel_bool_)
            || (relabel_overlap_
                && atomic_props >= (unsigned) relabel_overlap_))
          {
            // Make a very quick simplification path before for
            // Boolean subformulas, using only syntactic rules.  This
            // is to help getting formulas of the form
            //   FGp1 & FGp2 & ... & FGp32
            // into the shape
            //   FG(p1 & p2 & ... & p32)
            // where relabeling will be much more efficient.
            //
            // We reuse all options of simpl_ (to preserve things
            // like keep_top_xor or favor_event_univ).
            tl_simplifier_options options = simpl_->options();
            options.synt_impl = false;
            options.containment_checks = false;
            options.containment_checks_stronger = false;
            options.nenoform_stop_on_boolean = true;
            options.boolean_to_isop = false;
            tl_simplifier simpl(options, simpl_->get_dict());
            formula simplified = to_work_on = simpl.simplify(to_work_on);

            // Do we have Boolean subformulas that are not atomic
            // propositions?
            bool has_boolean_sub = false;
            to_work_on.traverse([&](const formula& f)
                                {
                                  if (f.is_boolean()
                                      && !f.is(op::ap, op::Not))
                                    {
                                      has_boolean_sub = true;
                                      return true;
                                    }
                                  return false;
                                });

            if (has_boolean_sub)
              {
                if (relabel_bool_
                    && atomic_props >= (unsigned) relabel_bool_)
                  {
                    formula relabeled = relabel_bse(to_work_on, Pnn, &m);
                    if (m.size() < atomic_props)
                      {
                        atomic_props = m.size();
                        to_work_on = relabeled;
                      }
                    else
                      {
                        m.clear();
                      }
                  }
                if (relabel_overlap_
                    && atomic_props >= (unsigned) relabel_overlap_)
                  {
                    relabeling_map m2;
                    formula relabeled =
                      relabel_overlapping_bse(simplified, Pnn, &m2);
                    if (m2.size() < atomic_props)
                      {
                        atomic_props = m2.size();
                        to_work_on = relabeled;
                        std::swap(m, m2);
                      }
                    m2.clear();
                  }
              }
          }
      }

    formula r = simpl_->simplify(to_work_on);
    if (to_work_on == *f)
      *f = r;
    else if (type_ != Finite)
      *f = relabel_apply(r, &m);
    // TODO: In the Finite case we should get rid of alive in the
    // formula before updating *f.

    auto aut = run_aux(r);

    if (!m.empty())
      {
        unsigned ne = aut->num_edges();
        relabel_here(aut, &m);
        if (aut->num_edges() < ne)
          aut = finalize(do_scc_filter(aut));
      }
    if (type_ == Finite)
      aut = to_finite(aut, alive_ap.c_str());
    return aut;
  }

  twa_graph_ptr translator::run(formula f)
  {
    return run(&f);
  }

  void translator::clear_caches()
  {
    simpl_->clear_caches();
  }
}
