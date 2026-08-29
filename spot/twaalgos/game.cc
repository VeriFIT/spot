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

#include <utility>

#include <spot/twaalgos/game.hh>
#include <spot/misc/escape.hh>
#include <spot/twaalgos/sccinfo.hh>

namespace spot
{
  namespace
  {
    constexpr unsigned unseen_mark = std::numeric_limits<unsigned>::max();
    using priority_t = int;
    constexpr priority_t limit_priority_even =
        std::numeric_limits<priority_t>::max() & 1
        ? std::numeric_limits<priority_t>::max()-3
        : std::numeric_limits<priority_t>::max()-2;
    using strat_t = long long;
    constexpr strat_t no_strat_mark = std::numeric_limits<strat_t>::min();


    static const std::vector<bool>*
    ensure_game(const const_twa_graph_ptr& arena, const char* fnname)
    {
      auto owner = arena->get_named_prop<std::vector<bool>>("state-player");
      if (!owner)
        throw std::runtime_error
          (std::string(fnname) + ": automaton should define \"state-player\"");
      if (owner->size() != arena->num_states())
        throw std::runtime_error
          (std::string(fnname) + ": \"state-player\" should have "
           "as many states as the automaton");
      return owner;
    }

    static const std::vector<bool>*
    ensure_parity_game(const const_twa_graph_ptr& arena, const char* fnname)
    {
      bool max, odd;
      bool is_par = arena->acc().is_parity(max, odd, true);
      if (!is_par)
        throw std::runtime_error
          (std::string(fnname) +
           ": arena must have one of the four parity acceptance conditions");
      return ensure_game(arena, fnname);
    }

    // Internal structs
    // winning regions for env and player
    struct winner_t
    {
      std::vector<bool> has_winner_;
      std::vector<bool> winner_;

      inline bool operator()(unsigned v, bool p)
      {
        // returns true if player p wins v
        // false otherwise
        return has_winner_[v] ? winner_[v] == p : false;
      }

      inline void set(unsigned v, bool p)
      {
        has_winner_[v] = true;
        winner_[v] = p;
      }

      inline void unset(unsigned v)
      {
        has_winner_[v] = false;
      }

      inline bool winner(unsigned v)
      {
        assert(has_winner_.at(v));
        return winner_[v];
      }
    }; // winner_t

    // Internal structs used by parity_game
    // Struct to change recursive calls to stack
    struct work_t
    {
      work_t(unsigned wstep_, unsigned rd_, priority_t min_priority_,
             priority_t max_priority_) noexcept
        : wstep(wstep_),
          rd(rd_),
          min_priority(min_priority_),
          max_priority(max_priority_)
      {
      }
      const unsigned wstep, rd;
      const priority_t min_priority, max_priority;
    }; // work_t

    // Collects information about an scc
    // Used to detect special cases
    struct subgame_info_t
    {
      typedef std::set<priority_t, std::greater<priority_t>> all_priorities_t;

      subgame_info_t() noexcept
      {
      }

      subgame_info_t(bool empty, bool one_priority, bool one_player0,
                     bool one_player1, all_priorities_t priorities) noexcept
        : is_empty(empty),
          is_one_priority(one_priority),
          is_one_player0(one_player0),
          is_one_player1(one_player1),
          all_priorities(priorities)
      {};
      bool is_empty; // empty subgame
      bool is_one_priority; // only one priority appears in the subgame
      // todo : Not used yet
      bool is_one_player0; // one player subgame for player0 <-> p==false
      bool is_one_player1; // one player subgame for player1 <-> p==true
      all_priorities_t all_priorities;
    }; // subgame_info_t


    // A class to solve parity games
    // The current implementation is inspired by
    // by oink however without multicore and adapted to transition based
    // acceptance
    class parity_game
    {
    public:

      bool solve(const twa_graph_ptr& arena, bool solve_globally)
      {
        // todo check if reordering states according to scc is worth it
        set_up(arena);
        // Start recursive zielonka in a bottom-up fashion on each scc
        subgame_info_t subgame_info;
        while (true)
          {
            // If we solve globally,
            auto maybe_useful = [&](unsigned scc_idx){
              if (info_->is_useful_scc(scc_idx))
                return true;
              if (!solve_globally)
                return false;
              // Check if we have an out-edge to a winning state
              // in another scc
              return std::any_of(
                  info_->states_of(scc_idx).begin(),
                  info_->states_of(scc_idx).end(),
                  [&](unsigned s){
                    return std::any_of(
                                arena->out(s).begin(),
                                arena->out(s).end(),
                                [&](const auto& e){
                                  assert ((subgame_[e.dst] == unseen_mark)
                                          || (info_->scc_of(e.dst) != scc_idx));
                                  return (info_->scc_of(e.dst) != scc_idx)
                                          && w_.winner(e.dst);
                                });
                  });
            };

            for (c_scc_idx_ = 0; c_scc_idx_ < info_->scc_count(); ++c_scc_idx_)
              {
                // Testing
                // Make sure that every state that has a winner also
                // belongs to a subgame
                assert([&]()
                        {
                          for (unsigned i = 0; i < arena_->num_states(); ++i)
                            if (w_.has_winner_[i]
                                && (subgame_[i] == unseen_mark))
                              return false;
                            return true;
                        }());
                // Useless SCCs are winning for player 0.
                if (!maybe_useful(c_scc_idx_))
                  {
                    // This scc also gets its own subgame
                    ++rd_;
                    for (unsigned v: c_states())
                      {
                        subgame_[v] = rd_;
                        w_.set(v, false);
                        rank_[v] = 0;
                        // The strategy for player 0 is to take the first
                        // available edge.
                        if ((*owner_ptr_)[v] == false)
                          for (const auto &e : arena_->out(v))
                            {
                              s_[v] = arena_->edge_number(e);
                              break;
                            }
                      }
                    continue;
                  }
                // Convert transitions leaving edges to self-loops
                // and check if trivially solvable
                subgame_info = fix_scc();
                // If empty, the scc was trivially solved
                if (!subgame_info.is_empty)
                  {
                    // Check for special cases
                    if (subgame_info.is_one_priority)
                      one_priority_subgame_solver(subgame_info,
                                               max_abs_priority_);
                    else
                      {
                        // "Regular" solver
                        max_abs_priority_ =
                          *subgame_info.all_priorities.begin();
                        w_stack_.emplace_back(0, 0,
                                              min_priority_graph_,
                                              max_abs_priority_);
                        zielonka();
                      }
                  }
              }
            if (!solve_globally)
              break;

            // Update the scc_info and continue
            unsigned new_init
              = std::distance(subgame_.begin(),
                              std::find(subgame_.begin(), subgame_.end(),
                                        unseen_mark));
            if (new_init == arena->num_states())
              break; // All states have been solved
            // Compute new sccs
            scc_info::edge_filter ef
              = [](const twa_graph::edge_storage_t&,
                   unsigned dst, void* subgame){
                const auto& sg = *static_cast<std::vector<unsigned>*>(subgame);
                return sg[dst] == unseen_mark ?
                          scc_info::edge_filter_choice::keep :
                          scc_info::edge_filter_choice::ignore;
              };
            info_ = std::make_unique<scc_info>(arena, new_init, ef, &subgame_);
          }
        // Every state needs a winner (solve_globally)
        // Or only those reachable
        assert((solve_globally
                && std::all_of(w_.has_winner_.cbegin(), w_.has_winner_.cend(),
                               [](bool b) { return b; }))
                || (!solve_globally
                    && [&](){
                         for (unsigned s = 0; s < arena->num_states(); ++s)
                            {
                              if ((info_->scc_of(s) != -1u)
                                  && !w_.has_winner_.at(s))
                                return false;
                            }
                          return true;
                        }()));
        // Only the states owned by the winner need a strategy
        assert([&]()
               {
                  std::unordered_set<unsigned> valid_strat;
                  for (const auto& e : arena_->edges())
                    valid_strat.insert(arena_->edge_number(e));

                  for (unsigned v = 0; v < arena_->num_states(); ++v)
                    {
                      if (!solve_globally && (info_->scc_of(v) == -1u))
                        continue;
                      if (((*owner_ptr_)[v] == w_.winner(v))
                          && (valid_strat.count(s_.at(v)) == 0))
                        return false;
                    }
                  return true;
               }());

        // Put the solution as named property
        region_t &w = *arena->get_or_set_named_prop<region_t>("state-winner");
        strategy_t &s = *arena->get_or_set_named_prop<strategy_t>("strategy");
        w.swap(w_.winner_);
        s.clear();
        s.reserve(s_.size());
        for (auto as : s_)
          s.push_back(as == no_strat_mark ? 0 : (unsigned) as);

        clean_up();
        return w[arena->get_init_state_number()];
      }

    private:

      // Returns the vector of states currently considered
      // i.e. the states of the current scc
      // c_scc_idx_ is set in the 'main' loop
      inline const std::vector<unsigned> &c_states()
      {
        assert(info_);
        return info_->states_of(c_scc_idx_);
      }

      void set_up(const twa_graph_ptr& arena)
      {
        owner_ptr_ = ensure_parity_game(arena, "solve_parity_game()");
        arena_ = arena;
        unsigned n_states = arena_->num_states();
        // Resize data structures
        subgame_.clear();
        subgame_.resize(n_states, unseen_mark);
        w_.has_winner_.clear();
        w_.has_winner_.resize(n_states, 0);
        w_.winner_.clear();
        w_.winner_.resize(n_states, 0);
        s_.clear();
        s_.resize(n_states, no_strat_mark);
        rank_.clear();
        rank_.resize(n_states, unseen_mark);
        // Init
        rd_ = 0;
        info_ = std::make_unique<scc_info>(arena_);
        // Create all the priorities
        // we want zielonka to work with any of the four parity types
        // and we want it to work on partially colored arenas
        // However the actual algorithm still supposes max odd.
        // Therefore (and in order to avoid the manipulation of the mark
        // at each step) we generate a vector directly storing the
        // "equivalent" priority for each edge
        bool max, odd;
        arena_->acc().is_parity(max, odd, true);
        max_abs_priority_ = arena_->acc().all_sets().max_set()-1;
        // Make it the next larger odd
        priority_t next_max_priority = max_abs_priority_ + 1;
        all_edge_priorities_.resize(arena_->edge_vector().size(),
                             std::numeric_limits<priority_t>::max());

        // The priorities are modified much like for colorize_parity
        // however if the acceptance condition is "min", we negate all
        // priorities to get "max"
        // The algorithm works on negative or positive priorities alike.
        //
        // | kind/style | empty tr.   | other tr.  | result       |
        // |------------+-------------+------------+--------------|
        // | max odd    | set to -1   | unchanged  | max odd n    |
        // | max even   | set to 0    | add 1      | max odd n+1  |
        // | min odd    | set to -n   | negate     | max odd 0    |
        // | min even   | set to -n+1 | negate + 1 | max odd +1   |
        min_priority_graph_ = -(!max*max_abs_priority_) - (max*odd);
        max_priority_graph_ = max*(max_abs_priority_ + !odd) + !max*!odd;

        for (const auto& e : arena_->edges())
          {
            unsigned e_idx = arena_->edge_number(e);
            priority_t e_priority =
              (max ? e.acc.max_set() : e.acc.min_set()) - 1;
            // If "min" and empty -> set to n
            if (!max & (e_priority == -1))
              e_priority = next_max_priority;
            // Negate if min
            e_priority *= 2*max-1;
            // even -> odd
            e_priority += !odd;
            all_edge_priorities_[e_idx] = e_priority;
          }
      }

      // Checks if an scc is empty and reports the occurring priorities
      // or special cases
      inline subgame_info_t
      inspect_scc(priority_t max_priority)
      {
        subgame_info_t info;
        info.is_empty = true;
        info.is_one_player0 = true;
        info.is_one_player1 = true;
        for (unsigned v : c_states())
          {
            if (subgame_[v] != unseen_mark)
              continue;

            bool multi_edge = false;
            for (const auto &e : arena_->out(v))
              if (subgame_[e.dst] == unseen_mark)
                {
                  info.is_empty = false;
                  priority_t this_priority = to_priority(e);
                  if (this_priority <= max_priority)
                    {
                      info.all_priorities.insert(this_priority);
                      multi_edge = true;
                    }
                }
            if (multi_edge)
              {
                // This state has multiple edges, so it is not
                // a one player subgame for !owner
                if ((*owner_ptr_)[v])
                  info.is_one_player1 = false;
                else
                  info.is_one_player0 = false;
              }
          } // v
        assert(info.all_priorities.size() || info.is_empty);
        info.is_one_priority = info.all_priorities.size() == 1;
        // Done
        return info;
      }

      // Computes the trivially solvable part of the scc
      // That is the states that can be attracted to an
      // outgoing transition
      inline subgame_info_t
      fix_scc()
      {
        // Note that the winner of the transitions
        // leaving the scc are already determined
        // attr(...) will only modify the
        // states within the current scc
        // but we have to "trick" it into
        // not disregarding the transitions leaving the scc
        // dummy needed to pass asserts
        max_abs_priority_ = limit_priority_even+2;
        // The attractors should define their own subgame
        // but as we want to compute the attractors of the
        // leaving transitions, we need to make
        // sure that
        // a) no transition is excluded due to its parity
        // b) no transition is considered accepting/winning
        //    due to its priority
        // Final note: Attractors cannot intersect by definition
        //             therefore the order in which they are computed
        //             is irrelevant
        unsigned dummy_rd = 0;
        // Attractor of outgoing transitions winning for env
        attr(dummy_rd, false, limit_priority_even, true,
             limit_priority_even, false);
        // Attractor of outgoing transitions winning for player
        attr(dummy_rd, true, limit_priority_even+1, true,
             limit_priority_even+1, false);

        // No strategy fix need
        // assert if all winning states of the current scc have a valid strategy

        assert([&]()
               {
                 for (unsigned v : c_states())
                   {
                     if (!w_.has_winner_[v])
                       continue;
                     // We only need a strategy if the winner
                     // of the state is also the owner
                     if (w_.winner(v) != (*owner_ptr_)[v])
                       continue;
                     if (s_[v] <= 0)
                       {
                         std::cerr << "state " << v << " has a winner "
                                   << w_.winner(v) << " and owner "
                                   << (*owner_ptr_)[v]
                                   << " but no strategy "
                                   << s_[v] << '\n';
                         return false;
                       }
                     const auto& e = arena_->edge_storage(s_[v]);
                     if (!w_.has_winner_[e.dst]
                         || (w_.winner(e.src) != w_.winner(e.dst)))
                       {
                         std::cerr << "state " << v << " has a winner "
                                   << w_.winner(v)
                                   << " but no valid strategy\n";
                         return false;
                       }
                   }
                 return true;
               }());

        auto ins = inspect_scc(limit_priority_even);
        return ins;
      } // fix_scc

      inline bool
      attr(unsigned &rd, bool p, priority_t max_priority,
           bool acc_par, priority_t min_winning_priority, bool respect_sg=true)
      {
        // In fix_scc, the attr computation is
        // abused so we can not check certain things
        // Computes the attractor of the winning set of player p within a
        // subgame given as rd.
        // If acc_par is true, max_priority transitions are also accepting and
        // the subgame count will be increased
        // The attracted vertices are directly added to the set

        // Increase rd meaning we create a new subgame
        if (acc_par)
          rd = ++rd_;
        // todo replace with a variant of topo sort ?
        // As proposed in Oink! / PGSolver
        // Needs the transposed graph however

        assert((!acc_par) || (acc_par && to_player(max_priority) == p));
        assert(!acc_par || (min_priority_graph_ <= min_winning_priority));
        assert((min_winning_priority <= max_priority)
               && (max_priority <= max_abs_priority_));

        bool grown = false;
        // We could also directly mark states as owned,
        // instead of adding them to to_add first,
        // possibly reducing the number of iterations.
        // However by making the algorithm complete a loop
        // before adding it is like a backward bfs and (generally) reduces
        // the size of the strategy
        static std::vector<unsigned> to_add;

        assert(to_add.empty());

        do
          {
            grown |= !to_add.empty();
            for (unsigned v : to_add)
              {
                // v is winning
                w_.set(v, p);
                if (rank_[v] == unseen_mark)
                  rank_[v] = 0;
                // Mark if demanded
                if (acc_par)
                  {
                    assert(subgame_[v] == unseen_mark);
                    subgame_[v] = rd;
                  }
              }
            to_add.clear();

            for (unsigned v : c_states())
              {
                if ((subgame_[v] < rd) || (w_(v, p)))
                  // Not in subgame or winning for p
                  continue;

                bool is_owned = (*owner_ptr_)[v] == p;
                bool wins = !is_owned;
                // Loop over out-going

                // Optim: If given the choice,
                // we seek to go to the "oldest" subgame
                // That is the subgame with the lowest rd value
                unsigned min_subgame_idx = unseen_mark;
                for (const auto &e: arena_->out(v))
                  {
                    priority_t this_priority = to_priority(e);
                    if ((!respect_sg || (subgame_[e.dst] >= rd))
                         && (this_priority <= max_priority))
                      {
                        // Check if winning
                        if (w_(e.dst, p)
                            || (acc_par
                                && (min_winning_priority <= this_priority)))
                          {
                            assert(!acc_par
                                   || (this_priority < min_winning_priority)
                                   ||
                                   (acc_par
                                    && (min_winning_priority <= this_priority)
                                    &&
                                    (to_player(this_priority) == p)));
                            if (is_owned)
                              {
                                wins = true;
                                if (acc_par)
                                  {
                                    s_[v] = arena_->edge_number(e);
                                    if (min_winning_priority <= this_priority)
                                      // max-priority edge
                                      // change sign -> mark as needs
                                      // to be possibly fixed
                                      s_[v] = -s_[v];
                                    break;
                                  }
                                else
                                  {
                                    //snapping
                                    if (subgame_[e.dst] < min_subgame_idx)
                                      {
                                        s_[v] = arena_->edge_number(e);
                                        min_subgame_idx = subgame_[e.dst];
                                        rank_[v] =
                                          rank_[e.dst] == unseen_mark
                                          ? 0 : rank_[e.dst] + 1;

                                        if (!p)
                                          // No optim for env
                                          break;
                                      }
                                  }
                              }// owned
                          }
                        else
                          {
                            if (!is_owned)
                              {
                                wins = false;
                                break;
                              }
                          } // winning
                      } // subgame
                  }// for edges
                if (wins)
                  to_add.push_back(v);
              } // for v
          } while (!to_add.empty());
        // done

        assert(to_add.empty());
        return grown;
      }

      // We need to check if transitions that are accepted due
      // to their parity remain in the winning region of p
      inline bool
      fix_strat_acc(unsigned rd, bool p,
                     priority_t min_winning_priority,
                     priority_t max_priority)
      {
        for (unsigned v : c_states())
          {
            // Only current attractor and owned
            // and winning vertices are concerned
            if ((subgame_[v] != rd) || !w_(v, p)
                || ((*owner_ptr_)[v] != p) || (s_[v] > 0))
              continue;

            // owned winning vertex of attractor
            // Get the strategy edge
            s_[v] = -s_[v];
            const auto &e_s = arena_->edge_storage(s_[v]);
            // Optimization only for player
            if (!p && w_(e_s.dst, p))
              // If current strat is admissible ->
              // nothing to do for env
              continue;

            // This is an accepting edge that is no longer admissible
            // or we seek a more desirable edge (for player)
            assert(min_winning_priority <= to_priority(e_s));
            assert(to_priority(e_s) <= max_priority);

            // Strategy heuristic: prefer the lowest rank, then the oldest
            // winning subgame.  An accepting edge may point to a state in
            // the current attractor, which has no subgame number yet.
            unsigned min_subgame_idx = unseen_mark;
            unsigned min_rank = unseen_mark;
            unsigned min_dst = unseen_mark;

            s_[v] = no_strat_mark;
            for (const auto &e_fix : arena_->out(v))
              {
                priority_t this_priority = to_priority(e_fix);
                // This edge must have less than max_priority, otherwise it
                // would have already been attracted.
                assert((this_priority <= max_priority)
                       || (to_player(this_priority) != (max_priority&1)));
                // If it is accepting and leads to the winning region, it is
                // a valid fix.
                if ((min_winning_priority <= this_priority)
                    && (this_priority <= max_priority)
                    && w_(e_fix.dst, p))
                  {
                    unsigned subgame_idx = subgame_[e_fix.dst] == unseen_mark
                      ? rd : subgame_[e_fix.dst];
                    unsigned edge_rank = rank_[e_fix.dst] == unseen_mark
                      ? 0 : rank_[e_fix.dst] + 1;
                    bool better = edge_rank < min_rank
                      || (edge_rank == min_rank
                          && subgame_idx < min_subgame_idx)
                      || (edge_rank == min_rank
                          && subgame_idx == min_subgame_idx
                          && e_fix.dst < min_dst);
                    if (better)
                      {
                        s_[v] = arena_->edge_number(e_fix);
                        min_subgame_idx = subgame_idx;
                        min_rank = edge_rank;
                        min_dst = e_fix.dst;
                        rank_[v] = edge_rank;
                      }
                  }
              }
            if (s_[v] == no_strat_mark)
              // NO fix found
              // This state is NOT won by p due to any accepting edges
              return true; // true -> grown
          }
        // Nothing to fix or all fixed
        return false; // false -> not grown == all good
      }

      inline void zielonka()
      {
        while (!w_stack_.empty())
          {
            auto this_work = w_stack_.back();
            w_stack_.pop_back();

            switch (this_work.wstep)
              {
              case (0):
                {
                  assert(this_work.rd == 0);
                  assert(this_work.min_priority == min_priority_graph_);

                  unsigned rd;
                  assert(this_work.max_priority <= max_abs_priority_);

                  // Check if empty and get priorities
                  subgame_info_t subgame_info =
                    inspect_scc(this_work.max_priority);

                  if (subgame_info.is_empty)
                    // Nothing to do
                    break;
                  if (subgame_info.is_one_priority)
                    {
                      // Can be trivially solved
                      one_priority_subgame_solver(subgame_info,
                                               this_work.max_priority);
                      break;
                    }

                  // Compute the winning priority boundaries
                  // -> Priority compression
                  // Optional, improves performance
                  // Highest actually occurring
                  // Attention in partially colored graphs
                  // the priority -1 and 0 appear
                  priority_t max_priority =
                    *subgame_info.all_priorities.begin();
                  priority_t min_winning_priority = max_priority;
                  while ((min_winning_priority >= (min_priority_graph_+2)) &&
                         (!subgame_info.all_priorities.count(
                             min_winning_priority - 1)))
                    min_winning_priority -= 2;
                  assert(min_winning_priority >= min_priority_graph_);
                  assert(max_priority >= min_winning_priority);
                  assert((max_priority&1) == (min_winning_priority&1));
                  assert(!subgame_info.all_priorities.empty());

                  // Get the player
                  bool p = to_player(min_winning_priority);
                  // Attraction to highest priority
                  // This increases rd_ and passes it to rd
                  attr(rd, p, max_priority, true, min_winning_priority);
                  // All those attracted get subgame_[v] <- rd

                  // Continuation
                  w_stack_.emplace_back(1, rd, min_winning_priority,
                                        max_priority);
                  // Recursion
                  w_stack_.emplace_back(0, 0, min_priority_graph_,
                                        min_winning_priority - 1);
                  // Others attracted will have higher counts in subgame
                  break;
                }
              case (1):
                {
                  unsigned rd = this_work.rd;
                  priority_t min_winning_priority = this_work.min_priority;
                  priority_t max_priority = this_work.max_priority;
                  assert(to_player(min_winning_priority)
                         == to_player(max_priority));
                  bool p = to_player(min_winning_priority);
                  // Check if the attractor of w_[!p] is equal to w_[!p]
                  // if so, player wins if there remain accepting transitions
                  // for max_priority (see fix_strat_acc)
                  // This does not increase but reuse rd
                  bool grown = attr(rd, !p, max_priority, false,
                                    min_winning_priority);
                  // todo investigate: A is an attractor, so the only way that
                  // attr(w[!p]) != w[!p] is if the max par "exit" edges lead
                  // to a trap for player/ exit the winning region of the
                  // player so we can do a fast check instead of the
                  // generic attr computation which only needs to be done
                  // if the fast check is positive

                  // Check if strategy needs to be fixed / is fixable
                  if (!grown)
                    // this only concerns priority accepting edges
                    grown = fix_strat_acc(rd, p, min_winning_priority,
                                         max_priority);
                  // If !grown we are done, and the partitions are valid

                  if (grown)
                    {
                      // Reset current game without !p attractor
                      for (unsigned v : c_states())
                        if (!w_(v, !p) && (subgame_[v] >= rd))
                          {
                            // delete ownership
                            w_.unset(v);
                            // Mark as unseen
                            subgame_[v] = unseen_mark;
                            // Unset strat for testing
                            s_[v] = no_strat_mark;
                          }
                      w_stack_.emplace_back(0, 0, min_priority_graph_,
                                            max_priority);
                      // No need to do anything else
                      // the attractor of !p of this level is not changed
                    }
                  break;
                }
              default:
                throw std::runtime_error("No valid workstep");
              } // switch
          } // while
      } // zielonka

      // Empty all internal variables
      inline void clean_up()
      {
        info_ = nullptr;
        subgame_.clear();
        w_.has_winner_.clear();
        w_.winner_.clear();
        s_.clear();
        rank_.clear();
        rd_ = 0;
        max_abs_priority_ = 0;
      }

      // Dedicated solver for special cases
      inline void one_priority_subgame_solver(const subgame_info_t &info,
                                         priority_t max_priority)
      {
        assert(info.all_priorities.size() == 1);
        // The entire subgame is won by the player of the only priority
        // Any edge will do
        // todo optim for smaller circuit
        // This subgame gets its own counter
        ++rd_;
        unsigned rd = rd_;
        priority_t one_priority = *info.all_priorities.begin();
        bool winner = to_player(one_priority);
        assert(one_priority <= max_priority);

        for (unsigned v : c_states())
          {
            if (subgame_[v] != unseen_mark)
              continue;
            // State of the subgame
            subgame_[v] = rd;
            w_.set(v, winner);
            // Get the strategy.  Prefer the oldest suitable subgame.
            // This is only a heuristic: the parity solver's winning
            // regions remain unchanged.
            assert(s_[v] == no_strat_mark);
            unsigned min_subgame_idx = unseen_mark;
            for (const auto &e : arena_->out(v))
              {
                priority_t this_priority = to_priority(e);
                if ((subgame_[e.dst] >= rd) && (this_priority <= max_priority))
                  {
                    assert(this_priority == one_priority);
                    // States in the current one-priority subgame are not
                    // assigned a subgame number until this loop completes.
                    // Consequently, prefer them over already solved exits.
                    unsigned subgame_idx =
                      subgame_[e.dst] == unseen_mark ? rd : subgame_[e.dst];
                    if (subgame_idx < min_subgame_idx)
                      {
                        min_subgame_idx = subgame_idx;
                        s_[v] = arena_->edge_number(e);
                      }
                  }
              }
            assert((0 < s_[v]) && (s_[v] < unseen_mark));
          }
        // Done
      }

      template <class EDGE>
      inline priority_t
      to_priority(const EDGE& e)
      {
        return all_edge_priorities_[arena_->edge_number(e)];
      }

      inline bool
      to_player(priority_t par)
      {
        return par & 1;
      }

      twa_graph_ptr arena_;
      const std::vector<bool> *owner_ptr_;
      unsigned rd_;
      winner_t w_;
      // Subgame array similar to the one from oink!
      std::vector<unsigned> subgame_;
      // strategies for env and player; For synthesis only player is needed
      // We need a signed value here in order to "fix" the strategy
      // during construction
      std::vector<strat_t> s_;
      // Heuristic distance to the seed of the current attractor.
      std::vector<unsigned> rank_;

      // Informations about sccs and the current scc
      std::unique_ptr<scc_info> info_;
      priority_t max_abs_priority_; // Max priority occurring in the current scc
      // Minimal and maximal priority occurring in the entire graph
      priority_t min_priority_graph_, max_priority_graph_;
      // Info on the current scc
      unsigned c_scc_idx_;
      // Change recursive calls to stack
      std::vector<work_t> w_stack_;
      // Directly store a vector of priorities
      // This vector will be created such
      // that it takes care of the actual parity condition
      // and after that zielonka can be called as if max odd
      std::vector<priority_t> all_edge_priorities_;
    };

  } // anonymous


  bool solve_parity_game(const twa_graph_ptr& arena, bool solve_globally)
  {
    parity_game pg;
    return pg.solve(arena, solve_globally);
  }

  bool solve_game(const twa_graph_ptr& arena)
  {
    bool dummy1, dummy2;
    auto& acc = arena->acc();
    if (acc.is_t())
      return solve_safety_game(arena);
    if (!arena->acc().is_parity(dummy1, dummy2, true))
      throw std::runtime_error
        ("solve_game(): unsupported acceptance condition.");
    return solve_parity_game(arena);
  }

  // backward compatibility
  void pg_print(std::ostream& os, const const_twa_graph_ptr& arena)
  {
    print_pg(os, arena);
  }

  std::ostream& print_pg(std::ostream& os, const const_twa_graph_ptr& arena)
  {
    bool is_par, max, odd;
    is_par = arena->acc().is_parity(max, odd, true);
    if (!is_par)
      throw std::runtime_error("print_pg: arena must have a parity acceptance");
    const region_t& owner = *ensure_game(arena, "print_pg");

    bool max_odd_colored =
      max && odd && std::all_of(arena->edges().begin(),
                                arena->edges().end(),
                                [](const auto& e)
                                {
                                  return (bool) e.acc;
                                });
    const_twa_graph_ptr towork = arena;
    if (!max_odd_colored)
      {
        twa_graph_ptr tmp =
          change_parity(arena, parity_kind_max, parity_style_odd);
        colorize_parity_here(tmp, true);
        towork = tmp;
      }

    auto sn = arena->get_named_prop<std::vector<std::string>>("state-names");
    unsigned ns = towork->num_states();
    unsigned init = towork->get_init_state_number();
    os << "parity " << ns - 1 << ";\n";
    std::vector<bool> seen(ns, false);
    std::vector<unsigned> todo({init});
    while (!todo.empty())
      {
        unsigned src = todo.back();
        todo.pop_back();
        if (seen[src])
          continue;
        seen[src] = true;
        os << src << ' ';
        os << towork->out(src).begin()->acc.max_set() - 1 << ' ';
        os << owner[src] << ' ';
        bool first = true;
        for (auto& e: arena->out(src))
          {
            if (!first)
              os << ',';
            first = false;
            os << e.dst;
            if (!seen[e.dst])
              todo.push_back(e.dst);
          }
        if (sn && sn->size() > src && !(*sn)[src].empty())
          {
            os << " \"";
            escape_str(os, (*sn)[src]);
            os << '"';
          }
        os << ";\n";
      }
    return os;
  }

  void alternate_players(spot::twa_graph_ptr& arena,
                         bool first_player, bool complete0)
  {
    auto um = arena->acc().unsat_mark();
    if (!um.first && complete0)
      throw std::runtime_error
        ("alternate_players(): Cannot complete monitor.");

    unsigned sink_env = 0;
    unsigned sink_con = 0;

    std::vector<bool> seen(arena->num_states(), false);
    unsigned init = arena->get_init_state_number();
    std::vector<unsigned> todo({init});
    auto owner = new std::vector<bool>(arena->num_states(), false);
    (*owner)[init] = first_player;
    while (!todo.empty())
      {
        unsigned src = todo.back();
        todo.pop_back();
        seen[src] = true;
        bdd missing = bddtrue;
        for (auto& e: arena->out(src))
          {
            bool osrc = (*owner)[src];
            if (complete0 && !osrc)
              missing -= e.cond;

            if (!seen[e.dst])
              {
                (*owner)[e.dst] = !osrc;
                todo.push_back(e.dst);
              }
            else if (e.src == e.dst)
              {
                if (e.cond == bddtrue)
                  {
                    // Fix trivial self-loop
                    // No need to add it to seen
                    auto inter = arena->new_state();
                    owner->push_back(!osrc);
                    e.dst = inter;
                    arena->new_edge(inter, src, bddtrue, e.acc);
                  }
                else
                  throw std::runtime_error("alternate_players(): "
                                            "Nontrivial selfloop");
              }
            else if ((*owner)[e.dst] == osrc)
              {
                delete owner;
                throw std::runtime_error
                  ("alternate_players(): Odd cycle detected.");
              }
          }
        if (complete0 && !(*owner)[src] && missing != bddfalse)
          {
            if (sink_env == 0)
              {
                sink_env = arena->new_state();
                sink_con = arena->new_state();
                owner->push_back(true);
                owner->push_back(false);
                arena->new_edge(sink_con, sink_env, bddtrue, um.second);
                arena->new_edge(sink_env, sink_con, bddtrue, um.second);
              }
            arena->new_edge(src, sink_env, missing, um.second);
            assert(owner->at(src) != owner->at(sink_env));
          }
      }

    assert([&]()
      {
        for (const auto& e : arena->edges())
          if (owner->at(e.src) == owner->at(e.dst))
            return false;
        return true;
      }() && "Not alternating");

    arena->set_named_prop("state-player", owner);
  }

  twa_graph_ptr
  highlight_strategy(twa_graph_ptr& aut,
                     int player0_color,
                     int player1_color)
  {
    auto owner = ensure_game(aut, "highlight_strategy()");
    region_t* w = aut->get_named_prop<region_t>("state-winner");
    strategy_t* s = aut->get_named_prop<strategy_t>("strategy");
    if (!w)
      throw std::runtime_error
        ("highlight_strategy(): "
         "winning region unavailable, solve the game first");
    if (!s)
      throw std::runtime_error
        ("highlight_strategy(): strategy unavailable, solve the game first");

    unsigned ns = aut->num_states();
    auto* hl_edges = aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
      ("highlight-edges");
    auto* hl_states = aut->get_or_set_named_prop<std::map<unsigned, unsigned>>
      ("highlight-states");

    if (unsigned sz = std::min(w->size(), s->size()); sz < ns)
      ns = sz;

    for (unsigned n = 0; n < ns; ++n)
      {
        int color = (*w)[n] ? player1_color : player0_color;
        if (color == -1)
          continue;
        (*hl_states)[n] = color;
        if ((*w)[n] == (*owner)[n])
          (*hl_edges)[(*s)[n]] = color;
      }

    return aut;
  }

  void set_state_players(twa_graph_ptr& arena, const region_t& owners)
  {
    set_state_players(arena, region_t(owners));
  }

  void set_state_players(twa_graph_ptr& arena, region_t&& owners)
  {
    if (owners.size() != arena->num_states())
      throw std::runtime_error
        ("set_state_players(): There must be as many owners as states");

    arena->set_named_prop<region_t>("state-player",
                                    new region_t(std::move(owners)));
  }

  void set_state_player(twa_graph_ptr& arena, unsigned state, bool owner)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("set_state_player(): invalid state number");

    region_t *owners = arena->get_named_prop<region_t>("state-player");
    if (!owners)
      throw std::runtime_error("set_state_player(): Can only set the state of "
                               "an individual "
                               "state if \"state-player\" already exists.");
    if (owners->size() != arena->num_states())
      throw std::runtime_error("set_state_player(): The \"state-player\" "
                               "vector has a different "
                               "size compared to the automaton! "
                               "Called new_state in between?");

    (*owners)[state] = owner;
  }

  const region_t& get_state_players(const const_twa_graph_ptr& arena)
  {
    region_t *owners = arena->get_named_prop<region_t>
      ("state-player");
    if (!owners)
      throw std::runtime_error
        ("get_state_players(): state-player property not defined, not a game?");

    return *owners;
  }

  const region_t& get_state_players(twa_graph_ptr& arena)
  {
    region_t *owners = arena->get_named_prop<region_t>
      ("state-player");
    if (!owners)
      throw std::runtime_error
        ("get_state_players(): state-player property not defined, not a game?");

    return *owners;
  }

  bool get_state_player(const const_twa_graph_ptr& arena, unsigned state)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("get_state_player(): invalid state number");

    region_t* owners = arena->get_named_prop<region_t>("state-player");
    if (!owners)
      throw std::runtime_error
        ("get_state_player(): state-player property not defined, not a game?");

    return (*owners)[state];
  }


  const strategy_t& get_strategy(const const_twa_graph_ptr& arena)
  {
    auto strat_ptr = arena->get_named_prop<strategy_t>("strategy");
    if (!strat_ptr)
      throw std::runtime_error("get_strategy(): Named prop "
                               "\"strategy\" not set. "
                               "Arena not solved?");
    return *strat_ptr;
  }

  void set_strategy(twa_graph_ptr& arena, const strategy_t& strat)
  {
    set_strategy(arena, strategy_t(strat));
  }
  void set_strategy(twa_graph_ptr& arena, strategy_t&& strat)
  {
    if (arena->num_states() != strat.size())
      throw std::runtime_error("set_strategy(): strategies need to have "
                               "the same size as the automaton.");
    arena->set_named_prop<strategy_t>("strategy",
        new strategy_t(std::move(strat)));
  }

  void set_synthesis_outputs(const twa_graph_ptr& arena, const bdd& outs)
  {
    arena->set_named_prop<bdd>("synthesis-outputs", new bdd(outs));
  }

  bdd get_synthesis_outputs(const const_twa_graph_ptr& arena)
  {
    if (auto outptr = arena->get_named_prop<bdd>("synthesis-outputs"))
      return *outptr;
    else
      throw std::runtime_error
          ("get_synthesis_outputs(): synthesis-outputs not defined");
  }

  std::vector<std::string>
  get_synthesis_output_aps(const const_twa_graph_ptr& arena)
  {
    std::vector<std::string> out_names;

    bdd outs = get_synthesis_outputs(arena);

    auto dict = arena->get_dict();

    auto to_bdd = [&](const auto& x)
      {
        return bdd_ithvar(dict->has_registered_proposition(x, arena.get()));
      };

    for (const auto& ap : arena->ap())
      if (bdd_implies(outs, to_bdd(ap)))
        out_names.push_back(ap.ap_name());

    return out_names;
  }


  void set_state_winners(twa_graph_ptr& arena, const region_t& winners)
  {
    set_state_winners(arena, region_t(winners));
  }

  void set_state_winners(twa_graph_ptr& arena, region_t&& winners)
  {
    if (winners.size() != arena->num_states())
      throw std::runtime_error
        ("set_state_winners(): There must be as many winners as states");

    arena->set_named_prop<region_t>("state-winner",
                                    new region_t(std::move(winners)));
  }

  void set_state_winner(twa_graph_ptr& arena, unsigned state, bool winner)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("set_state_winner(): invalid state number");

    region_t *winners = arena->get_named_prop<region_t>("state-winner");
    if (!winners)
      throw std::runtime_error("set_state_winner(): Can only set the state of "
                               "an individual "
                               "state if \"state-winner\" already exists.");
    if (winners->size() != arena->num_states())
      throw std::runtime_error("set_state_winner(): The \"state-winner\" "
                               "vector has a different "
                               "size compared to the automaton! "
                               "Called new_state in between?");

    (*winners)[state] = winner;
  }

  const region_t& get_state_winners(const const_twa_graph_ptr& arena)
  {
    region_t *winners = arena->get_named_prop<region_t>("state-winner");
    if (!winners)
      throw std::runtime_error
        ("get_state_winners(): state-winner property not defined, not a game?");

    return *winners;
  }

  // This second version should not be needed, but g++14 emits
  // "possibly dangling reference" warnings when it sees that the
  // first function is called with a temporary const_twa_graph_ptr to
  // return a reference.
  const region_t& get_state_winners(twa_graph_ptr& arena)
  {
    region_t *winners = arena->get_named_prop<region_t>("state-winner");
    if (!winners)
      throw std::runtime_error
        ("get_state_winners(): state-winner property not defined, not a game?");
    return *winners;
  }

  bool get_state_winner(const const_twa_graph_ptr& arena, unsigned state)
  {
    if (state >= arena->num_states())
      throw std::runtime_error("get_state_winner(): invalid state number");

    region_t* winners = arena->get_named_prop<region_t>("state-winner");
    if (!winners)
      throw std::runtime_error
        ("get_state_winner(): state-winner property not defined, not a game?");

    return (*winners)[state];
  }


  bool solve_safety_game(const twa_graph_ptr& game)
  {
    if (!game->acc().is_t())
      throw std::runtime_error
        ("solve_safety_game(): arena should have true acceptance");

    auto owners = get_state_players(game);

    unsigned ns = game->num_states();
    auto winners = new region_t(ns, true);
    game->set_named_prop("state-winner", winners);
    auto strategy = new strategy_t(ns, 0);
    game->set_named_prop("strategy", strategy);

    // transposed is a reversed copy of game to compute predecessors
    // more easily.  It also keep track of the original edge index.
    struct edge_data {
      unsigned edgeidx;
    };
    digraph<void, edge_data> transposed;
    // Reverse the automaton, compute the out degree of
    // each state, and save dead-states in queue.
    transposed.new_states(ns);
    std::vector<unsigned> out_degree;
    out_degree.reserve(ns);
    std::vector<unsigned> queue;
    for (unsigned s = 0; s < ns; ++s)
      {
        unsigned deg = 0;
        for (auto& e: game->out(s))
          {
            transposed.new_edge(e.dst, e.src, game->edge_number(e));
            ++deg;
          }
        out_degree.push_back(deg);
        if (deg == 0)
          {
            (*winners)[s] = false;
            queue.push_back(s);
          }
      }
    // queue is initially filled with dead-states, which are winning
    // for player 0.  Any predecessor owned by player 0 is therefore
    // winning as well (check 1), and any predecessor owned by player
    // 1 that has all its successors winning for player 0 (check 2) is
    // also winning.  Use queue to propagate everything.
    // For the second check, we decrease out_degree by each edge leading
    // to a state winning for player 0, so if out_degree reaches 0,
    // we have ensured that all outgoing transitions are winning for 0.
    //
    // We use queue as a stack, to propagate bad states in DFS.
    // However it would be ok to replace the vector by a std::deque
    // to implement a BFS and build shorter strategies for player 0.
    // Right no we are assuming that strategies for player 0 have
    // limited uses, so we just avoid the overhead of std::deque in
    // favor of the simpler std::vector.
    while (!queue.empty())
      {
        unsigned s = queue.back();
        queue.pop_back();
        for (auto& e: transposed.out(s))
          {
            unsigned pred = e.dst;
            if (!(*winners)[pred])
              continue;
            // check 1 || check 2
            bool check1 = owners[pred] == false;
            if (check1 || --out_degree[pred] == 0)
              {
                (*winners)[pred] = false;
                queue.push_back(pred);
                if (check1)
                  (*strategy)[pred] = e.edgeidx;
              }
          }
      }
    // Let's fill in the strategy for Player 1.
    for (unsigned s = 0; s < ns; ++s)
      if (owners[s] && (*winners)[s])
        for (auto& e: game->out(s))
          if ((*winners)[e.dst])
            {
              (*strategy)[s] = game->edge_number(e);
              break;
            }

    return (*winners)[game->get_init_state_number()];
  }
}
