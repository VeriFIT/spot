# `SPOT_DEPRECATED` Functions in Spot

## Spot 2.10

| Function | File | Replacement |
|---|---|---|
| `graph_t::defrag_states(vector<unsigned>&&, unsigned)` (rvalue overload) | `graph/graph.hh` | Reference overload: `defrag_states(vector<unsigned>&, unsigned)` |
| `twa_graph::defrag_states(vector<unsigned>&&, unsigned)` (rvalue overload) | `twa/twagraph.hh` | Reference overload |

## Spot 2.11

| Function | File | Replacement |
|---|---|---|
| `pg_print(std::ostream&, const_twa_graph_ptr&)` | `twaalgos/game.hh` | `print_pg()` (consistent with API naming) |

## Spot 2.12

| Function | File | Replacement |
|---|---|---|
| `is_terminal_automaton(const_twa_graph_ptr&, scc_info*, bool)` (3-arg form) | `twaalgos/strength.hh` | 2-arg form `is_terminal_automaton(aut, sm)` — third arg is now ignored |

## Spot 2.16.1

| Function | File | Replacement |
|---|---|---|
| `ltl_to_tgba_fm()`'s `simplifier` argument | `twaalgos/ltl2tgba_fm.hh` | Simplify the input formula yourself; simplifying destination states was unsound |
| `ltl_to_tgba_fm_otf` / `ltl_to_ba_otf`'s `simplifier` argument | `twaalgos/ltl2tgba_fm.hh` | Same |
