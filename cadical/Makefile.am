## Copyright (C) by the Spot authors, see the AUTHORS file for details.
##
## This file is part of Spot, a model checking library.
##
## Spot is free software; you can redistribute it and/or modify it
## under the terms of the GNU General Public License as published by
## the Free Software Foundation; either version 3 of the License, or
## (at your option) any later version.
##
## Spot is distributed in the hope that it will be useful, but WITHOUT
## ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
## or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
## License for more details.
##
## You should have received a copy of the GNU General Public License
## along with this program.  If not, see <http://www.gnu.org/licenses/>.

AUTOMAKE_OPTIONS = subdir-objects

noinst_LTLIBRARIES = libcadical.la

# Competition flags (as if Cadical were configured with --competition),
# using Spot's compiler options.  NBUILD avoids the need for a generated
# build.hpp; version.cpp falls back to built-in macros.
libcadical_la_CPPFLAGS = -DQUIET -DNTRACING -DNCONTRIB \
                         -DNIPASIR -DNBUILD -I$(srcdir)/src
if !DEVEL
# -DNCONTRACTS disables CaDiCaL's runtime invariant assertions.
libcadical_la_CPPFLAGS += -DNCONTRACTS
endif
# CaDiCaL uses closefrom(3) in its pipe fork-exec helper, but that function
# is BSD-only and not provided by musl libc.  Disable it whenever the
# system does not provide closefrom so that bundled CaDiCaL falls back to
# its simple per-fd close() loop.
if !HAVE_CLOSEFROM
libcadical_la_CPPFLAGS += -DNCLOSEFROM
endif

libcadical_la_SOURCES =				\
  src/analyze.cpp				\
  src/arena.cpp					\
  src/arena.hpp					\
  src/assume.cpp				\
  src/averages.cpp				\
  src/averages.hpp				\
  src/backbone.cpp				\
  src/backtrack.cpp				\
  src/backward.cpp				\
  src/bins.cpp					\
  src/bins.hpp					\
  src/block.cpp					\
  src/block.hpp					\
  src/cadical.hpp				\
  src/ccadical.cpp				\
  src/ccadical.h				\
  src/checker.cpp				\
  src/checker.hpp				\
  src/clause.cpp				\
  src/clause.hpp				\
  src/collect.cpp				\
  src/compact.cpp				\
  src/condition.cpp				\
  src/config.cpp				\
  src/config.hpp				\
  src/congruence.cpp				\
  src/congruence.hpp				\
  src/constrain.cpp				\
  src/contract.cpp				\
  src/contract.hpp				\
  src/cover.cpp					\
  src/cover.hpp					\
  src/decide.cpp				\
  src/decompose.cpp				\
  src/decompose.hpp				\
  src/deduplicate.cpp				\
  src/definition.cpp				\
  src/delay.hpp					\
  src/drattracer.cpp				\
  src/drattracer.hpp				\
  src/elim.cpp					\
  src/elimfast.cpp				\
  src/elim.hpp					\
  src/ema.cpp					\
  src/ema.hpp					\
  src/extend.cpp				\
  src/external.cpp				\
  src/external.hpp				\
  src/external_propagate.cpp			\
  src/factor.cpp				\
  src/factor.hpp				\
  src/file.cpp					\
  src/file.hpp					\
  src/flags.cpp					\
  src/flags.hpp					\
  src/flip.cpp					\
  src/format.cpp				\
  src/format.hpp				\
  src/frattracer.cpp				\
  src/frattracer.hpp				\
  src/gates.cpp					\
  src/heap.hpp					\
  src/idruptracer.cpp				\
  src/idruptracer.hpp				\
  src/instantiate.cpp				\
  src/instantiate.hpp				\
  src/internal.cpp				\
  src/internal.hpp				\
  src/inttypes.hpp				\
  src/ipasir.h					\
  src/kitten.c					\
  src/kitten.h					\
  src/level.hpp					\
  src/lidruptracer.cpp				\
  src/lidruptracer.hpp				\
  src/limit.cpp					\
  src/limit.hpp					\
  src/logging.cpp				\
  src/logging.hpp				\
  src/lookahead.cpp				\
  src/lratchecker.cpp				\
  src/lratchecker.hpp				\
  src/lrattracer.cpp				\
  src/lrattracer.hpp				\
  src/lucky.cpp					\
  src/message.cpp				\
  src/message.hpp				\
  src/minimize.cpp				\
  src/occs.cpp					\
  src/occs.hpp					\
  src/options.cpp				\
  src/options.hpp				\
  src/parse.cpp					\
  src/parse.hpp					\
  src/phases.cpp				\
  src/phases.hpp				\
  src/probe.cpp					\
  src/profile.cpp				\
  src/profile.hpp				\
  src/proof.cpp					\
  src/proof.hpp					\
  src/propagate.cpp				\
  src/queue.cpp					\
  src/queue.hpp					\
  src/radix.hpp					\
  src/random.cpp				\
  src/random.h					\
  src/random.hpp				\
  src/range.hpp					\
  src/reap.cpp					\
  src/reap.hpp					\
  src/reduce.cpp				\
  src/reluctant.hpp				\
  src/rephase.cpp				\
  src/report.cpp				\
  src/resources.cpp				\
  src/resources.hpp				\
  src/restart.cpp				\
  src/restore.cpp				\
  src/score.cpp					\
  src/score.hpp					\
  src/shrink.cpp				\
  src/signal.cpp				\
  src/signal.hpp				\
  src/solution.cpp				\
  src/solver.cpp				\
  src/stable.cpp				\
  src/stack.h					\
  src/stats.cpp					\
  src/stats.hpp					\
  src/subsume.cpp				\
  src/sweep.cpp					\
  src/sweep.hpp					\
  src/terminal.cpp				\
  src/terminal.hpp				\
  src/ternary.cpp				\
  src/testing.hpp				\
  src/tier.cpp					\
  src/tracer.hpp				\
  src/transred.cpp				\
  src/unstable.cpp				\
  src/util.cpp					\
  src/util.hpp					\
  src/var.cpp					\
  src/var.hpp					\
  src/veripbtracer.cpp				\
  src/veripbtracer.hpp				\
  src/version.cpp				\
  src/version.hpp				\
  src/vivify.cpp				\
  src/vivify.hpp				\
  src/walk.cpp					\
  src/walk_full_occs.cpp			\
  src/walk.hpp					\
  src/warmup.cpp				\
  src/watch.cpp					\
  src/watch.hpp

EXTRA_DIST = LICENSE README.md VERSION NEWS.md CONTRIBUTING.md src/README.md
