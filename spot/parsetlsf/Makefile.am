## -*- coding: utf-8 -*-
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

AM_CPPFLAGS = -I$(top_builddir) -I$(top_srcdir) $(BUDDY_CPPFLAGS) \
              -DYY_NO_INPUT -I$(top_builddir)/lib -I$(top_srcdir)/lib
# YY_NO_INPUT lets us avoid linking in any default input() function.
# Disable -Werror because too many versions of flex yield warnings.
AM_CXXFLAGS = $(WARNING_CXXFLAGS:-Werror=)

parsetlsfdir = $(pkgincludedir)/parsetlsf

parsetlsf_HEADERS = public.hh

noinst_LTLIBRARIES = libparsetlsf.la

# Bison/Flex integration mirroring spot/parseaut/Makefile.am.

TLSFPARSE_YY = parsetlsf.yy
FROM_TLSFPARSE_YY_MAIN = parsetlsf.cc
FROM_TLSFPARSE_YY_OTHERS = \
  stack.hh \
  parsetlsf.hh

FROM_TLSFPARSE_YY = $(FROM_TLSFPARSE_YY_MAIN) $(FROM_TLSFPARSE_YY_OTHERS)

BUILT_SOURCES = $(FROM_TLSFPARSE_YY) scantlsf.cc
MAINTAINERCLEANFILES = $(FROM_TLSFPARSE_YY) scantlsf.cc

# Bison invocation.  We must cd into $(srcdir) first because if we
# tell bison to read $(srcdir)/$(TLSFPARSE_YY), it will also use
# $(srcdir)/ in the generated #include statements.
$(FROM_TLSFPARSE_YY_MAIN): $(srcdir)/$(TLSFPARSE_YY)
	cd $(srcdir) && \
	  $(BISON) -Wall -Werror -Wno-yacc --report=all $(BISON_EXTRA_FLAGS) \
	  $(TLSFPARSE_YY) -o $(FROM_TLSFPARSE_YY_MAIN)
$(FROM_TLSFPARSE_YY_OTHERS): $(TLSFPARSE_YY)
	@test -f $@ || $(MAKE) $(AM_MAKEFLAGS) $(FROM_TLSFPARSE_YY_MAIN)

# Flex invocation.  Generate scantlsf.cc from scantlsf.ll.
# Note: we keep `%option reentrant` in scantlsf.ll (matching
# spot/parseaut/scanaut.ll), so we cannot pass `--c++` to flex:
# `-c++` and `--reentrant` are mutually exclusive.  The .ll therefore
# produces a C reentrant scanner; the output is a plain C source that
# we rename to .cc so g++ compiles it as C++.  Bison's bison-bridge
# mode declares yylex with C linkage, so the C scanner's yylex links
# cleanly with the C++ parser.
scantlsf.cc: $(srcdir)/scantlsf.ll
	$(LEX) $(LFLAGS) -o $@ $<

EXTRA_DIST = $(TLSFPARSE_YY) scantlsf.ll

libparsetlsf_la_SOURCES = \
  ast.hh \
  fmterror.cc \
  $(FROM_TLSFPARSE_YY) \
  scantlsf.cc \
  public.cc \
  parsedecl.hh \
  translate.cc \
  translate.hh
