/*========================================================================
	       Copyright (C) 2026 Alexandre Duret-Lutz
			    All rights reserved

    Permission is hereby granted, without written agreement and without
    license or royalty fees, to use, reproduce, prepare derivative
    works, distribute, and display this software and its documentation
    for any purpose, provided that (1) the above copyright notice and
    the following two paragraphs appear in all copies of the source code
    and (2) redistributions, including without limitation binaries,
    reproduce these notices in the supporting documentation. Substantial
    modifications to this software may be copyrighted by their authors
    and need not follow the licensing terms described here, provided
    that the new terms are clearly indicated in all files where they apply.

    IN NO EVENT SHALL JORN LIND-NIELSEN, OR DISTRIBUTORS OF THIS
    SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
    INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS
    SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE AUTHORS OR ANY OF THE
    ABOVE PARTIES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    JORN LIND-NIELSEN SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
    BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
    ON AN "AS IS" BASIS, AND THE AUTHORS AND DISTRIBUTORS HAVE NO
    OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
    MODIFICATIONS.
========================================================================*/

#include <assert.h>
#include "kernel.h"

/* The Minato-Morreale algorithm computes an irredundant sum of products
   (ISOP) of a BDD by a recursive descent over the variables.  A pair of
   functions (f_min, f_max), with f_min implying f_max, encodes the
   residual function: at each level, f_min and f_max are restricted to
   v=0 and v=1, an ISOP is computed for each of the two parts that are
   not covered by the other one, and the part that is left once the cubes
   found so far have been removed is processed last.  The value returned
   by each call is the cover of the residual subtree, so that a part
   already covered by a sibling is not enumerated twice, which is what
   makes the cover irredundant.

   The whole enumeration is done by one call to bdd_isop() and friends,
   which pass each prime implicant to a handler: this keeps the
   recursion outside of BuDDy's reference-counting and allows the caller
   to choose what to do with each cube.  The three entry points differ
   only by the way the status of a variable is decided: if v is
   positive-unate (i.e., f|v=0 implies f|v=1), the first step of the
   algorithm is empty and is skipped.  When no variable, or every
   variable, is known to be positive-unate, that decision is a constant
   and the positive-variable cube is not even looked at.

   Variables are consumed in increasing level order, and the variable to
   split on is simply the smallest level used by f_min or f_max.  Since
   bdd_restrict() is not used, a function that does not mention the
   split variable is left unchanged, and the recursion is at most as
   deep as the number of variables of the function.  */

/* Whether the split variable is known to be positive-unate. */
typedef enum
{
  NO_POSITIVE_VAR,    /* no variable is positive-unate */
  SOME_POSITIVE_VARS, /* only the variables of the POS cube are */
  ALL_POSITIVE_VARS   /* all variables are positive-unate */
} positive_mode;

typedef struct
{
  bddisophandler handler; /* called once per prime implicant */
  void* data;             /* second argument of HANDLER */
  positive_mode mode;     /* how to read the POS cube */
} isop_context;


/* Whether the variable of level LV is known to be positive-unate, and
   advance *POS past the variables of level below LV, so that the next
   call does not scan them again.

   POS is a cube of positive literals listing, in increasing level
   order, the variables that the caller claims to be positive-unate.
   Variables of level below LV have already been split by an ancestor of
   the current call, and cannot appear in the residual. */
static int isop_is_positive(isop_context* ctx, int lv, BDD* pos)
{
  BDD p;

  if (ctx->mode == NO_POSITIVE_VAR)
    return 0;
  if (ctx->mode == ALL_POSITIVE_VARS)
    return 1;

  p = *pos;
  while (p != BDDONE && LEVEL(p) < lv)
    p = HIGH(p);
  *pos = p;

  return p != BDDONE && LEVEL(p) == lv;
}


/* Pass CUBE to the handler.  The cube is referenced for the duration of
   the call, so the handler may run any BDD operation (garbage
   collection included) and may call bdd_addref() to keep the cube. */
static void isop_emit(isop_context* ctx, BDD cube)
{
  bdd_addref(cube);
  ctx->handler(cube, ctx->data);
  bdd_delref(cube);
}


/* Call the handler for each prime implicant of the residual (F_MIN,
   F_MAX) extended by the literals of CUBE.

   F_MIN must imply F_MAX.  POS is the suffix of the positive-unate
   variables, in increasing level order.

   The returned value is the cover of the residual, i.e., the
   disjunction of the cubes enumerated in this subtree, without the
   literals of CUBE.

   BuDDy's reference stack is sized after the number of variables, which
   is too small to hold the values of a recursive descent that can go as
   deep as the number of variables (and BuDDy's operators reset it).
   Values that must survive a recursive call are therefore protected
   with bdd_addref()/bdd_delref().  F_MIN, F_MAX, POS and CUBE do not
   need any: the entry points take a reference on their arguments, and
   the recursive calls only descend into subgraphs of these arguments.

   This routine assumes that reordering is disabled, so that the levels
   it compares in different frames keep their meaning.  See isop_top(). */
static BDD isop_rec(isop_context* ctx, BDD f_min, BDD f_max,
                    BDD pos, BDD cube)
{
  BDD f0_min, f1_min, f0_max, f1_max;
  BDD g0, g1, gs, res;
  int var, lv_min, lv_max, lv;

  if (f_min == BDDZERO)
    return BDDZERO;
  if (f_max == BDDONE)
    {
      /* No variable left to split: CUBE is a prime implicant. */
      isop_emit(ctx, cube);
      return BDDONE;
    }

  /* Split on the variable of the smallest level used by F_MIN or
     F_MAX.  Because variables are consumed in increasing level order,
     and because no variable occurs twice along a path, the levels of
     the splits are strictly increasing.

     F_MIN and F_MAX are not constants here: F_MIN implies F_MAX, so
     F_MIN != 0 (checked above) rules out F_MAX == 0, and F_MAX != 1
     (checked above) rules out F_MIN == 1.  LEVEL() is therefore
     defined, and the two tests below are enough to know which of the
     two functions mentions the split variable. */
  lv_min = LEVEL(f_min);
  lv_max = LEVEL(f_max);
  lv = lv_min < lv_max ? lv_min : lv_max;
  var = bddlevel2var[lv];

  /* Restrict F_MIN and F_MAX to v=0 and v=1.  Since LV is the smallest
     level used by the two functions, the function that does not mention
     V is left unchanged: there is no need to call bdd_restrict() here. */
  f0_min = lv_min == lv ? LOW(f_min) : f_min;
  f1_min = lv_min == lv ? HIGH(f_min) : f_min;
  f0_max = lv_max == lv ? LOW(f_max) : f_max;
  f1_max = lv_max == lv ? HIGH(f_max) : f_max;

  if (isop_is_positive(ctx, lv, &pos))
    {
      BDD v1, d1, nc1, t1, fs_min, cov;

      /* POSITIVE means that f0_max implies f1_max, so no prime
         implicant can contain !v and the first step of the algorithm
         (which looks for such cubes) can be skipped. */
      assert(bdd_implies(f0_max, f1_max));

      /* Cubes containing v. */
      v1 = bdd_addref(bdd_ithvar(var));
      d1 = bdd_addref(bdd_apply(f1_min, f0_max, bddop_diff));
      nc1 = bdd_addref(bdd_apply(cube, v1, bddop_and));
      g1 = bdd_addref(isop_rec(ctx, d1, f1_max, pos, nc1));
      bdd_delref(d1);
      bdd_delref(nc1);

      /* Then look for the cubes that do not mention V. */
      t1 = bdd_addref(bdd_apply(f1_min, g1, bddop_diff));
      fs_min = bdd_addref(bdd_apply(f0_min, t1, bddop_or));
      bdd_delref(t1);
      gs = bdd_addref(isop_rec(ctx, fs_min, f0_max, pos, cube));
      bdd_delref(fs_min);

      /* The cover of the residual is (v & g1) | gs. */
      cov = bdd_addref(bdd_apply(v1, g1, bddop_and));
      res = bdd_apply(cov, gs, bddop_or);
      bdd_delref(cov);
      bdd_delref(gs);
      bdd_delref(g1);
      bdd_delref(v1);
      return res;
    }

  /* Cubes containing !v: they must belong to the part of F0 that is not
     covered by F1. */
  {
    BDD v0 = bdd_addref(bdd_nithvar(var));
    BDD d0 = bdd_addref(bdd_apply(f0_min, f1_max, bddop_diff));
    BDD nc0 = bdd_addref(bdd_apply(cube, v0, bddop_and));
    g0 = bdd_addref(isop_rec(ctx, d0, f0_max, pos, nc0));
    bdd_delref(d0);
    bdd_delref(nc0);
    bdd_delref(v0);
  }

  /* Cubes containing v: same, with F1 and F0 swapped. */
  {
    BDD v1 = bdd_addref(bdd_ithvar(var));
    BDD d1 = bdd_addref(bdd_apply(f1_min, f0_max, bddop_diff));
    BDD nc1 = bdd_addref(bdd_apply(cube, v1, bddop_and));
    g1 = bdd_addref(isop_rec(ctx, d1, f1_max, pos, nc1));
    bdd_delref(d1);
    bdd_delref(nc1);
    bdd_delref(v1);
  }

  /* Cubes that do not mention V: they must lie in the intersection of
     the two residuals, minus the parts that the cubes above already
     cover. */
  {
    BDD fs_max, fs_min, t0, t1;

    fs_max = bdd_addref(bdd_apply(f0_max, f1_max, bddop_and));
    t0 = bdd_addref(bdd_apply(f0_min, g0, bddop_diff));
    t1 = bdd_addref(bdd_apply(f1_min, g1, bddop_diff));
    fs_min = bdd_addref(bdd_apply(t0, t1, bddop_or));
    bdd_delref(t0);
    bdd_delref(t1);
    t0 = bdd_addref(bdd_apply(fs_max, fs_min, bddop_and));
    bdd_delref(fs_min);
    gs = bdd_addref(isop_rec(ctx, t0, fs_max, pos, cube));
    bdd_delref(t0);
    bdd_delref(fs_max);
  }

  /* The cover of the residual is ite(v, g1, g0) | gs. */
  {
    BDD v1 = bdd_addref(bdd_ithvar(var));
    BDD cov = bdd_addref(bdd_ite(v1, g1, g0));
    bdd_delref(v1);
    res = bdd_apply(cov, gs, bddop_or);
    bdd_delref(cov);
  }
  bdd_delref(gs);
  bdd_delref(g0);
  bdd_delref(g1);
  return res;
}


/* Enumerate the prime implicants of F.  POS is handled according to
   CTX->mode. */
static void isop_top(isop_context* ctx, BDD f, BDD pos)
{
  BDD rest, cube;

  if (f == BDDZERO)
    return;
  if (f == BDDONE)
    {
      /* The empty cube is the only prime implicant of true. */
      isop_emit(ctx, BDDONE);
      return;
    }

  /* If F has the form a&b&c&(other function), compute the ISOP of the
     other function only, and prepend a&b&c to every cube.  This is a
     common case in the applications, and it saves the descent through
     the prefix. */
  rest = f;
  cube = bdd_addref(bdd_satprefix(&rest));

  /* The recursion compares the levels it sees in its different frames
     (to know which variable to split on, and which one is already in
     CUBE), so it assumes that the variable order, and hence the level
     of every node, does not change.  Disabling reordering guarantees
     that, and also means that bdd_makenode() cannot longjmp out of the
     recursion, since no reorder is ever needed. */
  bdd_disable_reorder();
  isop_rec(ctx, rest, rest, pos, cube);
  bdd_enable_reorder();

  bdd_delref(cube);
}


static void isop_start(BDD r, BDD pos, positive_mode mode,
		       bddisophandler handler, void* data)
{
  isop_context ctx;

  CHECKn(r);

  ctx.handler = handler;
  ctx.data = data;
  ctx.mode = mode;

  /* The recursion may run the garbage collector, and expects its
     arguments to stay live: protect them even if the caller passed an
     unreferenced BDD (e.g. the result of bdd_apply()). */
  bdd_addref(r);
  bdd_addref(pos);
  isop_top(&ctx, r, pos);
  bdd_delref(pos);
  bdd_delref(r);
}


/*
NAME    {* bdd\_isop *}
SECTION {* operator *}
SHORT   {* enumerates the prime implicants of a BDD *}
PROTO   {* void bdd_isop(BDD r, bddisophandler handler, void *data) *}
DESCR   {* Computes an irredundant sum of products (ISOP) of {\tt r}
	   with the Minato-Morreale algorithm, and calls {\tt handler}
	   once for each cube of that sum, with {\tt data} as second
	   argument.  The cubes only mention variables of the support of
	   {\tt r} (there is no need to call {\tt bdd\_support} first),
	   and their disjunction is {\tt r}.  No cube can be removed from
	   the sum without changing the function, and none of them can be
	   weakened.

	   The cubes are given to the handler in depth-first order, and
	   are referenced for the duration of the call: a handler that
	   wants to keep a cube must call {\tt bdd\_addref} on it.

	   {\tt r} must be a plain BDD, not one containing terminals (see
	   {\tt bdd\_terminal}).  Reordering is suspended for the duration
	   of the call. *}
ALSO    {* bdd\_isop\_with\_positive\_vars, bdd\_isop\_all\_positive *}
*/
void bdd_isop(BDD r, bddisophandler handler, void* data)
{
  isop_start(r, BDDONE, NO_POSITIVE_VAR, handler, data);
}


/*
NAME    {* bdd\_isop\_with\_positive\_vars *}
SECTION {* operator *}
SHORT   {* enumerates the prime implicants of a positive-unate BDD *}
PROTO   {* void bdd_isop_with_positive_vars(BDD r, BDD positive_vars,
				   bddisophandler handler, void *data) *}
DESCR   {* Same as {\tt bdd\_isop}, but assumes that {\tt r} is
	   positive-unate in the variables of {\tt positive_vars}, i.e.,
	   that {\tt r|v=0} implies {\tt r|v=1} for each of them.  No
	   negative literal of these variables will be produced, and the
	   algorithm is faster.  {\tt positive_vars} must be a cube of
	   positive literals ({\tt bddtrue} for none, which is the same as
	   calling {\tt bdd\_isop}). *}
ALSO    {* bdd\_isop, bdd\_isop\_all\_positive *}
*/
void bdd_isop_with_positive_vars(BDD r, BDD positive_vars,
				 bddisophandler handler, void* data)
{
  CHECKn(positive_vars);
  assert(bdd_is_cube(positive_vars));
  isop_start(r, positive_vars, SOME_POSITIVE_VARS, handler, data);
}


/*
NAME    {* bdd\_isop\_all\_positive *}
SECTION {* operator *}
SHORT   {* enumerates the prime implicants of a monotone BDD *}
PROTO   {* void bdd_isop_all_positive(BDD r, bddisophandler handler,
				 void *data) *}
DESCR   {* Same as {\tt bdd\_isop}, but assumes that {\tt r} is
	   positive-unate in all its variables (i.e., that {\tt r} is
	   monotone).  It is cheaper than passing a {\tt
	   positive\_vars} cube to {\tt bdd\_isop\_with\_positive\_vars},
	   and much cheaper than enumerating the negative branches that
	   would turn out to be empty. *}
ALSO    {* bdd\_isop, bdd\_isop\_with\_positive\_vars *}
*/
void bdd_isop_all_positive(BDD r, bddisophandler handler, void* data)
{
  isop_start(r, BDDONE, ALL_POSITIVE_VARS, handler, data);
}

/* EOF */
