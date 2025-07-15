/*========================================================================
               Copyright (C) 1996-2002 by Jorn Lind-Nielsen
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

/*************************************************************************
  FILE:  cppext.cxx
  DESCR: C++ extension of BDD package
  AUTH:  Jorn Lind
  DATE:  (C) august 1997
*************************************************************************/
#include <string.h>
#include <stdlib.h>
#include <iomanip>
#include <new>
#include <cassert>
#include <deque>
#include <unordered_map>
#include "kernel.h"
#include "bvecx.h"

using namespace std;

   /* Formatting objects for iostreams */
#define IOFORMAT_SET    0
#define IOFORMAT_TABLE  1
#define IOFORMAT_DOT    2
#define IOFORMAT_ALL    3
#define IOFORMAT_FDDSET 4

int bdd_ioformat::curformat = IOFORMAT_SET;
bdd_ioformat bddset(IOFORMAT_SET);
bdd_ioformat bddtable(IOFORMAT_TABLE);
bdd_ioformat bdddot(IOFORMAT_DOT);
bdd_ioformat bddall(IOFORMAT_ALL);
bdd_ioformat fddset(IOFORMAT_FDDSET);

   /* Constant true and false extension */
const bddxtrue bddtruepp;
const bddxfalse bddfalsepp;

   /* Internal prototypes */
static void bdd_printset_rec(ostream&, int, int*);
static void bdd_printdot_rec(ostream&, int);
static void fdd_printset_rec(ostream &, int, int *);


static bddstrmhandler strmhandler_bdd;
static bddstrmhandler strmhandler_fdd;

   // Avoid calling C++ version of anodecount
#undef bdd_anodecount

/*************************************************************************
  Setup (and shutdown)
*************************************************************************/

#undef bdd_init

int bdd_cpp_init(int n, int c)
{
   int ok = bdd_init(n,c);

   strmhandler_bdd = NULL;
   strmhandler_fdd = NULL;

   return ok;
}


/*************************************************************************
  BDD C++ functions
*************************************************************************/

bdd bdd_buildcube(int val, int width, const bdd *variables)
{
   BDD *var = NEW(BDD,width);
   BDD res;
   int n;

      // No need for ref.cou. since variables[n] holds the reference
   for (n=0 ; n<width ; n++)
      var[n] = variables[n].root;

   res = bdd_buildcube(val, width, var);

   free(var);

   return res;
}


int bdd_setbddpairs(bddPair *pair, int *oldvar, const bdd *newvar, int size)
{
   if (pair == NULL)
      return 0;

   for (int n=0,e=0 ; n<size ; n++)
      if ((e=bdd_setbddpair(pair, oldvar[n], newvar[n].root)) < 0)
	 return e;

   return 0;
}


int bdd_anodecountpp(const bdd *r, int num)
{
   BDD *cpr = NEW(BDD,num);
   int cou;
   int n;

      // No need for ref.cou. since r[n] holds the reference
   for (n=0 ; n<num ; n++)
      cpr[n] = r[n].root;

   cou = bdd_anodecount(cpr,num);

   free(cpr);

   return cou;
}


/*************************************************************************
  C++ iostream operators
*************************************************************************/

/*
NAME    {* bdd\_strm\_hook *}
SECTION {* kernel *}
SHORT   {* Specifies a printing callback handler *}
PROTO   {* bddstrmhandler bdd_strm_hook(bddstrmhandler handler) *}
DESCR   {* A printing callback handler for use with BDDs is used to
           convert the BDD variable number into something readable by the
	   end user. Typically the handler will print a string name
	   instead of the number. A handler could look like this:
	   \begin{verbatim}
void printhandler(ostream &o, int var)
{
   extern char **names;
   o << names[var];
}
\end{verbatim}

           \noindent
           The handler can then be passed to BuDDy like this:
	   {\tt bdd\_strm\_hook(printhandler)}.

	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
RETURN  {* The old handler *}
ALSO    {* bdd\_printset, bdd\_file\_hook, fdd\_strm\_hook *}
*/
bddstrmhandler bdd_strm_hook(bddstrmhandler handler)
{
   bddstrmhandler old = strmhandler_bdd;
   strmhandler_bdd = handler;
   return old;
}


ostream &operator<<(ostream &o, const bdd &r)
{
   if (bdd_ioformat::curformat == IOFORMAT_SET)
   {
      if (r.root < 2)
      {
	 o << (r.root == 0 ? "F" : "T");
	 return o;
      }

      int *set = new (std::nothrow) int[bddvarnum];
      if (set == NULL)
      {
	 bdd_error(BDD_MEMORY);
	 return o;
      }

      memset(set, 0, sizeof(int) * bddvarnum);
      bdd_printset_rec(o, r.root, set);
      delete[] set;
   }
   else
   if (bdd_ioformat::curformat == IOFORMAT_TABLE)
   {
      o << "ROOT: " << r.root << "\n";
      if (r.root < 2)
	 return o;

      bdd_mark(r.root);

      for (int n=0 ; n<bddnodesize ; n++)
      {
	 if (LEVEL(n) & MARKON)
	 {
	    BddNode *node = &bddnodes[n];

	    LEVELp(node) &= MARKOFF;

	    o << "[" << setw(5) << n << "] ";
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[LEVELp(node)]);
	    else
	       o << setw(3) << bddlevel2var[LEVELp(node)];
	    o << " :";
	    o << " " << setw(3) << LOWp(node);
	    o << " " << setw(3) << HIGHp(node);
	    o << "\n";
	 }
      }
   }
   else
   if (bdd_ioformat::curformat == IOFORMAT_DOT)
   {
      o << "digraph G {\n";
      bdd_printdot_rec(o, r.root);
      o << "}\n";

      bdd_unmark(r.root);
      UNMARK(0);                   /* those aren't covered by bdd_unmark */
      UNMARK(1);
   }
   else
   if (bdd_ioformat::curformat == IOFORMAT_FDDSET)
   {
      if (ISCONST(r.root))
      {
	 o << (r == 0 ? "F" : "T");
	 return o;
      }

      int *set = new (std::nothrow) int[bddvarnum];
      if (set == NULL)
      {
	 bdd_error(BDD_MEMORY);
	 return o;
      }

      memset(set, 0, sizeof(int) * bddvarnum);
      fdd_printset_rec(o, r.root, set);
      delete[] set;
   }

   return o;
}


/*
NAME    {* operator{\tt<<} *}
SECTION {* fileio *}
SHORT   {* C++ output operator for BDDs *}
PROTO   {* ostream &operator<<(ostream &o, const bdd_ioformat &f)
ostream &operator<<(ostream &o, const bdd &r) *}
DESCR   {* BDDs can be printed in various formats using the C++ iostreams
           library. The formats are the those used in {\tt bdd\_printset},
	   {\tt bdd\_printtable}, {\tt fdd\_printset} and {\tt bdd\_printdot}.
	   The format can be specified with the following format objects:
	   \begin{tabular}{ll}\\
	     {\tt bddset } & BDD level set format \\
	     {\tt bddtable } & BDD level table format \\
	     {\tt bdddot }   & Output for use with Dot \\
	     {\tt bddall }   & The whole node table \\
	     {\tt fddset }   & FDD level set format \\
	   \end{tabular}\\

	   \noindent
	   So a BDD {\tt x} can for example be printed as a table with the
	   command\\

	   \indent {\tt cout << bddtable << x << endl}.
	   *}
RETURN  {* The specified output stream *}
ALSO    {* bdd\_strm\_hook, fdd\_strm\_hook *}
*/
ostream &operator<<(ostream &o, const bdd_ioformat &f)
{
   if (f.format == IOFORMAT_SET  ||  f.format == IOFORMAT_TABLE  ||
       f.format == IOFORMAT_DOT  ||  f.format == IOFORMAT_FDDSET)
      bdd_ioformat::curformat = f.format;
   else
   if (f.format == IOFORMAT_ALL)
   {
      for (int n=0 ; n<bddnodesize ; n++)
      {
	 const BddNode *node = &bddnodes[n];

	 if (LOWp(node) != -1)
	 {
	    o << "[" << setw(5) << n << "] ";
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[LEVELp(node)]);
	    else
	       o << setw(3) << bddlevel2var[LEVELp(node)] << " :";
	    o << " " << setw(3) << LOWp(node);
	    o << " " << setw(3) << HIGHp(node);
	    o << "\n";
	 }
      }
   }

   return o;
}


static void bdd_printset_rec(ostream& o, int r, int* set)
{
   int n;
   int first;

   if (r == 0)
      return;
   else
   if (r == 1 || ISTERM(r))
   {
      o << "<";
      first = 1;

      for (n=0 ; n<bddvarnum ; n++)
      {
	 if (set[n] > 0)
	 {
	    if (!first)
	       o << ", ";
	    first = 0;
	    if (strmhandler_bdd)
	       strmhandler_bdd(o,bddlevel2var[n]);
	    else
	       o << bddlevel2var[n];
	    o << ":" << (set[n]==2 ? 1 : 0);
	 }
      }
      if (ISTERM(r))
        {
          if (!first)
            o << ", ";
          o << "Terminal(" << TERM(r) << ')';
        }
      o << ">";
   }
   else
   {
      set[LEVEL(r)] = 1;
      bdd_printset_rec(o, LOW(r), set);

      set[LEVEL(r)] = 2;
      bdd_printset_rec(o, HIGH(r), set);

      set[LEVEL(r)] = 0;
   }
}


static void bdd_printdot_rec(ostream& o, int r)
{
   if (MARKED(r))
      return;

   if (ISCONST(r))
     {
       SETMARK(r);
       o << r << "[shape=box, label=\""
         << r << "\", style=filled, height=0.3, width=0.3];\n";
       return;
     }
   if (ISTERM(r))
     {
       SETMARK(r);
       o << r << "[shape=pentagon, label=\""
         << TERM(r) << " (\\N)\", style=filled, height=0.3, width=0.3];\n";
       return;
     }

   o << r << "[label=\"";
   if (strmhandler_bdd)
      strmhandler_bdd(o,bddlevel2var[LEVEL(r)]);
   else
      o << bddlevel2var[LEVEL(r)];
   o << "\"];\n";
   o << r << " -> " << LOW(r) << "[style=dotted];\n";
   o << r << " -> " << HIGH(r) << "[style=filled];\n";

   SETMARK(r);

   bdd_printdot_rec(o, LOW(r));
   bdd_printdot_rec(o, HIGH(r));
}


static void fdd_printset_rec(ostream &o, int r, int *set)
{
   int n,m,i;
   int used = 0;
   int *binval;
   int ok, first;

   if (r == 0)
      return;
   else
   if (r == 1)
   {
      o << "<";
      first=1;
      int fdvarnum = fdd_domainnum();

      for (n=0 ; n<fdvarnum ; n++)
      {
	 int firstval=1;
	 used = 0;
	 int binsize = fdd_varnum(n);
	 int *vars = fdd_vars(n);

	 for (m=0 ; m<binsize ; m++)
	    if (set[vars[m]] != 0)
	       used = 1;

	 if (used)
	 {
	    if (!first)
	       o << ", ";
	    first = 0;
	    if (strmhandler_fdd)
	       strmhandler_fdd(o, n);
	    else
	       o << n;
	    o << ":";

	    for (m=0 ; m<(1<<binsize) ; m++)
	    {
	       binval = fdddec2bin(n, m);
	       ok=1;

	       for (i=0 ; i<binsize && ok ; i++)
		  if (set[vars[i]] == 1  &&  binval[i] != 0)
		     ok = 0;
		  else
		  if (set[vars[i]] == 2  &&  binval[i] != 1)
		     ok = 0;

	       if (ok)
	       {
		  if (firstval)
		     o << m;
		  else
		     o << "/" << m;
		  firstval = 0;
	       }

	       free(binval);
	    }
	 }
      }

      o << ">";
   }
   else
   {
      set[bddlevel2var[LEVEL(r)]] = 1;
      fdd_printset_rec(o, LOW(r), set);

      set[bddlevel2var[LEVEL(r)]] = 2;
      fdd_printset_rec(o, HIGH(r), set);

      set[bddlevel2var[LEVEL(r)]] = 0;
   }
}


/*=[ FDD I/O functions ]================================================*/

/*
NAME    {* fdd\_strm\_hook *}
SECTION {* fdd *}
SHORT   {* Specifies a printing callback handler *}
PROTO   {* bddstrmhandler fdd_strm_hook(bddstrmhandler handler) *}
DESCR   {* A printing callback handler for use with FDDs is used to
           convert the FDD integer identifier into something readable by the
	   end user. Typically the handler will print a string name
	   instead of the identifier. A handler could look like this:
	   \begin{verbatim}
void printhandler(ostream &o, int var)
{
   extern char **names;
   o << names[var];
}
\end{verbatim}

           \noindent
           The handler can then be passed to BuDDy like this:
	   {\tt fdd\_strm\_hook(printhandler)}.

	   No default handler is supplied. The argument {\tt handler} may be
	   NULL if no handler is needed. *}
RETURN  {* The old handler *}
ALSO    {* fdd\_printset, bdd\_file\_hook *}
*/
bddstrmhandler fdd_strm_hook(bddstrmhandler handler)
{
   bddstrmhandler old = strmhandler_fdd;
   strmhandler_fdd = handler;
   return old;
}


/*************************************************************************
   bvec functions
*************************************************************************/

bvec bvec::operator=(const bvec &src)
{
   if (&src != this)
   {
      bvec_free(roots);
      roots = bvec_copy(src.roots);
   }
   return *this;
}


void bvec::set(int bitnum, const bdd &b)
{
   bdd_delref(roots.bitvec[bitnum]);
   roots.bitvec[bitnum] = b.root;
   bdd_addref(roots.bitvec[bitnum]);
}


/*======================================================================*/

bvec bvec_map1(const bvec &a,
	       bdd (*fun)(const bdd &))
{
   bvec res;
   int n;

   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n]));

   return res;
}


bvec bvec_map2(const bvec &a, const bvec &b,
	       bdd (*fun)(const bdd &, const bdd &))
{
   bvec res;
   int n;

   if (a.bitnum() != b.bitnum())
   {
      bdd_error(BVEC_SIZE);
      return res;
   }

   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n], b[n]));

   return res;
}


bvec bvec_map3(const bvec &a, const bvec &b, const bvec &c,
	       bdd (*fun)(const bdd &, const bdd &, const bdd &))
{
   bvec res;
   int n;

   if (a.bitnum() != b.bitnum()  ||  b.bitnum() != c.bitnum())
   {
      bdd_error(BVEC_SIZE);
      return res;
   }

   res = bvec_false(a.bitnum());
   for (n=0 ; n < a.bitnum() ; n++)
      res.set(n, fun(a[n], b[n], c[n]) );

   return res;
}


ostream &operator<<(ostream &o, const bvec &v)
{
  for (int i=0 ; i<v.bitnum() ; ++i)
  {
    o << "B" << i << ":\n"
      << v[i] << "\n";
  }

  return o;
}

static bool has_true_rec(int r)
{
  if (MARKED(r))
    return false;

  if (ISCONST(r) || ISTERM(r))
    {
      SETMARK(r);               // cannot be done before ISTERM
      return r == 1;
    }
  SETMARK(r);
  return has_true_rec(LOW(r)) || has_true_rec(HIGH(r));
}

bool bdd_has_true(const std::vector<bdd>& res)
{
  bool has_true = false;
  for (const bdd& x : res)
    {
      has_true = has_true_rec(x.root);
      if (has_true)
        break;
    }
  for (const bdd& x : res)
    bdd_unmark(x.root);
  UNMARK(0);                   /* those aren't covered by bdd_unmark */
  UNMARK(1);
  return has_true;
}



static void leaves_of_rec(int r, std::vector<bdd>& res)
{
  if (MARKED(r))
    return;

  if (ISCONST(r) || ISTERM(r))
    {
      SETMARK(r);               // cannot be done before ISTERM
      res.push_back(bdd_from_int(r));
      return;
    }
  SETMARK(r);
  leaves_of_rec(LOW(r), res);
  leaves_of_rec(HIGH(r), res);
}



std::vector<bdd> leaves_of(const bdd& b)
{
  std::vector<bdd> res;
  leaves_of_rec(b.root, res);
  bdd_unmark(b.root);
  UNMARK(0);                   /* those aren't covered by bdd_unmark */
  UNMARK(1);
  return res;
}

std::vector<bdd> leaves_of(const std::vector<bdd>& b)
{
  std::vector<bdd> res;
  for (const bdd& x : b)
    leaves_of_rec(x.root, res);
  for (const bdd& x : b)
    bdd_unmark(x.root);
  UNMARK(0);                   /* those aren't covered by bdd_unmark */
  UNMARK(1);
  return res;
}

static bool find_leaf_rec(int b, bool (*pred)(int))
{
  if (MARKED(b))
    return false;

  if (ISCONST(b) || ISTERM(b))
    {
      bool res = pred(b);
      SETMARK(b);               // cannot be done before ISTERM
      return res;
    }
  SETMARK(b);
  return find_leaf_rec(LOW(b), pred) || find_leaf_rec(HIGH(b), pred);
}

bool bdd_find_leaf(const std::vector<bdd>& b, bool (*pred)(int))
{
  bool res = false;
  for (const bdd& x : b)
    {
      res = find_leaf_rec(x.root, pred);
      if (res)
        break;
    }
  for (const bdd& x : b)
    bdd_unmark(x.root);
  UNMARK(0);                   /* those aren't covered by bdd_unmark */
  UNMARK(1);
  return res;

}

void bdd_markcount_extra(int i, int *cou,  int* terms, int* consts)
{
   BddNode *node;
   if (__unlikely(i < 2))
     {
       if (i == 0)
         *consts |= 1;
       if (i == 1)
         *consts |= 2;
       return;
     }

   node = &bddnodes[i];
   if (MARKEDp(node)  ||  LOWp(node) == -1)
      return;

   if (__unlikely(ISTERMp(node)))
     {
       ++*terms;
       SETMARKp(node);
       return;
     }
   *cou += 1;
   SETMARKp(node);

   bdd_markcount_extra(LOWp(node), cou, terms, consts);
   bdd_markcount_extra(HIGHp(node), cou, terms, consts);
}


int bdd_anodecountpp(const std::vector<bdd>& b,
                     int& terms, bool& has_true, bool& has_false)
{
  int count = 0;
  int consts = 0;
  terms = 0;
  for (const bdd& x: b)
    bdd_markcount_extra(x.root, &count, &terms, &consts);
  for (const bdd& x: b)
    bdd_unmark(x.root);
  has_false = consts & 1;
  has_true = consts & 2;
  return count;
}


int bdd_anodecountpp(const std::vector<bdd>& b)
{
  int count = 0;
  for (const bdd& x: b)
    bdd_markcount(x.root, &count);
  for (const bdd& x: b)
    bdd_unmark(x.root);
  return count;
}

extern int *quantvarset;

std::tuple<bool, int, int> bdd_mt_quantified_low_high(int r)
{
  bool is_quant = quantvarset[LEVEL(r)];
  return make_tuple(is_quant, LOW(r), HIGH(r));
}

// This interprets the MTBDD of states as a graph in which
// a terminal labeled by X has term_succ(X) as successor.
//
// The function compute the maximal strongly connected components of
// that graph.  If there a N such SCCs, this returns a vector of the
// same size as STATES, indicating the SCC number (between 0 and N-1)
// of each states.  SCCs are topologically ordered, with state 0
// belonging to the largest SCC; an SCC can only reach SCCs with
// smaller indices.
std::vector<int> bdd_mt_sccs(const std::vector<bdd>& states,
                             int (*term_succ)(int),
                             std::unordered_map<int, int>* seen_res)
{
  unsigned ns = states.size();
  std::vector<int> res(ns, INT_MIN);
  // This uses Dijkstra's algorithm for enumerating SCC, combined
  // with a live stack.
  // - A DFS is used to discover new states.
  // - Each newly discovered state is added to a LIVE stack and assigned a
  //   unique increasing index
  // - A stack of SCC potential roots hold such indices, with the convention
  //   that if is stack contains [..., i, j, ...], then all live states
  //   whose indices are between i (included) and j (excluded) belong to
  //   the same SCC
  // - When the DFS discovers a cycle, i.e., a live state with index
  //   X, then all SCC roots larger than X are popped from the ROOTS
  //   stack, but the LIVE stack is untouched.
  // - When the DFS backtracks from a state that is the top of ROOTS, we
  //   use the LIVE stack to enumerate all states of that SCC and
  //   assign them a their SCC number.
  //
  // Additionally, the algorithm is slightly adapted to the BDD structure:
  // internal nodes have at most two successors, and terminal nodes have
  // exactly one successor.
  std::deque<int> roots;               // indices of SCC roots
  std::deque<int> live;                // bdd.id that have been
                                       // discovered but not assigned
                                       // to any SCC yet.
  std::unordered_map<int, int> seen;   // index of each live state; or
                                       // <0 if part of some SCC
                                       // already.
  unsigned state_index = 0;            // number to give to newly
                                       // discovered states.
  unsigned scc_index = 0;              // number to give to newly
                                       // found maximal SCCs.
  // The following DFS stack stores pairs (x, count) where
  //  count == 3  if x is value of a terminal to process
  //  count == 2  if x is an inner node for which no children has been
  //              visited (we should start with low)
  //  count == 1  if x is an inner node for which the low child has been
  //              visited (continue with high)
  //  count == 0  if all successors have been visited (backtrack now)
  std::deque<std::pair<int, int>> dfs_stack;

  for (unsigned i = 0; i < ns; ++i)
    {
      if (res[i] != INT_MIN) // already assigned to an SCC
        continue;
      int r = states[i].id();
      if (!seen.emplace(r, state_index).second)
        {
          // this is a trivial SCC, or we would have assigned i to
          // some SCC already.
          res[i] = scc_index++;
          continue;
        }
      live.push_back(r);
      roots.push_back(state_index);
      dfs_stack.emplace_back(r, ISTERM(r) ? 3 : 2);
      ++state_index;

      while (!dfs_stack.empty())
        {
          auto& [r, cnt] = dfs_stack.back();
          if (cnt == 0)         // we should backtrack
            {
              int rootidx = roots.back();
              if (rootidx == seen[r]) // r is an SCC root
                {
                  rootidx = ~rootidx;
                  roots.pop_back();
                  bool scc_index_assigned = false;
                  while (!live.empty())
                    {
                      int t = live.back();
                      live.pop_back();
                      auto it = seen.find(t);
                      int tindex = it->second;
                      it->second = rootidx;
                      if (ISTERM(t))
                        {
                          res[term_succ(TERM(t))] = scc_index;
                          scc_index_assigned = true;
                        }
                      if (t == r)
                        break;
                    }
                  if (scc_index_assigned)
                    ++scc_index;
                }
              dfs_stack.pop_back();
              continue;
            }
          int child;
          if (cnt == 3)         // looking at a terminal
            {
              int v = term_succ(TERM(r));
              assert(v < ns);
              child = states[v].id();
              cnt = 0;
            }
          else if (cnt == 2)
            {
              child = LOW(r);
              cnt = 1;
            }
          else
            {
              assert(cnt == 1);
              child = HIGH(r);
              cnt = 0;
            }
          if (ISCONST(child))   // ignore constant nodes
            continue;

          auto [it, ins] = seen.emplace(child, state_index);
          if (ins) // new state
            {
              // If r is pointing to a transient state, it is
              // possible that we have previously assigned an SCC
              // to it without ever encountering the corresponding
              // terminal.
              if (ISTERM(child) && res[term_succ(TERM(child))] != INT_MIN)
                continue;
              live.push_back(child);
              roots.push_back(state_index);
              ++state_index;
              dfs_stack.emplace_back(child, ISTERM(child) ? 3 : 2);
              continue;
            }

          int dstidx = it->second;;
          if (dstidx < 0) // goes to another SCC
            continue;
          // Closes a cycle: pop relevant SCC roots.
          while (roots.back() > dstidx)
            roots.pop_back();
        } // DFS
      if (res[i] == INT_MIN) // not assigned yet because trivial
        res[i] = scc_index++;
    }     // loop over all states
  if (seen_res)
    std::swap(seen, *seen_res);
  return res;
}
