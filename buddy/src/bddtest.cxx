/*========================================================================
               Copyright (C) 1996-2002, 2008 by Jorn Lind-Nielsen
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

#include <string>
#include <cstdlib>
#include <algorithm>
#include <vector>
#include "bddx.h"
#include "bvecx.h"

using namespace std;


#define ERROR(msg) fail(msg, __FILE__, __LINE__)

static void fail(const string msg, const char* file, int lineNum)
{
  cout << "Error in " << file << "(" << lineNum << "): " << msg << endl;
  exit(1);
}


static void testSupport(void)
{
  bdd even = bdd_ithvar(0) | bdd_ithvar(2) | bdd_ithvar(4);
  bdd odd  = bdd_ithvar(1) | bdd_ithvar(3) | bdd_ithvar(5);

  cout << "Testing support\n";

  bdd s1 = bdd_support(even);
  bdd s2 = bdd_support(odd);

  if (s1 != (bdd_ithvar(0) & bdd_ithvar(2) & bdd_ithvar(4)))
    ERROR("Support of 'even' failed\n");
  if (s2 != (bdd_ithvar(1) & bdd_ithvar(3) & bdd_ithvar(5)))
    ERROR("Support of 'odd' failed\n");

  /* Try many time in order check that the internal support ID
   * is set correctly */
  for (int n=0 ; n<500 ; ++n)
  {
    s1 = bdd_support(even);
    s2 = bdd_support(odd);

    if (s1 != (bdd_ithvar(0) & bdd_ithvar(2) & bdd_ithvar(4)))
      ERROR("Support of 'even' failed");
    if (s2 != (bdd_ithvar(1) & bdd_ithvar(3) & bdd_ithvar(5)))
      ERROR("Support of 'odd' failed");
  }
}


void testBvecIte()
{
  cout << "Testing ITE for vector\n";

  bdd  a = bdd_ithvar(0);
  bvec b = bvec_var(3, 1, 2);
  bvec c = bvec_var(3, 2, 2);

  bvec res = bvec_ite(a,b,c);

  bdd r0 = bdd_ite( bdd_ithvar(0), bdd_ithvar(1), bdd_ithvar(2) );
  bdd r1 = bdd_ite( bdd_ithvar(0), bdd_ithvar(3), bdd_ithvar(4) );
  bdd r2 = bdd_ite( bdd_ithvar(0), bdd_ithvar(5), bdd_ithvar(6) );

  if (res[0] != r0)
    ERROR("Bit 0 failed.");
  if (res[1] != r1)
    ERROR("Bit 1 failed.");
  if (res[2] != r2)
    ERROR("Bit 2 failed.");
}

void testShortest()
{
  cout << "Testing bdd_satoneshortest()\n";

  bdd a = bdd_ithvar(0);
  bdd b = bdd_ithvar(1);
  bdd c = bdd_ithvar(2);
  bdd d = bdd_ithvar(3);

  bdd cube1 = a&c&!d;
  bdd cube2 = a&!c&d;
  bdd cube3 = !a&b&c&!d;
  bdd cube4 = !a&!b&d;

  bdd f =  cube1 | cube2 | cube3 | cube4 ;

  // avoid don't care at all cost, prefer negative
  bdd res = bdd_satoneshortest(f, 0, 1, 4);
  if (res != cube3)
    ERROR("shortest 0 1 4 failed");

  // avoid don't care at all cost, prefer positive
  res = bdd_satoneshortest(f, 1, 0, 4);
  if (res != cube3)
    ERROR("shortest 1 0 4 failed");

  // avoid negative at all cost, prefer positive
  res = bdd_satoneshortest(f, 4, 0, 1);
  if (res != cube2)
    ERROR("shortest 4 0 1 failed");

  // avoid negative at all cost, prefer don't care
  res = bdd_satoneshortest(f, 4, 1, 0);
  if (res != cube2)
    ERROR("shortest 4 1 0 failed");

  // avoid positive at all cost, prefer don't care
  res = bdd_satoneshortest(f, 1, 4, 0);
  if (res != cube4)
    ERROR("shortest 1 4 0 failed");

  // avoid positive at all cost, prefer negative
  res = bdd_satoneshortest(f, 0, 4, 1);
  if (res != cube4)
    ERROR("shortest 0 4 1 failed");

  res = bdd_satoneshortest(bddfalse, 1, 2, 3);
  if (res != bddfalse)
    ERROR("shortest bddfalse failed");

  res = bdd_satoneshortest(bddtrue, 1, 2, 3);
  if (res != bddtrue)
    ERROR("shortest bddtrue failed");
}

void testIsCube(){
  cout << "Testing is_cube()\n";

  if (bdd_is_cube(bddfalse) != 0)
    ERROR("is_cube failed on false");
  if (bdd_is_cube(bddtrue) != 1)
    ERROR("is_cube failed on true");

  // Some cubes
  bdd a = bdd_ithvar(0);
  bdd b = bdd_ithvar(1);
  bdd c = bdd_ithvar(2);
  bdd d = bdd_ithvar(3);

  bdd cube1 = a&!c&d;
  bdd cube2 = a&c&!d;
  bdd cube3 = a&b&c&d;
  bdd cube4 = a&!b&!c&d;

  if (bdd_is_cube(cube1) != 1)
    ERROR("is_cube failed on cube1");
  if (bdd_is_cube(cube2) != 1)
    ERROR("is_cube failed on cube2");
  if (bdd_is_cube(cube3) != 1)
    ERROR("is_cube failed on cube3");
  if (bdd_is_cube(cube4) != 1)
    ERROR("is_cube failed on cube4");

  // Some non-cubes
  bdd b1 = cube1 | cube2;
  bdd b2 = cube3 | cube4;

  if (bdd_is_cube(b1) != 0)
    ERROR("is_cube failed on b1");
  if (bdd_is_cube(b2) != 0)
    ERROR("is_cube failed on b2");
}

void testMtSccs()
{
  cout << "Testing bdd_mt_sccs()\n";

  auto identity = [] (int x) { return x; };

  bdd a = bdd_ithvar(0);
  bdd b = bdd_ithvar(1);

  struct case_t
  {
    const char* name;
    std::vector<bdd> states;
    std::vector<int> scc;       // expected SCC number of each state
    std::vector<int> transient; // expected transient flag of each SCC
    // Expected successors of each SCC: SCC numbers, except -1 and -2
    // which stand for the implicit bddfalse and bddtrue sinks
    // (~bddfalse.id() and ~bddtrue.id()).
    std::vector<std::vector<int>> succs;
  };

  const case_t cases[] =
    {
      // Simple chains and cycles, with various acceptances.
      {"T1", {bdd_ite(a, bdd_terminal(2), bdd_terminal(1)),
              bdd_terminal(2), bdd_terminal(3), bdd_terminal(3)},
       {3, 2, 1, 0}, {0, 1, 1, 1}, {{}, {0}, {1}, {1, 2}}},
      {"T2", {bdd_terminal(1), bdd_terminal(2),
              bdd_ite(a, bdd_terminal(0), bdd_terminal(3)),
              bdd_terminal(2)},
       {0, 0, 0, 0}, {0}, {{}}},
      {"T3", {bdd_terminal(1), bdd_terminal(2), bdd_terminal(2)},
       {2, 1, 0}, {0, 1, 1}, {{}, {0}, {1}}},
      {"T4", {bdd_ite(a, bdd_terminal(0), bdd_terminal(1)),
              bdd_terminal(2), bdd_terminal(2)},
       {2, 1, 0}, {0, 1, 0}, {{}, {0}, {1}}},
      {"T5", {bdd_terminal(1), bdd_terminal(2), bdd_terminal(2),
              bdd_terminal(2)},
       {2, 1, 0, 3}, {0, 1, 1, 1}, {{}, {0}, {1}, {0}}},
      {"T6", {bdd_ite(a, bdd_terminal(1), bdd_terminal(2)),
              bdd_terminal(3), bdd_terminal(3), bdd_terminal(3)},
       {3, 2, 1, 0}, {0, 1, 1, 1}, {{}, {0}, {0}, {1, 2}}},
      {"T7", {bdd_ite(a, bdd_terminal(0), bdd_terminal(0)),
              bdd_terminal(1), bdd_terminal(2), bdd_terminal(3)},
       {0, 1, 2, 3}, {0, 0, 0, 0}, {{}, {}, {}, {}}},
      // Two states sharing the same BDD root.
      {"T8", {bdd_terminal(1), bdd_terminal(0), bdd_terminal(0)},
       {0, 0, 1}, {0, 1}, {{}, {0}}},
      // Mutual cycle between two states.
      {"T9", {bdd_terminal(1), bdd_terminal(0)},
       {0, 0}, {0}, {{}}},
      // A terminal pointing to an already-assigned state (this used
      // to leave a stale entry in the SEEN map that could be mistaken
      // for a cycle closure, corrupting the SCC partition).
      {"G38", {bdd_terminal(2),
               bdd_ite(b, bdd_terminal(0), bdd_terminal(4)),
               bdd_terminal(2),
               bdd_ite(a, bdd_ite(b, bdd_terminal(3), bdd_terminal(5)),
                       bdd_terminal(3)),
               bdd_ite(a, bdd_ite(b, bdd_terminal(3), bdd_terminal(0)),
                       bdd_terminal(3)),
               bdd_terminal(3)},
       {1, 4, 0, 2, 3, 2}, {0, 1, 0, 1, 1},
       {{}, {0}, {}, {1, 2}, {1, 3}}},
      // Constant state roots (these used to crash bdd_mt_sccs).
      // States 1 and 2 have the same root, a terminal pointing to
      // state 0, which is already assigned to an SCC (bddfalse) when
      // they are processed: those terminals are ghost entries, and
      // each state ends up in its own trivial SCC pointing to SCC 0.
      {"C1", {bddfalse, bdd_terminal(0), bdd_terminal(0), bddtrue},
       {0, 1, 2, 3}, {1, 1, 1, 1}, {{-1}, {0}, {0}, {-2}}},
      {"C2", {bddtrue, bdd_terminal(1), bdd_terminal(2), bddfalse},
       {0, 1, 2, 3}, {1, 0, 0, 1}, {{-2}, {}, {}, {-1}}},
      {"C3", {bdd_ite(a, bddfalse, bdd_terminal(1)),
              bdd_terminal(0), bddtrue},
       {0, 0, 1}, {0, 1}, {{-1}, {-2}}},
    };

  for (const case_t& c : cases)
    {
      std::vector<bool> transient;
      std::vector<std::vector<int>> succs;
      std::vector<int> scc = bdd_mt_sccs(c.states, identity, nullptr,
                                         &transient, &succs);
      if (scc != c.scc)
        ERROR(string(c.name) + ": unexpected SCC vector");
      if (transient.size() != c.transient.size())
        ERROR(string(c.name) + ": unexpected transient size");
      for (unsigned i = 0; i < transient.size(); ++i)
        if (transient[i] != (c.transient[i] != 0))
          ERROR(string(c.name) + ": unexpected transient flag");
      if (succs.size() != c.succs.size())
        ERROR(string(c.name) + ": unexpected succs size");
      for (unsigned i = 0; i < succs.size(); ++i)
        if (succs[i] != c.succs[i])
          ERROR(string(c.name) + ": unexpected succs list");
    }
}


void testHaveCommon()
{
  cout << "Testing have_common_assignment()\n";

  if (bdd_have_common_assignment(bddtrue, bddtrue) != 1)
    ERROR(" have_common_assignment on true, true");
  if (bdd_have_common_assignment(bddfalse, bddtrue) != 0)
    ERROR(" have_common_assignment on false, true");
  if (bdd_have_common_assignment(bddtrue, bddfalse) != 0)
    ERROR(" have_common_assignment on true, false");
  if (bdd_have_common_assignment(bddfalse, bddfalse) != 0)
    ERROR(" have_common_assignment on false, false");


  // Some cubes
  bdd a = bdd_ithvar(0);
  bdd b = bdd_ithvar(1);
  bdd c = bdd_ithvar(2);
  bdd d = bdd_ithvar(3);

  bdd ca[5];
  ca[0] = a&c;
  ca[1] = a&!c;
  ca[2] = c&d;
  ca[3] = a&b&c&!d;
  ca[4] = !a&!d;

  // Some tests
  for (unsigned i1 = 0; i1 < 5; i1++)
    {
      for (unsigned j1 = i1; j1 < 5; j1++)
        {
          if (bdd_have_common_assignment(ca[i1], ca[j1])
              != ((ca[i1] & ca[j1]) != bddfalse))
            ERROR("bdd_have_common_assignment(): failed on cube");
          for (unsigned i2 = 0; i2 < 5; i2++)
            {
              for (unsigned j2 = i2; j2 < 5; j2++)
                {
                  bdd b1 = ca[i1]|ca[j1];
                  bdd b2 = ca[i2]|ca[j2];
                  if (bdd_have_common_assignment(b1, b2)
                      != ((b1 & b2) != bddfalse))
                    ERROR("bdd_have_common_assignment(): failed on "
                          "disjunction of cubes");
                }
            }
        }
    }
}

void testRestrict()
{
  cout << "Testing bdd_restrict()\n";

  bdd vars[6];
  for (int v = 0; v < 6; ++v)
    vars[v] = bdd_ithvar(v);

  const bdd fs[] = {
    bddtrue,
    bddfalse,
    vars[0],
    vars[5],
    (vars[0] & vars[1]) | (vars[2] & !vars[3]) | vars[4],
    bdd_ite(vars[0], vars[4] & vars[5], !vars[1] & vars[2])
  };

  // Cubes over variables 0..3, represented by positive and negative
  // masks.
  struct cube_t
  {
    unsigned pos;
    unsigned neg;
  };

  const cube_t cubes[] = {
    {0, 0},               // empty cube
    {1, 0},               // v0
    {0, 1},               // !v0
    {1 | 4, 0},           // v0 & v2
    {0, 2 | 4},           // !v1 & !v2
    {8, 0},               // v3
    {1 | 2 | 4 | 8, 0},   // v0 & v1 & v2 & v3
    {0, 1 | 2 | 4 | 8}    // !v0 & !v1 & !v2 & !v3
  };

  for (const bdd& f : fs)
    for (const cube_t& c : cubes)
      {
        bdd var = bddtrue;
        bdd expected = f;
        for (int v = 0; v < 4; ++v)
          {
            if (c.pos & (1U << v))
              {
                var &= vars[v];
                expected = bdd_compose(expected, bddtrue, v);
              }
            else if (c.neg & (1U << v))
              {
                var &= !vars[v];
                expected = bdd_compose(expected, bddfalse, v);
              }
          }
        if (bdd_restrict(f, var) != expected)
          ERROR("bdd_restrict() failed on a cube");
      }
}



void testQuant()
{
  cout << "Testing quantification with uniform suffix optimization\n";


  bdd vars[4];
  for (int v = 0; v < 4; ++v) vars[v] = bdd_ithvar(v);

  // Test exist quantification: x over {x} should be true
  int varset1[] = {0};
  bdd f1 = bdd_exist(vars[0], bdd_makeset(varset1, 1));
  if (f1 != bddtrue) ERROR("bdd_exist over {x} failed");

  // Test forall quantification: x over {x} should be false
  bdd f2 = bdd_forall(vars[0], bdd_makeset(varset1, 1));
  if (f2 != bddfalse) ERROR("bdd_forall over {x} failed");

  // Test unique quantification: x over {x} should be true (1 path)
  bdd f3 = bdd_unique(vars[0], bdd_makeset(varset1, 1));
  if (f3 != bddtrue) ERROR("bdd_unique over {x} failed");

  // Test with 2 variables: exist over {x,y} should be true
  int varset2[] = {0, 1};
  bdd f4 = bdd_exist(vars[0] | vars[1], bdd_makeset(varset2, 2));
  if (f4 != bddtrue) ERROR("bdd_exist over {x,y} failed");

  // Test forall over {x,y} should be false
  bdd f5 = bdd_forall(vars[0] | vars[1], bdd_makeset(varset2, 2));
  if (f5 != bddfalse) ERROR("bdd_forall over {x,y} failed");

  // Test unique over {x,y} with x|y should be false (2 paths)
  bdd f6 = bdd_unique(vars[0] | vars[1], bdd_makeset(varset2, 2));
  if (f6 != bddfalse) ERROR("bdd_unique over {x|y}, {x,y} failed");

  // Test with 3 variables: majority (x&y)|(x&z)|(y&z) over {x,y,z}
  int varset3[] = {0, 1, 2};
  bdd z = bdd_ithvar(2);
  bdd maj = (vars[0] & vars[1]) | (vars[0] & z) | (vars[1] & z);
  bdd f7 = bdd_unique(maj, bdd_makeset(varset3, 3));
  // majority has 3 paths (odd), so unique should be true
  if (f7 != bddtrue) ERROR("bdd_unique over majority, {x,y,z} failed");
}

/* Return the literals of a cube as a vector of signed variable
   numbers (v for x, ~v for !x), in increasing level order. */
static std::vector<int> isop_literals(const bdd& c)
{
  std::vector<int> res;
  bdd l = c;
  while (l != bddtrue)
    {
      if (bdd_low(l) == bddfalse)
        {
          res.push_back(bdd_var(l));
          l = bdd_high(l);
        }
      else
        {
          res.push_back(~bdd_var(l));
          l = bdd_low(l);
        }
    }
  std::reverse(res.begin(), res.end());
  return res;
}

/* Check that CUBES is an irredundant cover of F made of prime
   implicants. */
static void check_isop(const std::vector<bdd>& cubes, const bdd& f,
                       const char* what)
{
  bdd cover = bddfalse;
  for (const bdd& c : cubes)
    {
      if (!bdd_is_cube(c))
        ERROR(string(what) + ": non-cube in the ISOP");
      if ((c - f) != bddfalse)
        ERROR(string(what) + ": non-implicant in the ISOP");
      cover |= c;
    }
  if (cover != f)
    ERROR(string(what) + ": the ISOP does not cover the function");

  for (unsigned i = 0; i < cubes.size(); ++i)
    {
      bdd others = bddfalse;
      for (unsigned j = 0; j < cubes.size(); ++j)
        if (i != j)
          others |= cubes[j];
      if ((cubes[i] - others) == bddfalse)
        ERROR(string(what) + ": redundant cube in the ISOP");

      /* A prime implicant cannot be weakened by dropping a literal. */
      std::vector<int> lits = isop_literals(cubes[i]);
      for (unsigned k = 0; k < lits.size(); ++k)
        {
          std::vector<int> sub = lits;
          sub.erase(sub.begin() + k);
          bdd weaker = bdd_ibuildcube2(static_cast<int>(sub.size()),
                                       sub.data());
          if ((weaker - f) == bddfalse)
            ERROR(string(what) + ": non-prime cube in the ISOP");
        }
    }
}

static bool has_cube(const std::vector<bdd>& cubes, const bdd& c)
{
  return std::find(cubes.begin(), cubes.end(), c) != cubes.end();
}

/* Handler of the C entry points, and the number of times it was called.
   Running a garbage collection here checks that the cube handed to the
   handler is referenced: were it not, the cube would be reclaimed
   before it is stored. */
static unsigned isop_hits;

static void isop_collect(BDD cube, void* data)
{
  ++isop_hits;
  bdd_gbc();
  static_cast<std::vector<bdd>*>(data)->push_back(bdd_from_int(cube));
}

/* Check that the three C entry points pass the same cubes to their
   handler as the corresponding C++ wrappers. */
static void check_c_api(const bdd& f, const bdd& positive_vars)
{
  std::vector<bdd> expected;
  std::vector<bdd> got;

  bdd_isop(f, expected);
  isop_hits = 0;
  bdd_isop(f.id(), isop_collect, &got);
  if (got != expected || isop_hits != expected.size())
    ERROR("the C API of bdd_isop() disagrees with the C++ wrapper");

  bdd_isop(f, positive_vars, expected);
  got.clear();
  isop_hits = 0;
  bdd_isop_with_positive_vars(f.id(), positive_vars.id(), isop_collect,
                              &got);
  if (got != expected || isop_hits != expected.size())
    ERROR("the C API of bdd_isop_with_positive_vars() disagrees with "
          "the C++ wrapper");

  bdd_isop_all_positive(f, expected);
  got.clear();
  isop_hits = 0;
  bdd_isop_all_positive(f.id(), isop_collect, &got);
  if (got != expected || isop_hits != expected.size())
    ERROR("the C API of bdd_isop_all_positive() disagrees with the "
          "C++ wrapper");
}

void testIsop()
{
  cout << "Testing bdd_isop()\n";

  bdd a = bdd_ithvar(0);
  bdd b = bdd_ithvar(1);
  bdd c = bdd_ithvar(2);
  bdd d = bdd_ithvar(3);

  std::vector<bdd> res;

  bdd_isop(bddfalse, res);
  if (!res.empty())
    ERROR("bdd_isop(false) should be empty");
  bdd_isop(bddtrue, res);
  if (res.size() != 1 || res[0] != bddtrue)
    ERROR("bdd_isop(true) should be {true}");

  /* A single cube */
  bdd_isop(a & b & !c, res);
  if (res.size() != 1 || res[0] != (a & b & !c))
    ERROR("bdd_isop() of a cube");

  /* The result vector is cleared, and its memory reused, by successive
     calls. */
  res.reserve(42);
  bdd_isop(a & b, res);
  bdd_isop(c, res);
  if (res.size() != 1 || res[0] != c)
    ERROR("bdd_isop() does not reset its result vector");
  if (res.capacity() < 42)
    ERROR("bdd_isop() released the memory of its result vector");

  /* The example from the Minato-Morreale paper: the prime implicants
     of (a&b) | c | (a&d) are {a,b}, {a,d}, and {c}. */
  for (bdd f : {(a & b) | c | (a & d), a | b, a ^ b, c & d,
                (a | b) & (c | d), (a & c) | (b & !c) | (!a & d)})
    {
      bdd_isop(f, res);
      check_isop(res, f, "hand-written function");
    }

  bdd f = (a & b) | c | (a & d);
  bdd_isop(f, res);
  if (res.size() != 3 || !has_cube(res, a & b) || !has_cube(res, a & d)
      || !has_cube(res, c))
    ERROR("bdd_isop() should return {a&b, a&d, c}");

  /* Positive variants.  (a|b)&(c|d) is positive-unate in all its
     variables. */
  f = (a | b) & (c | d);
  bdd_isop_all_positive(f, res);
  if (res.size() != 4 || !has_cube(res, a & c) || !has_cube(res, a & d)
      || !has_cube(res, b & c) || !has_cube(res, b & d))
    ERROR("bdd_isop_all_positive() should return the four cubes");
  bdd_isop(f, a & b & c & d, res);
  if (res.size() != 4 || !has_cube(res, a & c) || !has_cube(res, a & d)
      || !has_cube(res, b & c) || !has_cube(res, b & d))
    ERROR("bdd_isop() with positive variables should return four cubes");

  check_c_api(f, a & b & c & d);

  bdd vars[4] = {a, b, c, d};
  unsigned seed = 12345;
  auto rnd = [&seed](unsigned n)
    {
      seed = seed * 1103515245u + 12345u;
      return (seed >> 16) % n;
    };

  for (int i = 0; i < 300; ++i)
    {
      bdd g = bddfalse;
      bdd h = bddfalse;
      unsigned nterm = 1 + rnd(6);
      for (unsigned t = 0; t < nterm; ++t)
        {
          bdd ct = bddtrue;
          bdd ht = bddtrue;
          for (unsigned v = 0; v < 4; ++v)
            switch (rnd(3))
              {
              case 0:
                ct &= vars[v];
                ht &= vars[v];
                break;
              case 1:
                ct &= !vars[v];
                break;
              default:
                break;
              }
          g |= ct;
          h |= ht;
        }
      /* G is an arbitrary function, H is monotone. */
      bdd_isop(g, res);
      check_isop(res, g, "random function");
      bdd_isop_all_positive(h, res);
      check_isop(res, h, "random monotone function");
      bdd_isop(h, a & b & c & d, res);
      check_isop(res, h, "random monotone function with positive variables");
    }
}

int main(int ac, char** av)
{
  bdd_init(1000,1000);

  bdd_setvarnum(10);

  testSupport();
  testBvecIte();
  testShortest();
  testIsCube();
  testHaveCommon();
  testMtSccs();
  testRestrict();
  testQuant();
  testIsop();

  bdd_done();
  return 0;
}
