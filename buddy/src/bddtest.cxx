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

  bdd_done();
  return 0;
}
