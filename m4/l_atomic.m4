dnl Copyright (c) 2015 Tim Kosse <tim.kosse@filezilla-project.org>
dnl Copying and distribution of this file, with or without modification, are
dnl permitted in any medium without royalty provided the copyright notice
dnl and this notice are preserved. This file is offered as-is, without any
dnl warranty.

# Some versions of gcc/libstdc++ require linking with -latomic if
# using the C++ atomic library.
#
# Sourced from http://bugs.debian.org/797228

m4_define([_CHECK_ATOMIC_testbody], [[
#include <atomic>
#include <cstdint>

// Deliberately sized/aligned like brick::hashset::Tagged<int, void>:
// 16 bytes, so it is NOT naturally lock-free on a single machine word
// and compare_exchange requires either CMPXCHG16B or libatomic.
template< typename T >
struct Tagged
{
    T t;
    uint32_t _tag;
    uint64_t _pad; // pad out to 16 bytes to match the real hashset::Tagged
    static const int tag_bits = 16;
    void tag( uint32_t v ) { _tag = v; }
    uint32_t tag() { return _tag; }
    Tagged() noexcept : t(), _tag( 0 ), _pad( 0 ) {}
    Tagged( const T &t ) : t( t ), _tag( 0 ), _pad( 0 ) {}
    bool operator==( const Tagged &o ) const {
      return t == o.t && _tag == o._tag;
    }
};

int main() {
  std::atomic<int64_t> a{};
  int64_t v = 5;
  int64_t r = a.fetch_add(v);

  std::atomic<Tagged<int>> value;
  Tagged<int> expected = value.load();
  Tagged<int> desired  = expected;
  desired.tag( 1 );
  bool ok = value.compare_exchange_strong( expected, desired );

  return static_cast<int>(r) + value.load().t + (ok ? 0 : 1);
}
]])

AC_DEFUN([CHECK_ATOMIC], [
  AC_LANG_PUSH(C++)
  AC_MSG_CHECKING([whether std::atomic can be used without link library])
  AC_LINK_IFELSE([AC_LANG_SOURCE([_CHECK_ATOMIC_testbody])],[
      AC_MSG_RESULT([yes])
    ],[
      AC_MSG_RESULT([no])
      LIBS="$LIBS -latomic"
      AC_MSG_CHECKING([whether std::atomic needs -latomic])
      AC_LINK_IFELSE([AC_LANG_SOURCE([_CHECK_ATOMIC_testbody])],[
          AC_MSG_RESULT([yes])
        ],[
          AC_MSG_RESULT([no])
          AC_MSG_FAILURE([cannot figure out how to use std::atomic])
        ])
    ])
  AC_LANG_POP
])
