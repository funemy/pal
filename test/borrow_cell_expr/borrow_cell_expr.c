#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* `&a[i]` handed to a plain-`ref` parameter is borrowed out of the array with
 * `array_borrow_cell`. This was emitted only for a bare call statement; a call
 * in expression position -- an assignment's right-hand side, an `if`
 * condition, an operand of `&&` -- got `admit()` for the argument. The borrow
 * is one way: after the call the cell is still carved out of the array, and
 * the caller hands it back with `array_return_cell` (see test/array_to_ref). */

void bump(int32_t *p)
  _ensures(*p == 1)
{
  *p = 1;
}

int32_t read_val(int32_t *p)
  _ensures(return == *p && *p == _old(*p))
{
  return *p;
}

int32_t is_zero(int32_t *p)
  _ensures(return == (*p == 0 ? 1 : 0) && *p == _old(*p))
{
  return *p == 0;
}

/* Baseline: the statement form that already worked. */
void stmt_call(_array int32_t *a, size_t i)
  _requires(i < a._length)
{
  bump(&a[i]);
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
}

/* Assignment right-hand side. */
int32_t assign_rhs(_array int32_t *a, size_t i)
  _requires(i < a._length)
{
  int32_t v;
  v = read_val(&a[i]);
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
  return v;
}

/* `if` condition. */
int32_t in_condition(_array int32_t *a, size_t i)
  _requires(i < a._length)
{
  int32_t r = 0;
  if (!is_zero(&a[i])) {
    r = 1;
  }
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
  return r;
}

/* Operand of `&&`. */
int32_t in_and_chain(int32_t c, _array int32_t *a, size_t i)
  _requires(i < a._length)
{
  int32_t r;
  r = c != 0 && !is_zero(&a[i]);
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
  return r;
}
