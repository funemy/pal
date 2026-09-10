#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* `&a[i].f` -- the address of a *field* of an array element -- is the cell
 * borrowed out of the array and then projected to the field: the borrow is
 * hoisted into a `let` as for `&a[i]`, and the field projection is applied to
 * the borrowed `ref`. This is the spilled-register idiom:
 * `reg = &func->stack[j].spilled_ptr; reg->precise = true;`. */

struct slot {
  int32_t val;
  int32_t flag;
};

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

/* Statement call on a field of an array element. */
void stmt_call(_array struct slot *a, size_t i)
  _requires(i < a._length)
{
  bump(&a[i].val);
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
}

/* Cursor to a field of an array element through a local `ref`. */
void cursor(_array struct slot *a, size_t i)
  _requires(i < a._length)
{
  int32_t *v;
  v = &a[i].val;
  _ghost_stmt(array_cell_read $(a) $(i));
  *v = 7;
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
}

/* Call in expression position on a field of an array element. */
int32_t in_condition(_array struct slot *a, size_t i)
  _requires(i < a._length)
{
  int32_t r = 0;
  if (read_val(&a[i].flag) != 0) {
    r = 1;
  }
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(a) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(a));
  return r;
}
