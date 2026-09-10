#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* An array embedded in a struct by value (`int32_t regs[4]`) is a
 * `Pulse.Lib.C.Array.array` like an `_array` pointer is, and its cells can be
 * borrowed with `array_borrow_cell` the same way. The borrow paths only
 * accepted an `_array` *pointer* as the indexed base; a fixed-size array field
 * fell through to "cannot produce lvalue". This is the register-file idiom:
 * `reg = &state->regs[i]; reg->precise = true;`. */

struct regfile {
  int32_t regs[4];
  int32_t count;
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

/* Bare statement call with an embedded-array cell. */
void stmt_call(struct regfile *s, size_t i)
  _requires(i < 4)
{
  bump(&s->regs[i]);
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(s->regs) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(s->regs));
}

/* Cursor into the embedded array through a local `ref`. */
void cursor(struct regfile *s, size_t i)
  _requires(i < 4)
{
  int32_t *reg;
  reg = &s->regs[i];
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.forget_maybe $(reg));
  *reg = 7;
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(s->regs) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(s->regs));
}

/* Call in expression position with an embedded-array cell. */
int32_t in_condition(struct regfile *s, size_t i)
  _requires(i < 4)
{
  int32_t r = 0;
  if (read_val(&s->regs[i]) != 0) {
    r = 1;
  }
  _ghost_stmt(Pulse.Lib.C.MaybeUninit.intro_maybe_some (array_cell_ref $(s->regs) (SizeT.v $(i))));
  _ghost_stmt(array_return_cell $(s->regs));
  return r;
}
