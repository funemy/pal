#include "pal.h"
#include <stdint.h>

/* GNU `a ?: b` yields `a` when it is nonzero and `b` otherwise, evaluating
 * `a` only once. PAL keeps it as its own operator and emits it as a library
 * function (Pulse.Lib.C.Elvis.elvis_<type> a b), so `a` is evaluated exactly
 * once even when it has a side effect. `b` is evaluated unconditionally in
 * the translation, so a `b` with a side effect is reported as unsupported. */

int32_t elvis_ops_int(int32_t a, int32_t b)
    _ensures(return == (a != 0 ? a : b)) {
  return a ?: b;
}

uint32_t elvis_ops_chain(uint32_t x, uint32_t y, uint32_t z)
    _ensures(return == (x != 0 ? x : (y != 0 ? y : z))) {
  return x ?: y ?: z;
}

int32_t elvis_ops_as_condition(int32_t flag, int32_t fallback)
    _ensures(return == ((flag != 0 ? flag : fallback) != 0 ? 1 : 0)) {
  if (flag ?: fallback) {
    return 1;
  }
  return 0;
}

/* The left operand is a call: it must run exactly once. */
int32_t next_slot(int32_t q)
    _requires(q < 1000)
    _ensures(return == q + 1) {
  return q + 1;
}

int32_t elvis_ops_effectful_left(int32_t q, int32_t fallback)
    _requires(q < 1000)
    _ensures(return == (q + 1 != 0 ? q + 1 : fallback)) {
  return next_slot(q) ?: fallback;
}
