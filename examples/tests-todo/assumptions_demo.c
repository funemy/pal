#include "pal.h"
#include <stdint.h>

/* Demo for the assumptions report: two functions that are declared but never
 * defined. `clamp` carries a contract and is trusted as an axiom; `scale`
 * has none, so callers learn nothing about its result. */
int32_t clamp(int32_t x, int32_t lo, int32_t hi)
    _ensures(lo <= return && return <= hi);
int32_t scale(int32_t x);

int32_t total(int32_t n, int32_t lo, int32_t hi) {
  int32_t acc = 0;
  int32_t i;
  for (i = 0; i < n; i++) {
    acc = acc + clamp(scale(i), lo, hi);
  }
  return scale(acc);
}
