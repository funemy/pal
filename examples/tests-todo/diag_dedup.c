#include "pal.h"
#include <stdint.h>

/* Demo for diagnostics deduplication: one unsupported construct (pointer
 * arithmetic on a plain `char *`) is re-reported by every well-formedness
 * check pass that runs after the failing elaboration. */
void advance(char *buf, int32_t n) {
  buf += n;
}
