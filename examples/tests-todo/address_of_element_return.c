#include "pal.h"
#include <stdint.h>
#include <stddef.h>

/* Demo for the address-of diagnostic and --fail-on-error: returning the
 * address of an array element has no context to borrow the cell in. */
int32_t *last(_array int32_t *a, size_t n)
  _requires(0 < n && n <= a._length)
{
  return &a[n - 1];
}
