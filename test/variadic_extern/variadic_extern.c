#include "pal.h"
#include <stdint.h>

/* A variadic external function: only its fixed parameters are part of the
 * Pulse signature. A call passes the fixed arguments and drops the rest
 * (with a warning), so a logging call inside a verified function is a modeled
 * call against `log_msg`'s contract rather than an untranslatable
 * expression. A dropped argument may not have a side effect. */
int32_t log_msg(int32_t level, _plain const char *fmt, ...)
  _ensures(return == level);

int32_t work(int32_t x)
  _requires(0 <= x && x < 1000)
  _ensures(return == x + 1)
{
  int32_t lvl;
  lvl = log_msg(2, "x=%d next=%d", x, x + 1);
  log_msg(lvl, "done");
  return x + 1;
}
