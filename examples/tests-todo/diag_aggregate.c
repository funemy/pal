#include "pal.h"
#include <stdint.h>

/* Demo for diagnostics aggregation: the same unsupported construct (pointer
 * arithmetic on a plain `char *`) at many sites yields one report per site,
 * each re-reported by every later check pass. */
void a1(char *buf, int32_t n) { buf += n; }
void a2(char *buf, int32_t n) { buf += n; }
void a3(char *buf, int32_t n) { buf += n; }
void a4(char *buf, int32_t n) { buf += n; }
void a5(char *buf, int32_t n) { buf += n; }
void a6(char *buf, int32_t n) { buf += n; }
