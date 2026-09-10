#include "pal.h"
#include <stdint.h>
#include <project/types.h> /* not on the include path: a real C parse error */

/* Demo for parse-error cascade suppression: after clang reports the missing
 * header, every use of a type, field, constant or function it should have
 * declared is an error-recovery node that the translator reported one by one. */

uint32_t count_ready(struct queue *q) {
  uint32_t n = 0;
  slot_t *s;
  for (s = q->head; s != NULL; s = s->next) {
    if (s->state == SLOT_READY && s->owner != INVALID_OWNER) {
      n = n + slot_weight(s);
    }
  }
  return n;
}

void drain(struct queue *q, budget_t budget) {
  slot_t *s = q->head;
  while (s != NULL && budget > 0) {
    budget = budget - slot_cost(s);
    q->drained = q->drained + 1;
    s = s->next;
  }
  q->head = s;
}

int32_t rebalance(struct queue *a, struct queue *b) {
  if (a->depth > b->depth + REBALANCE_SLACK) {
    move_slots(a, b, (a->depth - b->depth) / 2);
    return 1;
  }
  return 0;
}
