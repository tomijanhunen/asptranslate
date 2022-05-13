/* lp2normal2 -- Normalizer for smodels programs (under ASPTOOLS)

   Copyright (C) 2022 Jori Bomanson / Tomi Janhunen

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/

/*
 * LP2NORMAL2 -- Normalize SMODELS programs
 *
 * (c) 2014 Jori Bomansson
 *
 */

#include <stdlib.h>

#include "condflags.h"

static CONDFLAGS *
condflags_last(CONDFLAGS *c)
{
  while (NULL != c->next) {
    c = c->next;
  }
  return c;
}

CONDFLAGS *
condflags_create()
{
  CONDFLAGS *c  = malloc(sizeof(CONDFLAGS));
  c->flags      = 0;
  c->condition  = NULL;
  c->next       = NULL;
  c->vars       = calloc(EXPRESSION_VARS_SIZE, sizeof(int));
  return c;
}

void
condflags_add_uncond(CONDFLAGS *c, uint64_t f)
{
  c->flags = f;
}

void
condflags_add(CONDFLAGS *c, EXPRESSION *e, uint64_t f)
{
  CONDFLAGS *n  = malloc(sizeof(CONDFLAGS));
  n->condition  = e;
  n->flags      = f;
  n->next       = NULL;
  n->vars       = NULL;

  condflags_last(c)->next = n;
}

void
condflags_add_str(CONDFLAGS *c, char *s, uint64_t f)
{
  condflags_add(c, expression_create(s), f);
}

uint64_t
condflags_eval(CONDFLAGS *c)
{
  uint64_t flags = c->flags;
  int *vars = c->vars;
  while (NULL != c->next) {
    c = c->next;
    if (expression_eval(c->condition, vars)) {
      return flags | c->flags;
    }
  }
  return flags;
}

void
condflags_set(CONDFLAGS *c, char var, int value)
{
  c->vars[(unsigned char) var] = value;
}

void
condflags_free(CONDFLAGS *c)
{
  while (NULL != c->next) {
    c = c->next;
    free(c->condition);
  }
  if (NULL != c->vars) {
    free(c->vars);
  }
  free(c);
}

int
condflags_size(CONDFLAGS *c)
{
  int n = 0;
  while (NULL != c->next) {
    c = c->next;
    n++;
  }
  return n;
}
