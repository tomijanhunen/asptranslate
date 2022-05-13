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

#ifndef CONDFLAGS_H
#define CONDFLAGS_H

#include <inttypes.h>     /* for uint64_t */

#include "expression.h"

typedef struct condflags CONDFLAGS;

struct condflags {
  EXPRESSION  *condition;
  uint64_t    flags;
  CONDFLAGS   *next;
  int         *vars;
};

extern CONDFLAGS * condflags_create();
extern void condflags_add_uncond(CONDFLAGS *c, uint64_t f);
extern void condflags_add(CONDFLAGS *c, EXPRESSION *e, uint64_t f);
extern void condflags_add_str(CONDFLAGS *c, char *s, uint64_t f);
extern uint64_t condflags_eval(CONDFLAGS *c);
extern void condflags_set(CONDFLAGS *c, char var, int value);
extern void condflags_free(CONDFLAGS *c);
extern int condflags_size(CONDFLAGS *c);

#endif
