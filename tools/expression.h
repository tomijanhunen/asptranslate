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

#ifndef EXPRESSION_H
#define EXPRESSION_H

#include "stdio.h"

#define EXPRESSION_VARS_SIZE 256

typedef struct expression EXPRESSION; 
typedef int (*expression_function)(int *vars, EXPRESSION *self);

struct expression {
  expression_function eval_on_rhs;
  expression_function eval_on_lhs;
  EXPRESSION *a;
  EXPRESSION *b;
  int constant;
  int origin;     /* Contains either a character or a special constant */
};

extern EXPRESSION *expression_create(char *s);
extern int expression_fprint(FILE *out, EXPRESSION *d);
extern void expression_free(EXPRESSION *d);
extern int expression_eval(EXPRESSION *d, int *vars);

#endif
