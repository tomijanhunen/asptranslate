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
 * Forward declarations used and defined in random places
 *
 * (c) 2014 Jori Bomanson
 */

#ifndef COMMON_H
#define COMMON_H

#include <inttypes.h>   /* for uint64_t */
#include <io.h>         /* For program_name */

void output_normal(int style, FILE *out,
                   int head,
		   int pos_cnt, int *pos,
                   int neg_cnt, int *neg,
                   ATAB *table);

void output_weight(int style, FILE *out, RULE *rule, ATAB *table);

void output_optimize(int style, FILE *out, RULE *rule, ATAB *table);

void output_choice(int style, FILE *out, RULE *rule, ATAB *table);

void output_constraint(int style, FILE *out, RULE *rule, ATAB *table);

void output_disjunctive(int style, FILE *out, RULE *rule, ATAB *table);

/* Debugging */

char *ma2s(int atom);

char *a2y(int c, int stride, int *a);

char *a2x(int c, int *a);

/* Misc */

void sort_body_descending(int pos_cnt, int *pos, int neg_cnt, int *neg,
                          int *weight, int *sorted_body, int *sorted_weight);

int gcd(int u, int v);

int pick_divisor(int bound, int cnt, int *w, int w_max, int lb, int ub,
                 int max_residue_sum);

void output_atom(int style, FILE *out, int atom, ATAB *table);

/* Memory allocation */

#ifndef DEBUG
#define MALLOC(x)         malloc_wrapper(x)
#define FREE(x)           free(x)

static void *malloc_wrapper(size_t amount)
{
  void *pointer = malloc(amount);
  if (NULL == pointer) {
    fprintf(stderr, "%s: Ran out of memory\n", program_name);
    fflush(stderr);
    exit(-1);
  }
  return pointer;
}

#else
#define MALLOC(x)         malloc_wrapper((x), __FILE__, __LINE__)
#define FREE(x)           free_wrapper((x), __FILE__, __LINE__)

static void *malloc_wrapper(size_t amount, char *file, int line)
{
  void *pointer = malloc(amount);
  if (NULL == pointer) {
    fprintf(stderr,
            "%s: %s: %d: Ran out of memory\n",
            program_name,
            file,
            line);
    fflush(stderr);
    exit(-1);
  }
  return pointer;
}

static void free_wrapper(void *pointer, char *file, int line)
{
  if (NULL == pointer) {
    fprintf(stderr,
            "%s: %s: %d: About to FREE a NULL pointer\n",
            program_name,
            file,
            line);
  }
  free(pointer);
}
#endif


#endif
