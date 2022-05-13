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
 * Command line argument related constants for LP2NORMAL2 that are useful to
 * have in a separate header
 *
 * (c) 2014 Jori Bomanson
 */

#ifndef ARGS_H
#define ARGS_H

#include "common.h"

#define FL_ADDER                                        0x01
#define FL_BINARY                                       0x02
#define FL_UNARY                                        0x04
#define FL_RAW                                          0x08

#define FL_KEEP_CO                                      0x10
#define FL_KEEP_WT                                      0x20
#define FL_KEEP_CH                                      0x40
#define FL_KEEP_OPT                                     0x80

#define FL_WT_TRIM                                      0x0
#define FL_WT_PRIME                                     0x0
#define FL_WT_THROW_PAIR                                0x0

#define FL_WT_ADDER                                     0x4000
#define FL_WT_STRETCH                                   0x200000
#define FL_WT_EXP                                       0x400000

#define FL_SHUFFLE_CO                                   0x8000000

#define FL_ANTIRAW                                      0x20000000

#define FL_WT_NORM_PART                                 0x0

#define FL_OPT_MERGE                                    0x800
#define FL_OPT_WEIGHT                                   0x1000
#define FL_OPT_OPT                                      0x2000

#define FL_OPT_SORT                                     0x8000
#define FL_OPT_SORT_UNIT                                0x10000
#define FL_OPT_SORT_RULE                                0x20000
#define FL_OPT_SORT_INTEGRITY                           0x40000
#define FL_OPT_SORT_LB_INTEGRITY                        0x80000
#define FL_OPT_SORT_UB_INTEGRITY                        0x100000

#define FL_OPT_PLAN                                     0x1000000
#define FL_OPT_PLAN_NEG                                 0x2000000
#define FL_OPT_PLAN_HALF                                0x4000000
#define FL_OPT_PLAN_MANY                                0x40000000
#define FL_OPT_PLAN_INDEPENDENT                         0x10000000000000
#define FL_OPT_PLAN_FAMILY_SINGLETON                    0x20000000000000
#define FL_OPT_PLAN_DOT                                 0x40000000000000

#define FL_ROBDD                                        0x80000000
#define FL_WT_ORDER_ASCENDING                           0x100000000
#define FL_WT_ORDER_DESCENDING                          0x200000000
#define FL_WT_ORDER_RANDOM                              0x800000000

#define FL_WT_BIT_DECOMPOSE                             0x400000000

#define FL_CO_OE_MERGE                                  0x1000000000
#define FL_CO_SELECT                                    0x2000000000

#define FL_CO_SELECT_O2                                 0x10000000000
#define FL_CO_SELECT_A2                                 0x20000000000

#define FL_CO_REC_SORT_PW                               0x40000000000
#define FL_CO_REC_SORT_EXP2                             0x800000

#define FL_CO_SEQ_SORT                                  0x4000000000

#define FL_CO_TOTALIZE                                  0x1000000000000

#define FL_CO_AUTO                                      0x2000000000000

#define FL_WT_SEQ_SORT                                  0x8000000000

#define FL_WT_MIX_UNR                                   0x80000000000

#define FL_WT_PLAN                                      0x100000000000
#define FL_WT_PLAN_INDEPENDENT                          0x200000000000
#define FL_WT_PLAN_FAMILY_SINGLETON                     0x400000000000
#define FL_WT_PLAN_DOT                                  0x800000000000

#define FL_CH_EXTERNAL                                  0x100
#define FL_CH_AUX                                       0x400

#define FL_OPT_DECISION                                 0x200

/* ------------------------------------------------------------------------- */

#define FL_WT_UNARY_SORT    (FL_WT_SEQ_SORT)

#define FL_CO_REC_SORT      (FL_CO_OE_MERGE | FL_CO_TOTALIZE)

#define FL_CO_UNARY_SORT    (FL_CO_SEQ_SORT | FL_CO_REC_SORT \
                              | FL_CO_SELECT | FL_CO_AUTO)

/* ------------------------------------------------------------------------- */

/* A number distinct from any STYLE_* defined in io.h.
   This is used to denote that no output should be printed. */
#define STYLE_DEV_NULL            111

/* ------------------------------------------------------------------------- */

#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) < (y) ? (y) : (x))

/* ------------------------------------------------------------------------- */

/*
 * A group of arguments that often go together
 */

typedef struct oargs_t {
  int style;
  FILE *out;
  ATAB *table;
  uint64_t flavors; /* used in selecting translations */
  CONDFLAGS *condmflavors;  /* used to conditionally set flavors */
  CONDFLAGS *condcflavors;
  CONDFLAGS *condwflavors;
  CONDFLAGS *condoflavors;
  int conddepth;    /* recursion depth measured in condition evaluations */
  int newatom;      /* used to allocate new atoms */
  int newrule;      /* number of produced rules */
  int newopt;       /* running number of optimization statements */
  int falsity;      /* some false atom */
  int optimize_lb;  /* no less than any optimization value */
  int optimize_ub;  /* no greater than any optimization value */
  int radix_lb;     /* no less than any radix */
  int radix_ub;     /* no greater than any radix */
  char *optimize_format;
} ARGS;

/* ---------------------- Conditional Flavors ---------------------------- */

void choose_flavors_for_arguments(ARGS *args, CONDFLAGS *f, int k, int n, int w);

void choose_flavors_for_constraint(ARGS *args, RULE *rule);

void choose_flavors_for_weight(ARGS *args, RULE *rule);

void choose_flavors_for_optimize(ARGS *args, RULE *rule);

uint64_t replace_flavors_for_unary_merger(ARGS *args, int bound, int leftn, int rightn);

uint64_t replace_flavors_for_unary_sorter(ARGS *args, int bound, int n);

uint64_t replace_flavors_for_unary_weight_sorter(ARGS *args, int bound, int n, int wsum);

void restore_flavors(ARGS *args, uint64_t saved_flavors);

/* ---------------------- ARGS Wrappers ---------------------------------- */

void args_output_weight(ARGS *args, RULE *rule)
{
  output_weight(args->style, args->out, rule, args->table);
}

void args_output_optimize(ARGS *args, RULE *rule)
{
  output_optimize(args->style, args->out, rule, args->table);
}

void args_output_normal(ARGS *args, int head,
                         int pos_cnt, int *pos,
                         int neg_cnt, int *neg)
{
  output_normal(args->style, args->out, head,
		pos_cnt, pos, neg_cnt, neg, args->table);
}

void args_output_choice(ARGS *args, RULE *rule)
{
  output_choice(args->style, args->out, rule, args->table);
}

void args_output_disjunctive(ARGS *args, RULE *rule)
{
  output_disjunctive(args->style, args->out, rule, args->table);
}

/* ---------------------- Things to keep robdd.h happy ------------------- */

void permute_weighted_array_in_place(ARGS *args, int cnt, int *body,
                                     int *weight);

/* ---------------------- Things to keep plan.h happy -------------------- */

void add_optimize_format_names(ARGS *args, int cnt, int *atoms, int *weights);

/* ---------------------- Things to keep implyaux.h happy ---------------- */

void normalize_choice_head(ARGS *args, int head_cnt, int *head);

#endif
