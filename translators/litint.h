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
 * Functions for dealing with literals and constants encoded in integers
 *
 * A few of the highest bits of an integer are used to determine its polarity
 * and whether it stands for one of the constants true / false / wanted /
 * dont_care. The remaining bits are used to store an atom number or specify
 * the constant.
 *
 * There are four kinds of output functions.
 *
 * litint_output_normal*
 * -- these understand positive and negative literals but no constants
 *
 * litint_output_new*
 * litint_output_ifw*
 * litint_output_*
 * -- these understand positive literals, negative literals and constants
 *
 * litint_output_new*
 * -- these define the head atom and return it or a constant if the body
 *    symbolically evaluates to a constant
 *
 * litint_output_ifw*
 * -- these operate like litint_output_new* if the output atom is marked as
 *    wanted, and otherwise do nothing
 *
 * litint_output_*
 * -- these use a given head atom but return SMX_TRUE if the body symbolically
 *     evaluates to true
 *
 * (c) 2014 Jori Bomanson
 *
 * NOTE: Requires boolean macro SMX_WANT_EVERYTHING       
 * TODO: Sort out MIX_* and SMX_* prefixes
 *
 */

#ifndef LITINT_H
#define LITINT_H

#include "args.h"
#include "common.h"       /* For MALLOC, FREE */

/* ---------------------- Configuration ------------------------------------ */

#define SMX_WANT_EVERYTHING       0
#define SMX_ENABLE_PROPAGATING    1
#define SMX_ENABLE_MODIFYING      1

/* --------------------- Mixed Literal Routines --------------------------- */

/* The bit that defines whether a literal is negative (1) or positive (0) */
#define MIX_NEG_FLAG      (INT_MIN)

/* Macros to encode and decode the (possible) negativity of a literal */
#define MIX_GET_NEG(x)    ((x) | MIX_NEG_FLAG)
#define MIX_GET_ATOM(x)   ((x) & ~MIX_NEG_FLAG)
#define MIX_COMPLEMENT(x) ((x) ^ MIX_NEG_FLAG)

/* Macros to check if a literal is positive or negative */
#define MIX_IS_NEG(x)     ((x) & MIX_NEG_FLAG)
#define MIX_IS_POS(x)     (!MIX_IS_NEG(x))

#define SMX_SPECIAL            ((int) (((unsigned int) INT_MIN) / 2))
#define SMX_TRUE               (SMX_SPECIAL | 0x01)
#define SMX_FALSE              (SMX_SPECIAL | 0x02)
#define SMX_WANTED             (SMX_SPECIAL | 0x04)
#define SMX_DONT_CARE          (SMX_SPECIAL | 0x08)

#define SMX_IS_SPECIAL(x)      ((x) & SMX_SPECIAL)

// TODO: Skip all == below

#define SMX_IS_TRUE(x)         (((x) & SMX_TRUE) == SMX_TRUE)

#define SMX_IS_FALSE(x)        (((x) & SMX_FALSE) == SMX_FALSE)

#define SMX_IS_WANTED(x)       ((SMX_WANT_EVERYTHING) \
                                || (((x) & SMX_WANTED) == SMX_WANTED))

#define SMX_IS_DONT_CARE(x)    (((x) & SMX_DONT_CARE) == SMX_DONT_CARE)

#define SMX_ENCODE_NEGATIVE(x)   MIX_GET_NEG(x)
#define SMX_DECODE_NEGATIVE(x)   MIX_GET_ATOM(x)
#define SMX_IS_NEGATIVE(x)       MIX_IS_NEG(x)

// FIXME MIX_COMPLEMENT(SMX_TRUE) != SMX_FALSE
// DONTFIXME SMX_IS_NEGATIVE(SMX_FALSE) == false
// -- On a second thought, false might not be considered negative

/* ---- Private-ish -------------------------------------------------------- */

void litint__swap(int *a, int *b)
{
  int x = *a;
  *a = *b;
  *b = x;
}

/* ------------------------------------------------------------------------- */

/*
 * Output a normal rule with a body of literals encoded in integers
 */

void litint_output_normal(ARGS *args, int head, int cnt, int *mix)
{
  args->newrule++;

  if(args->style == STYLE_DEV_NULL)
    return;

  int * const negpos = (int *)MALLOC(cnt * sizeof(mix));
  int pos_cnt = 0, neg_cnt = 0;
  int i;

  for(i = 0; i < cnt; i++)
    if(MIX_IS_NEG(mix[i]))
      negpos[neg_cnt++] = MIX_GET_ATOM(mix[i]);

  for(i = 0; i < cnt; i++)
    if(MIX_IS_POS(mix[i]))
      negpos[neg_cnt+pos_cnt++] = MIX_GET_ATOM(mix[i]);

  args_output_normal(args, head, pos_cnt, &negpos[neg_cnt], neg_cnt, negpos);

  FREE(negpos);
}

/*
 * Output a normal rule with a single body literal encoded in an integer
 */

void litint_output_normal_1(ARGS *args, int head, int x)
{
  litint_output_normal(args, head, 1, &x);
}

/*
 * Turn negative literals into mixed literal representation in place
 */

void litint_from_neg(int neg_cnt, int *neg)
{
  int i;

  for (i = 0; i < neg_cnt; i++)
    neg[i] = MIX_GET_NEG(neg[i]);
}

/*
 * Turn an array of literals into atom numbers ordered from negative to positive
 *
 * NOTE: Apparently unused
 */

int litint_to_neg_then_pos(int mix_cnt, int *mix)
{
  int i, n = 0, p = mix_cnt;

  /* invariant: neg,mix,pos: [0..n-1],[n..p-1],[p..mix_cnt] */

  while(n < p)
    if(MIX_IS_NEG(mix[n]))
      n++;
    else if(MIX_IS_POS(mix[p - 1]))
      p--;
    else
      litint__swap(&mix[n++], &mix[--p]);

  for(i = 0; i < n; i++)
    mix[i] = MIX_GET_ATOM(mix[i]);

  return n;
}

/*
 * Turn an array of literals into atom numbers ordered from negative to positive
 * and arrange weights accordingly
 */

int litint_to_neg_then_pos_with_weights_general(int mix_cnt, int *mix,
                                                int *weights)
{
  int i, n = 0, p = mix_cnt;

  /* invariant: neg,mix,pos: [0..n-1],[n..p-1],[p..mix_cnt] */

  while(n < p)
    if(MIX_IS_NEG(mix[n]))
      n++;
    else if(MIX_IS_POS(mix[p - 1]))
      p--;
    else {
      int a = n++;
      int b = --p;
      litint__swap(&mix[a], &mix[b]);
      litint__swap(&weights[a], &weights[b]);
    }

  for(i = 0; i < n; i++)
    mix[i] = MIX_GET_ATOM(mix[i]);

  return n;
}

/* Same as above, but for consecutive input literal and weight arrays */

int litint_to_neg_then_pos_with_weights(int mix_cnt, int *mix)
{
  return
    litint_to_neg_then_pos_with_weights_general(mix_cnt, mix, &mix[mix_cnt]);
}

/*
 * Package literals followed by weights into an optimization statement
 */

void litint_to_optimize(int cnt, int *mix, OPTIMIZE_RULE *optimize)
{
  optimize->neg_cnt = litint_to_neg_then_pos_with_weights(cnt, mix);
  optimize->pos_cnt = cnt - optimize->neg_cnt;
  optimize->neg    = mix;
  optimize->pos    = &optimize->neg[optimize->neg_cnt];
  optimize->weight = &optimize->pos[optimize->pos_cnt];
}

/*
 * Turn literals into a positive array by renaming negative literals
 */

void litint_rename_neg(ARGS *args, int cnt, int *mix)
{
  int i;
  for(i = 0; i < cnt; i++)
    if(MIX_IS_NEG(mix[i])) {
      litint_output_normal_1(args, args->newatom, mix[i]);
      mix[i] = args->newatom++;
    }
}

/* --------------------- Special Output Routines -------------------------- */

/*
 * Output a symbolically evaluated normal rule with a new head and a single
 * body literal
 *
 * The new head is returned
 */

int litint_output_new_1(ARGS *args, int x, int x_propagatable)
{
  if(SMX_IS_SPECIAL(x))
    return x;

#if SMX_ENABLE_PROPAGATING
  if(x_propagatable)
    return x;
#endif

  litint_output_normal(args, args->newatom, 1, &x);

  return args->newatom++;
}

/*
 * Output two symbolically evaluated normal rules with a common new head and a
 * single body literal each
 *
 * The new head is returned
 */
int litint_output_new_1x2(ARGS *args,
                          int x, int x_modifiable,
                          int y, int y_modifiable)
{
  if(SMX_IS_TRUE(x) || SMX_IS_TRUE(y))
    return SMX_TRUE;

  if(SMX_IS_FALSE(x) || SMX_IS_DONT_CARE(x))
    return litint_output_new_1(args, y, 1);

  if(SMX_IS_FALSE(y) || SMX_IS_DONT_CARE(y))
    return litint_output_new_1(args, x, 1);

#if SMX_ENABLE_MODIFYING
  if(x_modifiable) {
    litint_output_normal(args, x, 1, &y);
    return x;
  }

  if(y_modifiable) {
    litint_output_normal(args, y, 1, &x);
    return y;
  }
#endif

  litint_output_normal(args, args->newatom, 1, &x);
  litint_output_normal(args, args->newatom, 1, &y);

  return args->newatom++;
}

/*
 * Output a symbolically evaluated normal rule with a new head and two body
 * literals
 *
 * The new head is returned
 */

int litint_output_new_2(ARGS *args, int x, int y)
{
  if(SMX_IS_FALSE(x) || SMX_IS_FALSE(y))
    return SMX_FALSE;

  if(SMX_IS_TRUE(x) || SMX_IS_DONT_CARE(x))
    return litint_output_new_1(args, y, 1);

  if(SMX_IS_TRUE(y) || SMX_IS_DONT_CARE(y))
    return litint_output_new_1(args, x, 1);

  int body[2];
  body[0] = x;
  body[1] = y;
  litint_output_normal(args, args->newatom, 2, body);

  return args->newatom++;
}

/*
 * Output a symbolically evaluated normal rule with a new head and a single
 * body literal if the output is wanted
 *
 * The wanted state of the output is read from and the output set to *result
 */

void litint_output_ifw_1(ARGS *args, int *result, int x, int x_propagatable)
{
  if(SMX_IS_WANTED(*result))
    *result = litint_output_new_1(args, x, x_propagatable);
}

/*
 * Output two symbolically evaluated normal rules with a common new head and a
 * single body literal each if the output is wanted
 *
 * The wanted state of the output is read from and the output set to *result
 */

void litint_output_ifw_1x2(ARGS *args, int *result,
                           int x, int x_modifiable,
                           int y, int y_modifiable)
{
  if(SMX_IS_WANTED(*result))
    *result = litint_output_new_1x2(args, x, x_modifiable, y, y_modifiable);
}

/*
 * Output a symbolically evaluated normal rule with a new head and two
 * body literals if the output is wanted
 *
 * The wanted state of the output is read from and the output set to *result
 */

void litint_output_ifw_2(ARGS *args, int *result, int x, int y)
{
  if(SMX_IS_WANTED(*result))
    *result = litint_output_new_2(args, x, y);
}

/*
 * Output a symbolically evaluated normal rule with a single body literal
 *
 * The given head is returned unless the body evaluates to true
 * in which case SMX_TRUE is returned
 */

int litint_output_1(ARGS *args, int head, int mix)
{
  if(SMX_IS_SPECIAL(mix)) {
    if(SMX_IS_TRUE(mix))
      litint_output_normal(args, head, 0, NULL);
    else
      ; /* The body is false --> output nothing */
  } else {
    litint_output_normal_1(args, head, mix);
    return SMX_TRUE;
  }

  return head;
}

/*
 * Output a symbolically evaluated normal rule with up to two body literals
 *
 * The given head is returned unless the body evaluates to true
 * in which case SMX_TRUE is returned
 */

int litint_output_2(ARGS *args, int head, int x, int y)
{
  if(SMX_IS_TRUE(head) || (SMX_IS_TRUE(x) && SMX_IS_TRUE(y)))
    return SMX_TRUE;

  if(SMX_IS_FALSE(head))
    // FIXME This must be wrong
    return litint_output_new_2(args, x, y);

  if(SMX_IS_FALSE(x) || SMX_IS_FALSE(y))
    return head;

  if(SMX_IS_TRUE(x)) {
    litint_output_normal(args, head, 1, &y);
    return head;
  }

  if(SMX_IS_TRUE(y)) {
    litint_output_normal(args, head, 1, &x);
    return head;
  }

  int body[2];
  body[0] = x;
  body[1] = y;
  litint_output_normal(args, head, 2, body);

  return head;
}

#endif
