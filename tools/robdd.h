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
 * These functions are based on:
 *
 * Ignasi Ab\'{\i}o and
 * Robert Nieuwenhuis and
 * Albert Oliveras and
 * Enric Rodr\'{\i}guez-Carbonell and
 * Valentin Mayer-Eichberger.
 * A new look at BDDs for pseudo-Boolean constraints.
 * Journal of Artificial Intelligence Research,
 * 45:443-480, 2012.
 */

#ifndef ROBDD_H
#define ROBDD_H

#include <stdio.h>

/*#include "rule.h"*/

#include "args.h"

/*
 *
 */

typedef struct BDDNODE BDDNODE;

/*
 *
 */

struct BDDNODE {
  int lo;
  int hi;
  int literal;        /* auxiliary literal */
  BDDNODE *child[2];  /* these share the same selector literal */
};

/*
 *
 */

BDDNODE * search_bdd(int bound, BDDNODE *tree)
{
  if(tree == NULL)
    return NULL;

  if(bound < tree->lo)
    return search_bdd(bound, tree->child[0]);

  if(tree->hi < bound)
    return search_bdd(bound, tree->child[1]);

  return tree;
}

/*
 *
 */

void insert_bdd(BDDNODE *node, BDDNODE *tree)
{
  if(node->lo < tree->lo) {
    if(tree->child[0] == NULL)
      tree->child[0] = node;
    else
      insert_bdd(node, tree->child[0]);
  }
#if DEBUG
  else if(!(tree->lo < node->lo)) {
    fprintf(stderr, "insert_bdd: unexpected bounds\n");
  }
#endif
  else {
    if(tree->child[1] == NULL)
      tree->child[1] = node;
    else
      insert_bdd(node, tree->child[1]);
  }
}

/*
 *
 */

void free_bdd_node(BDDNODE *node)
{
  if(node == NULL)
    return;

  free_bdd_node(node->child[0]);
  free_bdd_node(node->child[1]);

  FREE(node);
}

/*
 *
 */

BDDNODE *output_bdd_sub(ARGS *args, int tot_cnt, int *mix, int *w,
                        int depth, int bound, BDDNODE *forest)
{
  BDDNODE *t, *f;
  BDDNODE *node = search_bdd(bound, &forest[depth]);

  if(node != NULL)
    return node;

#if DEBUG
  if(tot_cnt <= depth)
    fprintf(stderr, "error: tot_cnt = %i <= %i = depth\n", tot_cnt, depth);
#endif

  f = output_bdd_sub(args, tot_cnt, mix, w, depth + 1, bound,
                     forest);

  t = output_bdd_sub(args, tot_cnt, mix, w, depth + 1, bound - w[depth],
                     forest);

#if DEBUG
  if(!((f->lo <= bound) && (bound <= f->hi)))
    fprintf(stderr, "error: bound = %i \\notin [%i, %i] = [B_f, G_f]\n",
            bound, f->lo, f->hi);
  if(!((t->lo <= bound - w[depth]) && (bound - w[depth] <= t->hi)))
    fprintf(stderr, "error: bound = %i \\notin [%i, %i] = [B_t, G_t]\n",
            bound - w[depth], f->lo, f->hi);
#endif

  node = MALLOC(sizeof(BDDNODE));
  node->child[0] = NULL;
  node->child[1] = NULL;

  if(t->lo == f->lo) {

    node->literal = t->literal;
    node->lo = t->lo + w[depth];
    node->hi = t->hi;

  } else {

    /* Define a new atom to take the value of t->literal if mix[depth] is
     * true, and f->literal otherwise */

    int ite = -1;

    /* False branch */

    if(!SMX_IS_SPECIAL(f->literal)) {
      ite = args->newatom++;
      litint_output_normal(args, ite, 1, &f->literal);
    }

    /* True branch */

    if(!SMX_IS_SPECIAL(t->literal)) {
      int arr[2];
      arr[0] = mix[depth];
      arr[1] = t->literal;
      if(ite == -1)
        ite = args->newatom++;
      litint_output_normal(args, ite, 2, arr);
    } else {
      if(ite == -1)
        ite = mix[depth];
      else
        litint_output_normal(args, ite, 1, &mix[depth]);
    }

    node->literal = ite;
    node->lo = MAX(f->lo, t->lo + w[depth]);
    node->hi = MIN(f->hi, t->hi + w[depth]);
  }

  insert_bdd(node, &forest[depth]);

  return node;
}

/*
 * Output a sorter composed of shared ROBDDs
 */

void output_bdd_sorter(ARGS *args, int res_cnt, int *bounds, int *res,
                       int tot_cnt, int *mix, int *weight)
{
  BDDNODE * const forest = MALLOC((tot_cnt + 1) * sizeof(BDDNODE));
  int i, wsum;

  for(wsum = 0, i = tot_cnt; 0 <= i; wsum += (0 <= --i ? weight[i] : 0)) {

    BDDNODE * const f = &forest[i];
    BDDNODE * const t = MALLOC(sizeof(BDDNODE));

    f->lo = INT_MIN;
    f->hi = -1;
    f->literal = SMX_TRUE;
    f->child[0] = NULL;
    f->child[1] = t;

    t->lo = wsum;
    t->hi = INT_MAX;
    t->literal = SMX_FALSE;
    t->child[0] = NULL;
    t->child[1] = NULL;
  }

  for(i = 0; i < res_cnt; i++)
    res[i] = output_bdd_sub(args, tot_cnt, mix, weight,
                            0, bounds[i] - 1, forest)->literal;

  for(i = 0; i <= tot_cnt; i++) {
    free_bdd_node(forest[i].child[0]);
    free_bdd_node(forest[i].child[1]);
  }

  FREE(forest);
}

/*
 * WARNING: Changes the weight rule's negative array -- because it probably is
 *          not needed afterward
 * WARNING: Assumes that the given weight rule's positive atom array directly
 *          extends the negative one
 */

void output_bdd(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;
  int * const w = weight->weight;
  const int tot_cnt = weight->neg_cnt + weight->pos_cnt;
  int res = SMX_WANTED;

#if DEBUG
  if(weight->neg + weight->neg_cnt != weight->pos)
    fprintf(stderr, "output_bdd: pos does not come right after neg\n");
#endif

  litint_from_neg(weight->neg_cnt, weight->neg);
  permute_weighted_array_in_place(args, tot_cnt, weight->neg, w);

  output_bdd_sorter(args, 1, &weight->bound, &res,
                    tot_cnt, weight->neg, w);

#if DEBUG
  fprintf(stderr, "output_bdd: res = %s (%i)\n", ma2s(res), res);
#endif

  litint_output_1(args, weight->head, res);
}

#endif
