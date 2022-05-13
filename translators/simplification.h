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

#ifndef SIMPLIFICATION_H
#define SIMPLIFICATION_H

#include <stdio.h>    // for fprintf
#include <stdlib.h>   // for qsort

#include "args.h"
#include "litint.h"

/* ---------------------- Configuration ------------------------------------ */

/* Maximum number of "subleads" investigated in trim_trailing_weight_mix */
#define TTWM_SUBLEAD_MAX_CNT      3047

/* ---------------------- Light Weight Removal ---------------------------- */

/* for qsort */ 

static int compare_int_descending(const void *a, const void *b) 
{ 
  return *((const int *)b) - *((const int *)a); 
} 

/*
 * Generate new subleads and update the greatest of applicable sublead weights
 */

static int ttw_new_subleads(const int bound, const int r, const int i,
                            int * const weight, int * const w_sup,
                            int * const sublead_cnt,
                            const int N, int * const sublead_w)
{
  int k, j;
  const int w = weight[i - 1];

  for (k = r; k < i; k++) {

    /* The least sublead we do not want to add to because it is too big. */
    const int wlim = bound - w;

    const int jmin = (k ? sublead_cnt[k-1] : 0);
    
    /* Iterate over the subleads generated in the kth step in ascending order
     * (which is backwards in our case) */
    for (j = sublead_cnt[k] - 1; jmin <= j && sublead_w[j] < wlim; j--) {

      const int nw = sublead_w[j] + w;

      if (nw != sublead_w[sublead_cnt[i]-1] && nw != w_sup[i]) {
        /* The new weight migh be unique so we process it */

        if (sublead_cnt[i] >= N - 1) {
          /* Ran out of space for weights (and a sentinel) */
#if DEBUG
          fprintf(stderr, "TW ran out of space.\n");
#endif
          return 1;
        }

        if (w_sup[i] < nw)  /* The new weight is the greatest so far */
          w_sup[i] = nw;

        sublead_w[sublead_cnt[i]++] = nw;
      }
    }
  }

  return 0;
}

/*
 * Sort the most recently generated sublead weights and prune them
 */

static void ttw_prune_subleads(const int bound, const int significance,
                               const int i, const int tot_cnt,
                               int * const weight, int * const w_sup,
                               int * const sublead_cnt, int * const sublead_w)
{
  int j, k;

  /* Sort the sublead weights generated in the most recent round in ascending
   * order */
  qsort(&sublead_w[sublead_cnt[i-1]], 
        sublead_cnt[i] - sublead_cnt[i-1],
        sizeof(int), compare_int_descending);

  /* Mark unnecessary sublead weights for removal including duplicates, too
   * heavy and too light subleads. The iteration goes backwards to allow the
   * easy use of a sentinel. */

  sublead_w[sublead_cnt[i]] = 0;    /* Sentinel */
  int ts = 1, tb = 0;               /* Short cuts */

  /* Iterate over the most recently generated subleads in ascending order. */
  for (j = sublead_cnt[i] - 1; sublead_cnt[i-1] <= j; j--) {

    if (sublead_w[j] == sublead_w[j+1])
      sublead_w[j + 1] = 0;   /* Remove duplicate */
    else {
      /* True iff the sublead is so light that adding all trailing weights to
       * it would not be enough to affect significance */
      ts = ts && (sublead_w[j] < -significance);

      /* True iff the sublead is so heavy that adding the weight of the
       * lightest atom to it would take it to the bound or over it */
      tb = tb || (bound <= sublead_w[j] + weight[tot_cnt-1]);

      if ((ts || tb) && (sublead_w[j] != w_sup[i]))
        sublead_w[j] = 0;   /* Remove the weight */
    }
  }

  /* Remove any marked sublead weights while preserving the remaining weights
   * in sorted order */

  for (k = j = sublead_cnt[i-1]; j < sublead_cnt[i]; j++) {
    if (sublead_w[j]) {
      sublead_w[k++] = sublead_w[j];
    }
  }
  sublead_cnt[i] = k;
}

/*
 * trim_trailing_weight_mix -- Reduce traling atoms in a weight rule
 */

int trim_trailing_weight_mix(ARGS *args, int bound,
                             int tot_cnt, int *atom, int *weight)
{
#define SIGNIFICANCE(trailw, wsup) (trailw - (bound - wsup))

  const int enable_output = (args != NULL);

  /* These are for keeping track of the sums of all subsets of leading atoms'
   * weights that are below the bound excluding some pruned ones */
  const int N = TTWM_SUBLEAD_MAX_CNT;
  int sublead_w[TTWM_SUBLEAD_MAX_CNT];
  int * const sublead_cnt = (int *)MALLOC(tot_cnt * sizeof(int));

  /* These are used to keep track of the smallest significant weight */
  int * const w_sup = (int *)MALLOC(tot_cnt * sizeof(int));
  int * const trail_w = (int *)MALLOC(tot_cnt * sizeof(int));

  int i;
  int q = 0;

#if DEBUG
  int wups = 0;
#endif

  const int lsw = 1;  /* Least significant weight TODO: unnecessarily strict */

  /* Start with all atoms and their weight in the trailing part */
  trail_w[0] = 0;
  for(i = 0; i < tot_cnt; i++) {
    trail_w[0] += weight[i];
  }

  w_sup[0] = 0;
  sublead_w[0] = 0;
  sublead_cnt[0] = 1;

  /* Iterate until an uneventful pass is encountered */
  for(i = 0; !q && i < tot_cnt;) {

    /* Make a pass */
    //  && i < tot_cnt
    for(; !q; i++, trail_w[i] = trail_w[i-1] - weight[i-1],
        w_sup[i] = w_sup[i-1], sublead_cnt[i] = sublead_cnt[i-1]) {

      /* Assert i < tot_cnt */

      if(0 < i) {
        /* Generate new subleads and update the greatest of applicable sublead
         * weights w_sup[i] */

        /* Determine at which step to start going through sublead_w's */
        const int r = (1 < i && weight[i-2] == weight[i-1] ? i - 1 : 0);

        q = ttw_new_subleads(bound, r, i, weight, w_sup, sublead_cnt, N,
                             sublead_w);

        if(q)
          // TODO: This never happens!
          break;  /* Break out from both loops */
      }

      /* Break if there is no hope left */
      if(bound - w_sup[i] <= lsw) {

        // TODO: Test if this has any effect on the result

        q = 1;  /* Break out from both loops */
        break;
      }

      /* Compute the greatest difference the trailing atoms can make */
      const int significance = SIGNIFICANCE(trail_w[i], w_sup[i]);

      if(0 < i && i < tot_cnt - 1) {
        /* This is not the last run of this pass so we do some sorting and
         * pruning on the new sublead weights */

        ttw_prune_subleads(bound, significance, i, tot_cnt, weight, w_sup,
                           sublead_cnt, sublead_w);
      }

      if(significance < 0) {
#if DEBUG
        if(wups)
          fprintf(stderr, "WUPS: %d -> 1\n", wups);
        wups = 1;
#endif
        /* The trailing atoms can never make a difference so they can be
         * dropped completely */

        tot_cnt = i;

        if(tot_cnt == 0)
          break;  /* Break out from both loops */

        /* Rewind as long as the change in the weights makes a difference and
         * update the trailing weight for the (possible) consequent pass */
        int tmpw;
        for(tmpw = weight[tot_cnt-1]; 0 < i &&
            SIGNIFICANCE(tmpw, w_sup[i-1]) -
            enable_output*weight[tot_cnt-1] < 0;
            tmpw += weight[--i])
          ;
        trail_w[i] = tmpw;

        /* Begin the next pass */
        break;
      }

      if(enable_output &&
         significance - weight[tot_cnt-1] < 0 && i < tot_cnt - 1) {
#if DEBUG
        if(wups)
          fprintf(stderr, "WUPS: %d -> 2\n", wups);
        wups = 2;
#endif

        /* The trailing atoms can make a difference only when they are all
         * true, so we can AND them and sum their weights */

        const int auxatom = args->newatom++;
        litint_output_normal(args, auxatom, tot_cnt - i, &atom[i]);
        tot_cnt = i + 1;

        const int tmpw = trail_w[i];

        /* Find a place for the weight */
        for(; 0 < i && weight[i-1] < tmpw; i--) {
          atom[i] = atom[i-1];
          weight[i] = weight[i-1];
        }

        atom[i] = auxatom;
        weight[i] = tmpw;

        /* Rewind as long as the change in the weights makes a difference */
        for(; 0 < i &&
            SIGNIFICANCE(trail_w[i-1], w_sup[i-1]) - weight[tot_cnt-1] < 0;
            i--)
          ;

        /* Begin the next pass */
        break;
      }

      if(i + 1 == tot_cnt) {
        q = 1;  /* Break out from both loops */
        break;
      }
    }
  }

  FREE(sublead_cnt);
  FREE(trail_w);
  FREE(w_sup);
  return tot_cnt;
}

/* ---------------------- Heavy Weight Pair Simplification ---------------- */

/*
 * Return true if two consequtive weights in a sorted rule are equivalent
 */

int are_weights_equivalent(int bound, int cnt, int *w, int a,
                           int trail_has_been_trimmed)
{
  int i;
  const int b = a + 1;
  const int wa = w[a];
  const int wb = w[b];
  const int diff = wa - wb;

  /* Cheap checks */

  if(diff == 0)
    return 1;

  if(trail_has_been_trimmed && (w[cnt - 1] <= diff))

    /* FIXME: dead and probably untested code */

    return 0;

  /* Expensive check */

  /* Shift the weights starting from b to the left by one */

  for(i = b; i < cnt; i++)
    w[i - 1] = w[i];

  /* Append the difference, though it is not necessarily the smallest one */

  w[cnt - 1] = diff;

  /* Simplify */

  const int pruned_cnt = trim_trailing_weight_mix(NULL, bound, cnt, NULL, w);

  /* Restore the weight */

  for(i = cnt - 1; b <= i; i--)
    w[i] = w[i - 1];

  w[a] = wa;

  return (pruned_cnt < cnt);
}

/*
 * Try to replace heavy pairs with ORs
 * NOTE: Descendingly sorted input is wanted!
 */

int throw_out_weight_mix_pairs(ARGS *args, int bound, int head,
                               int cnt, int *atom, int *weight,
                               int trail_has_been_trimmed)
{
  int i, j, w1, w2, first_removed = INT_MAX, new_count = cnt;

  /* Skip weights that dominate alone */
  // TODO: This could possibly be forbidden for the sake of simplicity
  for(i = 0; i < cnt && bound <= weight[i]; i++) {

    if(first_removed == INT_MAX)
      first_removed = i;

    litint_output_normal(args, head, 1, &atom[i]);

    weight[i] = 0;  /* Mark the atom for removal */

    new_count--;
  }

  /* Iterate over all atom pairs that are heavy enough */
  for(; i < cnt - 1; i++) {

    w1 = weight[i];
    w2 = weight[i + 1];

    if(w1 + w2 < bound)
      break;

    if(are_weights_equivalent(bound, cnt, weight, i, /*i + 1,*/
                              trail_has_been_trimmed)) {

      /* Output an AND of the two atoms */
      litint_output_normal(args, head, 2, &atom[i]);

      if(i < cnt - 2) {  /* Insert the OR to the rule body and continue */

        /* Output an OR of the two atoms */
        const int aux_or = args->newatom++;
        litint_output_normal(args, aux_or, 1, &atom[i]);
        litint_output_normal(args, aux_or, 1, &atom[i + 1]);

        /* Mark the heavier atom for removal */
        weight[i] = 0;

        /* Replace the lighter atom in the rule with the auxiliary or */
        atom[i + 1] = aux_or;

        new_count--;

        if(first_removed == INT_MAX)
          first_removed = i;

      } else { /* Terminate */

        return 0; /* The given rule was consumed completely */
      }
    }
  }

  /* Remove marked atoms */
  for(j = i = first_removed; i < cnt; i++)
    if (weight[i]) {
      weight[j] = weight[i];
      atom[j] = atom[i];
      j++;
    }

  return new_count;
}

/* ---------------------- Required Weight Simplification ------------------ */

/*
 *
 */

int throw_out_weight_mix_needs(ARGS *args, int *bound, int *head,
                               int *cnt, int *body, int *weight)
{
  int i, wsum, a;

  for(wsum = 0, i = 0; i < *cnt; i++)
    wsum += weight[i];

  /* assert bound <= wsum */

  for(a = 0; (a < *cnt) && (wsum - weight[a] < *bound); a++)
    ;

  if(!a)
    return 0; /* Nothing was done */

  const int old_head = *head;
  int * const normal_part = (int *)MALLOC((a + 1) * sizeof(int));

  /* Allocate a new head */

  *head = args->newatom++;

  /* Output the normal part of the weight rule */

  for(i = 0; i < a; i++) {
    *bound -= weight[i];
    normal_part[i] = body[i];
  }

  if(0 < *bound) {

    normal_part[a] = *head;

    litint_output_normal(args, old_head, a + 1, normal_part);

    /* Shift the remaining elements in the body to the left */

    *cnt -= a;
    for(i = 0; i < *cnt; i++) {
      body[i] = body[i + a];
      weight[i] = weight[i + a];
    }
  } else { /* The rule corresponds to a normal rule */

    litint_output_normal(args, old_head, a, normal_part);
    *cnt = 0;
    *bound = 0;
  }

  FREE(normal_part);

  if(*cnt == 0)
    return -1; /* The rule was completely normalized */

  return 1; /* The rule was simplified */
}

/* ---------------------- Weight Residue Simplification ----------------- */

/*
 * pos_subset_sum_eq -- solve the positive subset sum problem
 */

int pos_subset_sum_eq(int n, int *value, int sum)
{
  /* This is the dynamic programming algorithm from wikipedia
   * (written here for positive inputs and nonzero target sum):
   * http://en.wikipedia.org/wiki/Subset_sum_problem
   * */

  int p, i, s;

  for(p = 0, i = 0; i < n; i++)
    p += value[i];

  if(p < sum)
    return 0;
  else if(p == sum)
    return 1;
  else if(sum*n <= 0)
    return 1;

  char * const q = (char *)MALLOC(n * sum * sizeof(char));

  for(s = 1; s <= sum; s++) {
    q[(s-1)*n] = (value[0] == s);
  }

  for(i = 1; i < n; i++) {
    const int v = value[i];

    for(s = 1; s <= sum; s++) {

      q[i + (s-1)*n] = q[i-1 + (s-1)*n] ||
                   (0 <= i-1 + (s-1-v)*n  && q[i-1 + (s-1-v)*n]) ||
                   (v == s);
    }
  }

  const int rvalue = q[sum*n-1];
  FREE(q);
  return rvalue;
}

/*
 * Divide the input and then solve the positive subset sum problem
 */

int pos_div_subset_sum_eq(int n, int *value, int sum, int divisor)
{
  int i;
  int * const quotient = (int *)MALLOC(n * sizeof(int));

  for (i = 0; i < n; i++)
    quotient[i] = value[i] / divisor;

  const int rvalue = pos_subset_sum_eq(n, quotient, sum / divisor);

  FREE(quotient);
  return rvalue;
}

/*
 *
 */

int divide_weight_if_free(int bound, int cnt, int *weight, int divisor)
{
  const int bound_r = bound % divisor;
  int sum_r = 0;
  int min_r = INT_MAX;
  int onzr_i = -1;
  int i;

  // bound_r -> divisor
  // TODO: Fix bound.
  for(i = 0;
      i < cnt && (sum_r < divisor || bound_r <= min_r || onzr_i != -2);
      i++) {

    const int w_r = weight[i] % divisor;

    if (w_r < min_r)
      min_r = w_r;

    if(w_r) {

      sum_r += w_r;

      if(0 <= onzr_i)
        onzr_i = -2;
      else if(onzr_i == -1)
        onzr_i = i;
    }
  }

  if(sum_r < divisor) {

    if(bound_r <= min_r) {

      /* Any body literal is enough to satisfy the residue bound -- transform
         to a non-strict inequality of quotients */

      bound = bound / divisor;
      for(i = 0; i < cnt; i++)
        weight[i] /= divisor;

    } else if((sum_r < bound_r)
           || !pos_div_subset_sum_eq(cnt, weight, bound, divisor)) {

      /* The residue bound can not be satisfied or it does not matter whether
         it can be -- transform to a strict inequality of quotients */

      bound = bound / divisor + 1;
      for (i = 0; i < cnt; i++)
        weight[i] /= divisor;

    } else if(0 <= onzr_i) {

      /* There is only one non-zero body residue -- transform to a strict
         inequality of quotients and increase the weight's quotient */

      bound = bound / divisor + 1;
      for(i = 0; i < cnt; i++)
        weight[i] /= divisor;

      weight[onzr_i]++;
    }
  }

  return bound;
}

/*
 * Try to divide the bound and weights in a weight rule until total failure
 */

int divide_weight_if_free_loop(int bound, int cnt, int *weight)
{
  int i, p, r;
  int max_i = 0;
  for(i = 1; i < cnt; i++)
    if(weight[max_i] < weight[i])
      max_i = i;

  /* Go through primes */
  for(i = 0; i < PRIME_COUNT;) {
    for(i = 0; i < PRIME_COUNT; i++) {
      p = prime_array[i];
      if(weight[max_i] < p) {
        i = PRIME_COUNT;
        break;
      }
      r = divide_weight_if_free(bound, cnt, weight, p);
      if(r != bound) {
        bound = r;
        break;
      }
    }
  }

  return bound;
}

/*
 * Try to reduce weight in a weight rule by dividing and flooring
 */

int reduce_weight_loop(int bound, int cnt, int *weight)
{
  while (1) {

    const int newbound = divide_weight_if_free_loop(bound, cnt, weight);
    if (newbound == bound)
      break;
    bound = newbound;

//    if (!trim_weight_residue_loop(bound, cnt, weight))
//      break;
  }

  return bound;
}

/* ------------------------------------------------------------------------ */

/*
 * simplify_weight -- Simplify a weight rule in a number of ways
 */

int simplify_weight(int style, FILE *out, WEIGHT_RULE *weight, ATAB *table)
{
  int *scan = NULL, *copy = NULL, *last = NULL;
  int *w = NULL, *copyw = NULL;
  int bound = weight->bound, head = weight->head;
  int div = bound;
  int *neg = weight->neg, *pos = weight->pos;
  int neg_cnt = weight->neg_cnt, pos_cnt = weight->pos_cnt;

  /* Go through all negative literals and the respective weights */

  for(scan = neg, copy = neg, last = &neg[neg_cnt],
      w = weight->weight, copyw = w; scan != last; scan++, w++) {

    if(*w >= bound)
      /* This negative literal is sufficient alone */
      output_normal(style, out, head, 0, NULL, 1, scan, table);

    if(*w == 0 || *w >= bound) {
      /* Delete this negative literal */
      weight->neg_cnt = (--neg_cnt);
    } else {
      /* Preserve this negative literal */
      *copy++ = *scan;
      div = gcd(div, *w);
      *copyw++ = *w;
    }
  }

  /* Go through all positive literals and the respective weights */

  for(scan = pos, copy = scan, last = &pos[pos_cnt]; scan != last;
      scan++, w++) {

    if(*w >= bound)
      /* This positive literal is sufficient alone */
      output_normal(style, out, head, 1, scan, 0, NULL, table);

    if(*w == 0 || *w >= bound) {
      /* Delete this positive literal */
      weight->pos_cnt = (--pos_cnt);
    } else {
      /* Preserve this positive literal */
      *copy++ = *scan;
      div = gcd(div, *w);
      *copyw++ = *w;
    }
  }

  weight->bound /= div;

  for(w = weight->weight, last = &w[neg_cnt+pos_cnt]; w != last; w++)
    *w /= div;

  return div;
}

/*
 *
 */

int simplify_weight_more(int style, FILE *out, RULE *rule,
		         ATAB *table, uint64_t flavors)
{
  int pos_cnt = 0, neg_cnt = 0, bound = 0, *weights = NULL;
  int sum = 0, div = 0;
  int i = 0;

  WEIGHT_RULE *weight = rule->data.weight;

  /* Perform preliminary simplifications */

  bound = weight->bound;
  if(bound>0) {
    weights = weight->weight;    
    pos_cnt = weight->pos_cnt;
    neg_cnt = weight->neg_cnt;

    for(i=0;i<pos_cnt+neg_cnt;i++)
      sum += weights[i];
    if(!(flavors & FL_RAW)) {
      div = simplify_weight(style, out, weight, table);
      sum /= div;
      bound /= div;
    }

    if(sum < bound)
      /* The body cannot be satisfied -- drop the whole rule */
      return 0;

    if(sum == bound) {
      /* The rule can be turned into a normal one directly */

      output_normal(style, out, weight->head,
		    pos_cnt, weight->pos, neg_cnt, weight->neg, table);
      return 0;
    }
      
  } else {
    /* The body is trivially satisfied -- create a fact */

    output_normal(style, out, weight->head, 0, NULL, 0, NULL, table);

    return 0;
  }

  return sum;
}

/* ------------------------------------------------------------------------ */

/*
 * Try to divide a weight rule with the gcd of all but one of its weights
 */

int simplify_weight_using_gcd(int *bound, int cnt, int *weight)
{
  if(cnt <= 0)
    return 0;

  int i;
  int *aux = MALLOC((cnt + 1) * sizeof(int));

  /* Compute cumulative gcds one way */

  aux[cnt] = weight[cnt - 1];
  for(i = cnt - 1; 0 <= i; i--)
    aux[i] = gcd(weight[i], aux[i + 1]);

  /* Compute cumulative gcds the other way, and pick the index whose exclusion
   * gives the maximum gcd */

  int best_div = 0;
  int best_idx = 0;
  int tmp = weight[0];
  for(i = 0; i < cnt; i++) {
    int div = gcd(tmp, aux[i + 1]);
    if(best_div < div) {
      best_div = div;
      best_idx = i;
    }
    tmp = gcd(tmp, weight[i]);
  }

  FREE(aux);

  if(best_div <= 1)
    return 0;

  /* Update the weight rule */

  int bound_rem = *bound % best_div;
  int bound_quo = *bound / best_div;

  if((tmp != best_div)
      && (bound_rem != 0)
      && (bound_rem <= (weight[best_idx] % best_div)))
    weight[best_idx] += best_div;
  
  *bound = bound_quo + (bound_rem != 0);
  for(i = 0; i < cnt; i++)
    weight[i] /= best_div;

  return 1;
}

/*
 * Simplify a descending mixed weight rule in a number of ways
 */

int simplify_weight_mix_basic(ARGS *args, int *bound, int *head,
                              int *cnt, int *body, int *weight)
{
  int i;
  int a, b;
  int div, wsum;

  if(bound == 0) {

    /* The body is trivially satisfied; so create a fact */

    litint_output_normal(args, *head, 0, NULL);
    return -1;
  }

  /* Output literals with dominating weights */

  for(a = 0; a < *cnt && *bound <= weight[a]; a++)
    litint_output_normal(args, *head, 1, &body[a]);

  /* Skip weights equal to zero */

  for(b = *cnt; a < b && weight[b - 1] == 0; b--)
    ;

  /* Count the sum of the remaining weights */

  for(wsum = 0, i = a; i < b; i++)
    wsum += weight[i];

  if((*bound <= wsum) && (wsum - weight[b - 1] < *bound)) {

    /* The remaining rule corresponds to a single basic rule */

    litint_output_normal(args, *head, (b - a), &body[a]);

    return -1;
  }

  if(wsum < *bound)

    /* The remaining rule is never satisfied */

    return -1;

#if 1
  /* Try gcd simplification, and return if nothing worked */

  if (!simplify_weight_using_gcd(bound, b - a, weight + a)
      && (a == 0) && (b == *cnt))
    return 0;

  /* Update and reposition the rule */

  *cnt = b - a;

  if(a != 0)
    for(i = 0; a + i < b; i++) {
      body[i] = body[a + i];
      weight[i] = weight[a + i];
    }

  return 1;


#else

  /* Compute the gcd */

  for(div = weight[a], i = a + 1; i < b; i++)
    div = gcd(div, weight[i]);

  /* Return if nothing changed nor would change */

  if(a == 0 && b == *cnt && div == 1)
    return 0;

  /* Divide the weights with their gcd and update the arrays */

  *bound = (*bound / div) + ((*bound % div) != 0);
  *cnt = b - a;

  for(i = 0; a + i < b; i++) {
    body[i] = body[a + i];
    weight[i] = weight[a + i] / div;
  }

  return 1;
#endif
}

/*
 *
 */

int simplify_weight_mix_needs(ARGS *args, int *bound, int *head,
                              int *cnt, int *body, int *weight)
{
  return throw_out_weight_mix_needs(args, bound, head, cnt, body, weight);
}

/*
 *
 */

int simplify_weight_mix_pairs(ARGS *args, int bound, int head,
                              int *cnt, int *body, int *weight)
{
  const int trail_has_been_trimmed = 0; // TODO: Perhaps "carry" from somewhere
  const int old_cnt = *cnt;

  *cnt = throw_out_weight_mix_pairs(args, bound, head,
                                    old_cnt, body, weight,
                                    trail_has_been_trimmed);

  if(*cnt == old_cnt)

    /* The rule was left untouched */

    return 0;

  if(*cnt == 0)

    /* The rule was devoured completely */

    return -1;

  /* The rule was simplified */

  return 1;
}

/*
 * Possibly remove traling atoms in a descending mixed weight rule
 */

int simplify_weight_mix_trail(ARGS *args, int bound, int *cnt,
                              int *body, int *weight)
{
  const int old_cnt = *cnt;

  *cnt = trim_trailing_weight_mix(args, bound, old_cnt, body, weight);

  if(*cnt == old_cnt)

    /* The rule was left untouched */

    return 0;

  if(*cnt == 0)

    /* The rule was devoured completely */

    return -1;

  /* The rule was modified */

  return 1;
}

/*
 *
 */

int simplify_weight_mix_prime(int *bound, int *cnt, int *body, int *weight)
{
  int i, j;
  const int old_bound = *bound;
  const int old_cnt = *cnt;

  *bound = reduce_weight_loop(old_bound, old_cnt, weight);

  /* Remove body literals with zero weights */

  for(j = i = 0; i < old_cnt; i++)
    if(weight[i]) {
      body[j] = body[i];
      weight[j] = weight[i];
      j++;
    }

  *cnt = j;

  if((*bound == old_bound) && (*cnt == old_cnt))

    /* The rule was left untouched */

    return 0;

  if(*cnt == 0)

    /* The rule was devoured completely */

    return -1;

  /* The rule was simplified */

  return 1;
}

/*
 * Try to simplify a weight rule
 * Returns -1   if the rule was simplified away completely
 *          0   if nothing was done
 *          1   if the rule was partially simplified
 */

int simplify_weight_mix(ARGS *args, int *bound, int *head,
                        int *cnt, int *body, int *weight)
{
  const int TRAIL = 1, PRIME = 2, PAIRS = 3, NEEDS = 4, EOW = 5;

  uint64_t flavors = args->flavors;
  int end_of_time = EOW;
  int modified = 0;
  int r = 0;

  if(*cnt == 0)
    return 0;

  r = simplify_weight_mix_basic(args, bound, head, cnt, body, weight);
  if(r < 0)
    return -1;
  
  modified = r;

  while(1) {

    if((flavors & FL_WT_NORM_PART) == FL_WT_NORM_PART) {
      if(end_of_time == NEEDS)
        break;
      r = simplify_weight_mix_needs(args, bound, head,
                                    cnt, body, weight);
      if(0 < r) {
        end_of_time = NEEDS;
        r = simplify_weight_mix_basic(args, bound, head, cnt, body, weight);
      }
      if(r < 0)
        break;
    }

    if((flavors & FL_WT_THROW_PAIR) == FL_WT_THROW_PAIR) {
      if(end_of_time == PAIRS)
        break;
      r = simplify_weight_mix_pairs(args, *bound, *head, cnt, body, weight);
      if(0 < r) {
        end_of_time = PAIRS;
        r = simplify_weight_mix_basic(args, bound, head, cnt, body, weight);
      }
      if(r < 0)
        break;
    }

    if((flavors & FL_WT_TRIM) == FL_WT_TRIM) {
      if(end_of_time == TRAIL)
        break;
      r = simplify_weight_mix_trail(args, *bound, cnt, body, weight);
      if(0 < r) {
        end_of_time = TRAIL;
        r = simplify_weight_mix_basic(args, bound, head, cnt, body, weight);
      }
      if(r < 0)
        break;
    }

    if((flavors & FL_WT_PRIME) == FL_WT_PRIME) {
      if(end_of_time == PRIME)
        break;
      r = simplify_weight_mix_prime(bound, cnt, body, weight);
      if(0 < r) {
        end_of_time = PRIME;
        r = simplify_weight_mix_basic(args, bound, head, cnt, body, weight);
      }
      if(r < 0)
        break;
    }

    if(end_of_time == EOW)
      break;

    modified = 1;
  }

  if(r < 0)
    return -1;

  return modified;
}

/*
 *
 */

int simplify_weight_2(ARGS *args, RULE *rule)
{
  int i;
  WEIGHT_RULE *weight = rule->data.weight;
  int bound = weight->bound, head = weight->head;
  int *neg = weight->neg, *pos = weight->pos;
  int neg_cnt = weight->neg_cnt, pos_cnt = weight->pos_cnt;
  int tot_cnt = neg_cnt + pos_cnt;
  int new_cnt, new_pos_cnt, new_neg_cnt;

  int * const sorted_body = (int *)MALLOC(tot_cnt * sizeof(int));
  int * const sorted_weight = (int *)MALLOC(tot_cnt * sizeof(int));

  /* Sort the body and weights according to the weights */
  sort_body_descending(pos_cnt, pos, neg_cnt, neg, weight->weight,
                       sorted_body, sorted_weight);

  /* Perform the simplifications */
  new_cnt = tot_cnt;
  const int r =
    simplify_weight_mix(args, &bound, &head,
                        &new_cnt, sorted_body, sorted_weight);

  if(r) {

    /* The simplifications had an effect -- update the rule */

    /* Compute (possibly) new positive and negative counts */
    for(new_neg_cnt = i = 0; i < new_cnt; i++)
      if(MIX_IS_NEG(sorted_body[i]))
        new_neg_cnt++;
    new_pos_cnt = new_cnt - new_neg_cnt;

    /* Reposition the positive array to come right after the negative one */
    /* To understand this you might have to take a look at input.c */
    pos = &neg[new_neg_cnt];
    weight->pos = pos;

    /* Transfer the sorted body and weight back into the weight rule */
    for(i = 0, neg_cnt = 0, pos_cnt = 0; i < new_cnt; i++) {
      if(MIX_IS_NEG(sorted_body[i])) {
        weight->weight[neg_cnt] = sorted_weight[i];
        neg[neg_cnt++] = MIX_GET_ATOM(sorted_body[i]);
      } else {
        weight->weight[new_neg_cnt+pos_cnt] = sorted_weight[i];
        pos[pos_cnt++] = sorted_body[i];
      }
    }

    weight->head = head;
    weight->bound = bound;
    weight->pos_cnt = pos_cnt;
    weight->neg_cnt = neg_cnt;
  }

  FREE(sorted_body);
  FREE(sorted_weight);

  return r;
}

#endif
