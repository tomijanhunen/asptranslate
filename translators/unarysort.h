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
 * Odd-even, Totalizer-based and Automated Merge-Sorting
 * as well as Sequential Sorting
 *
 * (c) 2014 Jori Bomanson
 */

#ifndef MERGESORT_H
#define MERGESORT_H

#include <stdio.h>

//#include "atom.h"

#include "common.h"
#include "args.h"
#include "litint.h"

/* ------------------------------------------------------------------------- */

#define UNARY_MERGER_TRICK        1
#define DEBUG_MERGESORT           ((DEBUG) && 0)
#define DEBUG_SEQ                 ((DEBUG) && 0)
#define DEBUG_LEAST               ((DEBUG) && 0)

/* A boolean controlling whether output_least_* functions guard against
 * recursive branching by checking for STYLE_DEV_NULL or not */
#define LEAST_GUARD_DEV_NULL      1

/* An upper bound on output_least_* recursion depth.  This takes effect only
 * if LEAST_GUARD_DEV_NULL is true. */
#define LEAST_GUARD_DEPTH         2

/* ------------------------------------------------------------------------- */

void output_unary_merger(ARGS *args, int bound, int *s,
                         int n_p, int *p, int n_q, int *q,
                         int p_dominates_q, int startatom);

void output_unary_merger_f(ARGS *args, int bound, int *s,
                           int n_p, int *p, int n_q, int *q,
                           int p_dominates_q, int startatom,
                           uint64_t flavors);

void output_unary_sorter(ARGS *args, int bound, int *res,
                         int tot_cnt, int *mix, int *startatom);

void output_unary_sorter_f(ARGS *args, int bound, int *res,
                           int tot_cnt, int *mix, int *startatom,
                           uint64_t flavors);

/* ---- Private-ish -------------------------------------------------------- */

int greatest_exp2_le(int x)
{
  x |= x >> 1;
  x |= x >> 2;
  x |= x >> 4;
  x |= x >> 8;
  x |= x >> 16;
  return ((x+1) >> 1);
}

/*
 * Return an estimation of the difficulty of dealing with a (sub)program that
 * contains the given numbers of atoms and rules.
 */

int get_atom_and_rule_cost(int atom_cnt, int rule_cnt)
{
  return atom_cnt + rule_cnt;
}

/* ------------------------------------------------------------------------- */

/* ===================== Odd=even and Totalizer-based Sorting ============= */

void output_oe_comparator(ARGS *args, int bound, int *s, int x, int y,
                          int startatom)
{
  const int w_s1 = ((2 <= bound) && SMX_IS_WANTED(s[1]));
  // FIXME: These conditions are not sufficient
  const int r_x = ((startatom <= x) && !w_s1);
  const int r_y = ((startatom <= y) && !w_s1);

#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- comparator(%s, %s)\n",
          a2x(MIN(bound, 2), s), ma2s(x), ma2s(y));
#endif

  litint_output_ifw_1x2(args, s, x, r_x, y, r_y);

  if(w_s1)
    litint_output_ifw_2(args, &s[1], x, y);
}

void output_oe_pair_sorter(ARGS *args, int bound, int *s, int stride,
                           int n_x, int *x, int n_y, int *y,
                           int output_identity, int startatom)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- pair_sorter(%s, %s)\n",
          a2x(MIN(bound, n_x + n_y), s),
          a2y(n_x, stride, x), a2y(n_y, stride, y));
#endif

  if(!n_x || !n_y || output_identity) {
    int i;
    for(i = 0; (i < n_x) && (i < bound); i++)
      s[i] = litint_output_new_1(args, x[stride * i], 1);
    for(i = 0; (i < n_y) && (n_x + i < bound); i++)
      s[n_x + i] = litint_output_new_1(args, y[stride * i], 1);
    return;
  }

  output_oe_comparator(args, bound, s, *x, *y, startatom);
}

void output_oe_balanced_merger(ARGS *args, int bound, int *s,
                               int n_d, int *d,
                               int n_e, int *e,
                               int startatom)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- balanced_merger(%s, %s)\n",
          a2x(MIN(bound, n_d + n_e), s), a2x(n_d, d), a2x(n_e, e));
#endif

  const int k = MIN(bound, n_d + n_e);
  int i;

  litint_output_ifw_1(args, s, *d, 1);

  for(i = 0; (i < n_d - 1) && (i < n_e) && (2 * i + 1 < k); i++)
    output_oe_pair_sorter(args, k - (2 * i + 1), &s[2 * i + 1],
                          1, 1, &d[i + 1], 1, &e[i], 0, startatom);

  if((n_d == n_e + 1) || (k != n_d + n_e))
    return;

  if(n_d == n_e)
    litint_output_ifw_1(args, &s[k - 1], e[n_e - 1], 1);
  else
    litint_output_ifw_1(args, &s[k - 1], d[n_d - 1], 1);
}

void propagate_oe_balanced_merger_w_x(int bound, int *s,
                                      int n_d, int *d,
                                      int n_e, int *e)
{
  const int k = MIN(bound, n_d + n_e);
  int i;

  *d = *s;

  for(i = 0; (i < n_d - 1) && (i < n_e); i++)
    d[i + 1]
      = e[i]
      = (((2 * i + 1 < k) && SMX_IS_WANTED(s[2 * i + 1]))
          || ((2 * i + 2 < k) && SMX_IS_WANTED(s[2 * i + 2]))
          ? SMX_WANTED
          : SMX_DONT_CARE);

  if(n_d != n_e + 1)
    *(n_d == n_e ? &e[n_e - 1] : &d[n_d - 1])
      = (k < n_d + n_e ? SMX_DONT_CARE : s[n_d + n_e - 1]);

#if DEBUG_MERGESORT
  fprintf(stderr, "Merger-B.M.: inferred from wanted results"
                  ", the wanted odd and even inputs: %s, %s, %s\n",
                  a2x(k, s), a2x(n_d, d), a2x(n_e, e));
#endif
}

void output_oe_merger_sub(ARGS *args, int bound, int *s,
                          int divisor, int residue,
                          int n_p, int *p,
                          int n_q, int *q,
                          int p_dominates_q, int startatom)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- merger(%s, %s)\n",
          a2x(MIN(bound, n_p + n_q), s),
          a2y(n_p, divisor, &p[residue]), a2y(n_q, divisor, &q[residue]));
#endif

  if(n_p * n_q <= 1) {
    output_oe_pair_sorter(args, bound, s, divisor,
                          n_p, &p[residue],
                          n_q, &q[residue],
                          p_dominates_q, startatom);
    return;
  }

  const int n_pe = n_p / 2;
  const int n_pd = n_p - n_pe;
  const int n_qe = n_q / 2;
  const int n_qd = n_q - n_qe;
  const int n_d = n_pd + n_qd;
  const int n_e = n_pe + n_qe;
  int * const d = (int *)MALLOC(n_d * sizeof(int));
  int * const e = (int *)MALLOC(n_e * sizeof(int));

  propagate_oe_balanced_merger_w_x(bound, s, n_d, d, n_e, e);

  output_oe_merger_sub(args, bound, d, 2 * divisor, residue,
                       n_pd, p, n_qd, q, p_dominates_q, startatom);
  output_oe_merger_sub(args, bound, e, 2 * divisor, divisor + residue,
                       n_pe, p, n_qe, q, p_dominates_q, startatom);
  output_oe_balanced_merger(args, bound, s, n_d, d, n_e, e, startatom);

  FREE(d);
  FREE(e);
}

void output_oe_merger(ARGS *args, int bound, int *s,
                      int n_p, int *p,
                      int n_q, int *q,
                      int p_dominates_q, int startatom)
{
  output_oe_merger_sub(args, bound, s, 1, 0, n_p, p, n_q, q,
                       p_dominates_q, startatom);
}

/*
 * Output rules for computing the unary sum of two unary numbers
 */

void output_totalizing_merger(ARGS *args, int bound, int *s,
                              int n_p, int *p,
                              int n_q, int *q,
                              int p_dom_q)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- merging_totalizer(%s, %s)\n",
          a2x(MIN(bound, n_p + n_q), s), a2x(n_p, p), a2x(n_q, q));
#endif

  const int k = MIN(bound, n_p + n_q);
  int i, j, r, t, head;

  for(i = 1; i <= k; i++) {
    if(!SMX_IS_WANTED(s[i - 1]))
      continue;

    r = (p_dom_q ? i / 2 : i);
    r = MIN(r, n_q);

    head = SMX_FALSE;

#if DEBUG_MERGESORT
    fprintf(stderr, "Inspecting %i\n", i);
#endif

    for(t = r, j = i - t; (j <= i) && (0 <= t) && (j <= n_p); j++, t--) {
      const int x = (j && (!p_dom_q || (t != j)) ? p[j - 1] : SMX_DONT_CARE);
      const int y = (t ? q[t - 1] : SMX_DONT_CARE);

#if DEBUG_MERGESORT
      fprintf(stderr, "Considering %s & %s\n", ma2s(x), ma2s(y));
#endif

      if(SMX_IS_FALSE(x) || SMX_IS_FALSE(y))
        continue;

      int z;
      if(SMX_IS_TRUE(x) || SMX_IS_DONT_CARE(x))
        z = y;
      else if(SMX_IS_TRUE(y) || SMX_IS_DONT_CARE(y))
        z = x;
      else
        z = 0;

      if(SMX_IS_TRUE(z) || !SMX_IS_SPECIAL(z)) {
        head = z;
        break;
      } else if(SMX_IS_DONT_CARE(z))
        head = z;
    }

#if DEBUG_MERGESORT
    fprintf(stderr, "Inspected %i -> %s\n", i, ma2s(head));
#endif

    if(SMX_IS_SPECIAL(head)) {
      s[i - 1] = head;
      continue;
    }

    head = args->newatom++;
    s[i - 1] = head;

    for(t = r, j = i - t; (j <= i) && (0 <= t) && (j <= n_p); j++, t--) {
      int x = (j && (!p_dom_q || (t != j)) ? p[j - 1] : SMX_DONT_CARE);
      int y = (t ? q[t - 1] : SMX_DONT_CARE);

      if(SMX_IS_FALSE(x) || SMX_IS_FALSE(y))
        continue;

      if(!SMX_IS_SPECIAL(x) && !SMX_IS_SPECIAL(y))
        litint_output_2(args, head, x, y);
      else if(!SMX_IS_SPECIAL(x))
        litint_output_normal(args, head, 1, &x);
      else if(!SMX_IS_SPECIAL(y))
        litint_output_normal(args, head, 1, &y);
    }
  }
}

void propagate_merger_w(int bound, int *res, int n_p, int *p,
                        int n_q, int *q, int p_dominates_q,
                        int *dominating, int *dominated)
{
  const int k = MIN(bound, n_p + n_q);
  int i, j, t, dummy;

  if(dominating == NULL)
    dominating = &dummy;
  if(dominated == NULL)
    dominated = &dummy;

  *dominating = SMX_DONT_CARE;
  *dominated = SMX_DONT_CARE;

  /* If there exists i = j + t for some j > t, such that res[i-1] is wanted,
     then both p[j-1] and q[t-1] are wanted as well,
     and on the other hand if j == t, then q[t-1] is wanted */

  for(i = 1; i <= k; i++) {
    if(!SMX_IS_WANTED(res[i - 1]))
      continue;
    t = (p_dominates_q ? i / 2 : i);
    t = MIN(t, n_q);
    for(j = i - t; (j <= i) && (0 <= t) && (j <= n_p); j++, t--) {
      if(j && !SMX_IS_WANTED(p[j - 1]) && (!p_dominates_q || (t != j)))
        p[j - 1] = *dominating = SMX_WANTED;
      if(t && !SMX_IS_WANTED(q[t - 1]))
        q[t - 1] = *dominated = SMX_WANTED;
    }
  }

#if DEBUG_MERGESORT
  fprintf(stderr, "Sorter-Merger: inferred from wanted results"
                  ", the wanted left and right inputs: %s, %s, %s\n",
                  a2x(k, res), a2x(n_p, p), a2x(n_q, q));
#endif
}

void propagate_merger_w_x(int bound, int *res, int n_p, int *p,
                             int n_q, int *q, int pw,
                             int *dominating, int *dominated)
{
  int_array_fill(n_p, p, SMX_DONT_CARE);
  int_array_fill(n_q, q, SMX_DONT_CARE);
  propagate_merger_w(bound, res, n_p, p, n_q, q, pw, dominating, dominated);
}

/*
 * WARNING: Works in place
 * NOTE: It is assumed that m < n
 */

void output_splitter(ARGS *args, int n, int *a, int m, int *b,
                     int startatom, int dominating, int dominated)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output splitter(%s, %s)\n", a2x(n, a), a2x(m, b));
#endif

  int i, s[2];

  for(i = 0; i < m; i++) {
    s[0] = dominating;
    s[1] = dominated;
    output_oe_comparator(args, 2, s, a[i], b[i], startatom);
    a[i] = s[0];
    b[i] = s[1];
  }
}

/*
 * Output a unary merge sorter
 *
 * WARNING: alters the mix array if flavors & FL_CO_REC_SORT_PW is nonzero
 */

void output_merge_sorter(ARGS *args, int bound, int *res, int tot_cnt, int *mix,
                      int startatom)
{
#if DEBUG_MERGESORT
  fprintf(stderr, "Output %s <- sorter(%s)\n",
          a2x(bound, res), a2x(tot_cnt, mix));
#endif

  if(tot_cnt <= 2) {
    output_oe_pair_sorter(args, bound, res, 1,
                          (1 <= tot_cnt), &mix[0],
                          (2 <= tot_cnt), &mix[1], 0, startatom);
    return;
  }

  const int pw = ((args->flavors & FL_CO_REC_SORT_PW) != 0);
  const int n = (args->flavors & FL_CO_REC_SORT_EXP2
                ? greatest_exp2_le(tot_cnt - 1)
                : (tot_cnt + 1) / 2);
  const int m = tot_cnt - n;
  const int w_n = MIN(n, bound);
  const int w_m = MIN(m, (pw ? bound / 2 : bound));
  int * const aux = (int *)MALLOC((w_n + w_m) * sizeof(int));

  int dominating, dominated;

  propagate_merger_w_x(bound, res, w_n, aux, w_m, &aux[w_n], pw,
                          &dominating, &dominated);

  if(args->flavors & FL_CO_REC_SORT_PW)
    output_splitter(args, n, mix, m, &mix[n],
                    startatom, dominating, dominated);

  if(SMX_IS_WANTED(dominating))
    output_merge_sorter(args, w_n, aux, n, mix, startatom);

  if(SMX_IS_WANTED(dominated))
    output_merge_sorter(args, w_m, &aux[w_n], m, &mix[n], startatom);

  output_unary_merger(args, bound, res, w_n, aux, w_m, &aux[w_n],
                      pw, startatom);

  FREE(aux);
}

/* ========================= Selectors ==================================== */

/*
 * Create a partition for input literals
 */

int assign_literals_to_chunks(int **chunk_out, int res_cnt, int tot_cnt,
                              uint64_t flavors)
{
  int i;
  const int sorter_cnt = (tot_cnt + res_cnt - 1) / res_cnt;

  int * const o_cnt = (int *)MALLOC(sorter_cnt * sizeof(int));

#if 0

  /* Distribute the input into as many bound-sized sorters as possible, and 
     leave the last one possibly underused */

  for(i = 0; i < sorter_cnt - 1; i++)
    o_cnt[i] = res_cnt;

  o_cnt[sorter_cnt - 1] = tot_cnt - (sorter_cnt - 1) * res_cnt;

#else

  /* Try to distribute the input evenly */

  const int over = sorter_cnt * res_cnt - tot_cnt;
  const int over_quotient = over / sorter_cnt;
  const int over_residue = over - over_quotient * sorter_cnt;
  const int base_bound = res_cnt - over_quotient;

  const int over_period = (over_residue
                           ? (sorter_cnt) / over_residue
                           : INT_MAX);

  const int over_offset = (over_residue
                          ? ((sorter_cnt + over_period - 1) / over_period
                            - over_residue) * over_period
                          : 0);

  o_cnt[0] = base_bound - ((over_offset <= 0) && (over_period != INT_MAX));

  for(i = 1; i < sorter_cnt; i++)
    o_cnt[i] = base_bound - ((over_offset <= i) && ((i % over_period) == 0));

#endif

  *chunk_out = o_cnt;

  return sorter_cnt;
}

/*
 * Output a unary selecter based on odd-even sorters
 */

void output_oe_selecter(ARGS *args, int bound, int *res, int tot_cnt,
                        int *mix, int *startatom)
{
  if(tot_cnt / 2 <= bound) {
    output_unary_sorter_f(args, bound, res, tot_cnt, mix, startatom,
                          args->flavors & ~FL_CO_SELECT);
    return;
  }

  int i, j, pos, chk, cnt[3], *aux[3], *sav[3], *chk_cnt;
  const int srt_cnt
    = assign_literals_to_chunks(&chk_cnt, bound, tot_cnt, args->flavors);

  for(i = 0; i < 3; i++)
    sav[i] = aux[i] = (int *)MALLOC(bound * sizeof(int));

  for(pos = 0, i = 0; i < srt_cnt; i++, pos += chk) {

    chk = cnt[1] = chk_cnt[i];

    for(j = 0; j < cnt[1]; j++)
      aux[1][j] = SMX_WANTED;

#if DEBUG_MERGESORT
    fprintf(stderr, "Output %s <- sorter(%s)\n",
            a2x(cnt[1], aux[1]), a2x(cnt[1], &mix[pos]));
#endif

    output_unary_sorter(args, cnt[1], aux[1], cnt[1], &mix[pos], startatom);

    if(i) {

      cnt[2] = bound;

      if(i + 1 < srt_cnt)
        for(j = 0; j < cnt[2]; j++)
          aux[2][j] = SMX_WANTED;
      else
        aux[2] = res;

#if DEBUG_MERGESORT
      fprintf(stderr, "Output %s <- merger(%s, %s)\n",
              a2x(cnt[2], aux[2]), a2x(cnt[0], aux[0]), a2x(cnt[1], aux[1]));
#endif

      output_unary_merger(args, cnt[2], aux[2], cnt[0], aux[0], cnt[1], aux[1],
                          0, *startatom);
    }

    const int r = (i == 0 ? 1 : 2);
    int * const t = aux[0];
    aux[0] = aux[r];
    aux[r] = t;
    cnt[0] = cnt[r];
  }

  FREE(chk_cnt);

  for(i = 0; i < 3; i++)
    FREE(sav[i]);
}

void output_two_oe_selecters(ARGS *args, int bound, int *res,
                             int tot_cnt, int *mix, int *startatom)
{
  if(tot_cnt / 2 <= bound) {
    output_unary_sorter_f(args, bound, res, tot_cnt, mix, startatom,
                          args->flavors & ~FL_CO_SELECT);
    return;
  }

  int i, j, q, r, pos, c, *chk_cnt, tmp_cnt, top_cnt;
  const int srt_cnt
    = assign_literals_to_chunks(&chk_cnt, bound, tot_cnt, args->flavors);
  int * const aux  = (int *)MALLOC((tot_cnt + 2 * bound) * sizeof(int));
  int ** const chk = (int **)MALLOC(srt_cnt * sizeof(int *));
  int * const idx  = (int *)MALLOC(srt_cnt * sizeof(int));
  int * const ppp  = (int *)MALLOC(2 * bound * sizeof(int));
  int *top         = &aux[tot_cnt], *tmp = &top[bound];

  /* Output sorters */

  for(pos = 0, i = 0; i < srt_cnt; i++, pos += c) {

    chk[i] = &aux[pos];
    idx[i] = i;

    c = chk_cnt[i];
    for(j = 0; j < c; j++)
      aux[pos + j] = SMX_WANTED;

#if DEBUG_MERGESORT
    fprintf(stderr, "Output %s <- sorter(%s)\n",
            a2x(c, &aux[pos]), a2x(c, &mix[pos]));
#endif

    output_unary_sorter(args, c, &aux[pos], c, &mix[pos], startatom);
  }

  /* Output mergers repetitively */

  for(r = 0; r < 2; r++)  {

    /* Initialize top to the first sorted chunk */

    q = idx[0];
    top_cnt = chk_cnt[q];
    for(j = 0; j < top_cnt; j++)
      top[j] = chk[q][j];

    /* */

    for(i = 1; i < srt_cnt; i++) {

      q = idx[i];
      tmp_cnt = bound;

      if(i + 1 < srt_cnt)
        for(j = 0; j < tmp_cnt; j++)
          tmp[j] = SMX_WANTED;
      else 
        for(j = 0; j < tmp_cnt; j++)
          tmp[j] = res[j];

#if DEBUG_MERGESORT
      fprintf(stderr, "Output %s <- merger(%s, %s)\n",
              a2x(tmp_cnt, tmp), a2x(top_cnt, top), a2x(chk_cnt[q], chk[q]));
#endif

      output_unary_merger(args, tmp_cnt, tmp, top_cnt, top, chk_cnt[q], chk[q],
                          0, *startatom);

      int * const t = top;
      top = tmp;
      tmp = t;
      top_cnt = tmp_cnt;
    }

    for(j = 0; j < top_cnt; j++)
      ppp[2 * j + r] = top[j];

    int_array_reverse(srt_cnt, idx);
  }

  /* Construct the output */

  for(j = 0; j < bound; j++)
    res[j] = (args->flavors & FL_CO_SELECT_A2
        ? litint_output_new_2(args, ppp[2 * j + 0], ppp[2 * j + 1])
        : litint_output_new_1x2(args, ppp[2 * j + 0], 0, ppp[2 * j + 1], 0));

  FREE(chk_cnt);
  FREE(aux);
  FREE(chk);
  FREE(idx);
  FREE(ppp);
}

/* ========================= Sequential Unary Counter ===================== */

/* Check to see if a partial sum digit in an s.u.s. is of interest */

int is_sequential_unary_partial_sum_wanted(int tot_cnt, int bound, int *sorted,
                                           int i, int j)
{
  int ans, k;

  for(ans = 0, k = 0; (j + k < bound) && (k < tot_cnt - i) && !ans; k++)
    ans = SMX_IS_WANTED(sorted[j + k]);

  return ans;
}

/* Check to see if a carry digit in an s.u.s. is of interest */

int is_sequential_unary_carry_wanted(int tot_cnt, int bound, int *sorted,
                                     int i, int j)
{
  return
    is_sequential_unary_partial_sum_wanted(tot_cnt, bound, sorted, i, j + 1);
}

/*
 * Sort literals by computing partial unary sums of inputs sequentially
 */

void output_sequential_unary_sorter(ARGS *args, int bound, int *sorted,
                                    int tot_cnt, int *mix)
{
  int * const pt_sum = (int *)MALLOC(bound * sizeof(int));
  const int startatom = args->newatom; /* This helps identify new aux atoms */
  int i, j;

  for(i = 0; i < bound; i++)
    pt_sum[i] = SMX_FALSE;

  for(i = 0; i < tot_cnt; i++) {

    /* Output rules for incrementing the unary partial sum if mix[i] holds */

    int carry = mix[i];

    for(j = 0; j < bound; j++) {

      const int s_ij = pt_sum[j];

      /* Determine preliminaries for use in symbolical evaluation */

      const int s_wanted
        = is_sequential_unary_partial_sum_wanted(tot_cnt, bound, sorted, i, j);
      const int carry_wanted
        = is_sequential_unary_carry_wanted(tot_cnt, bound, sorted, i, j);
      const int s_modifiable = (!carry_wanted && (startatom <= s_ij));
      const int carry_modifiable = (startatom <= carry);

      if(s_wanted)
        pt_sum[j] = litint_output_new_1x2(args,
                                           carry, carry_modifiable,
                                           s_ij, s_modifiable);

      if(carry_wanted)
        carry = litint_output_new_2(args, s_ij, mix[i]);
    }
  }

  /* Transfer the output */

  for(i = 0; i < bound; i++)
    sorted[i] = pt_sum[i];

  FREE(pt_sum);
}

/* ========================= Sequential Unary Weight Counter ============== */

/*
 * Sort sums of weights by computing partial weighted unary sums of inputs
 */

void output_sequential_unary_weight_sorter(ARGS *args, int bound, int *res,
                                           int tot_cnt, int *mix, int *weight)
{
  int * const s = &((int *)MALLOC((bound + 1) * sizeof(int)))[1];
  int * const d = (int *)MALLOC(bound * sizeof(int));
  char * const r = (char *)MALLOC(bound * tot_cnt * sizeof(int));
  char * const q = (char *)calloc(bound * tot_cnt, sizeof(int));
  const int startatom = args->newatom; /* This helps identify new aux atoms */
  int i, j, k, t, w, lo, hi, p_lo, p_hi, p_s;
  char *u, *v;

  /* Propagate W/X (1/0) values from right to left */

  i = tot_cnt - 1;

  for(u = &r[bound * i], j = 0; j < bound; j++)
    u[j] = (SMX_IS_WANTED(res[j]) ? 1 : 0);

  for(i--; 0 <= i; i--) {
    u = &r[bound * i];
    v = &u[bound];
    w = weight[i + 1];

    for(j = 0; j < bound - w; j++)
      u[j] = v[j] || v[j + w];

    for(; j < bound; j++)
      u[j] = v[j];
  }

#if DEBUG_SEQ
  for(j = 0; j < bound; j++) {
    for(i = 0; i < tot_cnt; i++) {
      fprintf(stderr, "%i", r[bound * i + j]);
    }
    fprintf(stderr, "\n");
  }
#endif

  /* Output the sorter from left to right */

  s[-1] = SMX_TRUE;

  for(j = 0; j < bound; j++)
    s[j] = SMX_FALSE;

  for(i = 0; i < tot_cnt; i++) {
    u = &r[bound * i];

    p_lo = SMX_DONT_CARE;
    p_hi = SMX_DONT_CARE;
    lo = SMX_FALSE;
    hi = SMX_FALSE;

    /* Define the digits for the i-th partial sum going from top to bottom */

    for(j = bound - 1; 0 <= j; j--) {

      k = MAX(j - weight[i], -1);

      if(!SMX_IS_FALSE(s[k]))
        lo = s[k];

      if(!SMX_IS_FALSE(s[j])) {
        hi = s[j];
        if(hi == lo)
          lo = SMX_FALSE;
      }

      if((lo == p_lo) && (hi == p_hi)) {
        s[j] = p_s; /* Reuse a "higher" digit with the same definition */
        continue;
      }

      if(!u[j]) {
        /* This does not seem to be needed: s[j] = SMX_FALSE; */
        continue;
      }

#if DEBUG_SEQ
      fprintf(stderr, "Defining s_{%i,%i}; lo = %s, hi = %s\n",
              i, j, ma2s(lo), ma2s(hi));
#endif

      const int hi_modifiable = ((startatom <= hi) && !SMX_IS_SPECIAL(hi)
                                 && !q[hi - startatom] && SMX_ENABLE_MODIFYING);

      if(hi_modifiable) {

        s[j] = litint_output_2(args, hi, lo, mix[i]);
#if DEBUG_SEQ
        fprintf(stderr, "--> s_{%i,%i} = %s; <no t>, hi_m = %i\n",
                i, j, ma2s(s[j]), hi_modifiable);
#endif
      } else {

        t = litint_output_new_2(args, lo, mix[i]);

        const int t_modifiable = ((startatom <= t) && !SMX_IS_SPECIAL(t)
                                  && !q[t - startatom]);

        s[j] = litint_output_new_1x2(args,
                                      t, t_modifiable,
                                      hi, hi_modifiable);

#if DEBUG_SEQ
        fprintf(stderr, "--> s_{%i,%i} = %s; t_m = %i, hi_m = %i\n",
                i, j, ma2s(s[j]), t_modifiable, hi_modifiable);
#endif
      }

      if((startatom <= lo) && !SMX_IS_SPECIAL(lo)) {
        q[lo - startatom] = 1;
#if DEBUG_SEQ
        fprintf(stderr, "Mark lo (%s) as having been used: q[%i] = %i\n",
                ma2s(lo), lo - startatom, (int) q[lo - startatom]);
#endif
      }

      if((startatom <= hi) && !SMX_IS_SPECIAL(hi)) {
        q[hi - startatom] = 1;
#if DEBUG_SEQ
        fprintf(stderr, "Mark hi (%s) as having been used: q[%i] = %i\n",
                ma2s(hi), hi - startatom, (int) q[hi - startatom]);
#endif
      }

      p_lo = lo;  /* Save s[j]'s rules to avoid printing them again */
      p_hi = hi;
      p_s = s[j];
    }
  }

  /* Wire the output */

  for(j = bound - 1; 0 <= j; j--) {
    if(SMX_IS_WANTED(res[j]))
      res[j] = s[j];
  }

  FREE(&s[-1]);
  FREE(d);
  FREE(r);
  FREE(q);
}

/* ========================= General Unary Constructions ================== */

/*
 * Count the atoms and rules that would be produced by output_unary_merger
 */

int count_unary_merger_cost_f(ARGS *args, int bound, int *s,
                              int n_p, int *p, int n_q, int *q,
                              int p_dominates_q, int startatom,
                              uint64_t shallow_flavors,
                              uint64_t deep_flavors,
                              int *atom_cnt, int *rule_cnt)
{
  const int saved_style = args->style;
  const int saved_newatom = args->newatom;
  const int saved_newrule = args->newrule;
  const uint64_t saved_flavors = args->flavors;

  int * const copies = (int *)MALLOC((bound + n_p + n_q) * sizeof(int));
  int * const c_s = copies;
  int * const c_p = &c_s[bound];
  int * const c_q = &c_p[n_p];

  int_array_copy(bound, c_s, s);
  int_array_copy(n_p, c_p, p);
  int_array_copy(n_q, c_q, q);

  args->style = STYLE_DEV_NULL;
  args->flavors = deep_flavors;

  output_unary_merger_f(args, bound, c_s, n_p, c_p, n_q, c_q, p_dominates_q,
                        startatom, shallow_flavors);

  FREE(copies);

  const int a = args->newatom - saved_newatom;
  const int r = args->newrule - saved_newrule;

  args->newatom = saved_newatom;
  args->newrule = saved_newrule;
  args->style = saved_style;
  args->flavors = saved_flavors;

  if(atom_cnt)
    *atom_cnt = a;
  if(rule_cnt)
    *rule_cnt = r;

  return get_atom_and_rule_cost(a, r);
}

/*
 * Output the conciser merger among the totalizing and odd-even ones
 */

void output_least_merger(ARGS *args, int bound, int *s,
                         int n_p, int *p, int n_q, int *q,
                         int p_dominates_q, int startatom)
{
#if LEAST_GUARD_DEV_NULL
  /* Guard against recursive branching */

  int b = (args->style == STYLE_DEV_NULL);

#if defined(LEAST_GUARD_DEPTH) && (1 < LEAST_GUARD_DEPTH)
  b = (b && (LEAST_GUARD_DEPTH < args->conddepth));
#endif

  if(b) {

    output_oe_merger(args, bound, s, n_p, p, n_q, q, p_dominates_q, startatom);
    return;
  }

  args->conddepth++; /* Make a little hijack here */
#endif

#define OLM_N 2
#define OLM_M 1

  const int n = OLM_N, m = OLM_M;
  uint64_t sflavors[OLM_N] = { FL_CO_OE_MERGE, FL_CO_TOTALIZE };
  uint64_t dflavors[OLM_M] = { 0 };
  uint64_t dmask = 0;
  int i, costs[OLM_N * OLM_M];

  for(i = 0; i < m; i++)
    dmask |= dflavors[i];

  for(i = 0; i < m; i++)
    dflavors[i] |= args->flavors & ~dmask;

  for(i = 0; i < n * m; i++)
    costs[i] = count_unary_merger_cost_f(args, bound, s, n_p, p, n_q, q,
                                         p_dominates_q, startatom,
                                         sflavors[i / m], dflavors[i % m],
                                         NULL, NULL);

  const int winner = int_array_min_index(n * m, costs);

#if DEBUG_LEAST
  fprintf(stderr, "Costs = %s\n", a2x(n * m, costs));
  fprintf(stderr, "Chose merger (%i,%i) for bound = %i, n_p = %i, n_q = %i\n",
          winner / m, winner % m, bound, n_p, n_q);
#endif

  const uint64_t saved_flavors = args->flavors;
  args->flavors = dflavors[winner % m];

  output_unary_merger_f(args, bound, s, n_p, p, n_q, q, p_dominates_q,
                        startatom, sflavors[winner / m]);

  args->flavors = saved_flavors;

#if LEAST_GUARD_DEV_NULL
  args->conddepth--;
#endif
}

/*
 * Try to make a merger's input more compact
 */

int output_unary_merger_preprocess(int *bound, int *s,
                                   int *n_p, int *p, int *n_q, int *q,
                                   int *mul, int *old_bound)
{
  const int mul_p = int_array_get_interleaved_multiplier(*n_p, p);
  const int mul_q = int_array_get_interleaved_multiplier(*n_q, q);

#if DEBUG_MERGESORT
    fprintf(stderr, "HELLO, mul_p = %i, mul_q = %i\n", mul_p, mul_q);
    fprintf(stderr, "     :  p: %s, q: %s\n", a2x(*n_p, p), a2x(*n_q, q));
#endif

  if(sorted_int_array_cmp_slice(*n_p, 0, mul_p, p, *n_q, 0, mul_q, q) == 0) {

#if DEBUG_MERGESORT
    fprintf(stderr, "p: %s, mul_p: %i\n", a2x(*n_p, p), mul_p);
    fprintf(stderr, "q: %s, mul_q: %i\n", a2x(*n_q, q), mul_q);
#endif

    int i, j, k, m = mul_p + mul_q;
    for(k = i = 0; (i < *n_p) && (k < *bound); i += mul_p)
      for(j = m; (0 < j) && (k < *bound); j--, k++)
        if(SMX_IS_WANTED(s[k]))
          s[k] = p[i];

#if DEBUG_MERGESORT
    fprintf(stderr, "s: %s, mul_s: %i\n",
            a2x(*bound, s), int_array_get_interleaved_multiplier(*bound, s));
#endif

    return 1;
  }

#if 0
  /* This is not working */

  if((*mul = gcd(mul_p, mul_q)) <= 1)
    return 0;

  *old_bound = *bound;
  *bound = (*bound + *mul - 1) / *mul;
  *n_p = int_array_unscatter(*n_p, p, 0, *mul);
  *n_q = int_array_unscatter(*n_q, q, 0, *mul);
#endif

  return 0;
}

/*
 * Revert any in-place preprocessing done on a merger's input
 */

void output_unary_merger_postprocess(int *bound, int *s,
                                     int *n_p, int *p, int *n_q, int *q,
                                     int mul, int old_bound)
{
#if 0
  /* This is not working */

  if(mul <= 1)
    return;

  *bound = int_array_repeat_interleaved_2(*bound, s, mul, old_bound);
  *n_p = int_array_repeat_interleaved(*n_p, p, mul);
  *n_q = int_array_repeat_interleaved(*n_q, q, mul);
#endif
}

/*
 * Output a unary merger specified by given flavors
 */

void output_unary_merger_f(ARGS *args, int bound, int *s,
                           int n_p, int *p, int n_q, int *q,
                           int p_dominates_q, int startatom,
                           uint64_t flavors)
{
#if UNARY_MERGER_TRICK
  int a, b;
  if(output_unary_merger_preprocess(&bound, s, &n_p, p, &n_q, q, &a, &b))
    return;
#endif

  if(flavors & FL_CO_TOTALIZE)

    output_totalizing_merger(args, bound, s, n_p, p, n_q, q, p_dominates_q);

  else if(flavors & FL_CO_OE_MERGE)

    output_oe_merger(args, bound, s, n_p, p, n_q, q, p_dominates_q, startatom);

  else /* if(flavors & FL_CO_AUTO) */

    output_least_merger(args,bound, s, n_p, p, n_q, q, p_dominates_q,
                        startatom);

#if UNARY_MERGER_TRICK
  output_unary_merger_postprocess(&bound, s, &n_p, p, &n_q, q, a, b);
#endif
}

/*
 * Output a unary merger
 */

void output_unary_merger(ARGS *args, int bound, int *s,
                         int n_p, int *p, int n_q, int *q,
                         int p_dominates_q, int startatom)
{
  uint64_t saved_flavors
    = replace_flavors_for_unary_merger(args, bound, n_p, n_q);

  output_unary_merger_f(args, bound, s, n_p, p, n_q, q, p_dominates_q,
                        startatom, args->flavors);

  restore_flavors(args, saved_flavors);
}

/*
 * Count the atoms and rules that would be produced by output_unary_sorter
 */

int count_unary_sorter_cost_f(ARGS *args, int bound, int *res,
                              int tot_cnt, int *mix, int *startatom,
                              uint64_t shallow_flavors, uint64_t deep_flavors,
                              int *atom_cnt, int *rule_cnt)
{
  const int saved_style = args->style;
  const int saved_newatom = args->newatom;
  const int saved_newrule = args->newrule;
  const uint64_t saved_flavors = args->flavors;

  int * const copies = (int *)MALLOC((bound + tot_cnt) * sizeof(int));
  int * const c_res = copies;
  int * const c_mix = &c_res[bound];

  int_array_copy(bound, c_res, res);
  int_array_copy(tot_cnt, c_mix, mix);

  args->style = STYLE_DEV_NULL;
  args->flavors = deep_flavors;

  output_unary_sorter_f(args, bound, c_res, tot_cnt, c_mix, startatom,
                        shallow_flavors);

  FREE(copies);

  const int a = args->newatom - saved_newatom;
  const int r = args->newrule - saved_newrule;

  args->newatom = saved_newatom;
  args->newrule = saved_newrule;
  args->style = saved_style;
  args->flavors = saved_flavors;

  if(atom_cnt)
    *atom_cnt = a;
  if(rule_cnt)
    *rule_cnt = r;

  return get_atom_and_rule_cost(a, r);
}

/*
 * Output the concisest sorter out of recursive, selecting and sequential ones
 */

void output_least_sorter(ARGS *args, int bound, int *res,
                         int tot_cnt, int *mix, int *startatom)
{
#if LEAST_GUARD_DEV_NULL
  /* Guard against recursive branching */
  int b = (args->style == STYLE_DEV_NULL);

#if defined(LEAST_GUARD_DEPTH) && (1 < LEAST_GUARD_DEPTH)
  b = (b && (LEAST_GUARD_DEPTH < args->conddepth));
#endif

  if(b) {

    output_merge_sorter(args, bound, res, tot_cnt, mix, *startatom);
    return;
  }

  args->conddepth++; /* Make a little hijack here */
#endif

#define OLS_N 2

  const int n = OLS_N;
  uint64_t sflavors[OLS_N] = { FL_CO_REC_SORT, FL_CO_REC_SORT };
  uint64_t dflavors[OLS_N] = { FL_CO_REC_SORT_EXP2,
                               FL_CO_REC_SORT_EXP2 | FL_CO_REC_SORT_PW };
  uint64_t dmask = 0;
  int i, costs[OLS_N];

  for(i = 0; i < n; i++)
    dmask |= dflavors[i];

  for(i = 0; i < n; i++)
    dflavors[i] |= args->flavors & ~dmask;

  for(i = 0; i < n; i++)
    costs[i] = count_unary_sorter_cost_f(args, bound, res, tot_cnt, mix,
                                         startatom, sflavors[i], dflavors[i],
                                         NULL, NULL);

  const int winner = int_array_min_index(n, costs);

#if DEBUG_LEAST
  fprintf(stderr, "Costs = %s\n", a2x(n, costs));
  fprintf(stderr, "Chose sorter %i for bound = %i, tot_cnt = %i\n",
          winner, bound, tot_cnt);
#endif

  const uint64_t saved_flavors = args->flavors;
  args->flavors = dflavors[winner];

  output_unary_sorter_f(args, bound, res, tot_cnt, mix,
                        startatom, sflavors[winner]);

  args->flavors = saved_flavors;

#if LEAST_GUARD_DEV_NULL
  args->conddepth--;
#endif
}

/*
 * Output a unary sorter specified by given flavors
 */

void output_unary_sorter_f(ARGS *args, int bound, int *res,
                           int tot_cnt, int *mix, int *startatom,
                           uint64_t flavors)
{
  if(flavors & FL_CO_SELECT) {

    if(flavors & (FL_CO_SELECT_O2 | FL_CO_SELECT_A2))

      output_two_oe_selecters(args, bound, res, tot_cnt, mix, startatom);

    else

      output_oe_selecter(args, bound, res, tot_cnt, mix, startatom);

  } else if(flavors & FL_CO_SEQ_SORT) {

    output_sequential_unary_sorter(args, bound, res, tot_cnt, mix);

    *startatom = MAX(*startatom, args->newatom);

  } else if(flavors & FL_CO_REC_SORT)

    output_merge_sorter(args, bound, res, tot_cnt, mix, *startatom);

  else /* if(flavors & FL_CO_AUTO) */

    output_least_sorter(args, bound, res, tot_cnt, mix, startatom);
}

/*
 * Output a unary sorter
 */

void output_unary_sorter(ARGS *args, int bound, int *res,
                         int tot_cnt, int *mix, int *startatom)
{
  uint64_t saved_flavors
    = replace_flavors_for_unary_sorter(args, bound, tot_cnt);

  output_unary_sorter_f(args, bound, res, tot_cnt, mix, startatom,
                        args->flavors);

  restore_flavors(args, saved_flavors);
}

/*
 * Encode a constraint by taking the bound-th digit of a unary sorter
 */

void output_unary_sorter_tester(ARGS *args, RULE *rule)
{
  CONSTRAINT_RULE * const constraint = rule->data.constraint;
  const int neg_cnt = constraint->neg_cnt, pos_cnt = constraint->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt, bound = constraint->bound;
  int * const mix = constraint->neg;
  int * const res = (int *)MALLOC(bound * sizeof(int));
  int startatom = args->newatom;
  int i;

  litint_from_neg(neg_cnt, mix);

  /* Specify that we only want to know the bound-th element */

  for(i = 0; i < bound - 1; i++)
    res[i] = SMX_DONT_CARE;

  res[bound - 1] = SMX_WANTED;

  /* Output a unary sorter */

  output_unary_sorter(args, bound, res, tot_cnt, mix, &startatom);

  /* Derive the head from the sorted output */

  litint_output_normal(args, constraint->head, 1, &res[bound - 1]);

  FREE(res);
}

#endif
