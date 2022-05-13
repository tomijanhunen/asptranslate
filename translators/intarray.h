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
 * Functions for integer arrays
 *
 * (c) 2014 Jori Bomanson
 *
 * TODO: Rename occurrence functions
 * TODO: Add deletion based occurrence functions
 */

#ifndef INT_ARRAY_H
#define INT_ARRAY_H

//#if INT_ARRAY_STATIC
//#define INT_ARRAY_PREFIX  static
//#else
//#define INT_ARRAY_PREFIX
//#endif

#define INT_ARRAY_PREFIX

#include <assert.h>
#include <limits.h>   /* for INT_MIN, INT_MAX */

#include "common.h"       /* For MALLOC, FREE */

/* ---- Private-ish -------------------------------------------------------- */

static
int int_array__gcd_single(int u, int v)
{
  int t = 0;

  if(u<0) u = -u;
  if(v<0) v = -v;

  while(v != 0) {
    t = u % v;
    u = v;
    v = t;
  }

  return u;
}

/* ------------------------------------------------------------------------- */

int int_array_gcd(int c, int *v)
{
  int g = (c == 0 ? 1 : v[0]);
  int i;

  for(i = 1; i < c; i++)
    g = int_array__gcd_single(g, v[i]);

  return g;
}

/* Get the sum of all numbers in an array */

INT_ARRAY_PREFIX
int int_array_sum(int c, int *v)
{
  int sum, i;
  for(sum = i = 0; i < c; i++)
    sum += v[i];
  return sum;
}

/* Get the sum of all numbers in an array if it were divided */

INT_ARRAY_PREFIX
int int_array_sum_residues(int cnt, int *w, int div)
{
  int sum = 0;
  int i;
  for(i = 0; i < cnt; i++)
    sum += w[i] % div;
  return sum;
}

/* Reverse the order of elements in an array in place */

INT_ARRAY_PREFIX
void int_array_reverse(int c, int *v)
{
  int i, j;
  for (i = 0, j = c - 1; i < j; i++, j--) {
    const int t = v[i];
    v[i] = v[j];
    v[j] = t;
  }
}

/* Get the index of the least element in an array */

INT_ARRAY_PREFIX
int int_array_min_index(int c, int *v)
{
  int i, min_i = 0;
  for(i = 1; i < c; i++)
    if(v[i] < v[min_i])
      min_i = i;
  return min_i;
}

/* Get the index of the greatest element in an array */

INT_ARRAY_PREFIX
int int_array_max_index(int c, int *v)
{
  int i, max_i = 0;
  for(i = 1; i < c; i++)
    if(v[max_i] < v[i])
      max_i = i;
  return max_i;
}

/* Get the least element in an array, or INT_MAX if c == 0 */

INT_ARRAY_PREFIX
int int_array_min(int c, int *v)
{
  int i, x = INT_MAX;
  for(i = 0; i < c; i++)
    if(v[i] < x)
      x = v[i];
  return x;
}

/* Get the greatest element in an array, or INT_MIN if c == 0 */

INT_ARRAY_PREFIX
int int_array_max(int c, int *v)
{
  int i, x = INT_MIN;
  for(i = 0; i < c; i++)
    if(x < v[i])
      x = v[i];
  return x;
}

/* Copy all elements to one array from another */

INT_ARRAY_PREFIX
void int_array_copy(int c, int *dst, int *src)
{
  int i;
  for(i = 0; i < c; i++)
    dst[i] = src[i];
}

/* Allocate and return a new copy of an array */

INT_ARRAY_PREFIX
int *int_array_new_copy(int c, int *v)
{
  int * const y = MALLOC(c * sizeof(int));
  int_array_copy(c, y, v);
  return y;
}

/* Set all elements in an array to a given value*/

INT_ARRAY_PREFIX
void int_array_fill(int c, int *v, int x)
{
  int i;
  for(i = 0; i < c; i++)
    v[i] = x;
}

/* Return a nonzero number if one or more array elements are nonzero */

INT_ARRAY_PREFIX
int int_array_or(int c, int *v)
{
  int i;
  for(i = 0; i < c; i++)
    if(v[i])
      return 1;
  return 0;
}

/* Get the number of consecutive repetitions of the first element in an array,
 * or 0 if c == 0 */

INT_ARRAY_PREFIX
int int_array_get_run_length(int c, int *v)
{
  int n;
  for(n = 0; (n < c) && (v[0] == v[n]); n++)
    ;
  return n;
}

/*
 * Determine if an array is sorted in ascending order
 */

INT_ARRAY_PREFIX
int int_array_is_ascending(int c, int *v)
{
  int i, b;
  for(b = 1, i = 1; (i < c) && b; i++)
    b = (v[i - 1] <= v[i]);
  return b;
}

/*
 * Check if a sorted array contains any elements of a second sorted array
 */

INT_ARRAY_PREFIX
int sorted_int_array_contains_any(int c, int *v, int d, int *w)
{
  int i = 0, j = 0, b = 0;
  while(!b && (i < c) && (j < d))
    if(v[i] < w[j])
      i++;
    else if(w[j] < v[i])
      j++;
    else
      b = 1;
  return b;
}

/*
 * Check if a sorted array contains all elements of a second sorted array
 */

INT_ARRAY_PREFIX
int sorted_int_array_contains_all(int c, int *v, int d, int *w)
{
  int i = 0, j = 0, x = 0;
  while((i < c) && (j < d))
    if(v[i] < w[j])
      i++;
    else if(w[j] < v[i])
      j++;
    else {
      x++;
      i++;
      j++;
    }
  return (x == d);
}

/*
 * Remove from the first of two sorted arrays any and all elements of the
 * second (at most as many times as they occur in the second) and return the
 * number of remaining items
 */

INT_ARRAY_PREFIX
int sorted_int_array_delete_another(int c, int *v, int d, int *w)
{
  int i, x, j;
  for(x = 0, i = 0, j = 0; (i < c) && (j < d);)
    if(v[i] < w[j])
      v[x++] = v[i++];
    else if(w[j] < v[i])
      j++;
    else {
      i++;
      j++;
    }
  while(i < c)
    v[x++] = v[i++];
  return x;
}

/*
 * Inserts elements into an int array pushing the existing ones higher without
 * growing the int array, but instead discarding the highest ones
 */

INT_ARRAY_PREFIX
void int_array_insert_no_grow(int c, int *v, int d, int *w)
{
  int i;
  for(i = c - 1; d <= i; i--)
    v[i] = v[i - d];
  for(; 0 <= i; i--)
    v[i] = w[i];
}

/* Delete the first n elements of an array by moving the remaining ones to the
 * left and return the number of remaining elements */

INT_ARRAY_PREFIX
int int_array_delete_head(int c, int *v, int n)
{
  int i;
  for(i = 0; i < c - n; i++)
    v[i] = v[i + n];
  return i;
}

/* Delete d index ranges of the form [starts[i], starts[i]+counts[i]) and
 * return remaining length */

INT_ARRAY_PREFIX
int int_array_delete_ranges(int c, int *v, int d, int *starts, int *counts)
{
  int i, n, j;
  assert(1 <= d);
  for(i = n = j = 0; j < d; n += counts[j++])
    i += int_array_delete_head(starts[j] - i, &v[i], n);
  return i + int_array_delete_head(c - i, &v[i], n);
}

/* Delete the range [from, from+count) of indices and return remaining length */

INT_ARRAY_PREFIX
int int_array_delete_range(int c, int *v, int from, int count)
{
  return from + int_array_delete_head(c - from, &v[from], count);
}

/* Check if a sorted array contains two sorted numbers */

INT_ARRAY_PREFIX
int sorted_int_array_contains_pair(int c, int *v, int a, int b)
{
  assert(a <= b);

  int w[2];
  w[0] = a;
  w[1] = b;
  return sorted_int_array_contains_all(c, v, 2, w);
}

/* Return any index i to a sorted array such that v[i] == w, or -1 if none
 * exists. When there are several such indices, no guarantee is made as to
 * which is returned. */

INT_ARRAY_PREFIX
int sorted_int_array_get_any_index_of(int c, int *v, int w)
{
  int lo = 0, hi = c - 1;
  while(lo <= hi) {
    const int mid = (lo + hi) / 2;
    if(v[mid] < w)
      lo = mid + 1;
    else if(w < v[mid])
      hi = mid - 1;
    else
      return mid;
  }
  return -1;
}

/* Do magic and return something
 * TODO: Test before use
 */

INT_ARRAY_PREFIX
int sorted_int_array_get_any_indices_of(int c, int *v, int d, int *w, int *o)
{
  int i, j, k;
  for(i = j = 0; j < d; o[j++] = i += k, i++)
    if((k = sorted_int_array_get_any_index_of(c - i, &v[i], w[j])) < 0)
      break;
  return j;
}

/* Get the starting index of a value and the number of indices containing that
 * value */

INT_ARRAY_PREFIX
void sorted_int_array_get_range_of(int c, int *v, int w, int *start, int *count)
{
  int i, j, any = sorted_int_array_get_any_index_of(c, v, w);
  for(i = any; (0 < i) && (v[i - 1] == w); i--);
  for(j = any; (0 <= j) && (j < c) && (v[j] == w); j++);
  if(start) { *start = i; }
  if(count) { *count = j - i; }
}

/* Get the starting indices and counts of value runs, expected to be in sorted
 * order */

INT_ARRAY_PREFIX
int sorted_int_array_get_ranges_of(int c, int *v, int d, int *w,
                                   int *starts, int *counts)
{
  int i, j;
  for(i = j = 0; j < d; i = starts[j++]) {
    sorted_int_array_get_range_of(c - i, &v[i], w[j], &starts[j], &counts[j]);
    if(starts[j] < 0)
      break;
    starts[j] += i;
  }
  return j;
}

/* 
 * Count the number of occurrences in a sorted array of another sorted array.
 *
 * The result is the product of the number of occurrences of the elements of
 * the second array in the first array.
 *
 * TODO: Works only for properly increasing int arrays
 * TODO: Find out what I was thinking when I wrote the above TODO
 */

INT_ARRAY_PREFIX
int sorted_int_array_count_occurrences_of(int c, int *v, int d, int *w)
{
  int i, j, from, k, prod;

  for(prod = 1, j = i = 0; (prod != 0) && (i < d); i++, j = from + k, prod *= k)
    sorted_int_array_get_range_of(c - j, &v[j], w[i], &from, &k);

  return prod;
}

/*
 * Count the number of times a sorted pair (a, b) occurs in a sorted array.
 *
 * If the pair is not contained, the result is zero.
 *
 * If the elements are both contained once, the result is one.
 *
 * If either element is contained more than once,
 * the result is the product of their multiplicities.
 */

INT_ARRAY_PREFIX
int sorted_int_array_count_pair_occurrences(int c, int *v, int a, int b)
{
  int ac, bc;
  sorted_int_array_get_range_of(c, v, a, NULL, &ac);
  if(a == b)
    return (ac * (ac - 1)) / 2;
  sorted_int_array_get_range_of(c, v, b, NULL, &bc);
  return ac * bc;
}

/* Turn [a b c d] into [x...x a x...x b x...x c x...x d]
   NOTE: c is supposed to be the resulting length */

INT_ARRAY_PREFIX
void int_array_scatter(int c, int *v, int offset, int stride, int filler)
{
  int i;
  for(i = c - 1; 0 <= i; i--)
    v[i] = ((i - offset + stride) % stride
         ? filler
         : v[i / stride]);
}

/* Turn [x...x a x...x b x...x c x...x d] into [a b c d] */

INT_ARRAY_PREFIX
int int_array_unscatter_to(int *dst, int c, int *src, int offset, int stride)
{
  int i, j;
  for(j = 0, i = (offset + stride) % stride; i < c; i += stride, j++)
    dst[j] = src[i];
  return j;
}

/* Unscatter an array in place */

INT_ARRAY_PREFIX
int int_array_unscatter(int c, int *v, int offset, int stride)
{
  return int_array_unscatter_to(v, c, v, offset, stride);
}

INT_ARRAY_PREFIX
int int_array_unscatter_size(int c, int offset, int stride)
{
  return (c - (offset + stride) % stride + stride - 1) / stride;
}

/* Turn [a b c d] into [a...a b...b c...c d...d] */

INT_ARRAY_PREFIX
int int_array_repeat_interleaved(int c, int *v, int multiplier)
{
  int i, k, value, j = c * multiplier;
  for(i = c - 1; 0 <= i; i--)
    for(value = v[i], k = j - 1, j = i * multiplier; j <= k; k--)
      v[k] = value;
  return c * multiplier;
}

/* Turn [a b c d] into [a...a b...b c...c d...d] */

INT_ARRAY_PREFIX
int int_array_repeat_interleaved_2(int c, int *v, int multiplier, int d)
{
  int i, k, value, j = d;
  for(i = c - 1; 0 <= i; i--)
    for(value = v[i], k = j - 1, j = i * multiplier; j <= k; k--)
      v[k] = value;
  return d;
}

/* Return a multiplier that might have been used on v */

INT_ARRAY_PREFIX
int int_array_get_interleaved_multiplier(int c, int *v)
{
  int i, s, g = -1;
  for(s = 0, i = 1; i < c; i++)
    if(v[s] != v[i]) {
      g = (g == -1 ? i - s : int_array__gcd_single(g, i - s));
      s = i;
    }
  return (g == -1 ? i - s : int_array__gcd_single(g, i - s));
}

/* Compare two strided slices of two sorted int arrays given in terms of total
 * counts, offsets, strides and pointers. */

INT_ARRAY_PREFIX
int sorted_int_array_cmp_slice(int c1, int o1, int s1, int *v1,
                               int c2, int o2, int s2, int *v2)
{
  int i1, i2, x = 0;
  for(i1 = o1, i2 = o2; (i1 < c1) && (i2 < c2) && (x == 0); i1 += s1, i2 += s2)
    x = (v1[i1] - v2[i2]);
  if(x)
    return x;
  if(i1 < c1)
    return -1;
  if(i2 < c2)
    return 1;
  return 0;
}


#endif
