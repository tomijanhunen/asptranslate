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

#ifndef PLAN_H
#define PLAN_H

/*#include "atom.h"*/

#include "common.h"
#include "args.h"

/* ---------------------- Configuration ------------------------------------ */

#define PLANBHASH_OVERFIT(x)      (3 * (x) / 2)

#define RADIX_MAX_BLOWUP(ub, cnt) (MIN(10, MAX(2, (ub))) * (cnt))

#define PAIR_MAX_BLOWUP(x)        (2 * (x))

/* ------------------------------------------------------------------------- */

#define WQ_RADIX_INF              SHRT_MAX

/* ========================= Planned Weight Counter ======================= */

/* */

void print_array(FILE *out, int c, int *v)
{
  int i;
  for(i = 0; i < c; i++)
    fprintf(out, " %i", v[i]);
}

/* */

void print_set(FILE *out, int *set)
{
  fprintf(out, " (%i)", set[0]);
  print_array(out, set[0], &set[1]);
}

/* */

void print_set_nl(FILE *out, int *set)
{
  print_set(out, set);
  fprintf(out, "\n");
}

/* Add an array to the end of an array of integer arrays */

void int_array_array_add_array(int *int_array_cnt, int *int_array_mem,
                           int ***array, int *arr)
{
  if(*int_array_cnt == *int_array_mem) {
    *int_array_mem *= 2;
    *array = (int **)realloc(*array, (*int_array_mem) * sizeof(int *));
  }
  (*array)[(*int_array_cnt)++] = arr;
}

/* Add a copy of a set to the end of an array of sets */

void set_array_add_copy(int *int_array_cnt, int *int_array_mem,
                        int ***array, int *set)
{
  int_array_array_add_array(int_array_cnt, int_array_mem, array,
                        int_array_new_copy(set[0] + 1, set));
}

/* Remove the intersection of two arrays from both and return it */

int extract_intersection(int *out_arr, int a_cnt, int *a, int b_cnt, int *b)
{
  int i = 0, j = 0, x = 0, y = 0, out_cnt = 0;
  while((i < a_cnt) && (j < b_cnt)) {
    if(a[i] < b[j])
      a[x++] = a[i++];
    else if(b[j] < a[i])
      b[y++] = b[j++];
    else {
      out_arr[out_cnt++] = a[i];
      i++;
      j++;
    }
  }
  if(out_cnt) {
    while(i < a_cnt)
      a[x++] = a[i++];
    while(j < b_cnt)
      b[y++] = b[j++];
  }
  return out_cnt;
}

/* Adds a set to an overlay / partition */

void overlay_add_set(int *overlay_cnt, int *overlay_mem,
                     int ***overlay, int *set)
{
  const int initial_overlay_cnt = *overlay_cnt;
  int * const intersection = (int *)MALLOC((set[0] + 1) * sizeof(int));
  int * const set_copy = int_array_new_copy(set[0] + 1, set);
  int i;

  for(i = 0; (i < initial_overlay_cnt) && (set_copy[0] != 0); i++) {

#if DEBUG_WQ && 0
    fprintf(stderr, "%% original left[%i]", i);
    print_set_nl(stderr, (*overlay)[i]);

    fprintf(stderr, "%% original right[%i]", i);
    print_set_nl(stderr, set_copy);
#endif

    intersection[0]
      = extract_intersection(&intersection[1],
                             (*overlay)[i][0], &(*overlay)[i][1],
                             set_copy[0], &set_copy[1]);

#if DEBUG_WQ && 0
    fprintf(stderr, "%% intersection[%i]", i);
    print_set_nl(stderr, intersection);
#endif

    if(intersection[0] != 0) {
      (*overlay)[i][0] -= intersection[0];
      set_copy[0] -= intersection[0];

#if DEBUG_WQ && 0
      fprintf(stderr, "%% reduced left[%i]", i);
      print_set_nl(stderr, (*overlay)[i]);

      fprintf(stderr, "%% reduced right[%i]", i);
      print_set_nl(stderr, set_copy);
#endif

      set_array_add_copy(overlay_cnt, overlay_mem, overlay, intersection);

      if((*overlay)[i][0] == 0) {
        FREE((*overlay)[i]);
        (*overlay)[i] = (*overlay)[--(*overlay_cnt)];
      }
    }
  }

  if(set_copy[0] != 0) {
#if DEBUG_WQ
    fprintf(stderr, "%% ERROR: remaining");
    print_set_nl(stderr, set_copy);
#endif
    set_array_add_copy(overlay_cnt, overlay_mem, overlay, set_copy);
  }

  FREE(intersection);
  FREE(set_copy);
}

/* Turn {aaaa,bb,cc,ddd,eeee,f} into {{ae},{bc},{d},{f}} */

void split_multiset(int *mset, int *pset_cnt, int *pset_mem, int ***psets)
{
  int i, j, mset_cnt = mset[0], *mset_val = &mset[1];
  int *visited = (int *)MALLOC(mset_cnt * sizeof(int));
  int *lengths = (int *)MALLOC(mset_cnt * sizeof(int));

  for(i = 0; i < mset_cnt; i += lengths[i]) {
    lengths[i] = int_array_get_run_length(mset_cnt - i, &mset_val[i]);
    visited[i] = 0;
  }

  for(i = 0; i < mset_cnt; i += lengths[i]) {
    int n, *set;

    if(visited[i])
      continue;

    n = 0;
    for(j = i; j < mset_cnt; j += lengths[j])
      if(lengths[i] == lengths[j])
        n++;

    set = (int *)MALLOC((n + 1) * sizeof(int));
    set[0] = n;
    n = 0;
    for(j = i; j < mset_cnt; j += lengths[j])
      if(lengths[i] == lengths[j]) {
        set[++n] = mset_val[j];
        visited[j] = 1;
      }

    int_array_array_add_array(pset_cnt, pset_mem, psets, set);
  }

  FREE(visited);
  FREE(lengths);
}

/* Turn a family of multi-sets into a family of sets (in a lossy way) */

void split_multiset_family_to_set_family(int mset_cnt, int **msets,
                                         int *pset_cnt, int ***psets)
{
  int i, set_mem = 16;
  *pset_cnt = 0;
  *psets = (int **)MALLOC(set_mem * sizeof(int *));

  for(i = 0; i < mset_cnt; i++)
    split_multiset(msets[i], pset_cnt, &set_mem, psets);
}

/* Creates an overlay of a set family */

void compute_family_overlay(int mset_cnt, int **msets,
                            int *o_overlay_cnt, int ***o_overlay,
                            int are_simple_sets)
{
  int i, set_cnt = mset_cnt, **sets = msets;

  if(!are_simple_sets) {
    split_multiset_family_to_set_family(mset_cnt, msets, &set_cnt, &sets);
#if DEBUG_WQ
    for(i = 0; i < set_cnt; i++) {
      fprintf(stderr, "%% SplitSet[%i]", i);
      print_set_nl(stderr, sets[i]);
    }
#endif
  }

  int overlay_cnt = 0, overlay_mem = 16;
  int **overlay = (int **)MALLOC(overlay_mem * sizeof(int *));

  for(i = 0; i < set_cnt; i++)
    overlay_add_set(&overlay_cnt, &overlay_mem, &overlay, sets[i]);

  if(sets != msets) {
    for(i = 0; i < set_cnt; i++)
      FREE(sets[i]);
    FREE(sets);
  }

  *o_overlay_cnt = overlay_cnt;
  *o_overlay = overlay;
}

/* Wraps an input array into an array of singleton sets
 * TODO: This could be modified to do renaming in order to please multi-sets
 */

void create_family_of_singletons(int c, int *o_cnt, int ***o)
{
  int i, **family = (int **)MALLOC(c * sizeof(int *));

  for(i = 0; i < c; i++) {
    family[i] = (int *)MALLOC(2 * sizeof(int));
    family[i][0] = 1;
    family[i][1] = i;
  }

  *o_cnt = c;
  *o = family;
}

/*
 * Replace all of part in set with part_idx if set contains part
 * That is,
 *            / set \ part U { part_idx }, if part \subseteq set
 *    set <- |
 *            \ set,                       otherwise
 */

int set_try_to_use_part(int set_cnt, int *set_val, int *part, int part_idx)
{
  int part_cnt = part[0], *part_val = &part[1];

  if(sorted_int_array_contains_all(set_cnt, set_val, part_cnt, part_val)) {

    // TODO: Optimize by putting these two together

    sorted_int_array_delete_another(set_cnt, set_val, part_cnt, part_val);

    int_array_insert_no_grow(set_cnt - part_cnt + 1, set_val, 1, &part_idx);

    return part_cnt;
  }

  return 0;
}

/*
 * Rewrite a (multi-)set in terms of overlay parts
 * That is, make it so that
 *
 *    <old-set> = \bigcup_{i \in <new-set>} overlay[i]
 *
 * TODO: with multi-sets, the order of "tries" might be relevant
 */

void multiset_to_part_set(int *set, int overlay_cnt, int **overlay)
{
  int i = 0, del, set_pos = 1, set_rem = set[0];
#if DEBUG_WQ
  fprintf(stderr, "%% multiset_to_part_set:");
  print_set_nl(stderr, set);
#endif
  /* invariant: set[1..set_pos-1] references part indices and
                set[set_pos..] references elements */
  /* NOTE: (i < overlay_cnt) should be redundant */
  while((i < overlay_cnt) && (0 < set_rem)) {
    if((del = set_try_to_use_part(set_rem, &set[set_pos], overlay[i], i))) {
      set_pos++; /* move over the part index inserted by set_try_to_use_part */
      set_rem -= del;
      set[0]  -= del - 1;
#if DEBUG_WQ
      fprintf(stderr, "%% progress (i=%i,del=%i,set_pos=%i,set_rem=%i):",
              i, del, set_pos, set_rem);
      print_set_nl(stderr, set);
#endif
    }
    else {  /* this could be done always when dealing with non-multi sets */
      i++;
    }
  }
#if DEBUG_WQ
  if(set_rem != 0)
    fprintf(stderr, "%% error: set_rem = %i != 0!\n", set_rem);
#endif
}

/*
 * Rewrites a family of sets in terms of overlay parts
 */

void multiset_family_to_part_multiset_family(int set_cnt, int **family,
                                             int overlay_cnt, int **overlay)
{
  int i;
  for(i = 0; i < set_cnt; i++)
    multiset_to_part_set(family[i], overlay_cnt, overlay);
}

/*
 *
 */

typedef struct PLANBNODE PLANBNODE;

/*
 * A binary tree node used in planning merging networks
 */

struct PLANBNODE {
  int occ_cnt;
  int tot_cnt;
  int *res;
  int sub[2];
};

/* Return the size of the biggest set in a collection */

int get_collection_max_size(int c, int **v)
{
  int i, m = 0;
  for(i = 0; i < c; i++)
    m = MAX(m, *(v[i]));
  return m;
}

/* Compute an upper bound for the number of nodes in a (shared) forest */

int get_forest_max_node_count(int collection_cnt, int **collection,
                              int overlay_cnt)
{
  int tree_cnt = collection_cnt;
  int tree_leaf_cnt = get_collection_max_size(collection_cnt, collection);
  int forest_leaf_cnt = overlay_cnt;

  int tree_max_inner_cnt = tree_leaf_cnt - 1;
  return forest_leaf_cnt + tree_max_inner_cnt * tree_cnt;
}

/* Allocate a forest guaranteed to be big enough for given parameters */

PLANBNODE *allocate_forest(int collection_cnt, int **collection,
                           int overlay_cnt)
{
  int n = get_forest_max_node_count(collection_cnt, collection, overlay_cnt);
#if DEBUG_WQ_CNT
  fprintf(stderr, "%% forest_max_node_cnt = %i\n", n);
#endif
  return (PLANBNODE *)MALLOC(n * sizeof(PLANBNODE));
}

/* Initialize a leaf to represent a parallel overlay part */

void init_overlay_leaf(int *part, PLANBNODE *leaf)
{
  leaf->tot_cnt = part[0];
  leaf->res = NULL;
  leaf->sub[0] = -1;
  leaf->sub[1] = -1;
}

/* Initialize a forest to represent a parallel overlay */

void init_overlay_leaves(int overlay_cnt, int **overlay, PLANBNODE *forest)
{
  int i;
  for(i = 0; i < overlay_cnt; i++)
    init_overlay_leaf(overlay[i], &forest[i]);
}

/*
 *
 */

void create_planbnode_pair(int a, int b, PLANBNODE *forest, PLANBNODE *newnode,
                           int occ_cnt)
{
  newnode->occ_cnt = occ_cnt;
  newnode->tot_cnt = forest[a].tot_cnt + forest[b].tot_cnt;
  newnode->res = NULL;
  newnode->sub[0] = a;
  newnode->sub[1] = b;
}

/* ------------------------------------------------------------------------- */

#define PLANBHASH_FIRST(a, b, c)   (((unsigned int) \
                                    (123123 * (a) + 321 * (b))) % (c))
#define PLANBHASH_NEXT(x, a, b, c) (((unsigned int) ((x) + 1)) % (c))

/* Store the queue index of a pair into a hash table */

void planbhash_add(int a, int b, int pair_cnt, PLANBNODE *pair_queue,
                   int hash_cnt, int *hash_table, int i)
{
  unsigned int x = PLANBHASH_FIRST(a, b, hash_cnt);
  int *hash_refs = &hash_table[hash_cnt];
  while((hash_refs[x]++) && (0 <= hash_table[x]))
    x = PLANBHASH_NEXT(x, a, b, hash_cnt);
  hash_table[x] = i;
}

/* Remove the existing queue index of a pair from a hash table */

void planbhash_remove(int a, int b, int pair_cnt, PLANBNODE *pair_queue,
                      int hash_cnt, int *hash_table)
{
  unsigned int x = PLANBHASH_FIRST(a, b, hash_cnt);
  int *hash_refs = &hash_table[hash_cnt];
  while((hash_table[x] < 0) || (pair_queue[hash_table[x]].sub[0] != a)
                            || (pair_queue[hash_table[x]].sub[1] != b)) {
    hash_refs[x]--;
    x = PLANBHASH_NEXT(x, a, b, hash_cnt);
  }
  hash_refs[x]--;
  hash_table[x] = -1;
}

/* Retrieve the queue index of a pair from a hash table or -1 if none exists */

int planbhash_get(int a, int b, int pair_cnt, PLANBNODE *pair_queue,
                  int hash_cnt, int *hash_table)
{
  unsigned int x = PLANBHASH_FIRST(a, b, hash_cnt);
  int *hash_refs = &hash_table[hash_cnt];
  while(hash_refs[x]
        && ((hash_table[x] < 0) || (pair_queue[hash_table[x]].sub[0] != a)
                                || (pair_queue[hash_table[x]].sub[1] != b)))
    x = PLANBHASH_NEXT(x, a, b, hash_cnt);
#if DEBUG_WQ
  fprintf(stderr, "get (%i, %i) = i = %i @ x = %i\n", a, b, hash_table[x], x);
#endif
  return hash_table[x];
}

/* Change the existing queue index of a pair in a hash table  */

void planbhash_change(int a, int b, int pair_cnt, PLANBNODE *pair_queue,
                     int hash_cnt, int *hash_table, int i)
{
  unsigned int x = PLANBHASH_FIRST(a, b, hash_cnt);
  while((hash_table[x] < 0) || (pair_queue[hash_table[x]].sub[0] != a)
                            || (pair_queue[hash_table[x]].sub[1] != b))
    x = PLANBHASH_NEXT(x, a, b, hash_cnt);
  hash_table[x] = i;
}

/* ------------------------------------------------------------------------- */

/*
 *
 */

void enqueue_new_planbnode_pair(int a, int b, PLANBNODE *forest,
                                int *pair_cnt, PLANBNODE *pair_queue,
                                int hash_cnt, int *hash_table,
                                int occ_cnt)
{
  create_planbnode_pair(a, b, forest, &pair_queue[*pair_cnt], occ_cnt);
  planbhash_add(a, b, *pair_cnt, pair_queue, hash_cnt, hash_table, *pair_cnt);
  (*pair_cnt)++;
}

/*
 *
 */

int count_pair_occurrences(int collection_cnt, int **collection, int a, int b)
{
  int i, cnt = 0;
  for(i = 0; i < collection_cnt; i++)
    cnt += sorted_int_array_count_pair_occurrences(collection[i][0],
                                               &collection[i][1], a, b);
  return cnt;
}

/* Find the highest graded queued planbnode */

int find_best_planbnode(int pair_cnt, PLANBNODE *pair_queue)
{
  int i, best = 0;
  for(i = 1; i < pair_cnt; i++) {
    const int x = pair_queue[best].occ_cnt - pair_queue[i].occ_cnt;
    const int y = pair_queue[best].tot_cnt - pair_queue[i].tot_cnt;
    if((x < 0) || ((x == 0) && (0 < y)))
      best = i;
  }
  return best;
}

/* Remove a planbnode from a queue (and a hash table) */

void planbnode_queue_remove(int *pair_cnt, PLANBNODE *pair_queue,
                            int hash_cnt, int *hash_table, int i)
{
  const int j = *pair_cnt - 1;

  planbhash_remove(pair_queue[i].sub[0], pair_queue[i].sub[1],
                   *pair_cnt, pair_queue, hash_cnt, hash_table);

  if(i != j) {
    planbhash_change(pair_queue[j].sub[0], pair_queue[j].sub[1],
                     *pair_cnt, pair_queue, hash_cnt, hash_table, i);

    pair_queue[i] = pair_queue[j];
  }

  *pair_cnt = j;
}

/* Take note of a new occurrence of the pair (a, b) where a <= b */

void note_new_pair_occurrence(int a, int b, int multiplicity,
                              PLANBNODE *forest,
                              int *pair_cnt, PLANBNODE *pair_queue,
                              int hash_cnt, int *hash_table)
{
  int idx = planbhash_get(a, b, *pair_cnt, pair_queue, hash_cnt, hash_table);
  if(idx < 0)
    enqueue_new_planbnode_pair(a, b, forest, pair_cnt, pair_queue,
                               hash_cnt, hash_table, multiplicity);
  else
    pair_queue[idx].occ_cnt += multiplicity;
#if DEBUG_WQ
  idx = planbhash_get(a, b, *pair_cnt, pair_queue, hash_cnt, hash_table);
  fprintf(stderr, "increased(%i,%i)@%i to %i\n",
          a, b, idx, pair_queue[idx].occ_cnt);
#endif
}

/* Take note of the presumably new occurrences (a,z),(b,z),... in (a,b,...),z */

void note_new_pair_occurrences(int *set, int node_idx, int multiplicity,
                               PLANBNODE *forest,
                               int *pair_cnt, PLANBNODE *pair_queue,
                               int pair_pitch, int *pair_table)
{
#if DEBUG_WQ
  fprintf(stderr, "note_new_pair_occurrences(");
  print_set(stderr, set);
  fprintf(stderr, ", %i = %i) PART 1\n", node_idx, multiplicity);
#endif
  int i;
  for(i = 1; i <= set[0]; i++)
    note_new_pair_occurrence(set[i], node_idx, multiplicity, forest,
                             pair_cnt, pair_queue, pair_pitch, pair_table);

#if DEBUG_WQ
  fprintf(stderr, "note_new_pair_occurrences(");
  print_set(stderr, set);
  fprintf(stderr, ", %i = %i) PART 2\n", node_idx, multiplicity);
#endif

  /* Reflexive occurrences */
  const int rmultiplicity = (multiplicity * (multiplicity - 1)) / 2;
  if(rmultiplicity) {
    note_new_pair_occurrence(node_idx, node_idx, rmultiplicity, forest,
                             pair_cnt, pair_queue, pair_pitch, pair_table);
  }
}

/* Take note of a lost occurrence of the pair (a, b) */

void note_lost_pair_occurrence(int a, int b, int multiplicity,
                               PLANBNODE *forest,
                               int *pair_cnt, PLANBNODE *pair_queue,
                               int hash_cnt, int *hash_table)
{
  const int x = MIN(a, b), y = MAX(a, b);
  const int idx = planbhash_get(x, y, *pair_cnt, pair_queue,
                                hash_cnt, hash_table);
#if DEBUG_WQ
  if(idx < 0)
    fprintf(stderr, "%% trying to decrease occurrence count of missing pair"
            " %i %i\n", x, y);
#endif
#if DEBUG_WQ
  fprintf(stderr, "decreasing(%i,%i)@%i to %i\n",
          x, y, idx, pair_queue[idx].occ_cnt - multiplicity);
#endif
  if((pair_queue[idx].occ_cnt -= multiplicity) == 0)
    planbnode_queue_remove(pair_cnt, pair_queue, hash_cnt, hash_table, idx);
#if DEBUG_WQ
  else if(pair_queue[idx].occ_cnt < 0)
    fprintf(stderr, "%% Got negative (%i,%i).occ_cnt = %i\n",
            x, y, pair_queue[idx].occ_cnt);
#endif
}

/* Take note of the lost occurrences
   (a,node_idx),(b,node_idx),...,(y,node_idx) in (a,b,...,y,z) */

void note_lost_pair_occurrences(int *set, int node_idx, int multiplicity,
                                PLANBNODE *forest,
                                int *pair_cnt, PLANBNODE *pair_queue,
                                int hash_cnt, int *hash_table)
{
#if DEBUG_WQ
  fprintf(stderr, "note_lost_pair_occurrences(");
  print_set(stderr, set);
  fprintf(stderr, ", %i = %i) PART 1\n", node_idx, multiplicity);
#endif
  int i;
  for(i = 1; i <= set[0]; i++)
    note_lost_pair_occurrence(set[i], node_idx, multiplicity, forest,
                              pair_cnt, pair_queue, hash_cnt, hash_table);
#if DEBUG_WQ
  fprintf(stderr, "note_lost_pair_occurrences(");
  print_set(stderr, set);
  fprintf(stderr, ", %i = %i) PART 2\n", node_idx, multiplicity);
#endif

  /* Reflexive occurrences */
  const int rmultiplicity = (multiplicity * (multiplicity - 1)) / 2;
  if(rmultiplicity) {
    note_lost_pair_occurrence(node_idx, node_idx, rmultiplicity, forest,
                              pair_cnt, pair_queue, hash_cnt, hash_table);
  }
}

/* Try to rewrite a set using a binary node in place of its children (x,x) */

void set_try_to_use_reflexive_pair(int *set, int node_idx, PLANBNODE *forest,
                                   int *pair_cnt, PLANBNODE *pair_queue,
                                   int hash_cnt, int *hash_table)
{
  PLANBNODE * const node = &forest[node_idx];
  int i, idx, cnt;

  sorted_int_array_get_range_of(set[0], &set[1], node->sub[0], &idx, &cnt);
  const int multiplicity = cnt / 2;

  if(multiplicity) {

    set[0] = int_array_delete_range(set[0], &set[1], idx, 2 * multiplicity);

    note_lost_pair_occurrences(set, node->sub[0], 2 * multiplicity,
                               forest, pair_cnt, pair_queue,
                               hash_cnt, hash_table);

    note_new_pair_occurrences(set, node_idx, multiplicity,
                              forest, pair_cnt, pair_queue,
                              hash_cnt, hash_table);

    for(i = 0; i < multiplicity; i++)
      set[++set[0]] = node_idx;
  }
}

/* Try to rewrite a set using a binary node in place of its children (x,y) */

void set_try_to_use_disjoint_pair(int *set, int node_idx, PLANBNODE *forest,
                                  int *pair_cnt, PLANBNODE *pair_queue,
                                  int hash_cnt, int *hash_table,
                                  int *idx, int *cnt)
{
  PLANBNODE * const node = &forest[node_idx];
  int i;
  const int multiplicity = MIN(cnt[0], cnt[1]);
  cnt[0] = multiplicity;
  cnt[1] = multiplicity;

#if DEBUG_WQ
  if(multiplicity <= 0) {
    fprintf(stderr, "%% Sick multiplicity: %i!!!\n", multiplicity);
    exit(-1);
  }
#endif

#if DEBUG_WQ
  const int z = int_array_is_ascending(set[0], &set[1]);
  int * const zz = int_array_new_copy(set[0] + 1, set);
#endif

  set[0] = int_array_delete_ranges(set[0], &set[1], 2, idx, cnt);

#if DEBUG_WQ
  if(z && !int_array_is_ascending(set[0], &set[1])) {
    fprintf(stderr, "%% Ascending set (idx[0]=%i,idx[1]=%i):\n",
            idx[0], idx[1]);
    print_set_nl(stderr, zz);
    fprintf(stderr, "%% became un-ascending:\n");
    print_set_nl(stderr, set);
  }
  FREE(zz);
#endif

  note_lost_pair_occurrences(set, node->sub[0], multiplicity,
                             forest, pair_cnt, pair_queue,
                             hash_cnt, hash_table);

  note_lost_pair_occurrences(set, node->sub[1], multiplicity,
                             forest, pair_cnt, pair_queue,
                             hash_cnt, hash_table);

#if DEBUG_WQ
fprintf(stderr, "note_lost_pair_occurrence*(");
print_set(stderr, set);
fprintf(stderr, ", %i = %i)\n", node_idx, multiplicity);
#endif

  note_lost_pair_occurrence(node->sub[0], node->sub[1],
                            multiplicity * multiplicity,
                            forest, pair_cnt, pair_queue,
                            hash_cnt, hash_table);

  note_new_pair_occurrences(set, node_idx, multiplicity,
                            forest, pair_cnt, pair_queue,
                            hash_cnt, hash_table);

  for(i = 0; i < multiplicity; i++)
    set[++set[0]] = node_idx;
}

/* Try to rewrite a set using a binary node in place of its children */

void set_try_to_use_pair(int *set, int node_idx, PLANBNODE *forest,
                         int *pair_cnt, PLANBNODE *pair_queue,
                         int hash_cnt, int *hash_table)
{
  PLANBNODE * const node = &forest[node_idx];
  int idx[2], cnt[2];

#if DEBUG_WQ
  fprintf(stderr, "set_try_to_use_pair(");
  print_set(stderr, set);
  fprintf(stderr, ", %i)\n", node_idx);
#endif

  if(node->sub[0] == node->sub[1]) {

    set_try_to_use_reflexive_pair(set, node_idx, forest,
                                  pair_cnt, pair_queue,
                                  hash_cnt, hash_table);

  } else if(sorted_int_array_get_ranges_of(set[0], &set[1],
                                           2, node->sub, idx, cnt) == 2) {

    set_try_to_use_disjoint_pair(set, node_idx, forest,
                                 pair_cnt, pair_queue,
                                 hash_cnt, hash_table,
                                 idx, cnt);
  }
}

/* Rewrites a collection using a binary node in place of a given pair */

void collection_use_pair(int collection_cnt, int **collection,
                         int node_idx, PLANBNODE *forest,
                         int *pair_cnt, PLANBNODE *pair_queue,
                         int hash_cnt, int *hash_table)
{
  int i;
  for(i = 0; i < collection_cnt; i++)
    set_try_to_use_pair(collection[i], node_idx, forest, pair_cnt, pair_queue,
                        hash_cnt, hash_table);
}

/* Turns an n-ary collection into a shared binary forest */

int plan_shared_binary_forest(int collection_cnt, int **collection,
                              int overlay_cnt, PLANBNODE *forest)
{
  int pair_cnt, forest_cnt = overlay_cnt;
  int i, j, occ_cnt;

  /* Compute a bound on memory used for queuing pairs */

  /*int*/ pair_cnt = 0;
  for(i = 0; i < overlay_cnt; i++)
    for(j = i; j < overlay_cnt; j++)
      if (0 != count_pair_occurrences(collection_cnt, collection, i, j))
        pair_cnt++;

  const int max_pair_cnt = PAIR_MAX_BLOWUP(pair_cnt);

#if DEBUG_WQ_CNT
  fprintf(stderr, "%% overlay_cnt = %i, max_pair_cnt = %i\n",
          overlay_cnt, max_pair_cnt);
#endif

  PLANBNODE * const pair_queue
    = (PLANBNODE *)MALLOC(max_pair_cnt * sizeof(PLANBNODE));
  const int hash_cnt = PLANBHASH_OVERFIT(max_pair_cnt);
  int * const hash_table = (int *)MALLOC(2 * hash_cnt * sizeof(int));
  int_array_fill(hash_cnt, hash_table, -1);
  int_array_fill(hash_cnt, &hash_table[hash_cnt], 0);

  /*int*/ pair_cnt = 0;
  for(i = 0; i < overlay_cnt; i++)
    for(j = i; j < overlay_cnt; j++)
      if((occ_cnt = count_pair_occurrences(collection_cnt, collection, i, j))) {
        enqueue_new_planbnode_pair(i, j, forest, &pair_cnt, pair_queue,
                                   hash_cnt, hash_table, occ_cnt);
#if DEBUG_WQ
        fprintf(stderr, "%% Initially (%i,%i).occ_cnt = %i\n",
                i, j, occ_cnt);
#endif
      }

#if DEBUG_WQ_CNT
  int occ_max;

  for(occ_max = i = 0; i < pair_cnt; i++)
    occ_max = MAX(occ_max, pair_queue[i].occ_cnt);

  int * const occ_hist = (int *)calloc(occ_max + 1, sizeof(int));
  int * const occ_sub0 = (int *)calloc(occ_max + 1, sizeof(int));
  int * const occ_sub1 = (int *)calloc(occ_max + 1, sizeof(int));

  for(i = 0; i < pair_cnt; i++) {
    j = pair_queue[i].occ_cnt;
    occ_hist[j]++;
    if((occ_sub0[j] == 0) && (occ_sub1[j] == 0)) {
      occ_sub0[j] = pair_queue[i].sub[0];
      occ_sub1[j] = pair_queue[i].sub[1];
    } else {
      occ_sub0[j] = -1;
      occ_sub1[j] = -1;
    }
  }

  fprintf(stderr, "%% \n");
  fprintf(stderr, "%% Occurrence occurrences:\n");
  for(i = 0; i <= occ_max; i++) {
    if(occ_hist[i]) {
      fprintf(stderr, "%% %i\t-\t%i", i, occ_hist[i]);
      if((0 < occ_sub0[i]) && (0 < occ_sub1[i])) {
        fprintf(stderr, "\t-\t(%i, %i)", occ_sub0[i], occ_sub1[i]);
      }
      fprintf(stderr, "\n");
    }
  }
  fprintf(stderr, "%%\n");

  FREE(occ_hist);
  FREE(occ_sub0);
  FREE(occ_sub1);
#endif

#if DEBUG_WQ_CNT
  const int debug_first_pair_cnt = pair_cnt;
  int debug_max_pair_cnt = 0;
#endif

  while(0 < pair_cnt) {

    const int index = find_best_planbnode(pair_cnt, pair_queue);
    forest[forest_cnt] = pair_queue[index];

#if DEBUG_WQ
    const int new_cnt =
      count_pair_occurrences(collection_cnt, collection, 
                             forest[forest_cnt].sub[0], 
                             forest[forest_cnt].sub[1]);
    fprintf(stderr, "%% Popped (%i, %i) occ_cnt = %i, newly counted = %i\n",
            forest[forest_cnt].sub[0],
            forest[forest_cnt].sub[1],
            forest[forest_cnt].occ_cnt,
            new_cnt);
    if(new_cnt != forest[forest_cnt].occ_cnt)
      exit(-1);
#endif

    collection_use_pair(collection_cnt, collection,
                        forest_cnt, forest,
                        &pair_cnt, pair_queue,
                        hash_cnt, hash_table);


#if DEBUG_WQ_CNT
    debug_max_pair_cnt = MAX(debug_max_pair_cnt, pair_cnt);
#endif

    forest_cnt++;
  }

#if DEBUG_WQ_CNT
  fprintf(stderr,
          "%% pair_cnt:\n"
          "\testimated max: %i\n"
          "\tobserved max:  %i\n"
          "\tobserved first: %i\n"
          "\tobserved last:  %i\n",
          max_pair_cnt,
          debug_max_pair_cnt,
          debug_first_pair_cnt,
          pair_cnt);
#endif

  FREE(pair_queue);
  FREE(hash_table);

  return forest_cnt;
}

/* Turns a single level n-ary tree into a binary tree */

int plan_binary_tree(int *set, int overlay_cnt,
                     int forest_cnt, PLANBNODE *forest)
{
  int i, set_cnt = set[0], *set_val = &set[1];
  for(; 1 < set_cnt; set_cnt = (set_cnt / 2) + (set_cnt % 2)) {
    for(i = 0; i < set_cnt / 2; i++) {
      create_planbnode_pair(set_val[2 * i], set_val[2 * i + 1],
                            forest, &forest[forest_cnt], 0);
      set_val[i] = forest_cnt++;
    }
    if(set_cnt % 2)
      set_val[i] = set_val[set_cnt - 1];
  }
  return forest_cnt;
}

/* Turns an n-ary collection into a binary forest (of independent trees) */

int plan_independent_binary_forest(int collection_cnt, int **collection,
                                   int overlay_cnt, PLANBNODE *forest)
{
  int i, forest_cnt = overlay_cnt;
  for(i = 0; i < collection_cnt; i++)
    forest_cnt = plan_binary_tree(collection[i], overlay_cnt,
                                  forest_cnt, forest);
  return forest_cnt;
}

/* Turns an n-ary collection into a binary forest */

int plan_binary_forest(int collection_cnt, int **collection,
                       int overlay_cnt, PLANBNODE *forest,
                       int independently)
{
  if(independently)

    return plan_independent_binary_forest(collection_cnt, collection,
                                          overlay_cnt, forest);

  else

    return plan_shared_binary_forest(collection_cnt, collection,
                                     overlay_cnt, forest);
}

/* Initializes the result arrays of all trees in a forest */

void init_forest_results(int forest_cnt, PLANBNODE *forest, int fillvalue)
{
  int i, j, n = 0;

  for(i = 0; i < forest_cnt; i++)
    n += forest[i].tot_cnt;

  forest[0].res = (int *)MALLOC(n * sizeof(int));
  int_array_fill(n, forest[0].res, fillvalue);

  for(j = i = 0; i < forest_cnt; j += forest[i++].tot_cnt)
    forest[i].res = &forest[0].res[j];
}

/* Cleans up after allocate_forest and init_forest_results */

void free_forest(int forest_cnt, PLANBNODE *forest)
{
  FREE(forest[0].res);
  FREE(forest);
}

/* Divide all elements in an array with their greatest common divisor */

int int_array_divide_with_gcd(int c, int *v)
{
  int div = int_array_gcd(c, v);
  int i;

  for(i = 0; i < c; i++)
    v[i] /= div;

  return div;
}

/* Perform gcd simplification on the components of a weight rule */

int weight_divide_with_gcd(int bound, int c, int *v)
{
  const int div = int_array_divide_with_gcd(c, v);
  return (bound / div) + (bound % div != 0);
}

/* Collect buckets and return a radix */

void collect_weight_buckets(ARGS *args, int bound, int tot_cnt, int *w,
                            int *collection_cnt, int ***collection, int **radix)
{
  const int w_max_i = int_array_max_index(tot_cnt, w);
  /* +1 is for the element count that will be stored in bucket[0] */
  const int bucket_mem = RADIX_MAX_BLOWUP(args->radix_ub, tot_cnt) + 1;
  int * const bucket = (int *)MALLOC(bucket_mem * sizeof(int));
  int i, j, bucket_cnt;

  *collection_cnt = 0;
  *collection = (int **)MALLOC(8 * sizeof(int) * sizeof(int *));
  *radix = (int *)MALLOC(8 * sizeof(int) * sizeof(int));

  while(1) {
    int div = pick_divisor(bound, tot_cnt, w, w[w_max_i],
                           args->radix_lb, args->radix_ub,
                           bucket_mem);

    if(w[w_max_i] / div == 0)
      div = WQ_RADIX_INF;

#if DEBUG_WQ
    fprintf(stderr, "collect_weight_buckets: div: %i\n", div);
#endif

    for(bucket_cnt = i = 0; i < tot_cnt; i++)
      for(j = w[i] % div; j; j--)
        bucket[++bucket_cnt] = i;

    for(i = 0; i < tot_cnt; i++)
      w[i] /= div;

    bucket[0] = bucket_cnt;

    (*collection)[*collection_cnt] = int_array_new_copy(bucket[0] + 1, bucket);
    (*radix)[*collection_cnt] = div;
    (*collection_cnt)++;

    if(w[w_max_i] == 0)
      break;

    bound = (bound / div) + ((bound % div) != 0);
  }

  FREE(bucket);
}

/**/

void identity_propagate_w(int c, int *dst, int *src)
{
  int i;
  for(i = 0; i < c; i++)
    if(SMX_IS_WANTED(src[i]))
      dst[i] = SMX_WANTED;
}

/* Initialize things and assign and propagate w/x information */
// TODO: Uses collection & forest only for roots

void init_forest_root_mergers(int bound, int collection_cnt, int **collection,
                              int *radix, PLANBNODE *forest,
                              int **o_merge_cnt, int ***o_merge,
                              int **o_bound_rem)
{
  int i, merge_tot_cnt = 0, carry_cnt = 0;

  *o_merge_cnt = (int *)MALLOC(collection_cnt * sizeof(int));
  *o_bound_rem = (int *)MALLOC(collection_cnt * sizeof(int));

  for(i = 0; i < collection_cnt; i++) {
    const int root = collection[i][1];
    const int bucket_cnt = forest[root].tot_cnt;

    const int merge_cnt = bucket_cnt + carry_cnt;
    merge_tot_cnt += merge_cnt;

    (*o_merge_cnt)[i] = merge_cnt;
    (*o_bound_rem)[i] = bound;

    const int div = radix[i];
    carry_cnt = ((merge_cnt - (bound - 1 + div) % div) + div - 1) / div;
    bound = (bound / div) + ((bound % div) != 0);

#if DEBUG_WQ
    fprintf(stderr, "computed carry_cnt = %i on %i for %i\n",
            carry_cnt, i, i + 1);
#endif
  }

  *o_merge = (int **)MALLOC(collection_cnt * sizeof(int *));
  int *merge = (int *)MALLOC(merge_tot_cnt * sizeof(int));
  int *carry;
  int_array_fill(merge_tot_cnt, merge, SMX_DONT_CARE);
  merge[(*o_bound_rem)[collection_cnt - 1] - 1] = SMX_WANTED;

  for(i = collection_cnt - 1; 0 < i; i--, merge = carry) {
    PLANBNODE * const root = &forest[collection[i][1]];
    const int bucket_cnt = root->tot_cnt;
    const int merge_cnt = (*o_merge_cnt)[i];
    carry_cnt = merge_cnt - bucket_cnt;
    carry = &merge[merge_cnt];

#if DEBUG_WQ
    fprintf(stderr, "fetched carry_cnt = %i at %i\n", carry_cnt, i);
#endif

    (*o_merge)[i] = merge;

    propagate_merger_w(merge_cnt, merge,
                          carry_cnt, carry,
                          root->tot_cnt, root->res,
                          0, NULL, NULL);

    const int div = radix[i - 1];
    bound = (*o_bound_rem)[i - 1];

#if DEBUG_WQ
    fprintf(stderr, "scatter(cnt=%i,offset=%i,stride=%i)\n",
            (*o_merge_cnt)[i - 1], bound - 1, div);
#endif

    // TODO: Make sure offset is non-negative and then simplify int_array_scatter
    int_array_scatter((*o_merge_cnt)[i - 1], carry, bound - 1, div, SMX_DONT_CARE);

#if DEBUG_WQ
    fprintf(stderr, "%% spread carry: %s\n",
            a2x((*o_merge_cnt)[i - 1], carry));
#endif
  }

  (*o_merge)[i] = merge;
  identity_propagate_w((*o_merge_cnt)[0], forest[collection[0][1]].res, merge);
}

/**/
// TODO: Uses collection & forest only for roots

void output_forest_root_mergers(ARGS *args,
                                int collection_cnt, int **collection,
                                int *radix, PLANBNODE *forest,
                                int *merge_cnt, int **merge, int *bound_rem)
{
  int i;

  int_array_copy(merge_cnt[0], merge[0], forest[collection[0][1]].res);

  for(i = 1; i < collection_cnt; i++) {
    PLANBNODE * const root = &forest[collection[i][1]];

#if DEBUG_WQ
    fprintf(stderr, "unscatter(cnt=%i,offset=%i,stride=%i)\n",
            merge_cnt[i - 1], bound_rem[i - 1] - 1, radix[i - 1]);

    fprintf(stderr, "carry before unscatter: %s\n",
            a2x(merge_cnt[i - 1], merge[i - 1]));
#endif

    // TODO: Make sure offset is non-negative and then simplify int_array_unscatter
    const int carry_cnt = int_array_unscatter(merge_cnt[i - 1], merge[i - 1],
                                          bound_rem[i - 1] - 1, radix[i - 1]);

#if DEBUG_WQ
    fprintf(stderr, "carry after unscatter: %s\n",
            a2x(carry_cnt, merge[i - 1]));
    fprintf(stderr, "Output merger forest[collection[%i][1]] = %i\n",
            i, collection[i][1]);
    fprintf(stderr, "carry_cnt = %i\n", carry_cnt);
#endif
    output_unary_merger(args,
                        merge_cnt[i], merge[i],
                        carry_cnt, merge[i - 1],
                        root->tot_cnt, root->res,
                        0, INT_MAX);
  }
}

/**/

void tree_propagate_w(int i, PLANBNODE *forest)
{
  const int a = forest[i].sub[0];
  const int b = forest[i].sub[1];
  if(0 <= a) {
    int a_summary, b_summary;
    propagate_merger_w(forest[i].tot_cnt, forest[i].res,
                          forest[a].tot_cnt, forest[a].res,
                          forest[b].tot_cnt, forest[b].res,
                          0, &a_summary, &b_summary);
    if(SMX_IS_WANTED(a_summary))
      tree_propagate_w(a, forest);
    if(SMX_IS_WANTED(b_summary))
      tree_propagate_w(b, forest);
  }
}

/* Propagates W(/X) information from the roots of a forest downward */

void forest_propagate_w(int collection_cnt, int **collection,
                        PLANBNODE *forest)
{
  int i;
  for(i = 0; i < collection_cnt; i++)
    tree_propagate_w(collection[i][1], forest);
}

/**/

void tree_print(FILE *out, int idx, int **overlay, PLANBNODE *forest)
{
  if(forest[idx].sub[0] == -1)
    print_set(out, overlay[idx]);
  else {
    fprintf(out, " (");
    tree_print(out, forest[idx].sub[0], overlay, forest);
    fprintf(out, " :");
    tree_print(out, forest[idx].sub[1], overlay, forest);
    fprintf(out, " )");
  }
}

/* Outputs the sorters and mergers represented by a planned forest */

void output_forest_sorters(ARGS *args, 
                           int overlay_cnt, int **overlay,
                           int forest_cnt, PLANBNODE *forest)
{
  int startatom = INT_MAX;
  int i;
  for(i = 0; i < overlay_cnt; i++) {
    output_unary_sorter(args,
                        forest[i].tot_cnt, forest[i].res,
                        overlay[i][0], &overlay[i][1],
                        &startatom);
  }
  for(; i < forest_cnt; i++) {
    const int a = forest[i].sub[0];  /* < i */
    const int b = forest[i].sub[1];  /* < i */
    output_unary_merger(args,
                        forest[i].tot_cnt, forest[i].res,
                        forest[a].tot_cnt, forest[a].res,
                        forest[b].tot_cnt, forest[b].res,
                        0, INT_MAX);
  }
}

/**/

void output_dot_header(FILE *out)
{
  fprintf(stderr, "digraph {\n");
  fprintf(stderr, "\trankdir=BT\n");
  fprintf(stderr, "\tsplines=spline\n");
  fprintf(stderr, "\tnode [shape=\"box\"]\n");
}

void output_dot_end(FILE *out)
{
  fprintf(stderr, "}\n");
  fflush(stderr);
}

/**/

void output_readable_literal_1(FILE *out, int mix, ATAB *table)
{
  if(MIX_IS_NEG(mix))
    fputs("not ", out);
  output_atom(STYLE_READABLE, out, MIX_GET_ATOM(mix), table);
}

/**/

void output_forest_as_dot(FILE *out,
                          int collection_cnt, int **collection,
                          int overlay_cnt, int **overlay,
                          int forest_cnt, PLANBNODE *forest,
                          ATAB *table)
{
  int i, j;

  /* Mark roots */

  for(i = 0; i < collection_cnt; i++)
    fprintf(out, "\t%i [penwidth=6.0]\n", collection[i][1]);

  /* Put all sorters in one rankset */

  fprintf(out, "\tsubgraph {\n");
  fprintf(out, "\t\trank=same\n");
  for(i = 0; i < overlay_cnt; i++)
    fprintf(out,  "\t\t%i\n", i);
  fprintf(out, "\t}\n");

  /* Put all overlay elements in one rankset */

  fprintf(out, "\tsubgraph {\n");
  fprintf(out, "\t\trank=same\n");
  for(i = 0; i < overlay_cnt; i++)
    for(j = 0; j < overlay[i][0]; j++) {
      fprintf(out, "\t\t_%u [label=\"", overlay[i][j + 1]);
      output_readable_literal_1(out, overlay[i][j + 1], table);
      fprintf(out, "\" fontsize=%f]\n", 32.0);
    }
  fprintf(out, "\t}\n");

  /* Output sorter nodes */

  for(i = 0; i < overlay_cnt; i++) {
    const double d = sqrt((double) forest[i].tot_cnt);
    fprintf(out, "\t%i [label=\"Sorter %i\" fontsize=%f]\n",
            i, forest[i].tot_cnt, 32.0 * d);
    for(j = 0; j < overlay[i][0]; j++)
      fprintf(out, "\t_%u -> %i\n", overlay[i][j + 1], i);
  }

  /* Output merger nodes */

  for(; i < forest_cnt; i++) {
    const int a = forest[i].sub[0];  /* < i */
    const int b = forest[i].sub[1];  /* < i */
    const double d = sqrt((double) forest[i].tot_cnt);
    fprintf(out, "\t%i [label=\"Merger %i,%i\" fontsize=%f]\n",
            i, forest[a].tot_cnt, forest[b].tot_cnt, 32.0 * d);
    fprintf(out, "\tsubgraph { %i %i } -> %i [arrowsize=%f]\n",
            a, b, i, 1.0 * d);
  }
}

/**/

int output_roots_as_dot(FILE *out, int collection_cnt, int **collection,
                        int *radix, int forest_cnt, PLANBNODE *forest,
                        int *merge_cnt, int **merge, int *bound_rem)
{
  int i, prev = collection[0][1], newidx = forest_cnt;

  for(i = 1; i < collection_cnt; i++, prev = newidx, newidx++) {
    const int root = collection[i][1];
    const double d = sqrt((double) merge_cnt[i]);
    const int carry_cnt = int_array_unscatter_size(merge_cnt[i - 1],
                                                   bound_rem[i - 1] - 1,
                                                   radix[i - 1]);
    fprintf(out, "\t%i [label=\"Merger %i,%i\" arrowsize=%f fontsize=%f]\n",
            newidx, carry_cnt, forest[root].tot_cnt, 1.0 * d, 32.0 * d);
    fprintf(out, "\t%i -> %i [label=\" %i+%ii\" arrowsize=%f fontsize=%f"
            " style=dashed]\n",
            prev, newidx,
            ((bound_rem[i - 1] - 1 + radix[i - 1]) % radix[i - 1]) + 1,
            radix[i - 1], 1.0 * d, 12.0 * d);
    fprintf(out, "\t%i -> %i [arrowsize=%f]\n", root, newidx, 1.0 * d);
  }

  return prev;
}

/**/

int output_head_as_dot(FILE *out, int top_root_node, int aux_head, int index,
                       ATAB *table)
{
  int aux_head_node = top_root_node + 1;
  double font_scale = sqrt((double) (index + 1));

  /* Create a node for the head */
  fprintf(out, "\t_%i [label=\"", aux_head_node);
  output_readable_literal_1(out, aux_head, table);
  fprintf(out, "\" fontsize=%f]\n", 32.0);

  /* Draw an edge */
  fprintf(out, "\t%i -> _%i [label=\" %i\" arrowsize=%f fontsize=%f"
          " style=dashed]\n",
          top_root_node, aux_head_node, index + 1, 1.0, 12.0 * font_scale);

  return aux_head_node;
}

/*
 *
 */

void output_planned_weight_counter(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;
  const int neg_cnt = weight->neg_cnt, pos_cnt = weight->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt, head = weight->head;
  int * const mix = weight->neg, * const w = weight->weight;
  const int bound = weight_divide_with_gcd(weight->bound, tot_cnt, w);

  int collection_cnt = 0, overlay_cnt = 0, forest_cnt;
  int **collection = NULL;
  int *radix = NULL;
  int **overlay = NULL;
  int *merge_cnt, **merge, *bound_rem;
  PLANBNODE *forest = NULL;

  int head_index, aux_head;
  int i, j;

  litint_from_neg(neg_cnt, mix);
  permute_weighted_array_in_place(args, tot_cnt, mix, w);

  collect_weight_buckets(args, bound, tot_cnt, w,
                         &collection_cnt, &collection, &radix);

#if DEBUG_WQ
  for(i = 0; i < collection_cnt; i++) {
    fprintf(stderr, "%% Collection[%i]", i);
    print_set_nl(stderr, collection[i]);
  }
#endif

  if(args->flavors & FL_WT_PLAN_FAMILY_SINGLETON)

    create_family_of_singletons(tot_cnt, &overlay_cnt, &overlay);

  else /* if(args->flavors & FL_WT_PLAN_FAMILY_OVERLAY) */

    compute_family_overlay(collection_cnt, collection, &overlay_cnt, &overlay,
                           (2 == int_array_max(collection_cnt, radix)));

#if DEBUG_WQ
  fprintf(stderr, "%% tot_cnt = %i, collection_cnt = %i, overlay_cnt = %i\n",
          tot_cnt, collection_cnt, overlay_cnt);
#endif

#if DEBUG_WQ
  for(i = 0; i < overlay_cnt; i++) {
    fprintf(stderr, "%% Overlay[%i]", i);
    print_set_nl(stderr, overlay[i]);
  }
#endif

  multiset_family_to_part_multiset_family(collection_cnt, collection,
                                          overlay_cnt, overlay);

#if DEBUG_WQ
  for(i = 0; i < collection_cnt; i++) {
    fprintf(stderr, "%% P.S.Collection[%i]", i);
    print_set_nl(stderr, collection[i]);
  }
#endif

#if DEBUG_WQ
  for(i = 0; i < collection_cnt; i++)
    if(!int_array_is_ascending(collection[i][0], &collection[i][1])) {
      fprintf(stderr, "%% Set is not ascending:");
      print_set_nl(stderr, collection[i]);
    }
#endif

  forest = allocate_forest(collection_cnt, collection, overlay_cnt);
  init_overlay_leaves(overlay_cnt, overlay, forest);
  forest_cnt = plan_binary_forest(collection_cnt, collection,
                                  overlay_cnt, forest,
                                  (args->flavors & FL_WT_PLAN_INDEPENDENT ? 1 : 0));

#if DEBUG_WQ
  for(i = 0; i < collection_cnt; i++) {
    fprintf(stderr, "%% Collection(final)[%i]", i);
    print_set_nl(stderr, collection[i]);
  }
#endif

  init_forest_results(forest_cnt, forest, SMX_DONT_CARE);

  for(i = 0; i < overlay_cnt; i++)
    for(j = 0; j < overlay[i][0]; j++)
      overlay[i][j + 1] = mix[overlay[i][j + 1]];

  init_forest_root_mergers(bound, collection_cnt, collection, radix, forest,
                           &merge_cnt, &merge, &bound_rem);

  forest_propagate_w(collection_cnt, collection, forest);

#if DEBUG_WQ

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% radix [%i] = %i\n", i, radix[i]);

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% bound_rem [%i] = %i\n", i, bound_rem[i]);

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% merge_cnt [%i] = %i\n", i, merge_cnt[i]);

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% merge [%i] = %s\n", i, a2x(merge_cnt[i], merge[i]));

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% bucket_cnt [%i] = %i\n",
            i, forest[collection[i][1]].tot_cnt);

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% carry_cnt [%i] = %i\n",
            i, merge_cnt[i] - forest[collection[i][1]].tot_cnt);

  for(i = 0; i < collection_cnt; i++) {
    fprintf(stderr, "%% forest[collection[%i][1]]:", i);
    tree_print(stderr, collection[i][1], overlay, forest);
    fprintf(stderr, "\n");
  }

  for(i = 0; i < collection_cnt; i++)
    fprintf(stderr, "%% forest[collection[%i][1]].res: %s\n",
            i, a2x(forest[collection[i][1]].tot_cnt,
            forest[collection[i][1]].res));
#endif

  output_forest_sorters(args, overlay_cnt, overlay, forest_cnt, forest);

  output_forest_root_mergers(args, collection_cnt, collection, radix, forest,
                             merge_cnt, merge, bound_rem);

  head_index = bound_rem[collection_cnt - 1] - 1;
  aux_head = merge[collection_cnt - 1][head_index];
  litint_output_normal(args, head, 1, &aux_head);

  if(args->flavors & FL_WT_PLAN_DOT) {
    output_dot_header(stderr);
    output_forest_as_dot(stderr, collection_cnt, collection,
                         overlay_cnt, overlay, forest_cnt, forest,
                         args->table);
    fprintf(stderr, "\n");
    int top_root_node
      = output_roots_as_dot(stderr, collection_cnt, collection, radix,
                            forest_cnt, forest, merge_cnt, merge, bound_rem);
    fprintf(stderr, "\n");
    (void) output_head_as_dot(stderr, top_root_node, head, head_index,
                              args->table);
    output_dot_end(stderr);
  }

  for(i = 0; i < collection_cnt; i++)
    FREE(collection[i]);
  FREE(collection);

  FREE(radix);

  for(i = 0; i < overlay_cnt; i++)
    FREE(overlay[i]);
  FREE(overlay);

  free_forest(forest_cnt, forest);

  FREE(merge_cnt);
  FREE(merge[collection_cnt - 1]);
  FREE(merge);
  FREE(bound_rem);
}

/* ========================= Planned Optimize Counter ===================== */

void output_mixed_radix_optimize(ARGS *args, RULE *rule,
                                 int collection_cnt, int **collection,
                                 int *radix, PLANBNODE *forest, int wgcd)
{
  OPTIMIZE_RULE * const optimize = rule->data.optimize;
  int i, j, factor, tot_cnt = 0, new_cnt = 0;

  for(factor = 1, i = 0; i < collection_cnt; factor *= radix[i++]) {
    PLANBNODE * const root = &forest[collection[i][1]];

    tot_cnt += root->tot_cnt;
  }

  int * const res = (int *)MALLOC(2 * tot_cnt * sizeof(int));
  int * const weight = &res[tot_cnt];

  for(factor = wgcd, i = 0; i < collection_cnt; factor *= radix[i++]) {
    PLANBNODE * const root = &forest[collection[i][1]];

    for(j = 0; j < root->tot_cnt; j++) {
      res[new_cnt] = root->res[j];
      weight[new_cnt] = factor;
      new_cnt++;
    }
  }

  /* Give names to new atoms */

  if(*args->optimize_format != '\0') {
    litint_rename_neg(args, new_cnt, res);
    add_optimize_format_names(args, new_cnt, res, weight);
  }

  FREE(optimize->neg);  /* This frees pos & weight as well */

  litint_to_optimize(new_cnt, res, optimize);
  args_output_optimize(args, rule);
}

int get_unary_residue_size(int div, int cnt)
{
  return MIN(div - 1, cnt);
}

int output_unary_residue(ARGS *args, int div, int *res, int cnt, int *mix)
{
  int i, b, body[2];

  for(i = 0; i <= cnt; i++) {
    const int j = i % div;

    if(j == 0) {

      b = (i + div <= cnt ? 1 : 0);
      if(b)
        body[0] = MIX_COMPLEMENT(mix[i + div - 1]);

    } else if(!SMX_IS_DONT_CARE(res[j - 1])) {

      if(SMX_IS_WANTED(res[j - 1]))
        res[j - 1] = args->newatom++;

      body[b] = mix[i - 1];
      litint_output_normal(args, res[j - 1], b + 1, body);
    }
  }

  return get_unary_residue_size(div, cnt);
}

void output_unique_mixed_radix_optimize(ARGS *args, RULE *rule,
                                        int collection_cnt, int **collection,
                                        int *radix, PLANBNODE *forest, int wgcd)
{
  OPTIMIZE_RULE * const optimize = rule->data.optimize;
  int max_cnt = 0, tot_cnt = 0;
  int *mem[2], aux_cnt[3], *aux[3], *res, *weight;
  int * const residue_size_array = (int *)MALLOC(collection_cnt * sizeof(int));
  int i, j, pos, num, div, factor;

#if DEBUG_WQ
  fprintf(stderr, "%% Radix = %s\n", a2x(collection_cnt, radix));
#endif

  /* Pass 1: calculate total number of literals and the largest bucket size */

  pos = 0;
  div = 1;
  aux_cnt[2] = 0;
  for(factor = wgcd, i = 0; i < collection_cnt; factor *= radix[i++]) {
    PLANBNODE * const root = &forest[collection[i][1]];

    aux_cnt[0] = int_array_unscatter_size(aux_cnt[2], div - 1, div);
    aux_cnt[1] = root->tot_cnt;
    aux_cnt[2] = aux_cnt[0] + aux_cnt[1];

    max_cnt = MAX(max_cnt, aux_cnt[2]);

    div = radix[i];
    num = get_unary_residue_size(div, aux_cnt[2]);
    pos += num;

    residue_size_array[i] = num;  /* Cache the size for convenience */
  }
  tot_cnt = pos;

  mem[0] = (int *)MALLOC(2 * max_cnt * sizeof(int));
  mem[1] = &mem[0][max_cnt];

  res = (int *)MALLOC(2 * tot_cnt * sizeof(int));
  int_array_fill(tot_cnt, res, SMX_WANTED);
  weight = &res[tot_cnt];

  /* Pass 2: Output a merger and a residue program for each bucket */

  pos = 0;
  div = 1;
  aux_cnt[2] = 0;
  aux[2]     = NULL;
  for(factor = wgcd, i = 0; i < collection_cnt; factor *= radix[i++]) {
    PLANBNODE * const root = &forest[collection[i][1]];

    aux[0]     = aux[2];
    aux_cnt[0] = int_array_unscatter(aux_cnt[2], aux[0], div - 1, div);
    aux[1]     = root->res;
    aux_cnt[1] = root->tot_cnt;
    aux[2]     = mem[i % 2];
    aux_cnt[2] = aux_cnt[0] + aux_cnt[1];

    int_array_fill(aux_cnt[2], aux[2], SMX_WANTED);
    output_unary_merger(args,
                        aux_cnt[2], aux[2],
                        aux_cnt[0], aux[0],
                        aux_cnt[1], aux[1],
                        0, INT_MAX);

    div = radix[i];
    num = output_unary_residue(args, div, &res[pos], aux_cnt[2], aux[2]);
#if DEBUG_WQ
    fprintf(stderr, "%% Residue of %s / %i = %s\n",
            a2x(aux_cnt[2], aux[2]), div, a2x(num, &res[pos]));
#endif
    int_array_fill(num, &weight[pos], factor);
    pos += num;
  }

  /* Output one or more optimization statements */

  if(*args->optimize_format != '\0') {
    /* Give names to new atoms, and rename all negative literals */

    litint_rename_neg(args, tot_cnt, res);
    add_optimize_format_names(args, tot_cnt, res, weight);
  }

#if DEBUG_WQ
  fprintf(stderr, "%% Output #minimize[%s = %s].\n",
          a2x(tot_cnt, res), a2x(tot_cnt, weight));
#endif

  /* Prepare a temporary optimization rule for printing purposes */
  RULE out_rule;
  OPTIMIZE_RULE out_optimize;
  out_rule.type           = TYPE_OPTIMIZE;
  out_rule.data.optimize  = &out_optimize;
  out_rule.next           = NULL;

  if(args->flavors & FL_OPT_PLAN_MANY) {
    /* output increasingly significant optimize statements */

    int *tmp = mem[0]; /* Reuse this arbitrarily */

    pos = 0;
    for(i = 0; i < collection_cnt; i++) {

      num = residue_size_array[i];

      /* Copy literals to a temporary array and use 1 for all weights */
      int_array_copy(num, tmp, &res[pos]);
      for(j = 0; j < num; j++)
        tmp[num + j] = 1;

      litint_to_optimize(num, tmp, &out_optimize);
      args_output_optimize(args, &out_rule);
      pos += num;
    }

  } else {
    /* output a single optimize statement */

    litint_to_optimize(tot_cnt, res, &out_optimize);
    args_output_optimize(args, &out_rule);
  }

  FREE(mem[0]);
  FREE(res);
  FREE(residue_size_array);
}

/*
 * Re-represent optimize statement literals in a unary mixed base
 */

void plan_optimize(ARGS *args, RULE *rule)
{
  OPTIMIZE_RULE * const optimize = rule->data.optimize;
  const int neg_cnt = optimize->neg_cnt, pos_cnt = optimize->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt;
  int * const mix = optimize->neg, * const w = optimize->weight;
  const int wgcd = int_array_divide_with_gcd(tot_cnt, w);

  int collection_cnt = 0, overlay_cnt = 0, forest_cnt;
  int **collection = NULL, *radix = NULL, **overlay = NULL;
  PLANBNODE *forest = NULL;

  int i, j;

  litint_from_neg(neg_cnt, mix);
  permute_weighted_array_in_place(args, tot_cnt, mix, w);

  /* INT_MAX is hopefully somewhat non-intrusive here */
  collect_weight_buckets(args, INT_MAX, tot_cnt, w,
                         &collection_cnt, &collection, &radix);

  if(args->flavors & FL_OPT_PLAN_FAMILY_SINGLETON)

    create_family_of_singletons(tot_cnt, &overlay_cnt, &overlay);

  else /* if(args->flavors & FL_WT_PLAN_FAMILY_OVERLAY) */

    compute_family_overlay(collection_cnt, collection, &overlay_cnt, &overlay,
                           (2 == int_array_max(collection_cnt, radix)));

  multiset_family_to_part_multiset_family(collection_cnt, collection,
                                          overlay_cnt, overlay);

  forest = allocate_forest(collection_cnt, collection, overlay_cnt);
  init_overlay_leaves(overlay_cnt, overlay, forest);
  forest_cnt = plan_binary_forest(collection_cnt, collection,
                                  overlay_cnt, forest,
                                  (args->flavors & FL_OPT_PLAN_INDEPENDENT ? 1 : 0));

  init_forest_results(forest_cnt, forest, SMX_WANTED);

  for(i = 0; i < overlay_cnt; i++)
    for(j = 0; j < overlay[i][0]; j++)
      overlay[i][j + 1] = mix[overlay[i][j + 1]];

  if(args->flavors & FL_OPT_PLAN_DOT) {
    output_dot_header(stderr);
    output_forest_as_dot(stderr, collection_cnt, collection,
                         overlay_cnt, overlay, forest_cnt, forest,
                         args->table);
    output_dot_end(stderr);
  }

  output_forest_sorters(args, overlay_cnt, overlay, forest_cnt, forest);

  for(i = 0; i < overlay_cnt; i++)
    FREE(overlay[i]);
  FREE(overlay);

  if(args->flavors & FL_OPT_PLAN_HALF)
    /* Stop here and output a non-unique representation of the weight sum */

    output_mixed_radix_optimize(args, rule, collection_cnt, collection,
                                radix, forest, wgcd);

  else /* if(args->flavors & FL_OPT_PLAN_NEG) */
    /* Construct and output a unique representation of the weight sum */

    output_unique_mixed_radix_optimize(args, rule, collection_cnt, collection,
                                       radix, forest, wgcd);

  for(i = 0; i < collection_cnt; i++)
    FREE(collection[i]);
  FREE(collection);

  FREE(radix);

  free_forest(forest_cnt, forest);
}

#endif
