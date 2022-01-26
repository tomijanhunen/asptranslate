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
 * Functions for using implications instead of equivalences
 *
 * (c) 2014 Jori Bomanson
 */

//#include "atom.h"
//#include "rule.h"

#include "args.h"

/*
 * Remove rules of the form "a :- b." where a is an atom with a known status
 * and compensate by updating the status of b.
 */

void backpropagate_statuses(RULE **program, ATAB *table)
{
  RULE **prevnext = program;
  RULE *scan = *program;

  while(scan) {

    int is_grabbed = 0;

    if(scan->type == TYPE_BASIC) {

      BASIC_RULE *basic = scan->data.basic;

      if(basic->neg_cnt + basic->pos_cnt == 1) {

        int head_atom = basic->head;
        int status = get_status(table, head_atom);

        if(status & MARK_FALSE) {

          int body_atom = basic->neg[0];  // See input.c
          int is_body_neg = (basic->neg_cnt != 0);
          int mask = (is_body_neg ? MARK_TRUE : MARK_FALSE);

          set_status(table, body_atom, mask);

          *prevnext = scan->next;
          free_rule(scan);
          scan = *prevnext;

          is_grabbed = 1;
        }
      }
    }

    if(!is_grabbed) {
      prevnext = &scan->next;
      scan = scan->next;
    }
  }
}

/*
 * Output a choice rule for the atoms in [auxstart, auxlimit)
 */

void add_aux_choice(ARGS *args, int auxstart, int auxlimit)
{
  if(!(args->flavors & FL_CH_AUX))
    return;

  int count = auxlimit - auxstart;
  if (count <= 0)
    return;

  int *choice = MALLOC(count * sizeof(*choice));
  int i;

  for (i = 0; i < count; i++)
    choice[i] = auxstart + i;

  normalize_choice_head(args, count, choice);

  FREE(choice);
}

/*
 * If applicable, output a choice rule for the atoms in [auxstart, auxlimit)
 */

void try_add_aux_choice(ARGS *args, int head, int auxstart, int auxlimit)
{
  if(!(args->flavors & FL_CH_AUX))
    return;

  if(!(get_status(args->table, head) & MARK_FALSE))
    return;

  add_aux_choice(args, auxstart, auxlimit);
}
