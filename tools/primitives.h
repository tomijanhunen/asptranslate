/* asptranslate -- Translation-Based ASP under ASPTOOLS

   Copyright (C) 2022 Tomi Janhunen

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
 * primitives.h -- Routines related to counters (for lp2lp)
 *
 * (c) 2002, 2004-2005 Tomi Janhunen
 *
 * External definitions
 */

extern void _version_primitives_c();

typedef struct vector {
  int length;            /* Number of bits */
  int counter;           /* Counter1 starts from this atom */
  int successor;         /* Counter2 starts from this atom */
} VECTOR;

typedef struct vtab {
  int count;
  int offset;
  VECTOR **vectors;
  struct vtab *next;
} VTAB;

VTAB *allocate_counters(int *newatom, OCCTAB *occtab);
VECTOR *find_vectors(VTAB *vtab, int atom);
extern int base2log(int n);

extern void generate_sel(int style, FILE *out, int bits,
                         int atom, ATAB *table, int vec,
                         int atom2, ATAB *table2);

extern void generate_nxt(int style, FILE *out, int bits,
                         int atom, ATAB *table, int vec,
                         int atom2, ATAB *table2, int vec2);

extern void generate_clr(int style, FILE *out, int bits,
			 int atom, ATAB *table, int vec,
			 int body_true, int contradiction);

extern void generate_eq(int style, FILE *out, int bits,
			int atom1, ATAB *table1, int vec1,
			int atom2, ATAB *table2, int vec2,
			int eq);

extern void generate_lt(int style, FILE *out, int bits,
                        int atom1, ATAB *table1, int vec1,
                        int atom2, ATAB *table2, int vec2,
                        int vec);

extern void generate_eq_and_lt(int style, FILE *out, int bits,
			       int atom, ATAB *table, int counter,
			       int atom2, ATAB *table2, int counter2,
			       int eq, int vec);

extern void write_atom_if_possible(int style, FILE *out,
				   int atom, ATAB *table);

extern void write_symbols_for_counters(int style, FILE *out, ATAB *table,
                                       OCCTAB *occtab, VTAB *vtab);
