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
 * counter.h -- Routines related to counters
 *
 * (c) 2002, 2004 Tomi Janhunen
 *
 * External definitions
 */

extern void _version_counter_c();

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
			 int atom, ATAB *table, ATAB *negtable, int vec,
			 int atom2, ATAB *table2, int vec2);

extern void generate_lthan(int style, FILE *out, int bits,
			   int atom1, ATAB *table1, int vec1,
			   int atom2, ATAB *table2, int vec2,
			   int vec, int body_false);

extern void generate_equality(int style, FILE *out, int bits,
			      int atom1, ATAB *table1, int vec1,
			      int atom2, ATAB *table2, int vec2,
			      int eq, int body_false);

extern void generate_clear(int style, FILE *out, int bits,
			   int atom, ATAB *table, int vec,
			   int body_false, int contradiction);

extern void write_symbols_for_counters(int style, FILE *out, ATAB *table,
				       OCCTAB *occtab, VTAB *vtab);

