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
 * Definitions related to strongly connected components (SCCs)
 *
 * (c) 2004-2006 Tomi Janhunen
 */

#define _SCC_H_RCSFILE  "$RCSfile: scc.h,v $"
#define _SCC_H_DATE     "$Date: 2021/05/27 11:30:47 $"
#define _SCC_H_REVISION "$Revision: 1.12 $"

extern void _version_scc_c();

/* Defining rules */

typedef struct def {
  int rule_cnt;        /* Number of defining rules */
  RULE **rules;        /* First rule */
  int scc;             /* Number of the strongly connected component */
  int scc_size;        /* Size of the srongly connected component */
  int visited;         /* For Tarjan's algorithm */
  int status;          /* Status bits */
  int border_size;     /* Number of border atoms within the SCC */
  int other;           /* Corresponding atom in the other program */
} DEF;

/* Occurrences in rule bodies */

typedef struct occ {
  int rule_cnt;        /* Number of rules */
  RULE **rules;        /* First rule */
} OCC;

/* Occurrence tables (analogous to atom tables) */

typedef struct occtab {
  int count;                /* Number of atoms/references */
  int offset;               /* Index = atom number - offset */
  DEF *def;                 /* Head occurrences (defining rules) */
  OCC *pbody;               /* Positive occurrences in body */
  OCC *nbody;               /* Negative occurrences in body */
  struct occtab *next;      /* Next piece (if any) */
  ATAB *atoms;              /* Respective atom table */
} OCCTAB;

/* Control flags */

#define SCC_NEG         0x1 /* Activate also negative dependencies */
#define SCC_SKIP_CHOICE 0x2 /* Ignore dependencies of choice atoms */

extern void scc_set(int mask);
extern void scc_clear(int mask);
extern OCCTAB *initialize_occurrences(ATAB *table, int pb, int nb);
extern void compute_occurrences(RULE *program, OCCTAB *occtab,
				int prune, int special_atom);
extern void free_occurrences(OCCTAB *occtab);
extern DEF *definition(OCCTAB *occtab, int atom);
extern OCC *pbody_occs(OCCTAB *occtab, int atom);
extern OCC *nbody_occs(OCCTAB *occtab, int atom);
extern void compute_sccs(OCCTAB *occtable, int max_atom);
extern void compute_borders(OCCTAB *occtable, int max_atom);
extern void print_sccs(int style, FILE *out, int zip, OCCTAB *occtable);
extern void merge_sccs(OCCTAB *occtab, int max_atom);
