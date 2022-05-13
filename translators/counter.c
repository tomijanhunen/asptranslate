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
 * counter.c -- Routines related to counters
 *
 * (c) 2002, 2004 Tomi Janhunen
 */

#include <stdlib.h>
#include <stdio.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

#include "scc.h"
#include "counter.h"

void _version_counter_c()
{
  _version("$RCSfile: counter.c,v $",
	   "$Date: 2021/05/27 11:43:43 $",
	   "$Revision: 1.8 $");
}

#define RESERVE_ATOMS(counter,count) counter; counter+=count

VTAB *allocate_counters(int *newatom, OCCTAB *reftab)
{
  int count = reftab->count;
  VTAB *rvalue = (VTAB *)malloc(sizeof(VTAB)*(count+1));
  VTAB *new = rvalue;

  while(reftab) {
    int offset = reftab->offset;
    int i = 0;

    new->count = count;
    new->offset = offset;
    new->vectors = (VECTOR **)malloc(sizeof(VECTOR *)*(count+1));

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = definition(reftab, atom);
      int scc_size = d->scc_size;

      if(scc_size>1) {
	VECTOR *nvec = (VECTOR *)malloc(sizeof(VECTOR));
	int bits = base2log(scc_size+1);

	nvec->length = bits;
	nvec->counter = RESERVE_ATOMS(*newatom, 2*bits);
	nvec->successor = RESERVE_ATOMS(*newatom, 2*bits);
	new->vectors[i] = nvec;
      } else
	new->vectors[i] = NULL;
    }

    if(reftab = reftab->next) {
      count = reftab->count;
      new->next = (VTAB *)malloc(sizeof(VTAB)*(count +1));
      new = new->next;
    } else
      new->next = NULL;
  }

  return rvalue;
}

VECTOR *find_vectors(VTAB *vtab, int atom)
{
  while(vtab) {
    int count = vtab->count;
    int offset = vtab->offset;
    if(atom > offset && atom <= offset+count)
      return (vtab->vectors)[atom-offset];
    vtab = vtab->next;
  }
  return NULL;
}

int base2log(int n)
{
  int result = 0;

  n--;
  while(n)
    n=n/2, result++;
  return result;
}

void write_atom_if_possible(int style, FILE *out, int atom, ATAB *table)
{
  if(table) 
    write_atom(style, out, atom, table);
  else {
    if(style == STYLE_READABLE)
      fprintf(out, "_%i", atom);
    else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom);
  }
  return;
}

/*
 * generate_sel -- Choose a value for a counter (conditionally)
 */

void generate_sel(int style, FILE *out, int bits,
		  int atom, ATAB *table, int vec,
		  int atom2, ATAB *table2)
{
  int i = 0;
  int negvec = vec+bits;

  if(style == STYLE_READABLE) {

    fprintf(out, "%% Subprogram SEL_%i(", bits);
    write_atom_if_possible(style, out, atom, table);
    fputs(",", out);
    write_atom_if_possible(style, out, atom2, table2);
    fputs("):\n\n", out);

    for(i=0; i<bits; i++) {
      
      fprintf(out, "_one_%i_", i);
      write_atom_if_possible(style, out, atom, table);
      fprintf(out, " :- not _zero_%i_", i);
      write_atom_if_possible(style, out, atom, table);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ".\n");

      fprintf(out, "_zero_%i_", i);
      write_atom_if_possible(style, out, atom, table);
      fprintf(out, " :- not _one_%i_", i);
      write_atom_if_possible(style, out, atom, table);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ".\n");

    }

    fputs("\n", out);

  } else if(style == STYLE_SMODELS) {

    int cond = atom2;

    if(table2)
      cond += table2->shift;

    for(i=0; i<bits; i++) {

      fprintf(out, "1 %i 2 2 %i %i\n", vec+i, negvec+i, cond);
      fprintf(out, "1 %i 2 2 %i %i\n", negvec+i, vec+i, cond);

    }

  }

  return;
}

/*
 * generate_nxt -- The value of the latter counter is the successor
 *                 of the value of the former counter (conditionally)
 */

void generate_nxt(int style, FILE *out, int bits,
		  int atom, ATAB *table, ATAB *negtable, int vec,
		  int atom2, ATAB *table2, int vec2)
{
  int i = 0;
  int negvec = vec+bits;
  int negvec2 = vec2+bits;
  
  if(style == STYLE_READABLE) {

    fprintf(out, "%% Subprogram NXT_%i(", bits);
    write_atom_if_possible(style, out, atom, table);
    fputs(",", out);
    write_atom_if_possible(style, out, atom2, table2);
    fputs(",", out);
    write_atom_if_possible(style, out, atom, negtable);
    fputs("):\n\n", out);

    for(i=0; i<bits; i++) {

      /* Three combinations that cause the bit be 1 */

      fprintf(out, "_one_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _one_%i_", i);
      write_atom_if_possible(style, out, atom, table);
      if(i+1<bits) {
	fprintf(out, ", not _zero_%i_", i+1);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, ", not _one_%i_", i+1);
	write_atom_if_possible(style, out, atom2, table2);
      }
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, atom, negtable);
      fprintf(out, ".\n");

      if(i+1<bits) {
	fprintf(out, "_one_%i_", i);
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, " :- not _zero_%i_", i);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, ", not _one_%i_", i+1);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, ", not ");
	write_atom_if_possible(style, out, atom, negtable);
	fprintf(out, ".\n");
      }

      if(i+1<bits) {
	fprintf(out, "_one_%i_", i);
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, " :- not _zero_%i_", i);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, ", not _zero_%i_", i+1);
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, ", not ");
	write_atom_if_possible(style, out, atom, negtable);
	fprintf(out, ".\n");
      }

      /* By default, the bit is 0 */

      fprintf(out, "_zero_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _one_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, atom, negtable);
      fprintf(out, ".\n");
    }
    fputs("\n", out);

  } else if(style == STYLE_SMODELS) {

    for(i=0; i<bits; i++) {

      int cond = atom + negtable->shift;

      /* Three combinations that cause the bit be 1 */

      if(i+1<bits)
	fprintf(out, "1 %i 4 4 %i %i %i %i\n",
		vec2+i, vec+i, negvec+i+1, vec2+i+1, cond);
      else
	fprintf(out, "1 %i 2 2 %i %i\n", vec2+i, vec+i, cond);

      if(i+1<bits) {
	fprintf(out, "1 %i 3 3 %i %i %i\n",
		vec2+i, negvec+i, vec+i+1, cond);
	fprintf(out, "1 %i 3 3 %i %i %i\n",
		vec2+i, negvec+i, negvec2+i+1, cond);
      }

      /* By default, the bit is 0 */

      fprintf(out, "1 %i 2 2 %i %i\n", negvec2+i, vec2+i, cond);

    }
  }

  return;
}

/*
 * generate_zero -- Make all bits of a counter zero (conditionally)
 */

void generate_clear(int style, FILE *out, int bits,
		    int atom, ATAB *table, int vec,
		    int body_false, int contradiction)
{
  int negvec = vec+bits;

  if(style == STYLE_READABLE) {
    int i = 0;

    fprintf(out, "%% Subprogram CLEAR_%i(", bits);
    write_atom_if_possible(style, out, atom, table);
    fputs("):\n\n", out);

    for(i=0; i<bits; i++) {
      fprintf(out, "_%i :- not _zero_%i_", contradiction, i);
      write_atom_if_possible(style, out, atom, table);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, ".\n");
    }
    fputs("\n", out);

  } else if(style == STYLE_SMODELS) {
    int i = 0;

    for(i=0; i<bits; i++) {
      fprintf(out, "1 %i 2 2 %i", contradiction, negvec+i);
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, "\n");
    }

  }

  return;
}

/*
 * generate_lthan -- Compare the values of two counters using
 *                   the lower than / greater than or equal relation
 */

void generate_lthan(int style, FILE *out, int bits,
	            int atom1, ATAB *table1, int vec1,
	            int atom2, ATAB *table2, int vec2,
		    int vec, int body_false)
{
  int i = 0;
  int negvec = vec+bits;
  int negvec1 = vec1+bits;
  int negvec2 = vec2+bits;

  /* The first bits (position 0) of vec and negvec determine answer */

  if(style == STYLE_READABLE) {

    fprintf(out, "%% Subprogram LTHAN_%i(", bits);
    write_atom_if_possible(style, out, atom1, table1);
    fputs(",", out);
    write_atom_if_possible(style, out, atom2, table2);
    fputs("):\n\n", out);

    for(i=0; i<bits; i++) {

      fprintf(out, "_lt_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, "_");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _one_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, ", not _zero_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, ".\n");

      fprintf(out, "_geq_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, "_");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _lt_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, "_");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, ".\n");

      if((i+1)<bits) {

	fprintf(out, "_lt_%i_", i);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, "_");
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, " :- not _one_%i_", i);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, ", not _one_%i_", i);
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, ", not _geq_%i_", i+1);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, "_");
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, ", not ");
	write_atom_if_possible(style, out, body_false, NULL);
	fprintf(out, ".\n");

	fprintf(out, "_lt_%i_", i);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, "_");
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, " :- not _zero_%i_", i);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, ", not _zero_%i_", i);
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, ", not _geq_%i_", i+1);
	write_atom_if_possible(style, out, atom1, table1);
	fprintf(out, "_");
	write_atom_if_possible(style, out, atom2, table2);
	fprintf(out, ", not ");
	write_atom_if_possible(style, out, body_false, NULL);
	fprintf(out, ".\n");

      }
    }
    fputs("\n", out);

  } else if(style == STYLE_SMODELS) {

    for(i=0; i<bits; i++) {

      fprintf(out, "1 %i 3 3 %i %i %i\n",
	      vec+i, vec1+i, negvec2+i, body_false);
      fprintf(out, "1 %i 2 2 %i %i\n", negvec+i, vec+i, body_false);
      if((i+1)<bits) {
	fprintf(out, "1 %i 4 4 %i %i %i %i\n",
		vec+i, vec1+i, vec2+i, negvec+i+1, body_false);
	fprintf(out, "1 %i 4 4 %i %i %i %i\n",
		vec+i, negvec1+i, negvec2+i, negvec+i+1, body_false);
      }

    }

  }

  return;
}

/*
 * generate_equality -- Compare the values of two counter using
 *                      equality / inequality relation
 */

void generate_equality(int style, FILE *out, int bits,
	               int atom1, ATAB *table1, int vec1,
	               int atom2, ATAB *table2, int vec2,
		       int eq, int body_false)
{
  int i = 0;
  int negvec1 = vec1+bits;
  int negvec2 = vec2+bits;
  int neq = eq+1;

  /* The atoms eq and neq determine answers to (in)equality */

  if(style == STYLE_READABLE) {

    fprintf(out, "%% Subprogram EQ_%i(", bits);
    write_atom_if_possible(style, out, atom1, table1);
    fputs(",", out);
    write_atom_if_possible(style, out, atom2, table2);
    fputs("):\n\n", out);

    /* Equality by default */

    fprintf(out, "_eq_");
    write_atom_if_possible(style, out, atom1, table1);
    fprintf(out, "_");
    write_atom_if_possible(style, out, atom2, table2);
    fprintf(out, " :- not _neq_");
    write_atom_if_possible(style, out, atom1, table1);
    fprintf(out, "_");
    write_atom_if_possible(style, out, atom2, table2);
    fprintf(out, ", not ");
    write_atom_if_possible(style, out, body_false, NULL);
    fprintf(out, ".\n");

    for(i=0; i<bits; i++) {

      /* Exceptions to equality */

      fprintf(out, "_neq_");
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, "_");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _zero_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, ", not _one_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, ".\n");

      fprintf(out, "_neq_");
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, "_");
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, " :- not _one_%i_", i);
      write_atom_if_possible(style, out, atom1, table1);
      fprintf(out, ", not _zero_%i_", i);
      write_atom_if_possible(style, out, atom2, table2);
      fprintf(out, ", not ");
      write_atom_if_possible(style, out, body_false, NULL);
      fprintf(out, ".\n");
    }
    fputs("\n", out);

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "1 %i 2 2 %i %i\n", eq, neq, body_false);

    for(i=0; i<bits; i++) {

	fprintf(out, "1 %i 3 3 %i %i %i\n",
		neq, negvec1+i, vec2+i, body_false);
	fprintf(out, "1 %i 3 3 %i %i %i\n",
		neq, vec1+i, negvec2+i, body_false);
    }
  }

  return;
}

/* Miscellaneous routines */

void write_symbols_for_counters(int style, FILE *out, ATAB *table,
				OCCTAB *occtable, VTAB *vtab)
{
  while(table) {
    int count = table->count;
    int offset = table->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      VECTOR *vec = find_vectors(vtab, atom);

      if(vec) {
	int b = 0;
	int counter = vec->counter;
	int successor = vec->successor;
	DEF *d = definition(occtable, atom);
	int scc_size = d->scc_size;
	int bits = base2log(scc_size+1);

	for(b=0; b<bits; b++)
	  if(style == STYLE_READABLE) {
	  
	    fprintf(out, "%% _%i = _one_%i_", counter+b, b);
	    write_atom(style, out, atom, table);
	    fputs("\n", out);

	  } else if(style == STYLE_SMODELS) {
	  
	    fprintf(out, "%i _one_%i_", counter+b, b);
	    write_atom(STYLE_READABLE, out, atom, table);
	    fputs("\n", out);

	  }

	for(b=0; b<bits; b++)
	  if(style == STYLE_READABLE) {

	    fprintf(out, "%% _%i = _zero_%i_", counter+bits+b, b);
	    write_atom(style, out, atom, table);
	    fputs("\n", out);

	  } else if(style == STYLE_SMODELS) {
	  
	    fprintf(out, "%i _zero_%i_", counter+bits+b, b);
	    write_atom(STYLE_READABLE, out, atom, table);
	    fputs("\n", out);

	  }

	for(b=0; b<bits; b++)
	  if(style == STYLE_READABLE) {

	    fprintf(out, "%% _%i = _one_%i_nxt_", successor+b, b);
	    write_atom(style, out, atom, table);
	    fputs("\n", out);

	  } else if(style == STYLE_SMODELS) {

	    fprintf(out, "%i _one_%i_nxt_", successor+b, b);
	    write_atom(STYLE_READABLE, out, atom, table);
	    fputs("\n", out);

	  }

	for(b=0; b<bits; b++)
	  if(style == STYLE_READABLE) {

	    fprintf(out, "%% _%i = _zero_%i_nxt_", successor+bits+b, b);
	    write_atom(style, out, atom, table);
	    fputs("\n", out);

	  } else if(style == STYLE_SMODELS) {

	    fprintf(out, "%i _zero_%i_nxt_", successor+bits+b, b);
	    write_atom(STYLE_READABLE, out, atom, table);
	    fputs("\n", out);
	  }
      }
    }

    table = table->next;
  }
  return;
}
