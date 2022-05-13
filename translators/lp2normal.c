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
 * LP2NORMAL -- Transform an SMODELS program into a normal program
 *
 * (c) 2009-2012 Tomi Janhunen
 *
 * Main program and routines for rule level translation
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <libgen.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

void _version_lp2normal_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: lp2normal.c,v $",
	   "$Date: 2021/05/27 11:38:21 $",
	   "$Revision: 1.16 $");
  _version_atom_c();
  _version_input_c();
  _version_rule_c();
  _version_symbol_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   lp2normal <options> [<file>]\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "   -ca -- Adder-based translation for cardinalities\n");
  fprintf(stderr, "   -cb -- Binary translation for cardinalities\n");
  fprintf(stderr, "   -cu -- Unary translation for cardinalities\n");
  fprintf(stderr, "   -k  -- Keep choice rules\n");
  fprintf(stderr, "   -kc -- Keep cardinality rules\n");
  fprintf(stderr, "   -kw -- Keep weight rules\n");
  fprintf(stderr, "   -ko -- Keep optimize statements\n");
  fprintf(stderr, "   -r  -- Raw translation without simplification\n");

  fprintf(stderr, "\n");

  return;
}

#define FL_ADDER     0x01
#define FL_BINARY    0x02
#define FL_UNARY     0x04
#define FL_RAW       0x08
#define FL_KEEP_CO   0x10
#define FL_KEEP_WT   0x20
#define FL_KEEP_CH   0x40
#define FL_KEEP_OPT  0x80

void normalize_program(int style, FILE *out, RULE *rule,
		       ATAB *table, int flavors, int newatom);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL;

  ATAB *table = NULL;       /* For the original program */

  int size = 0, number = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;

  char *arg = NULL;
  int which = 0;
  int error = 0;
  int flavors = 0;

  program_name = argv[0];

  /* Process options */

  for(which=1; which<argc; which++) {
    arg = argv[which];

    if(strcmp(arg, "-h") == 0 || strcmp(arg, "--help") == 0)
      option_help = -1;
    else if(strcmp(arg, "--version") == 0)
      option_version = -1;
    else if(strcmp(arg, "-v") == 0)
      option_verbose = -1;
    else if(strcmp(arg, "-ca") == 0)
      flavors |= FL_ADDER;
    else if(strcmp(arg, "-cb") == 0)
      flavors |= FL_BINARY;
    else if(strcmp(arg, "-cu") == 0)
      flavors |= FL_UNARY;
    else if(strcmp(arg, "-r") == 0)
      flavors |= FL_RAW;
    else if(strcmp(arg, "-k") == 0)
      flavors |= FL_KEEP_CH;
    else if(strcmp(arg, "-kc") == 0)
      flavors |= FL_KEEP_CO;
    else if(strcmp(arg, "-kw") == 0)
      flavors |= FL_KEEP_WT;
    else if(strcmp(arg, "-ko") == 0)
      flavors |= FL_KEEP_OPT;
    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }

  }

  if(option_help) usage();
  if(option_version) _version_lp2normal_c();

  if(option_help || option_version)
    exit(0);

  if(error) {
    usage();
    exit(-1);
  }

  /* Read in logic programs */

  if(file == NULL)
    file = "-";

  if(strcmp("-", file) == 0) {
    in = stdin;
  } else {
    if((in = fopen(file, "r")) == NULL) {
      fprintf(stderr, "%s: cannot open file %s\n", program_name, file);
      exit(-1);
    }
  }

  program = read_program(in);
  table = read_symbols(in);
  number = read_compute_statement(in, table);

  size = table_size(table);

  /* Produce the desired output */

  if(option_verbose) {

    fprintf(out, "%% Program '%s' normalized:\n\n", basename(file));
    normalize_program(STYLE_READABLE, out, program, table, flavors, size+1);
    fprintf(out, "\n");

    fprintf(out, "compute { ");
    write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE_OR_FALSE);
    fprintf(out, " }.\n\n");

    write_input(STYLE_READABLE, out, table);

    fprintf(out, "%% The symbols of '%s' (%i symbols):\n\n",
            basename(file), size);
    write_symbols(STYLE_READABLE, out, table);
    fprintf(out, "\n");

  } else {

    normalize_program(STYLE_SMODELS, out, program, table, flavors, size+1);
    fprintf(out, "0\n");

    write_symbols(STYLE_SMODELS, out, table);
    fprintf(out, "0\n");

    fprintf(out, "B+\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_TRUE);
    fprintf(out, "0\n");

    fprintf(out, "B-\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_FALSE);
    fprintf(out, "0\n");

    fprintf(out, "E\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_INPUT);
    fprintf(out, "0\n");

    fprintf(out, "%i\n", number);
  }

  exit(0);
}

/* --------------------------- Local Routines ------------------------------ */

void output_normal(int style, FILE *out, int head,
		   int pos_cnt, int *pos, int neg_cnt, int *neg, ATAB *table);

int rename_positive(int style, FILE *out,
		    int pos_cnt, int *pos,
		    ATAB *table, int newatom)
{
  int i = 0;

  for(i=0; i<pos_cnt; i++) {
    int head = newatom++;
    output_normal(style, out, head, 1, &pos[i], 0, NULL, table);
    pos[i] = head;
  }

  return newatom;
}

int rename_negative(int style, FILE *out,
		    int neg_cnt, int *neg,
		    ATAB *table, int newatom)
{
  int i = 0;

  for(i=0; i<neg_cnt; i++) {
    int head = newatom++;
    output_normal(style, out, head, 0, NULL, 1, &neg[i], table);
    neg[i] = head;
  }

  return newatom;
}

int rename_literals(int style, FILE *out, RULE *rule,
			 ATAB *table, int newatom)
{
  switch(rule->type) {
  case TYPE_BASIC:
    { BASIC_RULE *basic = rule->data.basic;

      newatom = rename_negative(style, out,
 			        basic->neg_cnt, basic->neg,
			        table, newatom);

      newatom = rename_positive(style, out,
 			        basic->pos_cnt, basic->pos,
			        table, newatom);

      /* See input.c */
      basic->pos = basic->neg;
      basic->pos_cnt += basic->neg_cnt;
      basic->neg_cnt = 0;
    }
    break;

  case TYPE_CONSTRAINT:
    { CONSTRAINT_RULE *constraint = rule->data.constraint;

      newatom = rename_negative(style, out,
 			        constraint->neg_cnt, constraint->neg,
			        table, newatom);

      newatom = rename_positive(style, out,
 			        constraint->pos_cnt, constraint->pos,
			        table, newatom);

      /* See input.c */
      constraint->pos = constraint->neg;
      constraint->pos_cnt += constraint->neg_cnt;
      constraint->neg_cnt = 0;
    }
    break;

  case TYPE_CHOICE:
    { CHOICE_RULE *choice = rule->data.choice;

      newatom = rename_negative(style, out,
 			        choice->neg_cnt, choice->neg,
			        table, newatom);

      newatom = rename_positive(style, out,
 			        choice->pos_cnt, choice->pos,
			        table, newatom);

      /* See input.c */
      choice->pos = choice->neg;
      choice->pos_cnt += choice->neg_cnt;
      choice->neg_cnt = 0;
    }
    break;

  case TYPE_WEIGHT:
    { WEIGHT_RULE *weight = rule->data.weight;

      newatom = rename_negative(style, out,
 			        weight->neg_cnt, weight->neg,
			        table, newatom);

      newatom = rename_positive(style, out,
 			        weight->pos_cnt, weight->pos,
			        table, newatom);

      /* See input.c */
      weight->pos = weight->neg;
      weight->pos_cnt += weight->neg_cnt;
      weight->neg_cnt = 0;
    }
    break;

  default:
    fprintf(stderr, "%s: rule type %i not supported!\n",
	    program_name, rule->type);
    exit(-1);
  }

  return newatom;
}

/*
 * output_atom -- Write a (new) atom in an appropriate style
 */

void output_atom(int style, FILE *out, int atom, ATAB *table)
{
  ATAB *piece = find_atom(table, atom);

  if(style != STYLE_READABLE && style != STYLE_SMODELS) {
      fprintf(stderr, "%s: unknown style %i for _%i\n",
	      program_name, style, atom);
      exit(-1);
  }

  if(piece) {
    /* The atom is within the scope of the symbol table */

    int offset = piece->offset;
    int shift = piece->shift;
    SYMBOL **names = piece->names;
    SYMBOL *name = names[atom-offset];

    if(style == STYLE_READABLE) {

      if(name)
	write_name(out, name, piece->prefix, piece->postfix);
      else
	fprintf(out, "_%i", atom+shift);

    } else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom+shift);

  } else {
    /* The atom is new atom outside the scope of the symbol table */

    if(style == STYLE_READABLE)
      fprintf(out, "_%i", atom);
    else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom);

  }

  return;
}

/*
 * output_literal_list -- Output lists of positive and negative literals
 */

void output_literal_list(int style, FILE *out, char *separator,
			 int pos_cnt, int *pos,
			 int neg_cnt, int *neg,
			 ATAB *table)
{
  int *scan = NULL;
  int *last = NULL;

  for(scan = neg, last = &neg[neg_cnt];
      scan != last; ) {
    if(style == STYLE_READABLE)
      fprintf(out, "not ");
    output_atom(style, out, *scan, table);
    scan++;
    if(style == STYLE_READABLE)
      if(scan != last || pos_cnt)
	fputs(separator, out);
  }

  for(scan = pos, last = &pos[pos_cnt];
      scan != last; ) {
    output_atom(style, out, *scan, table);
    scan++;
    if(style == STYLE_READABLE)
      if(scan != last)
	fputs(separator, out);
  }

  return;
}

/*
 * output_normal -- Print a normal rule (as a basic rule)
 */

void output_normal(int style, FILE *out,
		   int head, int pos_cnt, int *pos, int neg_cnt, int *neg,
		   ATAB *table)
{
  int *scan = NULL;
  int *last = NULL;

  if(style == STYLE_SMODELS)
    fprintf(out, "1");

  output_atom(style, out, head, table);

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", (pos_cnt+neg_cnt), neg_cnt);

  if(pos_cnt || neg_cnt) {
    if(style == STYLE_READABLE)
      fprintf(out, " :- ");

    output_literal_list(style, out, ", ",
			pos_cnt, pos,
			neg_cnt, neg, table);
  }

  if(style == STYLE_READABLE)
    fprintf(out, ".");
  fprintf(out, "\n");

  return;
}

/*
 * output_normal_cond -- Output a normal rule with potential extra conditions
 */

void output_normal_cond(int style, FILE *out, int head,
			int pos_cnt, int *pos, int pos_cond,
			int neg_cnt, int *neg, int neg_cond,
			ATAB *table)
{
  int *new_pos = NULL, *new_neg = NULL;
  
  if(pos_cond) {
    int i = 0;

    new_pos = (int *)malloc((pos_cnt+1)*sizeof(int));

    for(i = 0; i<pos_cnt; i++)
      new_pos[i] = pos[i];
    new_pos[pos_cnt] = pos_cond;

  } else
    new_pos = pos;

  if(neg_cond) {
    int i = 0;

    new_neg = (int *)malloc((neg_cnt+1)*sizeof(int));

    for(i = 0; i<neg_cnt; i++)
      new_neg[i] = neg[i];
    new_neg[neg_cnt] = neg_cond;

  } else
    new_neg = neg;

  output_normal(style, out, head,
		pos_cond ? pos_cnt+1 : pos_cnt, new_pos,
		neg_cond ? neg_cnt+1 : neg_cnt, new_neg,
		table);

  if(pos_cond) free(new_pos);
  if(neg_cond) free(new_neg);

  return;
}

/*
 * output_literal_rules -- Output a rule for each literal
 */

void output_literal_rules(int style, FILE *out,
			  RULE *rule, ATAB *table)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt;
  int neg_cnt = constraint->neg_cnt;
  int *scan = NULL, *last = NULL;

  if(pos_cnt)
    for(scan = constraint->pos, last = &scan[pos_cnt]; scan != last; scan++)
      output_normal(style, out, constraint->head, 1, scan, 0, NULL, table);

  if(neg_cnt)
    for(scan = constraint->neg, last = &scan[neg_cnt]; scan != last; scan++)
      output_normal(style, out, constraint->head, 0, NULL, 1, scan, table);

  return;
}

/*
 * output_literal_pair_rules -- Output a rule for each literal pair
 */

void output_literal_pair_rules(int style, FILE *out,
			       RULE *rule, ATAB *table)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt;
  int neg_cnt = constraint->neg_cnt;
  int *scan = NULL, *last = NULL;

  if(pos_cnt)
    for(scan = constraint->pos, last = &scan[pos_cnt];
	scan != last; scan++) {
      int *scan2 = NULL, *last2 = NULL;
      int new_pos[2] = {0, 0};

      new_pos[0] = *scan;

      for(scan2 = constraint->pos, last2 = &scan2[pos_cnt];
	  scan2 != last2; scan2++) {

	if(scan < scan2) {
	  new_pos[1] = *scan2;

	  output_normal(style, out, constraint->head,
			2, new_pos, 0, NULL, table);
	}
      }

      if(scan < constraint->neg)
	for(scan2 = constraint->neg, last2 = &scan2[neg_cnt];
	    scan2 != last2; scan2++)
	  output_normal(style, out, constraint->head,
			1, scan, 1, scan2, table);
    }

  if(neg_cnt)
    for(scan = constraint->neg, last = &scan[neg_cnt];
	scan != last; scan++) {
      int *scan2 = NULL, *last2 = NULL;
      int new_neg[2] = {0, 0};

      if(scan<constraint->pos)
	for(scan2 = constraint->pos, last2 = &scan2[pos_cnt];
	    scan2 != last2; scan2++)
	  output_normal(style, out, constraint->head,
			1, scan2, 1, scan, table);

      new_neg[0] = *scan;

      for(scan2 = constraint->neg, last2 = &scan2[neg_cnt];
	  scan2 != last2; scan2++) {

	if(scan < scan2) {
	  new_neg[1] = *scan2;
	    
	  output_normal(style, out, constraint->head,
			0, NULL, 2, new_neg, table);
	}
      }
    }

  return;
}

/*
 * output_counting_chain -- Count atoms up to two using a chain
 */

int output_counting_chain(int style, FILE *out, RULE *rule,
			  ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *scan = NULL, *last = NULL;
  int previous = newatom++;
      
  if(pos_cnt) {

    /* Generate: f_1 :- l_1. */

    output_normal(style, out,
		  previous, 1, constraint->pos, 0, NULL, table);

    scan = constraint->pos;

    for(last = &scan[pos_cnt], scan=&scan[1]; scan != last; scan++) {
      int new_pos[2] = {0, 0};

      /* For i>1: a :- f_(i-1), l_i. */

      new_pos[0] = previous;
      new_pos[1] = *scan;
      output_normal(style, out, constraint->head,
		    2, new_pos, 0, NULL, table);

      /* For i>1: f_i :- f_(i-1). */

      output_normal(style, out, newatom, 1, &previous, 0, NULL, table);
      previous = newatom++;

      /* For i>1: f_i :- l_i. */

      output_normal(style, out, previous, 1, scan, 0, NULL, table);
    }
  }

  if(neg_cnt) {

    if(!pos_cnt)   /* Generate: f_1 :- l_1. */
      output_normal(style, out,
		    previous, 0, NULL, 1, constraint->neg, table);

    scan = constraint->neg;

    for(last = &scan[neg_cnt], scan = (pos_cnt ? &scan[0] : &scan[1]);
	scan != last; scan++) {

      /* For i>1: a :- f_(i-1), l_i. */

      output_normal(style, out, constraint->head,
		    1, &previous, 1, scan, table);

      /* For i>1: f_i :- f_(i-1). */

      output_normal(style, out, newatom, 1, &previous, 0, NULL, table);
      previous = newatom++;

      /* For i>1: f_i :- l_i. */

      output_normal(style, out, previous, 0, NULL, 1, scan, table);
    }
  }

  return newatom;
}

/*
 * output_counting_triangle -- Count atoms up to k using a triangular structure
 */

int output_counting_triangle(int style, FILE *out, RULE *rule,
			     ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *intermediate = (int *)malloc((pos_cnt+neg_cnt)*sizeof(int));
  int i = 0, j = 0;

  for(i=0; i < constraint->bound; i++) {   /* Levels i = 0..bound-1 */

    if(neg_cnt)
      for(j=pos_cnt+(neg_cnt-1); (i>pos_cnt-1?i:pos_cnt)<=j; j--) {

	intermediate[j] = newatom++;

	if(i>0)
	  /* Generate: d(i,j) :- d(i-1,j-1), l_j. */
	  output_normal(style, out, intermediate[j],
			1, &intermediate[j-1],
			1, &constraint->neg[j-pos_cnt], table);
	else
	  /* Generate: d(i,j) :- l_j. */
	  output_normal(style, out, intermediate[j],
			0, NULL, 1, &constraint->neg[j-pos_cnt], table);

	if(j<pos_cnt+(neg_cnt-1))
	  /* Generate: d(i,j+1) :- d(i,j). */
	  output_normal(style, out, intermediate[j+1],
			1, &intermediate[j], 0, NULL, table);
      }

    if(pos_cnt)
      for(j=pos_cnt-1; i<=j; j--) {

	intermediate[j] = newatom++;

	if(i>0) {  /* Generate: d(i,j) :- d(i-1,j-1), l_j. */
	  int new_pos[2] = {0, 0};

	  new_pos[0] = intermediate[j-1];
	  new_pos[1] = constraint->pos[j];

	  output_normal(style, out, intermediate[j],
			2, new_pos, 0, NULL, table);

	} else /* Generate: d(i,j) :- l_j. */
	  output_normal(style, out, intermediate[j],
			1, &constraint->pos[j], 0, NULL, table);

	/* Generate: d(i,j+1) :- d(i,j). */

	if(j<pos_cnt+(neg_cnt-1))
	  output_normal(style, out, intermediate[j+1],
			1, &intermediate[j], 0, NULL, table);
      }
  }

  /* Derive the head atom */

  output_normal(style, out, constraint->head,
		1, &intermediate[pos_cnt+neg_cnt-1], 0, NULL, table);

  free(intermediate);

  return newatom;
}

/*
 * output_counting_net -- Count atoms up to k using a net structure
 */

int output_counting_net(int style, FILE *out, RULE *rule,
			ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int cnt = pos_cnt + neg_cnt;
  int *values = (int *)malloc(cnt*sizeof(int));
  int *intermediate = (int *)malloc(cnt*sizeof(int));
  int i = 0, head = 0;

  /* Rename both positive and negative literals in the rule */

  for(i=0; i<cnt; i++) {
    head = newatom++;

    if(i<pos_cnt)
      output_normal(style, out, head, 1, &(constraint->pos[i]),
		    0, NULL, table);
    else
      output_normal(style, out, head, 0, NULL,
		    1, &(constraint->neg[i-pos_cnt]), table);

    values[i] = head;
    intermediate[i] = 0;
  }

  while(bound != 1) {

    /* Output XORs: xor(i) :- l(i-1), not l(i).  xor(i) :- l(i), not l(i-1). */

    for(i=0; i<cnt; i++) {
      if(i == 0)
	/* Just copy the first entry */
	intermediate[i] = values[i];
      else if(i != cnt-1 || (bound & 1)){
	head = newatom++;

	output_normal(style, out, head,
		      1, &values[i], 1, &intermediate[i-1], table);
	output_normal(style, out, head,
		      1, &intermediate[i-1], 1, &values[i], table);
	intermediate[i] = head;
      } else
	/* Last entry not needed */
	intermediate[i] = 0;
    }

    /* Output ANDs: and(i) :- l(i), l(i+1). */

    for(i=0; i<cnt-1; i++) {
	head = newatom++;
	int pos[2] = {0, 0};
	
	pos[0] = intermediate[i];
	pos[1] = values[i+1];

	output_normal(style, out, head, 2, pos, 0, NULL, table);
	values[i] = head;
      }
    values[cnt-1] = intermediate[cnt-1];

    if(bound & 1)
      bound++;
    else
      cnt--;

    bound >>= 1;
  }

  /* Derive the head atom */

  for(i=0; i<cnt; i++)
    output_normal(style, out, constraint->head,
		  1, &values[i], 0, NULL, table);

  return newatom;
}

/*
 * output_counting_grid -- Count atoms up to k using a grid structure
 */

int output_counting_grid(int style, FILE *out, RULE *rule,
			 ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *intermediate =
    (int *)malloc((pos_cnt+neg_cnt-bound+1)*sizeof(int));
  int i = 0, j = 0;

  for(i=0; i < constraint->bound; i++)      /* Levels i = 0..bound-1 */
    for(j=0; j<=pos_cnt+neg_cnt-bound; j++) {
      int new_head = newatom++;
      int lit = pos_cnt+neg_cnt-j-i-1;      /* Which (diagonal) literal */

      if(pos_cnt && lit<pos_cnt) {
	/* A positive literal l is used */

	if(i>0) {  /* Generate: d(j,i) :- d(j,i-1), l_lit. */
	  int new_pos[2] = {0, 0};

	  new_pos[0] = intermediate[j];
	  new_pos[1] = constraint->pos[lit];

	  output_normal(style, out, new_head,
			2, new_pos, 0, NULL, table);

	} else /* Generate: d(j,i) :- l_lit. */
	  output_normal(style, out, new_head,
			1, &constraint->pos[lit], 0, NULL, table);

	intermediate[j] = new_head;

	if(j > 0)
	  /* Generate: d(j,i) :- d(j-1,i). */
	  output_normal(style, out, new_head,
			1, &intermediate[j-1], 0, NULL, table);
      }

      if(neg_cnt && lit>=pos_cnt && lit<pos_cnt+neg_cnt) {
	/* A negative literal l is used */

	if(i>0)
	  /* Generate: d(j,i) :- d(j,i-1), l_lit. */
	  output_normal(style, out, new_head,
			1, &intermediate[j],
			1, &constraint->neg[lit-pos_cnt], table);

	else /* Generate: d(j,i) :- l_lit. */
	  output_normal(style, out, new_head,
			0, NULL, 1, &constraint->neg[lit-pos_cnt], table);

	intermediate[j] = new_head;

	if(j > 0)
	  /* Generate: d(j,i) :- d(j-1,i). */
	  output_normal(style, out, new_head,
			1, &intermediate[j-1], 0, NULL, table);
      }
    }

  /* Derive the head atom */

  output_normal(style, out, constraint->head,
		1, &intermediate[pos_cnt+neg_cnt-bound], 0, NULL, table);

  free(intermediate);

  return newatom;
}

/* ========================= SYMBOLIC TRANSLATION ========================= */

/*
 * output_symbolic_and -- Calculate conjunction symbolically
 */

int output_symbolic_and(int style, FILE *out, int x, int y,
			int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x<0) {             /* x is true */
    if(y<0) {           /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y == 0) { /* y is false */
      /* No rules needed */
      answer = 0;
    } else {            /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x == 0) {   /* x is false */
    /* No rules needed */
    answer = 0;
  } else {              /* x is an atom */
    if(y<0) {           /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y == 0)   /* y is false */
      /* No rules needed */
      answer = 0;
    else {              /* y is an atom */
      if(x != y) {
	int pos[2] = {0, 0};

	pos[0] = x<y ? x : y;
	pos[1] = x<y ? y : x;

	output_normal_cond(style, out, answer = (*newatom)++,
			   2, pos, pos_cond, 0, NULL, neg_cond, table);
      } else { /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     1, &x, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional atom */
	  answer = x;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_or -- Calculate disjunction symbolically
 */

int output_symbolic_or(int style, FILE *out, int x, int y,
		       int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x == 0) {        /* x is false */
    if(y == 0)        /* y is false */
      /* No rules needed */
      answer = 0;
    else if(y<0) {    /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {          /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else 
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x < 0) {  /* x is true */
    if(pos_cond || neg_cond)
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 0, NULL, neg_cond, table);
    else
      /* Propagate an unconditional value */
      answer = -1;
  } else {            /* x is an atom */
    if(y == 0) {      /* y is false */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y < 0) {   /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {            /* y is an atom */
      if(x != y) {
	answer = (*newatom)++;
	output_normal_cond(style, out, answer,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
	output_normal_cond(style, out, answer,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      } else {        /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     1, &x, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional atom */
	  answer = x;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_eq -- Calculate equivalence symbolically
 */

int output_symbolic_eq(int style, FILE *out, int x, int y,
		       int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x < 0) {           /* x is true */
    if(y < 0) {         /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y == 0) { /* y is false */
      /* No rules needed */
      answer = 0;
    } else {            /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x == 0) {   /* x is false */
    if(y < 0) {
      /* No rules are needed */
      answer = 0;
    } else if(y == 0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond,
			 1, &y, neg_cond, table);

  } else {             /* x is an atom */
    if(y < 0) {        /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y == 0) {  /* y is false */
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &x, neg_cond, table);
    } else {           /* y is an atom */
      if(x != y) {
	int body[2] = {0, 0};

	body[0] = x<y ? x : y;
	body[1] = x<y ? y : x;
	answer = (*newatom)++;

	output_normal_cond(style, out, answer,
			   2, body, pos_cond, 0, NULL, neg_cond, table);
	output_normal_cond(style, out, answer,
			   0, NULL, pos_cond, 2, body, neg_cond, table);
      } else { /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     0, NULL, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional value */
	  answer = -1;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_excl -- Calculate exclusion symbolically
 */

int output_symbolic_excl(int style, FILE *out, int x, int y,
			 int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x == 0) {         /* x is false */
    if(y == 0) {
      /* No rules are needed */
      answer = 0;
    } else if(y<0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x < 0) {   /* x is true */
    if(y == 0) {       /* y is false */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y < 0) { /* y is true */
      /* No rules are needed */
      answer = 0;
    } else {           /* y is an atom */
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &y, neg_cond, table);
    }
  } else {             /* x is an atom */
    if(y == 0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y < 0) {
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &x, neg_cond, table);
    } else {
      if(x != y) {
	answer = (*newatom)++;
	output_normal_cond(style, out, answer,
			   1, &x, pos_cond, 1, &y, neg_cond, table);
	output_normal_cond(style, out, answer,
			   1, &y, pos_cond, 1, &x, neg_cond, table);
      } else /* Atoms are the same */
	/* No rules needed */
	/* Propagate an unconditional value */
	answer = 0;
    }
  }

  return answer;
}

/*
 * output_symbolic_adder_seq -- Produce a sequence of adders symbolically
 */

int output_symbolic_adder_seq(int style, FILE *out,
			      int bound,
			      int neg_cnt, int *neg,
			      int pos_cnt, int *pos,
			      int *weights, int bits,
			      ATAB *table, int *newatom)
{
  int i = 0, j = 0, answer = 0;
  int *sum = (int *)malloc(bits*sizeof(int));
  int *carry = (int *)malloc(bits*sizeof(int));
  int *gte = NULL;

  /* Initialize vectors */

  for(j=0; j<bits; j++) {
    sum[j] = 0;    /* False */
    carry[j] = 0;  /* False */
  }

  for(i=0; i<neg_cnt+pos_cnt; i++) { /* Process literals one by one */
    int neg_cond = i<neg_cnt ? neg[i] : 0;
    int pos_cond = i<neg_cnt ? 0 : pos[i-neg_cnt];
    int weight = weights[i];
    int old_carry = 0;

    for(j=0; j<bits; j++) {
      int sum_bit = 0, carry_bit = 0;

      if(weight & 1) {

	sum_bit =
	  output_symbolic_eq(style, out, sum[j], j>0 ? carry[j-1] : 0,
			     pos_cond, neg_cond, table, newatom);

	if(sum[j]>0) /* Copy the value */
	  output_normal_cond(style, out, sum_bit,
			     1, &sum[j], neg_cond, 0, NULL, pos_cond, table);

	carry_bit =
	  output_symbolic_or(style, out, sum[j], j>0 ? carry[j-1] : 0,
			     pos_cond, neg_cond, table, newatom);

      } else {

	sum_bit =
	  output_symbolic_excl(style, out, sum[j], j>0 ? carry[j-1] : 0,
			       pos_cond, neg_cond, table, newatom);

	if(sum[j]>0) /* Copy the value */
	  output_normal_cond(style, out, sum_bit,
			     1, &sum[j], neg_cond, 0, NULL, pos_cond, table);

	carry_bit =
	  output_symbolic_and(style, out, sum[j], j>0 ? carry[j-1] : 0,
			      pos_cond, neg_cond, table, newatom);
      }	

      sum[j] = sum_bit;
      carry[j] = carry_bit;

      weight >>= 1;
    }
  }

  /* Test the outcome, sum[bits-1]...sum[0], against bound */

  gte = carry; /* To be reused */

  for(j = 0; j<bits; j++) {
    if(j == 0) {
      if(bound & 1)
	gte[j] = sum[j];
      else
	gte[j] = -1;  /* True */

    } else { /* j > 0 */
      if(bound & 1)
	gte[j] =
	  output_symbolic_and(style, out, sum[j], gte[j-1],
			      0, 0, table, newatom);
      else
	gte[j] =
	  output_symbolic_or(style, out, sum[j], gte[j-1],
			     0, 0, table, newatom);
    }
    bound >>= 1;
  }

  answer = gte[bits-1];

  free(sum);
  free(gte);

  return answer;
}

/* ======================== NORMALIZATION ROUTINES ======================== */

/*
 * normalize_basic -- Produce the normalized version of a basic rule
 */

int normalize_basic(int style, FILE *out, RULE *rule,
		    ATAB *table, int newatom)
{
  BASIC_RULE *basic = rule->data.basic;

  output_normal(style, out, basic->head,
		basic->pos_cnt, basic->pos, basic->neg_cnt, basic->neg,
		table);

  return newatom;
}

/*
 * normalize_constraint -- Produce the normalized version of a constraint rule
 */

int normalize_constraint(int style, FILE *out, RULE *rule,
			 ATAB *table, int flavors, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *scan = NULL, *last = NULL;

  /* Handle special cases first */

  if(bound == 0) {

    /* The body is trivially satisfied; so create a fact */

    output_normal(style, out, constraint->head, 0, NULL, 0, NULL, table);

  } else if(bound == 1 && pos_cnt+neg_cnt>1) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */

    /* The rule corresponds to (pos_cnt+neg_cnt) basic rules
       of the following form: a :- l.*/

    output_literal_rules(style, out, rule, table);

  } else if(bound == 2 && pos_cnt+neg_cnt>2) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */
    
    if(pos_cnt+neg_cnt < 7)

      /* The rule corresponds to (pos_cnt+neg_cnt over 2) basic rules
         of the following form: a :- l_1, l_2. */

      output_literal_pair_rules(style, out, rule, table);

    else

      /* The rule corresponds to 3*(pos_cnt+neg_cnt)-2 basic rules */

      newatom = output_counting_chain(style, out, rule, table, newatom);

  } else if(bound == pos_cnt+neg_cnt) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */

    /* The rule corresponds to a single basic rule */

    output_normal(style, out, constraint->head,
		  pos_cnt, constraint->pos, neg_cnt, constraint->neg, table);

  } else if(bound < pos_cnt+neg_cnt) {

    /* Handle the general case: 2 < bound < pos_cnt+neg_cnt */

  raw:

    if(flavors & FL_ADDER) {
      int cnt = neg_cnt+pos_cnt, test = 0, bits = 0;
      int *weights = (int *)malloc(cnt*sizeof(int));
      int i = 0;

      /* Have to do this for the soundness of stable models: */
      newatom = rename_literals(style, out, rule, table, newatom);

      for(i=0; i<cnt; i++)
	weights[i] = 1;

      while(cnt)
	bits++, cnt >>= 1;

      test = output_symbolic_adder_seq(style, out, bound, 0, NULL,
				       constraint->pos_cnt, constraint->pos,
				       weights, bits, table, &newatom);

      output_normal(style, out, constraint->head, 1, &test, 0, NULL, table);

    } else if(flavors & FL_BINARY) {

      /* The rule corresponds to a total of
	 3*(pos_cnt+neg_cnt)*log_2(bound) basic rules */

      newatom = output_counting_net(style, out, rule, table, newatom);

    } else if(flavors & FL_UNARY) {

      /* The rule corresponds to a total of
	 2*(pos_cnt+neg_cnt)*bound - bound^2 + 1 basic rules */

      newatom = rename_literals(style, out, rule, table, newatom);
      newatom = output_counting_triangle(style, out, rule, table, newatom);

    } else /* The rule corresponds to a total of
	      2*(pos_cnt+neg_cnt)*bound - 2*bound^2 + bound + 1 basic rules */

      newatom = output_counting_grid(style, out, rule, table, newatom);
  }

  return newatom;
}

/*
 * normalize_choice -- Produce the normalized version of a choice rule
 */

int normalize_choice(int style, FILE *out, RULE *rule,
		     ATAB *table, int newatom)
{
  int head_cnt = 0;
  int pos_cnt = 0;
  int neg_cnt = 0;
  int *scan = NULL;
  int *last = NULL;
  int body = 0;

  CHOICE_RULE *choice = rule->data.choice;

  head_cnt = choice->head_cnt;
  pos_cnt = choice->pos_cnt;
  neg_cnt = choice->neg_cnt;

  if(head_cnt>1 && pos_cnt+neg_cnt>0) {
    
    /* Create a shorthand for the body to avoid
       unnecessary (quadratic) copying of the body */

    body = newatom++;
    output_normal(style, out,
		  body, pos_cnt, choice->pos, neg_cnt, choice->neg,
		  table);
  }

  /* Process head atoms in order */

  for(scan = choice->head, last = &scan[head_cnt]; scan != last; ) {
    int head = *scan++;
    int neg_head = newatom++;

    /* Create a basic rule for deriving this head atom */

    if(body)
      output_normal(style, out, head, 1, &body, 1, &neg_head, table);
    else {
      int *new_neg = (int *)malloc((neg_cnt+1)*sizeof(int));

      memcpy(new_neg, choice->neg, neg_cnt*sizeof(int));
      new_neg[neg_cnt] = neg_head;

      output_normal(style, out, head,
		    pos_cnt, choice->pos, neg_cnt+1, new_neg,
		    table);

      free(new_neg);
    }

    /* Create a basic rule for deriving the complement of this head atom */

    output_normal(style, out, neg_head, 0, NULL, 1, &head, table);
  }

  return newatom;
}

/*
 * gcd -- Calculate the greatest common divisor
 */

int gcd(int u, int v)
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

/*
 * simplify_weight -- Simplify a weight rule in a number of ways
 */

int simplify_weight(int style, FILE *out, WEIGHT_RULE *weight, ATAB *table)
{
  int *scan = NULL, *copy = NULL, *last = NULL;
  int *w = NULL, *copyw = NULL;
  int bound = weight->bound, head = weight->head;
  int sum = 0, div = bound;
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
      sum += *w;
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
      sum += *w;
      div = gcd(div, *w);
      *copyw++ = *w;
    }
  }

  weight->bound /= div;

  for(w = weight->weight, last = &w[neg_cnt+pos_cnt]; w != last; w++)
    *w /= div;

  return sum/div;
}

/*
 * normalize_weight -- Produce the normalized version of a weight rule
 */

int normalize_weight(int style, FILE *out, RULE *rule,
		     ATAB *table, int flavors, int newatom)
{
  int head = 0, pos_cnt = 0, neg_cnt = 0, bound = 0, *weights = NULL;
  int *scan = NULL, *last = NULL;
  int sum = 0, bits = 0, test = 0;
  int i = 0, j = 0;

  WEIGHT_RULE *weight = rule->data.weight;
  bound = weight->bound;

  /* Perform preliminary simplifications */

  if(bound>0) {
    weights = weight->weight;    
    pos_cnt = weight->pos_cnt;
    neg_cnt = weight->neg_cnt;

    if(flavors & FL_RAW) {
      for(i=0;i<pos_cnt+neg_cnt;i++)
	sum += weights[i];
    } else {
      sum = simplify_weight(style, out, weight, table);
      bound = weight->bound;
    }

    if(sum < bound)
      /* The body cannot be satisfied -- drop the whole rule */
      return newatom;

    if(sum == bound) {
      /* The rule can be turned into a normal one directly */

      output_normal(style, out, weight->head,
		    pos_cnt, weight->pos, neg_cnt, weight->neg, table);
      return newatom;
    }
      
  } else {
    /* The body is trivially satisfied -- create a fact */

    output_normal(style, out, weight->head, 0, NULL, 0, NULL, table);

    return newatom;
  }

  /* Now (0 < bound < sum) holds and the body is non-empty */

  newatom = rename_literals(style, out, rule, table, newatom);

  head = weight->head;
  pos_cnt = weight->pos_cnt;
  neg_cnt = weight->neg_cnt;

  /* Handle the general case */

  i = sum;

  while(i>0)
    bits++, i >>= 1;

  test = output_symbolic_adder_seq(style, out, bound,
				   neg_cnt, weight->neg,
				   pos_cnt, weight->pos,
				   weight->weight, bits,
				   table, &newatom);

  output_normal(style, out, head, 1, &test, 0, NULL, table);

  return newatom;
}

/*
 * normalize_rule --- Produce the normalized version of a rule
 */

int normalize_rule(int style, FILE *out, RULE *rule, ATAB *table,
		   int flavors, int newatom)
{
  switch(rule->type) {
  case TYPE_BASIC:

    newatom = normalize_basic(style, out, rule, table, newatom);
    break;

  case TYPE_CONSTRAINT:
    if(flavors & FL_KEEP_CO)
      write_rule(style, out, rule, table);
    else
      newatom = normalize_constraint(style, out, rule,
				     table, flavors, newatom);
    break;

  case TYPE_CHOICE:
    if(flavors & FL_KEEP_CH)
      write_rule(style, out, rule, table);
    else
      newatom = normalize_choice(style, out, rule, table, newatom);
    break;

  case TYPE_WEIGHT:
    if(flavors & FL_KEEP_WT)
      write_rule(style, out, rule, table);
    else
      newatom = normalize_weight(style, out, rule, table, flavors, newatom);
    break;

  case TYPE_OPTIMIZE:
    if(flavors & FL_KEEP_OPT)
      write_rule(style, out, rule, table);
    else {
      fprintf(stderr, "%s: optimize statements not supported!\n", program_name);
      fprintf(stderr, "Please consider the use of option -ko\n");
      exit(-1);
    }
    break;

  default:
    fprintf(stderr, "%s: rule type %i not supported!\n",
	    program_name, rule->type);
    exit(-1);
  }

  return newatom;
}

/*
 * normalize_rule --- Produce the normalized version of an entire program
 */

void normalize_program(int style, FILE *out, RULE *program,
		       ATAB *table, int flavors, int newatom)
{
  while(program) {
    newatom = normalize_rule(style, out, program, table, flavors, newatom);

    program = program->next;
  }
  return;
}
