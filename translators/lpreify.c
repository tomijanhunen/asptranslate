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
 * LPREIFY -- Print a ground logic program as a set of facts
 *
 * (c) 2014, 2022 Tomi Janhunen
 *
 * Main program and routines for rule level reification
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

#include "scc.h"
#include "primitives.h"

void _version_lpreify_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: lpreify.c,v $",
	   "$Date: 2022/02/23 21:58:12 $",
	   "$Revision: 1.7 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
  _version_scc_c();
  _version_primitives_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   lpreify [<file>]\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "   -d -- the input is a CNF in DIMACS format\n");
  fprintf(stderr, "   -s -- represent symbols separately\n");
  fprintf(stderr, "   -c -- include component information (SCCs)\n");
  fprintf(stderr, "   -p<prefix> -- set prefix for naming invisible atoms\n");
  fprintf(stderr, "\n");

  return;
}

char *prefix = "_int";

void reify_program(FILE *out, RULE *program, int symbols, ATAB *table);
void reify_sccs(FILE *out, int symbols, ATAB *table, OCCTAB *occtab);
void reify_symbol_table(FILE *out, ATAB *table);
void reify_compute_statement(FILE *out, int symbols, ATAB *table, int mask);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL;
  RULE *scan = NULL;

  ATAB *table = NULL;     /* For the original program */
  int size = 0;           /* and the size of the table */
  OCCTAB *occtable = NULL;
  int number = 0;
  int weighted = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;
  int option_dimacs = 0;
  int option_symbols = 0;
  int option_sccs = 0;

  char *arg = NULL;
  int which = 0;
  int error = 0;

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
    else if(strcmp(arg, "-d") == 0)
      option_dimacs = -1;
    else if(strcmp(arg, "-s") == 0)
      option_symbols = -1;
    else if(strcmp(arg, "-c") == 0)
      option_sccs = -1;
    else if(strncmp(arg, "-p", 2) == 0) {
      if(strlen(arg)>2)
        prefix = &arg[2];
    } else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }

  }

  if(option_help) usage();
  if(option_version) _version_lpreify_c();

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

  if(option_dimacs) {
    program = read_cnf(in, &table, &weighted);
    if(weighted)
      fprintf(out, "maxw(%ld).\n", max_weight);
  } else {
    program = read_program(in);
    table = read_symbols(in);
    number = read_compute_statement(in, table);
  }

  /* Compute strongly connected components (i.e., SCCs) */

  if(option_sccs) {
    occtable = initialize_occurrences(table, 0, 0);
    compute_occurrences(program, occtable, 0, 0);
    size = table_size(table);
    compute_sccs(occtable, size);
  }

  /* Produce the desired output */

  reify_program(out, program, option_symbols, table);
  if(option_sccs)
    reify_sccs(out, option_symbols, table, occtable);
  if(option_symbols)
    reify_symbol_table(out, table);
  if(!option_dimacs)
    reify_compute_statement(out, option_symbols, table,
			    MARK_TRUE|MARK_FALSE|MARK_INPUT);

  exit(0);
}

/* --------------------- Local reification routines ------------------------ */

void reify_number(FILE *out, char *name, int id, int number)
{
  fprintf(out, "%s(%i,%i).\n", name, id, number);

  return;
}

void reify_atom(FILE *out, char *name, int id, int symbols,
		int atom, ATAB *table)
{
  if(symbols)
    fprintf(out, "%s(%i,%i).\n", name, id, atom);
  else {
    fprintf(out, "%s(%i,", name, id);
    if(invisible(table, atom) && prefix)
      fputs(prefix, out);
    write_atom(STYLE_READABLE, out, atom, table);
    fputs(").\n", out);
  }
  
  return;
}

void reify_atom_list(FILE *out, char *name, int id, int symbols,
                     int cnt, int *atoms, ATAB *table)
{
  int i=0;

  for(i=0; i<cnt; i++)
    reify_atom(out, name, id, symbols, atoms[i], table);

  return;
}

void reify_weighted_atom(FILE *out, char *name, int id, int symbols,
			 int atom, int weight, ATAB *table)
{
  if(symbols)
    fprintf(out, "%s(%i,%i,%i).\n", name, id, atom, weight);
  else {
    fprintf(out, "%s(%i,", name, id);
    if(invisible(table, atom) && prefix)
      fputs(prefix, out);
    write_atom(STYLE_READABLE, out, atom, table);
    fprintf(out, ",%i).\n", weight);
  }

  return;
}

void reify_weighted_atom_list(FILE *out, char *name, int id, int symbols,
			      int cnt, int *atoms, int *weights, ATAB *table)
{
  int i=0;

  for(i=0; i<cnt; i++)
    reify_weighted_atom(out, name, id, symbols, atoms[i], weights[i], table);

  return;
}

/*
 * reify_basic -- Reify a basic rule
 */

void reify_basic(FILE *out, int id, BASIC_RULE *basic,
		 int symbols, ATAB *table)
{
  reify_atom(out, "head", id, symbols, basic->head, table);
  reify_atom_list(out, "pbody", id, symbols, basic->pos_cnt, basic->pos, table);
  reify_atom_list(out, "nbody", id, symbols, basic->neg_cnt, basic->neg, table);

  return;
}

/*
 * reify_constraint -- Reify a constraint rule
 */

void reify_constraint(FILE *out, int id, CONSTRAINT_RULE *constraint,
		      int symbols, ATAB *table)
{
  reify_atom(out, "head", id, symbols, constraint->head, table);
  reify_number(out, "bound", id, constraint->bound);
  reify_atom_list(out, "pbody", id, symbols,
		  constraint->pos_cnt, constraint->pos, table);
  reify_atom_list(out, "nbody", id, symbols,
		  constraint->neg_cnt, constraint->neg, table);

  return;
}

/*
 * reify_choice -- Reify a choice rule
 */

void reify_choice(FILE *out, int id, CHOICE_RULE *choice,
		  int symbols, ATAB *table)
{
  reify_atom_list(out, "head", id, symbols,
		  choice->head_cnt, choice->head, table);
  reify_atom_list(out, "pbody", id, symbols,
		  choice->pos_cnt, choice->pos, table);
  reify_atom_list(out, "nbody", id, symbols,
		  choice->neg_cnt, choice->neg, table);

  return;
}

/*
 * reify_weight -- Reify a weight rule
 */

void reify_weight(FILE *out, int id, WEIGHT_RULE *weight,
		  int symbols, ATAB *table)
{
  reify_atom(out, "head", id, symbols, weight->head, table);
  reify_number(out, "bound", id, weight->bound);
  reify_weighted_atom_list(out, "pbody", id, symbols,
			   weight->pos_cnt, weight->pos,
			   &(weight->weight[weight->neg_cnt]),
			   table);
  reify_weighted_atom_list(out, "nbody", id, symbols,
			   weight->neg_cnt, weight->neg,
			   weight->weight,
			   table);

  return;
}

/*
 * reify_optimize -- Reify an optimization statement
 */

void reify_optimize(FILE *out, int id, OPTIMIZE_RULE *optimize,
		    int symbols, ATAB *table)
{
  reify_weighted_atom_list(out, "pcond", id, symbols,
			   optimize->pos_cnt, optimize->pos,
			   &(optimize->weight[optimize->neg_cnt]),
			   table);
  reify_weighted_atom_list(out, "ncond", id, symbols,
			   optimize->neg_cnt, optimize->neg,
			   optimize->weight,
			   table);

  return;
}

/*
 * reify_disjunctive -- Reify a (proper) disjunctive rule
 */

void reify_disjunctive(FILE *out, int id, DISJUNCTIVE_RULE *disjunctive,
		       int symbols, ATAB *table)
{
  reify_atom_list(out, "head", id, symbols,
		  disjunctive->head_cnt, disjunctive->head, table);
  reify_atom_list(out, "pbody", id, symbols,
		  disjunctive->pos_cnt, disjunctive->pos, table);
  reify_atom_list(out, "nbody", id, symbols,
		  disjunctive->neg_cnt, disjunctive->neg, table);

  return;
}

/*
 * reify_clause -- Reify a clause
 */

void reify_clause(FILE *out, int id, CLAUSE *clause,
		  int symbols, ATAB *table)
{
  reify_atom_list(out, "pcond", id, symbols,
		  clause->pos_cnt, clause->pos, table);
  reify_atom_list(out, "ncond", id, symbols,
		  clause->neg_cnt, clause->neg, table);

  return;
}

void reify_rule(FILE *out, int id, RULE *rule, int symbols, ATAB *table)
{
  switch(rule->type) {
  case TYPE_BASIC:
    fprintf(out, "rule(%i,basic).\n", id);
    reify_basic(out, id, rule->data.basic, symbols, table);
    break;

  case TYPE_CONSTRAINT:
    fprintf(out, "rule(%i,card).\n", id);
    reify_constraint(out, id, rule->data.constraint, symbols, table);
    break;

  case TYPE_CHOICE:
    fprintf(out, "rule(%i,choice).\n", id);
    reify_choice(out, id, rule->data.choice, symbols, table);
    break;

  case TYPE_WEIGHT:
    fprintf(out, "rule(%i,weight).\n", id);
    reify_weight(out, id, rule->data.weight, symbols, table);
    break;

  case TYPE_OPTIMIZE:
    fprintf(out, "rule(%i,opt).\n", id);
    reify_optimize(out, id, rule->data.optimize, symbols, table);
    break;

  case TYPE_DISJUNCTIVE:
    fprintf(out, "rule(%i,disj).\n", id);
    reify_disjunctive(out, id, rule->data.disjunctive, symbols, table);
    break;

  case TYPE_CLAUSE:
    fprintf(out, "rule(%i,clause).\n", id);
    reify_clause(out, id, rule->data.clause, symbols, table);
    break;

  default:
    error("unknown rule type");
  }
}

void reify_program(FILE *out, RULE *rule, int symbols, ATAB *table)
{
  int id = 1;

  while(rule) {
    reify_rule(out, id++, rule, symbols, table);
    rule = rule->next;
  }
  return;
}

void reify_sccs(FILE *out, int symbols, ATAB *table, OCCTAB *occtable)
{
  ATAB *passby = table;

  /* Process all atoms one by one */

  while(passby) {
    int count = passby->count;
    int offset = passby->offset;
    int i = 0;
    SYMBOL **names = passby->names;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = definition(occtable, atom);
      int scc = d->scc;
      int scc_size = d->scc_size;
      RULE *r = NULL;
      int j = 0;
      SYMBOL *name = names[i];

      if(scc) {
	if(symbols)
	  fprintf(out, "scc(%i,%i).\n", scc, atom);
	else {
	  fprintf(out, "scc(%i,", scc);
	  if(!name && prefix)
	    fputs(prefix, out);
	  write_atom(STYLE_READABLE, out, atom, table);
	  fputs(").\n", out);
	}
      }

    }
    passby = passby->next;
  }
  return;
}

/*
 * reify_symbol_table -- Represent symbols using a separate relation
 */

void reify_symbol_table(FILE *out, ATAB *table)
{
  while(table) {
    int count = table->count;
    int offset = table->offset;
    int shift = table->shift;
    int *statuses = table->statuses;
    SYMBOL **names = table->names;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      int status = statuses[i];
      SYMBOL *name = names[i];

      fprintf(out, "symbol(%i,", atom);
      if(!name && prefix)
	fputs(prefix, out);
      write_atom(STYLE_READABLE, out, atom, table);
      fputs(").\n", out);
    }
    table = table->next;
  }
  return;
}

/*
 * reify_compute_statement -- Reify a compute statement
 */

void reify_compute_statement(FILE *out, int symbols, ATAB *table, int mask)
{
  while(table) {
    int count = table->count;
    int offset = table->offset;
    int shift = table->shift;
    int *statuses = table->statuses;
    SYMBOL **names = table->names;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      int status = statuses[i];
      SYMBOL *name = names[i];

      if(status & MARK_TRUE) {
	if(symbols)
	  fprintf(out, "mark(%i,true).\n", atom);
	else {
	  fputs("mark(", out);
	  if(!name && prefix)
	    fputs(prefix, out);
	  write_atom(STYLE_READABLE, out, atom, table);
	  fputs(",true).\n", out);
	}
      }

      if(status & MARK_FALSE) {
	if(symbols)
	  fprintf(out, "mark(%i,false).\n", atom);
	else {
	  fputs("mark(", out);
	  if(!name && prefix)
	    fputs(prefix, out);
	  write_atom(STYLE_READABLE, out, atom, table);
	  fputs(",false).\n", out);
	}
      }
	
      if(status & MARK_INPUT) {
	if(symbols)
	  fprintf(out, "mark(%i,external).\n", atom);
	else {
	  fputs("mark(", out);
	  if(!name && prefix)
	    fputs(prefix, out);
	  write_atom(STYLE_READABLE, out, atom, table);
	  fputs(",external).\n", out);
	}
      }
    }

    table = table->next;
  }
  return;
}
