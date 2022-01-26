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
 * UNSAT2LP -- LP encoding of UNSAT problems
 *
 * (c) 2021 Tomi Janhunen
 *
 * Driver program
 */

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <limits.h>
#include <string.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

extern void write_literal_list(int style, FILE *out, char *sep,
			       int pos_cnt, int *pos,
			       int neg_cnt, int *neg,
			       int *weight, ATAB *table);

#include "scc.h"

void _version_unsat2lp_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: unsat2lp.c,v $",
	   "$Date: 2021/09/29 19:53:18 $",
	   "$Revision: 1.6 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
  _version_output_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   unsat2lp <options> [<file>]\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "\n");

  return;
}

void write_clause_as_positive_rule(int style, FILE *out,
				   RULE *clause,
				   int contradiction,
				   ATAB *table);

void gen_saturating_rules(int style, FILE *out, int contradiction, ATAB *table);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  RULE *clause = NULL;
  ATAB *table = NULL;
  int clauses = 0, weighted = 0;
  int size = 0, newatom = 0, contradiction = 0;

  FILE *out = stdout;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;
  char *arg = NULL;
  int which = 0;
  int style = 0;

  program_name = argv[0];

  for(which=1; which<argc; which++) {
    arg = argv[which];

    if(strcmp(arg, "-h") == 0 || strcmp(arg, "--help") == 0)
      option_help = -1;
    else if(strcmp(arg, "--version") == 0)
      option_version = -1;
    else if(strcmp(arg, "-v") == 0)
      option_verbose = -1;
    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      fprintf(stderr,
	      "usage: unsat2lp [-v] <file>\n");
      exit(-1);
    }
  }

  if(option_help) usage();
  if(option_version) _version_unsat2lp_c();

  if(option_help || option_version)
    exit(0);

  if(file == NULL || strcmp("-", file) == 0) {
    in = stdin;
  } else {
    if((in = fopen(file, "r")) == NULL) {
      fprintf(stderr, "%s: cannot open file %s\n", program_name, file);
      exit(-1);
    }
  }

  table = initialize_cnf(in, &clauses, &weighted);

  size = table_size(table);
  newatom = size+1;
  contradiction = newatom++;

  if(option_verbose) {
    fprintf(out, "%% unsat2lp %s\n", file);
    fprintf(out, "\n");
    style = STYLE_READABLE;
  } else
    style = STYLE_SMODELS;

  while(clauses) {
    clause = read_clause(in, weighted);

    write_clause_as_positive_rule(style, out, clause, contradiction, table);
    free_rule(clause);

    clauses--;
  }

  if(option_verbose) {
    gen_saturating_rules(STYLE_READABLE, out, size+1, table);
    fprintf(out, "\n");

    fprintf(out, "compute { ");
    write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE|MARK_FALSE);
    fprintf(out, " }.\n");

  } else { /* !option_verbose */

    gen_saturating_rules(STYLE_SMODELS, out, size+1, table);
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
    
    fprintf(out, "%i\n", 0);
  }

  exit(0);
}

/* --------------------------- Local translation --------------------------- */

void write_clause_as_positive_rule(int style, FILE *out, RULE *rule,
				   int contradiction,
				   ATAB *table)
{
  int pos_cnt = 0;
  int neg_cnt = 0;
  CLAUSE *clause = rule->data.clause;

  pos_cnt = clause->pos_cnt;
  neg_cnt = clause->neg_cnt;
  
  /* A clause 'a | -b' is expressed as
     a positive disjunctive rule "_u | a :- b." */

  if(style == STYLE_SMODELS)
    fprintf(out, "8 %i %i", pos_cnt+1, contradiction);
  else {
    fputs("_u ", out);
    if(pos_cnt)
      fputs("| ", out);
  }

  write_literal_list(style, out, " | ",
		     pos_cnt, clause->pos,
		     0, NULL,
		     NULL, table);
  
  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", neg_cnt, 0);

  if(neg_cnt) {
    if(style == STYLE_READABLE)
      fprintf(out, " :- ");

    write_literal_list(style, out, ", ",
		       neg_cnt, clause->neg,
		       0, NULL,
		       NULL, table);
  }
  
  if(style == STYLE_READABLE)
    fprintf(out, ".");

  fprintf(out, "\n");

}

void gen_saturating_rules(int style, FILE *out, int contradiction, ATAB *table)
{
  while(table) {
    int count = table->count;
    int i = 0;
    SYMBOL **names = table->names;
    int *statuses = table->statuses;
    
    for(i=1; i<=count; i++) {
      int offset = table->offset;
      int atom = i+offset;

      /* Make acyc-atoms effectively invisble */
      if(names[i] && strncmp(names[i]->name, "_acyc_", 6) == 0)
	names[i] = NULL;
      
      if(names[i])
	/* Treat visible atoms as input atoms */
	statuses[i] |= MARK_INPUT;
      else {
	/* For each invisible atom a,
           we produce a positive saturating rule "a :- _u." */

	switch(style) {
	case STYLE_READABLE:
	  write_atom(style, out, atom, table);
	  fprintf(out, " :- _u.\n");
	  break;

	case STYLE_SMODELS:
	  fprintf(out, "1");
	  write_atom(style, out, atom, table);
	  fprintf(out, " 1 0 %i\n", contradiction);
	  break;

	default:
	  break;
	}
      }
    }
    table = table->next;
  }

  /* Finally, produce the normal rule "_u :- not _u." using
     the name _u to avoid naming conflicts with existing atoms */

  switch(style) {
  case STYLE_READABLE:
    fprintf(out, "_u :- not _u.");
    break;

  case STYLE_SMODELS:
    fprintf(out, "1 %i", contradiction);
    fprintf(out, " 1 1 %i\n", contradiction);
    break;

  default:
    break;
  }

  return;
}
