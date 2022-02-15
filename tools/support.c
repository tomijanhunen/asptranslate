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
 * SUPPORT -- Capture supported models of a logic program
 *
 * (c) 2005, 2022 Tomi Janhunen
 *
 * Main program and routines for rule level translation
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
#include "counter.h"

void _version_support_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: support.c,v $",
	   "$Date: 2022/02/15 16:07:38 $",
	   "$Revision: 1.9 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   support <options> <file>\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "\n");

  return;
}

#define RESERVE_ATOMS(counter,count) counter; counter+=count

void tr_rules(int style, FILE *out, RULE *rule, ATAB *table, ATAB* negtable);
void tr_atoms(int style, FILE *out, ATAB *table, ATAB *negtable);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL;
  RULE *scan = NULL;

  ATAB *table = NULL;     /* For the original program */
  int size = 0;           /* and the size of the table */
  ATAB *negtable = NULL;  /* For negated atoms */

  int atom = 0, number = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;

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
    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }

  }

  if(option_help) usage();
  if(option_version) _version_support_c();

  if(option_help || option_version)
    exit(0);

  if(error) {
    usage();
    exit(-1);
  }

  /* Read in logic program */

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

  /* Create copies of atoms (negations) */

  size = table_size(table);
  negtable = copy_table(table);
  set_shift(negtable, size);
  set_prefix(negtable, "_not_");

  /* Mark positive occurrences */

  scan = program;
  while(scan) {
    /* Skip headless rules which do not contribute to support */
    if(scan->type == TYPE_INTEGRITY || scan->type == TYPE_OPTIMIZE)
      continue;
    else {
      int pos_cnt = get_pos_cnt(scan);
      int *pos = get_pos(scan);

      int i = 0;

      for(i=0; i<pos_cnt; i++)
	set_status(table, pos[i], MARK_POSOCC);
    }
      
    scan = scan->next;
  }
  
  /* Produce the desired output */

  if(option_verbose) { /* Use symbolic (human readable) format */

    fputs("% Define the complements of atoms:\n\n", out);
    tr_atoms(STYLE_READABLE, out, table, negtable);
    fputs("\n", out);

    fprintf(out, "%% Translation of the program %s:\n\n", file);

    tr_rules(STYLE_READABLE, out, program, table, negtable);
    fprintf(out, "\n");

    fprintf(out, "%% List of %i atoms:\n\n", table_size(table));
    write_symbols(STYLE_READABLE, out, table);
    fprintf(out, "\n");

    fprintf(out, "%% Negated atoms (%i atoms):\n\n", table_size(negtable));
    write_symbols(STYLE_READABLE, out, negtable);
    fprintf(out, "\n");

    fprintf(out, "compute { ");
    write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE|MARK_FALSE);
    fprintf(out, " }.\n");

    write_input(STYLE_READABLE, out, table);

  } else { /* !option_verbose: use internal format */

    tr_atoms(STYLE_SMODELS, out, table, negtable);
    tr_rules(STYLE_SMODELS, out, program, table, negtable);

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

/* --------------------- Local translation routines ------------------------ */


void define_complement(int style, FILE *out, int atom,
		       ATAB *table, ATAB *negtable)
{
  if(style == STYLE_READABLE) {

    write_atom(style, out, atom, negtable);
    fprintf(out, " :- not ");
    write_atom(style, out, atom, table);
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "1");
    write_atom(style, out, atom, negtable);
    fprintf(out, " %i %i", 1, 1);
    write_atom(style, out, atom, table);
    fprintf(out, "\n");

  }

  return;
}

void tr_head_list(int style, FILE *out, int cnt, int *atoms,
		  int *weights, ATAB *table)
{
  int i = 0;

  /* Needed by disjunctive rules only */
  
  while(i<cnt) {
    write_atom(style, out, atoms[i], table);
    if(style == STYLE_READABLE && weights)
      fprintf(out, "=%i", weights[i]);
    i++;
    if(style == STYLE_READABLE && i<cnt)
      fputs(" | ", out);
  }

  return;
}

void tr_body_list(int style, FILE *out, int cnt, int *atoms,
		  int *weights, ATAB *table)
{
  int i = 0;

  while(i<cnt) {
    if(style == STYLE_READABLE)
      fputs("not ", out);  /* All negated */
    write_atom(style, out, atoms[i], table);
    if(style == STYLE_READABLE && weights)
      fprintf(out, "=%i", weights[i]);
    i++;
    if(style == STYLE_READABLE && i< cnt)
      fputs(", ", out);
  }

  return;
}

void tr_basic_as_atomic(int style, FILE *out,
			BASIC_RULE *basic,
			ATAB *table, ATAB *negtable)
{
  int head = basic->head;
  int pos_cnt = basic->pos_cnt;
  int neg_cnt = basic->neg_cnt;

  if(style == STYLE_READABLE) {

    write_atom(style, out, head, table);
    if(pos_cnt || neg_cnt)
      fprintf(out, " :- ");
    tr_body_list(style, out, pos_cnt, basic->pos, NULL, negtable);
    if(pos_cnt && neg_cnt)
      fprintf(out, ", ");
    tr_body_list(style, out, neg_cnt, basic->neg, NULL, table);
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "1 %i", head);
    fprintf(out, " %i %i", pos_cnt+neg_cnt, pos_cnt+neg_cnt);
    tr_body_list(style, out, pos_cnt, basic->pos, NULL, negtable);
    tr_body_list(style, out, neg_cnt, basic->neg, NULL, table);
    fprintf(out, "\n");

  }

  return;
}

void tr_constraint_as_atomic(int style, FILE *out,
			     CONSTRAINT_RULE *constraint,
			     ATAB *table, ATAB *negtable)
{
  int head = constraint->head;
  int pos_cnt = constraint->pos_cnt;
  int neg_cnt = constraint->neg_cnt;

  if(style == STYLE_READABLE) {

    write_atom(style, out, head, table);
    if(pos_cnt || neg_cnt)
      fprintf(out, " :- {");
    tr_body_list(style, out, pos_cnt, constraint->pos, NULL, negtable);
    if(pos_cnt && neg_cnt)
      fprintf(out, ", ");
    tr_body_list(style, out, neg_cnt, constraint->neg, NULL, table);
    if(pos_cnt || neg_cnt)
      fprintf(out, "}");
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "1 %i", head);
    fprintf(out, " %i %i", pos_cnt+neg_cnt, pos_cnt+neg_cnt);
    tr_body_list(style, out, pos_cnt, constraint->pos, NULL, negtable);
    tr_body_list(style, out, neg_cnt, constraint->neg, NULL, table);
    fprintf(out, "\n");

  }

  return;
}

void tr_choice_as_atomic(int style, FILE *out,
			 CHOICE_RULE *choice,
			 ATAB *table, ATAB *negtable)
{
  int head_cnt = choice->head_cnt;
  int pos_cnt = choice->pos_cnt;
  int neg_cnt = choice->neg_cnt;

  if(style == STYLE_READABLE) {

    fprintf(out, "{");
    write_atom_list(style, out, head_cnt, choice->head, table);
    fprintf(out, "}");
    if(pos_cnt || neg_cnt)
      fprintf(out, " :- ");
    tr_body_list(style, out, pos_cnt, choice->pos, NULL, negtable);
    if(pos_cnt && neg_cnt)
      fprintf(out, ", ");
    tr_body_list(style, out, neg_cnt, choice->neg, NULL, table);
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "3 %i", head_cnt);
    tr_head_list(style, out, head_cnt, choice->head, NULL, table);
    fprintf(out, " %i %i", pos_cnt+neg_cnt, pos_cnt+neg_cnt);
    tr_body_list(style, out, pos_cnt, choice->pos, NULL, negtable);
    tr_body_list(style, out, neg_cnt, choice->neg, NULL, table);
    fprintf(out, "\n");

  }

  return;
}

void tr_weight_as_atomic(int style, FILE *out,
			 WEIGHT_RULE *weight,
			 ATAB *table, ATAB *negtable)
{
  int head = weight->head;
  int bound = weight->bound;
  int pos_cnt = weight->pos_cnt;
  int neg_cnt = weight->neg_cnt;

  if(style == STYLE_READABLE) {

    write_atom(style, out, head, table);
    fprintf(out, " :- %i [", bound);
    tr_body_list(style, out, pos_cnt, weight->pos,
		 &(weight->weight)[neg_cnt], negtable);
    if(pos_cnt && neg_cnt)
      fprintf(out, ", ");
    tr_body_list(style, out, neg_cnt, weight->neg, weight->weight, table);
    fprintf(out, "]");
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {
    int i = 0;

    fprintf(out, "5 %i %i", head, bound);
    fprintf(out, " %i %i", pos_cnt+neg_cnt, pos_cnt+neg_cnt);
    tr_body_list(style, out, pos_cnt, weight->pos, NULL, negtable);
    tr_body_list(style, out, neg_cnt, weight->neg, NULL, table);
    for(i=0; i<pos_cnt; i++)
      fprintf(out, " %i", (weight->weight)[neg_cnt+i]);
    for(i=0; i<neg_cnt; i++)
      fprintf(out, " %i", (weight->weight)[i]);
    fprintf(out, "\n");

  }

  return;
}

void tr_disjunctive_as_atomic(int style, FILE *out,
			      DISJUNCTIVE_RULE *disjunctive,
			      ATAB *table, ATAB *negtable)
{
  int head_cnt = disjunctive->head_cnt;
  int pos_cnt = disjunctive->pos_cnt;
  int neg_cnt = disjunctive->neg_cnt;
  
  if(style == STYLE_READABLE) {

    tr_head_list(style, out, head_cnt, disjunctive->head, NULL, table);
    if(pos_cnt || neg_cnt)
      fprintf(out, " :- ");
    tr_body_list(style, out, pos_cnt, disjunctive->pos, NULL, negtable);
    if(pos_cnt && neg_cnt)
      fprintf(out, ", ");
    tr_body_list(style, out, neg_cnt, disjunctive->neg, NULL, table);
    fprintf(out, ".\n");

  } else if(style == STYLE_SMODELS) {

    fprintf(out, "8 %i", head_cnt);
    tr_head_list(style, out, head_cnt, disjunctive->head, NULL, table);
    fprintf(out, " %i %i", pos_cnt+neg_cnt, pos_cnt+neg_cnt);
    tr_body_list(style, out, pos_cnt, disjunctive->pos, NULL, negtable);
    tr_body_list(style, out, neg_cnt, disjunctive->neg, NULL, table);
    fprintf(out, "\n");

  }

  return;
}

/*
 * tr_rules --- Define complements for atoms
 */

void tr_rules(int style, FILE *out, RULE *rule, ATAB *table, ATAB* negtable)
{
  while(rule) {
    switch(rule->type){

    case TYPE_BASIC:
      tr_basic_as_atomic(style, out, rule->data.basic,
			 table, negtable);
      break;

    case TYPE_CONSTRAINT:
      tr_constraint_as_atomic(style, out, rule->data.constraint,
			      table, negtable);
      break;

    case TYPE_CHOICE:
      tr_choice_as_atomic(style, out, rule->data.choice, table, negtable);
      break;

    case TYPE_WEIGHT:
      tr_weight_as_atomic(style, out, rule->data.weight,
			  table, negtable);
      break;

    case TYPE_INTEGRITY:
    case TYPE_OPTIMIZE:
      /* These are headless, hence no concern */
      break;

    case TYPE_DISJUNCTIVE:
      tr_disjunctive_as_atomic(style, out, rule->data.disjunctive,
			       table, negtable);
      break;
      
    default:
      fprintf(stderr, "%s: unsupported rule type %i\n",
	      program_name, rule->type);
      exit(-1);
      break;
    }

    rule = rule->next;
  }
}

/*
 * tr_atoms --- Define complements for atoms
 */

void tr_atoms(int style, FILE *out, ATAB *table, ATAB *negtable)
{
  ATAB *passby = table;

  /* Process all atoms one by one */

  while(passby) {
    int count = passby->count;
    int offset = passby->offset;
    int i = 0;
    int *statuses = passby->statuses;
    
    for(i=1; i<=count; i++) {
      int atom = i+offset;

      if(statuses[i] & MARK_POSOCC)
	define_complement(style, out, atom, table, negtable);
    }
    passby = passby->next;
  }
  return;
}
