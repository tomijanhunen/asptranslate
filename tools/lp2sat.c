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
 * LP2SAT -- Reduce normal programs (under supported models)
 *           to propositional satisfiability
 *
 * (c) 2002, 2004, 2010, 2014-2015 Tomi Janhunen
 *
 * Main program and the necessary utilities
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
#include "acyc.h"

void _version_lp2sat_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: lp2sat.c,v $",
	   "$Date: 2021/05/27 11:25:26 $",
	   "$Revision: 1.26 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   lp2sat <options> [<file>]\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -d -- drop optimization statements\n");
  fprintf(stderr, "   -g -- generate graph/acyc extensions\n");
  fprintf(stderr, "   -u -- unary counters\n");
  fprintf(stderr, "   -b -- binary counters\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "\n");

  return;
}

#define STYLE_ACYC 6
#define STYLE_ACYC_READABLE 7

RULE *merge_optimize_statements(RULE *statements);
void tr_program_into_eq(int style, FILE *out, RULE *program, ATAB *table,
			int limit, int weight_sum);
void tr_atoms_into_eq(int style, FILE *out, ATAB *table, OCCTAB *occtab,
		      int weight_sum);
void tr_optimize_statement_into_cnf(int style, FILE *out,
				    RULE *statement, ATAB *table);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  RULE *program = NULL, *statements = NULL, *merged = NULL;
  ATAB *table = NULL;
  ATAB *passby = NULL;
  int size = 0;
  OCCTAB *occtable = NULL;
  GRAPH *graphs = NULL;
  int number = 0;
  int weight_sum = 0;

  RULE *scan = NULL, *prev = NULL;
  int atom_count = 0, clause_count = 0;

  FILE *out = stdout;

  int newatom = 0, atom = 0;
  int flavor = FL_ACYC_BIN;  /* Default */

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;
  int option_dropt = 0;
  int option_graph = 0;
  int option_unary = 0;
  int option_binary = 0;

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
      option_dropt = -1;
    else if(strcmp(arg, "-g") == 0)
      option_graph = -1;
    else if(strcmp(arg, "-u") == 0)
      option_unary = -1;
    else if(strcmp(arg, "-b") == 0)
      option_binary = -1;
    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }

  }

  if(option_help) usage();
  if(option_version) _version_lp2sat_c();

  if(option_help || option_version)
    exit(0);

  if(option_unary && option_binary) {
    fprintf(stderr, "%s: options -u and -b mutually exclusive\n", program_name);
    error = -1;
  }

  if(option_unary && option_graph) {
    fprintf(stderr, "%s: options -u and -g mutually exclusive\n", program_name);
    error = -1;
  }

  if(option_binary && option_graph) {
    fprintf(stderr, "%s: options -b and -g mutually exclusive\n", program_name);
    error = -1;
  }

  if(error) {
    usage();
    exit(-1);
  }

  /* Read in logic program */

  if(file == NULL || strcmp("-", file) == 0) {
    in = stdin;
    if(file == NULL)
      file = "stdin";
  } else {
    if((in = fopen(file, "r")) == NULL) {
      fprintf(stderr, "%s: cannot open file %s\n", program_name, file);
      exit(-1);
    }
  }
  program = read_program(in);
  table = read_symbols(in);
  number = read_compute_statement(in, table);

  /* Handle optimization statemens first */

  scan = program;
  while(scan) {
    RULE *next = scan->next;

    if(scan->type == TYPE_OPTIMIZE) {

      if(prev)
	prev->next = next;

      if(program == scan)
	program = next;

      scan->next = statements;
      statements = scan;

    } else
      prev = scan;

    scan = next;
  }

  if(statements) {
    if(option_dropt)
      merged = NULL;
    else
      merged = merge_optimize_statements(statements);

    scan = statements;
    while(scan) {
      RULE *next = scan->next;

      scan->next = NULL;
      free(scan);

      scan = next;
    }
  }

  if(merged) {
    OPTIMIZE_RULE *optimize = merged->data.optimize;
    int i=0;
    int cnt = optimize->pos_cnt + optimize->neg_cnt;
    int *weight = optimize->weight;

    clause_count +=cnt;

    weight_sum = 1;

    for(i=0; i<optimize->pos_cnt; i++)
      set_status(table, optimize->pos[i], MARK_POSOCC);

    for(i=0; i<optimize->neg_cnt; i++)
      set_status(table, optimize->neg[i], MARK_NEGOCC);

    for(i=0; i<cnt; i++) weight_sum += weight[i];
  }

  /* Check that only basic or single-head choice rules remain */

  scan = program;
  while(scan) {
    switch(scan->type) {
    case TYPE_BASIC:
      break;

    case TYPE_CHOICE:
      { CHOICE_RULE* choice = scan->data.choice;
	if(choice->head_cnt == 1)
	  break;
      }

    default:
      fprintf(stderr, "%s: ", program_name);      
      fprintf(stderr, "only basic or single-head choice rules supported!\n");
      exit(-1);
      /* Not reached */
      break;
    }

    scan = scan->next;
  }

  /* Remove certain unuseful rules */

  scan = program;
  while(scan) {
    int pos_cnt = get_pos_cnt(scan);
    int *pos = get_pos(scan);
    int neg_cnt = get_neg_cnt(scan);
    int *neg = get_neg(scan);

    int i = 0;

    for(i=0; i<pos_cnt; i++)
      set_status(table, pos[i], MARK_POSOCC);

    for(i=0; i<neg_cnt; i++)
      set_status(table, neg[i], MARK_NEGOCC);

    scan = scan->next;
  }

  scan = program;
  prev = NULL;

  while(scan) {

    if(scan->type == TYPE_BASIC) {
      BASIC_RULE *basic = scan->data.basic;
      int head = basic->head;
      SYMBOL *name = find_name(table, head);
      int status = get_status(table, head);

      if(!name && status >= 0 &&
	 !(status & (MARK_TRUE_OR_FALSE | MARK_POSOCC_OR_NEGOCC))) {
	/* The head atom is useless: invisible & without
	   occurrences in rule bodies or optimization/compute statement */
	if(scan == program)
	  program = scan->next;
	if(prev)
	  prev->next = scan->next;
      } else
	prev = scan;

    } else if(scan->type == TYPE_CHOICE) {
      CHOICE_RULE *choice = scan->data.choice;
      int head = choice->head[0];
      SYMBOL *name = find_name(table, head);
      int status = get_status(table, head);

      if(!name && status >= 0 &&
	 !(status & (MARK_TRUE_OR_FALSE | MARK_POSOCC_OR_NEGOCC))) {
	/* The head atom is useless: invisible & without
	   occurrences in rule bodies or optimization/compute statement */
	if(scan == program)
	  program = scan->next;
	if(prev)
	  prev->next = scan->next;
      } else
	prev = scan;
    }

    scan = scan->next;
  }

  /* Compute head occurrences (form definitions) */

  occtable = initialize_occurrences(table, 0, 0);
  compute_occurrences(program, occtable, 0, 0);

  /* Rename head atoms and count atoms and clauses in advance
     (this is a nasty feature of the DIMACS format) */

  size = table_size(table);
  newatom = size + 1;
  atom_count += size;

  scan = program;
  while(scan) {

    if(scan->type == TYPE_BASIC) {
      BASIC_RULE *basic = scan->data.basic;
      int head = basic->head;
      int status = get_status(table, head);
      DEF *d = definition(occtable, head);

      if(status >= 0) { /* The atom was found */

	if(status & MARK_TRUE) { /* The head is assigned to true */

	  if((d->rule_cnt)>1) {
	    basic->head = newatom++;
	    atom_count++;
	    clause_count++;
	  }

	  clause_count += (basic->neg_cnt + basic->pos_cnt);
	}

	if(status & MARK_FALSE) /* The head is assigned to false */
	  clause_count++;

	if(!(status & MARK_TRUE_OR_FALSE)) {

	  if((d->rule_cnt)>1) {
	    /* The head atom appears as a head in at least two rules */

	    basic->head = newatom++;
	    atom_count++;

	  }
	  clause_count += (basic->neg_cnt + basic->pos_cnt + 1);

	}

      }

    } else if(scan->type == TYPE_CHOICE) {
      CHOICE_RULE *choice = scan->data.choice;
      int head = choice->head[0];
      int status = get_status(table, head);
      DEF *d = definition(occtable, head);

      if(status >=0) { /* The atom was found */
	/* TODO: Counting clauses for choice rules */

	if(!(status & MARK_FALSE)) {
	  clause_count += choice->pos_cnt;
	  clause_count += choice->neg_cnt;
	}
      }
    }
    scan = scan->next;
  }

  /* Go through atoms once more */

  passby = table;
  
  while(passby) {
    int count = passby->count;
    int offset = passby->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = definition(occtable, atom);
      int status = (passby->statuses)[i];
      int rcnt = d->rule_cnt;

      if(status & MARK_TRUE) clause_count++;

      if(status & MARK_FALSE) clause_count++;

      if(rcnt != 1 &&
	 !(rcnt>1 && (status & MARK_FALSE)) &&
	 !(rcnt == 0 && (status & MARK_INPUT))) {
	if((status & MARK_TRUE) && (d->rule_cnt)>1)
	  clause_count++;
	else
	  clause_count += (d->rule_cnt) + 1;
      }
  
    }
    passby = passby->next;
  }

  /* Extract graph for acyclicity checks (if present) */

  graphs = extract_acyc_graphs(table);
  if(graphs && !option_graph) {
    int saved = newatom;

    if(option_unary)
      flavor = FL_ACYC_UN;
    else if(option_binary)
      flavor = FL_ACYC_BIN;

    newatom = acyc_cnf_size(graphs, flavor, &clause_count, newatom);

    atom_count += newatom-saved;
  }

  /* Extend symbol table */

  if(newatom > size+1)
    (void) extend_table(table, newatom-(size+1), size);

  /* Produce the desired output */

  if(option_verbose) {

    if(option_graph) {
      /* Output graph/acyc extensions */

      fprintf(out, "%% p cnf %i %i\n", atom_count, clause_count);
      if(graphs)
	tr_acyc_into_graph(STYLE_READABLE, out, graphs);
      if(merged && weight_sum)
	tr_optimize_statement_into_cnf(STYLE_ACYC_READABLE,
				       out, merged, table);
      tr_program_into_eq(STYLE_READABLE, out, program, table, size, 0);
      tr_atoms_into_eq(STYLE_READABLE, out, table, occtable, 0);

    } else {
      /* Translate everything into (weighted) cnf */

      if(weight_sum)
	fprintf(out, "%% p wcnf %i %i %i\n",
		atom_count, clause_count, weight_sum);
      else
	fprintf(out, "%% p cnf %i %i\n", atom_count, clause_count);
      if(graphs)
	tr_acyc_into_cnf(STYLE_READABLE, flavor, out, graphs, weight_sum);
      if(merged && weight_sum)
	tr_optimize_statement_into_cnf(STYLE_READABLE, out, merged, table);
      tr_program_into_eq(STYLE_READABLE, out, program, table, size, weight_sum);
      tr_atoms_into_eq(STYLE_READABLE, out, table, occtable, weight_sum);
    }

  } else { /* !option_verbose */

    if(option_graph) {
      /* Output graph/acyc extensions */

      fprintf(out, "p cnf %i %i\n", atom_count, clause_count);
      write_symbols(STYLE_DIMACS, out, table);
      if(graphs)
	tr_acyc_into_graph(STYLE_DIMACS, out, graphs);
      if(merged && weight_sum)
	tr_optimize_statement_into_cnf(STYLE_ACYC, out, merged, table);
      tr_program_into_eq(STYLE_DIMACS, out, program, table, size, 0);
      tr_atoms_into_eq(STYLE_DIMACS, out, table, occtable, 0);

    } else {
      /* Either cnf of weighted cnf as output */

      if(merged && weight_sum)
	fprintf(out, "p wcnf %i %i %i\n", atom_count, clause_count, weight_sum);
      else
	fprintf(out, "p cnf %i %i\n", atom_count, clause_count);
      write_symbols(STYLE_DIMACS, out, table);
      if(graphs)
	tr_acyc_into_cnf(STYLE_DIMACS, flavor, out, graphs, weight_sum);
      tr_program_into_eq(STYLE_DIMACS, out, program, table, size, weight_sum);
      if(merged && weight_sum)
	tr_optimize_statement_into_cnf(STYLE_DIMACS, out, merged, table);
      tr_atoms_into_eq(STYLE_DIMACS, out, table, occtable, weight_sum);
    }
  }

  exit(0);
}

/* --------------------- Local translation routines ------------------------ */

void tr_atom_list(int style, FILE *out, int cnt, int *atoms,
		  ATAB *table, int negated)

{
  int i = 0;

  for(i=0 ; i<cnt; ) {
    int atom = atoms[i];

    if(negated)
      fputs("-", out);
    if(style == STYLE_READABLE)
      write_atom(style, out, atom, table);
    else
      write_classical_atom(style, out, atom, table);
    i++;
    if(i != cnt) {
      if(style == STYLE_READABLE)
	fputs(" |", out);
      fputs(" ", out);
    }
  }

  return;
}

void tr_basic_into_eq(int style, FILE *out, RULE *rule, ATAB *table,
		      int limit, int weight_sum)
{
  BASIC_RULE *basic = rule->data.basic;

  int pos_cnt = basic->pos_cnt;
  int neg_cnt = basic->neg_cnt;

  int head = basic->head;
  int status = 0;
 
  if(head <= limit)
    status = get_status(table, head);
  else
    status = 0;

  if(status >= 0) {
    int weight_out = 0;

    /* Generate clause "h | -l_1 | ... | -l_n" (if necessary) */

    if(!(status & MARK_TRUE_OR_FALSE)) { /* The value of head unknown */

      /* Generate the weight if present */

      if(weight_sum && style == STYLE_DIMACS) {
	fprintf(out, "%i ", weight_sum);
	weight_out = -1;
      }

      if(head <= limit) {
	/* The only head occurrence */

	if(style == STYLE_READABLE)
	  write_atom(style, out, head, table);
	else
	  write_classical_atom(style, out, head, table);
      } else {
	/* The head has been renamed */

	if(style == STYLE_READABLE)
	  fputs("v", out);
	fprintf(out, "%i", head);
      }

    }

    /* The body part -l_1 | ... | -l_n is generated only if needed */

    if(!(status & MARK_TRUE) || (status & MARK_FALSE)) {
      int first = -1;

      if(weight_sum && !weight_out && style == STYLE_DIMACS)
	fprintf(out, "%i ", weight_sum);

      if(pos_cnt) {
	if(style == STYLE_READABLE && !(status & MARK_FALSE))
	  fputs(" |", out);

	if(!(status & MARK_FALSE))
	  fputs(" ", out);

	tr_atom_list(style, out, pos_cnt, basic->pos, table, -1);

	first = 0;
      }

      if(neg_cnt) {
	if(style == STYLE_READABLE && !((status & MARK_FALSE) && first))
	  fputs(" |", out);

	if(!((status & MARK_FALSE) && first))
	  fputs(" ", out);

	tr_atom_list(style, out, neg_cnt, basic->neg, table, 0);

	first = 0;
      }

      if(style == STYLE_READABLE) {
	if(weight_sum)
	  fprintf(out, " = %i.\n", weight_sum);
	else
	  fputs(".\n", out); 
      } else {
	if(!((status & MARK_FALSE) && first))
	  fputs(" ", out);
	fputs("0\n", out);
      }

    }

    /* Generate clauses "-h | l_1", ..., "-h | l_n" (if necessary) */

    if(!(status & MARK_FALSE)) {
      int *atoms = basic->pos;
      int cnt = basic->pos_cnt;
      int i = 0;

      for(i=0; i<cnt; i++) {
	int atom = atoms[i];

	if(weight_sum && style == STYLE_DIMACS)
	  fprintf(out, "%i ", weight_sum);

	if(!(status & MARK_TRUE)) {

	  fputs("-", out);

	  if(head <= limit) {
	    if(style == STYLE_READABLE)
	      write_atom(style, out, head, table);
	    else
	      write_classical_atom(style, out, head, table);
	  } else {
	    if(style == STYLE_READABLE)
	      fputs("v", out);
	    fprintf(out, "%i", head);
	  }

	}

	if(style == STYLE_READABLE && !(status & MARK_TRUE))
	  fputs(" |", out);
	if(!(status & MARK_TRUE))
	  fputs(" ", out);

	if(style == STYLE_READABLE)
	  write_atom(style, out, atom, table);
	else
	  write_classical_atom(style, out, atom, table);

	if(style == STYLE_READABLE) {
	  if(weight_sum)
	    fprintf(out, " = %i.\n", weight_sum);
	  else
	    fputs(".\n", out);
	} else
	  fputs(" 0\n", out);
      }

      atoms = basic->neg;
      cnt = basic->neg_cnt;

      for(i=0; i<cnt; i++) {
	int atom = atoms[i];

	if(weight_sum && style == STYLE_DIMACS)
	  fprintf(out, "%i ", weight_sum);

	if(!(status & MARK_TRUE)) {

	  fputs("-", out);

	  if(head <= limit) {
	    if(style == STYLE_READABLE)
	      write_atom(style, out, head, table);
	    else
	      write_classical_atom(style, out, head, table);
	  } else {
	    if(style == STYLE_READABLE)
	      fputs("v", out);
	    fprintf(out, "%i", head);
	  }

	}

	if(style == STYLE_READABLE && !(status & MARK_TRUE))
	  fputs(" |", out);
	if(!(status & MARK_TRUE))
	  fputs(" ", out);

	fputs("-", out);

	if(style == STYLE_READABLE)
	  write_atom(style, out, atom, table);
	else
	  write_classical_atom(style, out, atom, table);

	if(style == STYLE_READABLE) {
	  if(weight_sum)
	    fprintf(out, " = %i.\n", weight_sum);
	  else
	    fputs(".\n", out);
	} else
	  fputs(" 0\n", out);
      }
    }
  }

  return;
}

void tr_choice_into_impl(int style, FILE *out, RULE *rule, ATAB *table,
			 int limit, int weight_sum)
{
  CHOICE_RULE *choice = rule->data.choice;

  int pos_cnt = choice->pos_cnt;
  int neg_cnt = choice->neg_cnt;

  int head = choice->head[0]; /* Only singleton heads supported */
  int status = 0;
 
  if(head <= limit)
    status = get_status(table, head);
  else
    status = 0;

  if(status >= 0) {
    /* Generate clauses "-h | l_1", ..., "-h | l_n" (if necessary) */

    if(!(status & MARK_FALSE)) {
      int *atoms = choice->pos;
      int cnt = choice->pos_cnt;
      int i = 0;

      for(i=0; i<cnt; i++) {
	int atom = atoms[i];

	if(weight_sum && style == STYLE_DIMACS)
	  fprintf(out, "%i ", weight_sum);

	if(!(status & MARK_TRUE)) {

	  fputs("-", out);

	  if(head <= limit) {
	    if(style == STYLE_READABLE)
	      write_atom(style, out, head, table);
	    else
	      write_classical_atom(style, out, head, table);
	  } else {
	    if(style == STYLE_READABLE)
	      fputs("v", out);
	    fprintf(out, "%i", head);
	  }

	}

	if(style == STYLE_READABLE && !(status & MARK_TRUE))
	  fputs(" |", out);
	if(!(status & MARK_TRUE))
	  fputs(" ", out);

	if(style == STYLE_READABLE)
	  write_atom(style, out, atom, table);
	else
	  write_classical_atom(style, out, atom, table);

	if(style == STYLE_READABLE) {
	  if(weight_sum)
	    fprintf(out, " = %i.\n", weight_sum);
	  else
	    fputs(".\n", out);
	} else
	  fputs(" 0\n", out);
      }

      atoms = choice->neg;
      cnt = choice->neg_cnt;

      for(i=0; i<cnt; i++) {
	int atom = atoms[i];

	if(weight_sum && style == STYLE_DIMACS)
	  fprintf(out, "%i ", weight_sum);

	if(!(status & MARK_TRUE)) {

	  fputs("-", out);

	  if(head <= limit) {
	    if(style == STYLE_READABLE)
	      write_atom(style, out, head, table);
	    else
	      write_classical_atom(style, out, head, table);
	  } else {
	    if(style == STYLE_READABLE)
	      fputs("v", out);
	    fprintf(out, "%i", head);
	  }

	}

	if(style == STYLE_READABLE && !(status & MARK_TRUE))
	  fputs(" |", out);
	if(!(status & MARK_TRUE))
	  fputs(" ", out);

	fputs("-", out);

	if(style == STYLE_READABLE)
	  write_atom(style, out, atom, table);
	else
	  write_classical_atom(style, out, atom, table);

	if(style == STYLE_READABLE) {
	  if(weight_sum)
	    fprintf(out, " = %i.\n", weight_sum);
	  else
	    fputs(".\n", out);
	} else
	  fputs(" 0\n", out);
      }
    }
  }

  return;
}

void tr_program_into_eq(int style, FILE *out, RULE *program, ATAB *table,
			int limit /* To distinguish original atoms */,
			int weight_sum)
{
  RULE *scan = program;

  while(scan) {

    switch(scan->type) {
    case TYPE_BASIC:
      tr_basic_into_eq(style, out, scan, table, limit, weight_sum);
      break;

    case TYPE_CHOICE:
      tr_choice_into_impl(style, out, scan, table, limit, weight_sum);
      break;
    }

    scan = scan->next;
  }

  return;
}

void tr_atoms_into_eq(int style, FILE *out, ATAB *table, OCCTAB *occtab,
		      int weight_sum)
{
  while(table) {
    int count = table->count;
    int offset = table->offset;
    int i = 0;
  
    for(i=1; i<=count; i++) {
      int head = i+offset;
      DEF *d = definition(occtab, head);

      if(d != NULL) { /* Only original atoms may have refererences */
	int rcnt = d->rule_cnt;
	RULE **rules = d->rules;
	int *statuses = table->statuses;
	int status = statuses[i];
	int j = 0;

	/* Check if the truth value is known by compute statement */

	if(status & MARK_TRUE) {
	  if(style == STYLE_READABLE) {
	    write_atom(style, out, head, table);
	    if(weight_sum)
	      fprintf(out, " = %i.\n", weight_sum);
	    else
	      fputs(".\n", out);
	  } else {
	    if(weight_sum && style == STYLE_DIMACS)
	      fprintf(out, "%i ", weight_sum);
	    write_classical_atom(style, out, head, table);
	    fputs(" 0\n", out);
	  }
	}

	if(status & MARK_FALSE) {
	  if(weight_sum && style == STYLE_DIMACS)
	    fprintf(out, "%i ", weight_sum);
	  fputs("-", out);
	  if(style == STYLE_READABLE) {
	    write_atom(style, out, head, table);
	    if(weight_sum)
	      fprintf(out, " = %i.\n", weight_sum);
	    else
	      fputs(".\n", out);
	  } else {
	    write_classical_atom(style, out, head, table);
	    fputs(" 0\n", out);
	  }
	}
     
	/* Skip cases that need no completion */

	if(rcnt == 1 || (rcnt>1 && (status & MARK_FALSE))
           || (rcnt == 0 && (status & MARK_INPUT)))
	  continue;

	/* Produce the completing clause
           "-a | b_1 | ... | b_n"  for the atom "a" */

	if(weight_sum && style == STYLE_DIMACS)
	  fprintf(out, "%i ", weight_sum);

	if(!((status & MARK_TRUE) && rcnt>1)) {
	  fputs("-", out);

	  if(style == STYLE_READABLE)
	    write_atom(style, out, head, table);
	  else
	    write_classical_atom(style, out, head, table);

	  if(rcnt>0) {
	    if(style == STYLE_READABLE)
	      fputs(" |", out);
	    fputs(" ", out);
	  }

	}
  
	for(j=0; j<rcnt; ) {
	  RULE *rule = rules[j];
	  BASIC_RULE *basic = rule->data.basic;
	  int other_head = basic->head;

	  if(style == STYLE_READABLE)
	    fputs("v", out);
	  fprintf(out, "%i", other_head);

	  j++;
	  if(j<rcnt) {
	    if(style == STYLE_READABLE)
	      fputs(" |", out);
	    fputs(" ", out);
	  }
	}

	if(style == STYLE_READABLE) {
	  if(weight_sum)
	    fprintf(out, " = %i.\n", weight_sum);
	  else
	    fputs(".\n", out);
	} else
	  fputs(" 0\n", out);

	/* Produce forward chaining clauses
           "h | -b_1", ..., "h | -b_n" for the atom "a" */

	if(!((status & MARK_TRUE) && (rcnt)>1)) {

	  for(j=0; j<rcnt; j++) {
	    RULE *rule = rules[j];
	    BASIC_RULE *basic = rule->data.basic;
	    int other_head = basic->head;

	    if(weight_sum && style == STYLE_DIMACS)
	      fprintf(out, "%i ", weight_sum);

	    if(style == STYLE_READABLE)
	      write_atom(style, out, head, table);
	    else
	      write_classical_atom(style, out, head, table);

	    if(style == STYLE_READABLE)
	      fputs(" |", out);
	    fputs(" -", out);

	    if(style == STYLE_READABLE)
	      fputs("v", out);
	    fprintf(out, "%i", other_head);

	    if(style == STYLE_READABLE) {
	      if(weight_sum)
		fprintf(out, " = %i.\n", weight_sum);
	      else
		fputs(".\n", out);
	    } else
	      fputs(" 0\n", out);

	  }
	}
      }
    }
    table = table->next;
  }

  return;
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

int array_gcd(int c, int *v)
{
  int g = (c == 0 ? 1 : v[0]);
  int i;

  for(i = 1; i < c; i++)
    g = gcd(g, v[i]);

  return g;
}

/*
 * merge_optimize_statements -- Merge optimize statements lexicographically
 * WARNING: This does gcd simplification even with a single statement
 */

RULE *merge_optimize_statements(RULE *statements)
{
  RULE *scan, *rule;
  OPTIMIZE_RULE *optimize;
  int neg_cnt = 0, pos_cnt = 0;
  int *wneg, *wpos, *wweightneg, *wweightpos;
  int base = 1;

  /* Compute the total number of positive and negative literals */

  for(scan = statements; scan; scan = scan->next) {
    neg_cnt += scan->data.optimize->neg_cnt;
    pos_cnt += scan->data.optimize->pos_cnt;
  }

  /* Return an empty statement if there are no literals */

  if((neg_cnt == 0) && (pos_cnt == 0))
    return statements;

  /* Allocate the new rule */

  rule = (RULE *)malloc(sizeof(RULE));
  optimize = (OPTIMIZE_RULE *)malloc(sizeof(OPTIMIZE_RULE));

  rule->type = TYPE_OPTIMIZE;
  rule->data.optimize = optimize;
  rule->next = NULL;

  optimize->neg_cnt = neg_cnt;
  optimize->pos_cnt = pos_cnt;
  optimize->neg = wneg = (int *)malloc(2*(neg_cnt+pos_cnt)*sizeof(int));
  optimize->pos = wpos = &optimize->neg[neg_cnt];
  optimize->weight = wweightneg = &optimize->pos[pos_cnt];
  wweightpos = &wweightneg[neg_cnt];

  /* Fill the rule */

  for(scan = statements; scan; scan = scan->next) {
    OPTIMIZE_RULE *o  = scan->data.optimize;
    int *rlit, *rlast;
    int *rweight      = o->weight;
    int rsum          = 0;

    int div = array_gcd(o->neg_cnt + o->pos_cnt, o->weight);

    for(rlast = &o->neg[o->neg_cnt], rlit = o->neg;
        rlit != rlast;
        rlit++, rweight++, wneg++, wweightneg++) {

      int r       = *rweight / div;
      *wneg       = *rlit;
      *wweightneg = r * base;
      rsum        += r;
    }

    for(rlast = &rlit[o->pos_cnt];
        rlit != rlast;
        rlit++, rweight++, wpos++, wweightpos++) {

      int r       = *rweight / div;
      *wpos       = *rlit;
      *wweightpos = r * base;
      rsum        += r;
    }

    base *= (1 + rsum);
  }

  return rule;
}

void tr_optimize_statement_into_cnf(int style, FILE *out,
				    RULE *statement, ATAB *table)
{
  OPTIMIZE_RULE *optimize = statement->data.optimize;
  int i = 0, j = 0;
  int pos_cnt = optimize->pos_cnt;
  int neg_cnt = optimize->neg_cnt;
  int *pos = optimize->pos;
  int *neg = optimize->neg;
  int *weight = optimize->weight;

  if(style == STYLE_ACYC)
    fputs("c minweight", out);

  for(i=0; i<neg_cnt; i++)
    switch(style) {
    case STYLE_DIMACS:
      fprintf(out, "%i ", weight[j++]);
      tr_atom_list(style, out, 1, &(neg[i]), table, 0);
      fputs(" 0\n", out);
      break;

    case STYLE_ACYC:
      fputs(" ", out);
      tr_atom_list(STYLE_DIMACS, out, 1, &(neg[i]), table, -1);
      fprintf(out, " %i", weight[j++]);
      break;
      
    case STYLE_READABLE:
      tr_atom_list(style, out, 1, &(neg[i]), table, 0);
      fprintf(out, " = %i.\n", weight[j++]);
      break;

    case STYLE_ACYC_READABLE:
      fputs("% wt(", out);
      tr_atom_list(STYLE_READABLE, out, 1, &(neg[i]), table, -1);
      fprintf(out, ") = %i.\n", weight[j++]);
      break;
    }

  for(i=0; i<pos_cnt; i++)
    switch(style) {
    case STYLE_DIMACS:
      fprintf(out, "%i ", weight[j++]);
      tr_atom_list(style, out, 1, &(pos[i]), table, -1);
      fputs(" 0\n", out);
      break;

    case STYLE_ACYC:
      fputs(" ", out);
      tr_atom_list(STYLE_DIMACS, out, 1, &(pos[i]), table, 0);
      fprintf(out, " %i", weight[j++]);
      break;

    case STYLE_READABLE:
      tr_atom_list(style, out, 1,  &(pos[i]), table, -1);
      fprintf(out, " = %i.\n", weight[j++]);
      break;

    case STYLE_ACYC_READABLE:
      fputs("% wt(", out);
      tr_atom_list(STYLE_READABLE, out, 1, &(pos[i]), table, 0);
      fprintf(out, ") = %i.\n", weight[j++]);
      break;
    }

  if(style == STYLE_ACYC)
    fputs("\n", out);

  return;
}
