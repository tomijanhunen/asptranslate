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
 * LP2ACYC -- Capture stable models of a normal program via acyclicity
 *
 * (c) 2014-2015 Tomi Janhunen
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
#include "acyc.h"

void _version_lp2acyc_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: lp2acyc.c,v $",
	   "$Date: 2021/05/27 11:17:49 $",
	   "$Revision: 1.30 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
  _version_scc_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   lp2acyc <options> <file>\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "   -r -- print reduced program and exit\n");
  fprintf(stderr, "   -k -- keep the program as is (except choice rules)\n");
  fprintf(stderr, "   -s -- include symbolic names for new atoms\n");
  fprintf(stderr, "   -w -- weak translation (no acyc constraints)\n");
  fprintf(stderr, "   -d -- drop optimization statements\n");
  fprintf(stderr, "   -x -- ignore atoms in bodyless choices in scc check\n");
  fprintf(stderr, "   -p<prefix> -- set prefix for invisible atoms\n");
  fprintf(stderr, "\n");

  return;
}

#define RESERVE_ATOMS(variable,count) variable; variable+=count

int size = 0; /* The size of the symbol table */
AQUEUE *new_symbols = NULL;
void write_new_symbols(int style, FILE *out);
char *prefix = "_";

GRAPH *graph = NULL;  /* Storing atoms related with the acyclicity check */

RULE *add_facts(RULE *program, ATAB *table);

int simplify_weight(RULE *rule);
RULE *simplify_program(RULE *program, ATAB *table,
		       int *contradiction, int *newatom, int keep);
void tr_atoms(int style, FILE *out, ATAB *table, OCCTAB *occtable,
	      int weak, int *contradiction, int newatom);

typedef struct weighted_atom {
  int atom;
  int weight;
} WATOM;

void sort_weighted_atoms(int cnt, int *atoms, int *weights,
			 int (*comparator)(const void *, const void *));
int cmp_atoms_asc(const void *a, const void *b);
int cmp_weights_asc(const void *a, const void *b);

int count_duplicate_atoms(int cnt, int *atoms);
void remove_duplicate_atoms(int cnt, int *atoms, int *weights);
int remove_duplicate_weighted_atoms(int cnt, int *atoms, int *weights);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL, *statements = NULL, *tail=NULL;
  RULE *scan = NULL, *prev = NULL;

  ATAB *table = NULL;     /* For the original program */

  OCCTAB *occtable = NULL;
  int number = 0;

  int newatom = 0, atom = 0, contradiction = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;
  int option_reduce = 0;
  int option_keep = 0;
  int option_symbols = 0;
  int option_dropt = 0;
  int option_weak = 0;
  int option_prefix = 0;

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
    else if(strcmp(arg, "-r") == 0)
      option_reduce = -1;
    else if(strcmp(arg, "-k") == 0)
      option_keep = -1;
    else if(strcmp(arg, "-s") == 0)
      option_symbols = -1;
    else if(strcmp(arg, "-w") == 0)
      option_weak = -1;
    else if(strcmp(arg, "-d") == 0)
      option_dropt = -1;
    else if (strcmp(arg, "-x") == 0)
      scc_set(SCC_SKIP_CHOICE);				
    else if(strncmp(arg, "-p", 2) == 0) {
      option_prefix = -1;
      prefix = &arg[2];
    } else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }
  }

  if(option_help) usage();
  if(option_version) _version_lp2acyc_c();

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

  /* Symbol checks */

  if(table_size(table) == 0) {
    if(option_verbose)
      fprintf(out, "%% %s contains no atoms, hence no output!\n", file);
    else
      fprintf(out, "0\n0\nB+\n0\nB-\n0\nE\n0\n1\n");
    exit(0);
  }

  if(option_symbols) {
    new_symbols = (AQUEUE *)malloc(sizeof(AQUEUE));
    new_symbols->first = NULL;
    new_symbols->last = NULL;
  }

  /* Extract potential optimization statements and
     check particular kinds of atom occurrences for simplification */

  scan = program;
  prev = NULL;

  while(scan) {
    RULE *next = scan->next;

    switch(scan->type) {
    case TYPE_OPTIMIZE:
      if(prev)
	prev->next = next;
      else
	program = next;

      scan->next = NULL;
      if(tail)
	tail->next = scan;
      else
	statements = scan;
      tail = scan;
      break;

    case TYPE_CHOICE:
      if(get_pos_cnt(scan)+get_neg_cnt(scan)==0) {
	int *heads = get_heads(scan);
	int i = 0, cnt = 0;
	for (i = 0, cnt = get_head_cnt(scan); i != cnt; ++i) {
	  set_status(table, heads[i], MARK_CHOICE);
	}
      }
      prev = scan;
      break;

    case TYPE_BASIC:
    case TYPE_CONSTRAINT:
    case TYPE_WEIGHT:
      { int head = get_head(scan);
	set_status(table, head, MARK_ODEF);

	if(get_pos_cnt(scan)+get_neg_cnt(scan)==0)
	  set_status(table, head, MARK_FACT);

	if(scan->type == TYPE_CONSTRAINT) {
	  CONSTRAINT_RULE *constraint = scan->data.constraint;
	  int *space = NULL;
	  int pos_cnt = constraint->pos_cnt;
	  int *pos = constraint->pos;
	  int neg_cnt = constraint->neg_cnt;
	  int *neg = constraint->neg;
	  int new_cnt = 0;

	  if(pos_cnt>1) { /* Remove duplicates (if any) */

	    sort_weighted_atoms(pos_cnt, pos, NULL, cmp_atoms_asc);
	    new_cnt = pos_cnt-count_duplicate_atoms(pos_cnt, pos);

	    if(new_cnt<pos_cnt) { /* There is something to remove */
	      RULE *new = (RULE *)malloc(sizeof(RULE));
	      WEIGHT_RULE *weight = (WEIGHT_RULE *)malloc(sizeof(WEIGHT_RULE));
	      int i = 0;

	      /* Allocate memory in analogy to input.c */
	      space = (int *)malloc(sizeof(int)*(2*neg_cnt+2*new_cnt));

	      new->type = TYPE_WEIGHT;
	      new->data.weight = weight;
	      new->next = scan->next;

	      weight->head = constraint->head;
	      weight->bound = constraint->bound;

	      weight->neg_cnt = neg_cnt;
	      weight->neg = space;
	      memcpy(weight->neg, constraint->neg, neg_cnt*sizeof(int));

	      weight->pos_cnt = new_cnt;
	      weight->pos = &space[neg_cnt];
	      weight->weight = &space[neg_cnt+new_cnt];
	      remove_duplicate_atoms(pos_cnt, pos, &(weight->weight[neg_cnt]));
	      memcpy(weight->pos, pos, new_cnt*sizeof(int));

	      for(i=0; i<neg_cnt; i++)
		weight->weight[i] = 1;

	      if(prev)
		prev->next = new;
	      else
		program = new;

	      scan->next = NULL;
	      free_rule(scan);
	      scan = new;
	    }
	  }
	} else if(scan->type == TYPE_WEIGHT) {
	  WEIGHT_RULE *weight = scan->data.weight;

	  if(weight->pos_cnt>1) {
	    /* Remove duplicates (if any) and then sort by weight */

	    sort_weighted_atoms(weight->pos_cnt,
				weight->pos,
				&(weight->weight[weight->neg_cnt]),
				cmp_atoms_asc);

	    weight->pos_cnt =
	      remove_duplicate_weighted_atoms(weight->pos_cnt,
					      weight->pos,
					      &(weight->
						weight[weight->neg_cnt]));

	    sort_weighted_atoms(weight->pos_cnt,
				weight->pos,
				&(weight->weight[weight->neg_cnt]),
				cmp_weights_asc);
	  }
	}
	/* Proceed to default */
      }
    default:
      prev = scan;
    }

    scan = next;
  }

  size = table_size(table);
  newatom = size+1;

  if(program) {
    program = simplify_program(program, table, &contradiction, &newatom,
			       option_keep);
    if(!option_keep) {
      /* Add detected facts to the beginning of the program */

      program = add_facts(program, table);

      /* Remove choice rules having an input atom as head */

      scan = program;
      prev = NULL;

      while(scan) {
	RULE *next = scan->next;

	switch(scan->type) {
	case TYPE_CHOICE:
	  { int *heads = get_heads(scan);
	    int head = heads[0]; /* Only one after simplification */

	    if(get_status(table, head) & MARK_INPUT) {
	      if(prev)
		prev->next = next;
	      else
		program = next;

	      scan->next = NULL;
	      free_program(scan);
	      break;
	    }
	    /* Fall to defaut */
	  }
	default:
	  prev = scan;
	}

	scan = next;
      }
    }
  }

  if(newatom > size+1) { /* At least one new atom was introduced */
    (void) extend_table(table, newatom-(size+1), size);
    size += newatom-(size+1);

    if(contradiction)
      set_status(table, contradiction, MARK_FALSE);
  }

  if(option_prefix)
    name_invisible_atoms(prefix, table);

  if(option_reduce) { /* Write the input program (for debugging) */

    if(option_verbose) {

      fprintf(out, "%% Program %s:\n\n", file);

      write_program(STYLE_READABLE, out, program, table);
      if(statements && !option_dropt)
	write_program(STYLE_READABLE, out, statements, table);

      fprintf(out, "%% List of %i atoms:\n\n", table_size(table));
      write_symbols(STYLE_READABLE, out, table);
      fprintf(out, "\n");

      fprintf(out, "#compute { ");
      write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE_OR_FALSE);
      fprintf(out, " }.\n\n");

      write_input(STYLE_READABLE, out, table);

    } else {

      write_program(STYLE_SMODELS, out, program, table);
      if(statements && !option_dropt)
	write_program(STYLE_SMODELS, out, statements, table);
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
  /* Check head occurrences */

  occtable = initialize_occurrences(table, 0, 0);
  compute_occurrences(program, occtable, 0, 0);
  compute_sccs(occtable, size);

  /* Compute strongly connected components (i.e., SCCs) */

  /* Produce the desired output */

  if(option_verbose) { /* Use symbolic (human readable) format */

    fprintf(out, "%% Translation of the program %s:\n\n", file);

    tr_atoms(STYLE_READABLE, out, table, occtable,
	     option_weak, &contradiction, newatom);

    if(graph) {
      fprintf(out, "%% Choices for acyclicity atoms:\n\n");

      tr_acyc_choices(STYLE_READABLE, out, graph, table);
    }

    fprintf(out, "%% List of %i atoms:\n\n", table_size(table));
    write_symbols(STYLE_READABLE, out, table);
    fprintf(out, "\n");

    if(option_symbols || graph)
      fprintf(out, "%% Other auxiliary atoms:\n\n");

    if(option_symbols) {
      write_new_symbols(STYLE_READABLE, out);
      fputs("\n", out);
    }
    if(graph) {
      tr_acyc_symbols(STYLE_READABLE, out, graph);
      fputs("\n", out);
    }

    if(statements && !option_dropt)
      write_program(STYLE_READABLE, out, statements, table);

    if(contradiction>0)
      fprintf(out, "#compute { not %s%i }.\n", prefix, contradiction);

    fprintf(out, "#compute { ");
    write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE_OR_FALSE);
    fprintf(out, " }.\n\n");

    write_input(STYLE_READABLE, out, table);

  } else { /* !option_verbose: use internal format */

    tr_atoms(STYLE_SMODELS, out, table, occtable,
	     option_weak, &contradiction, newatom);
    if(statements && !option_dropt)
      write_program(STYLE_SMODELS, out, statements, table);
    if(graph)
      tr_acyc_choices(STYLE_SMODELS, out, graph, table);
    fprintf(out, "0\n");

    write_symbols(STYLE_SMODELS, out, table);
    if(option_symbols)
      write_new_symbols(STYLE_SMODELS, out);
    if(graph)
      tr_acyc_symbols(STYLE_SMODELS, out, graph);
    fprintf(out, "0\n");

    fprintf(out, "B+\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_TRUE);
    fprintf(out, "0\n");

    fprintf(out, "B-\n");
    if(contradiction>0)
      fprintf(out, "%i\n", contradiction);
    write_compute_statement(STYLE_SMODELS, out, table, MARK_FALSE);
    fprintf(out, "0\n");

    fprintf(out, "E\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_INPUT);
    fprintf(out, "0\n");

    /* Suggest computing only one stable model */
    fprintf(out, "%i\n", 1);
  }

  exit(0);
}

/* ------------------- Routines for atoms and symbols ---------------------- */

void write_atom_if_possible(int style, FILE *out, int atom, ATAB *table)
{
  if(table) 
    write_atom(style, out, atom, table);
  else {
    if(style == STYLE_READABLE)
      fprintf(out, "%s%i", prefix, atom);
    else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom);
  }
  return;
}

/*
 * write_new_symbols -- Declare names for some auxiliary atoms
 */

void write_new_symbols(int style, FILE *out)
{
  QELEM *q = new_symbols->first;

  while(q) {
    switch(style) {
    case STYLE_READABLE:
      fprintf(out, "%% %s%i = ", prefix, q->elem.atom);
      break;
    case STYLE_SMODELS:
      fprintf(out, "%i ", q->elem.atom);
      break;
    }
    q = print_elem(out, q->next);
    fprintf(out, "\n");
  }

  return;
}

/* ------------------------- Program simplification ------------------------ */

/*
 * useless -- Check for potentially useless rules or positive literals
 */

int useless(RULE *rule, ATAB *table)
{
  int i = 0;
  int status = 0;

  /* Can handle basic, cardinality, and weight rules */

  switch(rule->type) {

  case TYPE_BASIC:

    { BASIC_RULE *basic = rule->data.basic;
      int head = basic->head;
      int pos_cnt = basic->pos_cnt;
      int *pos = basic->pos;

      if(get_status(table, head) & MARK_FACT)
	return -1;

      for(i=0; i < pos_cnt; i++)
        if(head == pos[i])  /* Head occurs positively */
          return -1;
    }
    break;

  case TYPE_CONSTRAINT:

    { CONSTRAINT_RULE *constraint = rule->data.constraint;
      int head = constraint->head;
      int pos_cnt = constraint->pos_cnt;
      int *pos = constraint->pos;
      int j = 0;

      if(get_status(table, head) & MARK_FACT)
	return -1;

      for(i=0; i < pos_cnt; i++)
        if(head != pos[i]) {
          if(j<i)
            pos[j] = pos[i];
          j++;
        }

      pos_cnt -= (i-j);
      if(pos_cnt+constraint->neg_cnt < constraint->bound)
        return -1;
      else
        constraint->pos_cnt = pos_cnt;
    }
    break;

  case TYPE_WEIGHT:
    { int sum = 0;
      int head = get_head(rule);
      WEIGHT_RULE *weight = rule->data.weight;

      if(get_status(table, head) & MARK_FACT)
	return -1;
      else
	sum = simplify_weight(rule);

      if(sum < weight->bound)
        return -1;
    }
    break;
  }

  return 0;
}

/*
 * remove_tautological_heads -- Remove heads that appear in the positive body
 */

void remove_tautological_heads(RULE *rule, ATAB *table)
{
  CHOICE_RULE *choice = rule->data.choice;
  int head_cnt = choice->head_cnt;
  int *head = choice->head;
  int pos_cnt = choice->pos_cnt;
  int *pos = choice->pos;
  int i = 0, j = 0, k = 0;

  for(i=0, j=0; i<head_cnt; i++) {
    int atom = head[i];
    int occurs = 0;
    int status = get_status(table, atom);

    for(k=0; k<pos_cnt; k++)
      if(atom == pos[k])
        occurs = -1;

    if(!occurs && !(status & (MARK_INPUT|MARK_FACT))) {
      /* Preserve a copy of this head atom */

      if(j<i)
        head[j] = head[i];
      j++;
    }
  }

  if(j<i)
    choice->head_cnt -= (i-j);

  return;
}

/*
 * copyinsert_basic -- Add a new basic rule (to the beginning of the program)
 */

RULE *copyinsert_basic(int head,
                       int pos_cnt, int *pos, int extra_pos,
                       int neg_cnt, int *neg, int extra_neg,
                       RULE *prev)
{
  RULE *rule = (RULE *)malloc(sizeof(RULE));
  BASIC_RULE *basic = (BASIC_RULE *)malloc(sizeof(BASIC_RULE));
  int *table = NULL;

  prev->next = rule;

  rule->type = TYPE_BASIC;
  rule->data.basic = basic;
  rule->next = NULL;

  basic->head = head;

  if(extra_pos) pos_cnt++;
  basic->pos_cnt = pos_cnt;

  if(extra_neg) neg_cnt++;
  basic->neg_cnt = neg_cnt;

  /* Allocate only one slice of memory in analogy to input.c */

  table = (int *)malloc((neg_cnt+pos_cnt)*sizeof(int));

  /* Copy negative body conditions */

  basic->neg = table;
  if(extra_neg) {
    if(neg_cnt>1)
    memcpy(table, neg, (neg_cnt-1)*sizeof(int));
    table[neg_cnt-1] = extra_neg;
  } else
    memcpy(table, neg, neg_cnt*sizeof(int));

  /* Copy positive body conditions */

  basic->pos = &table[neg_cnt];
  if(extra_pos) {
    if(pos_cnt>1)
      memcpy(basic->pos, pos, (pos_cnt-1)*sizeof(int));
    table[neg_cnt+pos_cnt-1] = extra_pos;
  } else
    memcpy(basic->pos, pos, pos_cnt*sizeof(int));

  return rule;
}

/*
 * copyinsert_choice -- Add a new choice rule (to the beginning of the program)
 */

RULE *copyinsert_choice(int head, /* Only one head atom allowed */
			int pos_cnt, int *pos, int extra_pos,
			int neg_cnt, int *neg, int extra_neg,
			RULE *prev)
{
  RULE *rule = (RULE *)malloc(sizeof(RULE));
  CHOICE_RULE *choice = (CHOICE_RULE *)malloc(sizeof(CHOICE_RULE));
  int *table = NULL;

  prev->next = rule;

  rule->type = TYPE_CHOICE;
  rule->data.choice = choice;
  rule->next = NULL;

  choice->head_cnt = 1;
  choice->head = (int *)malloc(sizeof(int));
  choice->head[0] = head;

  if(extra_pos) pos_cnt++;
  choice->pos_cnt = pos_cnt;

  if(extra_neg) neg_cnt++;
  choice->neg_cnt = neg_cnt;

  /* Allocate only one slice of memory in analogy to input.c */

  table = (int *)malloc((neg_cnt+pos_cnt)*sizeof(int));

  /* Copy negative body conditions */

  choice->neg = table;
  if(extra_neg) {
    if(neg_cnt>1)
    memcpy(table, neg, (neg_cnt-1)*sizeof(int));
    table[neg_cnt-1] = extra_neg;
  } else
    memcpy(table, neg, neg_cnt*sizeof(int));

  /* Copy positive body conditions */

  choice->pos = &table[neg_cnt];
  if(extra_pos) {
    if(pos_cnt>1)
      memcpy(choice->pos, pos, (pos_cnt-1)*sizeof(int));
    table[neg_cnt+pos_cnt-1] = extra_pos;
  } else
    memcpy(choice->pos, pos, pos_cnt*sizeof(int));

  return rule;
}

/*
 * simplify_choice -- Simplify choice rules to have only one head atom each
 */

int simplify_choice(RULE *rule, ATAB *table, int newatom)
{
  RULE *prev = rule;   /* For inserting rules after this rule */
  CHOICE_RULE *choice = rule->data.choice;

  int head_cnt = 0, pos_cnt = 0, neg_cnt = 0;
  int *head = NULL;
  int i = 0, body = 0;

  /* It is assumed that the original rule will be destructed */

  head_cnt = choice->head_cnt;
  head = choice->head;
  pos_cnt = choice->pos_cnt;
  neg_cnt = choice->neg_cnt;

  if(head_cnt>1 && pos_cnt+neg_cnt>0) {

    /* The body is renamed in order to avoid a quadratic blow-up */

    body = newatom++;

    prev = copyinsert_basic(body, pos_cnt, choice->pos, 0,
			          neg_cnt, choice->neg, 0, prev);
  }

  /* Process head atoms in order */

  for(i=0; i<head_cnt; i++) {
    int atom = head[i];
    int status = get_status(table, atom);

    /* Add a choice rule for deriving this head atom */

    if(body)
      prev = copyinsert_choice(atom, 0, NULL, body,
			             0, NULL, 0, prev);

    else { /* head_cnt == 1 || pos_cnt+neg_cnt == 0 */

      if(pos_cnt+neg_cnt == 0
	 && !invisible(table, atom) /* The atom has a name */
	 && !(status & MARK_ODEF))  /* No other defining rules */
	set_status(table, atom, MARK_INPUT);
      else { /* head_cnt == 1 && pos_cnt+neg_cnt > 0 */

        prev = copyinsert_choice(atom, pos_cnt, choice->pos, 0,
				       neg_cnt, choice->neg, 0, prev);
      }
    }
  }

  return newatom;
}

/*
 * gcd -- greatest common divisor
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

int simplify_weight(RULE *rule)
{
  RULE *prev = rule;
  WEIGHT_RULE *weight = rule->data.weight;
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
      prev = copyinsert_basic(head, 0, NULL, 0, 1, scan, 0, prev);

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
      prev = copyinsert_basic(head, 1, scan, 0, 0, NULL, 0, prev);

    if(*scan == head || *w == 0 || *w >= bound) {
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
 * cmp_weights_asc -- Comparison routine for quicksort (weights)
 */

int cmp_weights_asc(const void *a, const void *b) 
{ 
  const WATOM *wa1 = (const WATOM *)a;
  const WATOM *wa2 = (const WATOM *)b;
  return wa1->weight - wa2->weight; 
} 

/*
 * compare_watom_asc -- Comparison routine for quicksort (atom numbers)
 */

int cmp_atoms_asc(const void *a, const void *b) 
{ 
  const WATOM *wa1 = (const WATOM *)a;
  const WATOM *wa2 = (const WATOM *)b;
  return wa1->atom - wa2->atom; 
} 


/*
 * sort_weighted_atoms -- Sort atoms by their weights or numbers
 */

void sort_weighted_atoms(int cnt, int *atoms, int *weights,
			 int (*comparator)(const void *, const void *))
{
  WATOM * const watoms = (WATOM *)malloc(cnt * sizeof(WATOM));
  int i = 0;

  /* Store the weights in the weighted index array */

  for(i = 0; i < cnt; i++) {
    watoms[i].atom = atoms[i];
    watoms[i].weight = weights ? weights[i] : 1;
  }

  /* Sort the weighted indices */

  qsort(watoms, cnt, sizeof(WATOM), comparator);

  /* Transfer the now ordered data back */

  for(i = 0; i < cnt; i++) {
    atoms[i] = watoms[i].atom;
    if(weights)
      weights[i] = watoms[i].weight;
  }

  free(watoms);
}

/*
 * count_duplicate_atoms -- Count the number of duplicate atoms
 */

int count_duplicate_atoms(int cnt, int *atoms)
{
  int i=0, k=0;

  for(i=0; i+1<cnt; i++)
    if(atoms[i]==atoms[i+1])
      k++;

  return k;
}

/*
 * remove_duplicate_weighted_atoms -- Remove duplicate atoms with weights
 */

void remove_duplicate_atoms(int cnt, int *atoms, int *weights)
{
  int i=0, j=0, k=0;

  /* Atoms must be sorted */

  for(i=0, j=i+1; j<cnt; i++, j++) {
    int atom = atoms[i];
    weights[i] = 1;

    while(j<cnt && atom == atoms[j]) { /* Accumulate at location i */
      weights[i]++;
      j++;
      k++;
    }
    if(j<cnt)
      atoms[i+1] = atoms[j];
  }

  return;
}

/*
 * remove_duplicate_weighted_atoms -- Remove duplicate atoms with weights
 */

int remove_duplicate_weighted_atoms(int cnt, int *atoms, int *weights)
{
  int i=0, j=0, k=0;

  /* Atoms must be sorted */

  for(i=0, j=i+1; i<cnt-k; i++, j++) {
    int atom = atoms[i];

    while(j<cnt && atom == atoms[j]) { /* Accumulate at location i */
      weights[i] += weights[j];
      j++;
      k++;
    }
    if(j<cnt) {
      atoms[i+1] = atoms[j];
      weights[i+1] = weights[j];
    }
  }

  return cnt-k;
}

/*
 * add_facts -- Add facts to the program
 */

RULE *add_facts(RULE *program, ATAB *table)
{
  while(table) {
    int count = table->count;
    int offset = table->offset;
    int shift = table->shift;
    int *statuses = table->statuses;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      int status = statuses[i];

      if(status & MARK_FACT) {
	RULE *new = (RULE *)malloc(sizeof(RULE));
	BASIC_RULE *basic = (BASIC_RULE *)malloc(sizeof(BASIC_RULE));
	
	new->type = TYPE_BASIC;
	new->next = program;
	program = new;

	new->data.basic = basic;
	basic->head = atom;
	basic->pos_cnt = 0;
	basic->pos = NULL;
	basic->neg_cnt = 0;
	basic->neg = NULL;
      }
    }
    table = table->next;
  }

  return program;
}

/*
 * simplify_program -- Simplify the program slightly
 */

RULE *simplify_program(RULE *program, ATAB *table,
		       int *contradiction, int *newatom,
		       int keep)
{
  RULE *prev = NULL;
  RULE *scan = program;

  while(scan) {
    RULE *next = scan->next;
    RULE *extra = NULL;
    int remove = 0;

    scan->next = NULL;

    /* Check what is to be removed and/or inserted */

    switch(scan->type) {

    case TYPE_BASIC:

      if(!keep && useless(scan, table))
        remove = -1;
      break;

    case TYPE_CHOICE:

      remove_tautological_heads(scan, table);

      /* Adds corresponding basic rules after choice rule */
      *newatom = simplify_choice(scan, table, *newatom);

      remove = -1;  /* Removed anyway */
      break;

    case TYPE_CONSTRAINT:

      { CONSTRAINT_RULE *constraint = scan->data.constraint;

	if(!keep) {
	  if(useless(scan, table))
	    remove = -1;
	  else if(constraint->bound == 0) {

	    /* The body is trivially satisfied; turn into a fact */

	    int head = constraint->head;
	    int status = get_status(table, head);
	    BASIC_RULE *basic = (BASIC_RULE *)constraint;

	    constraint->pos_cnt = 0;
	    constraint->neg_cnt = 0;
          
	    if(constraint->neg) /* See input.c */
	      free(constraint->neg);

	    scan->type = TYPE_BASIC;

	    if(status & MARK_INPUT) {
	      /* Create a constraint ":- not head." */

	      if(!contradiction)
		*contradiction = (*newatom)++;
              
	      basic->head = *contradiction;
	      basic->neg = (int *) malloc(sizeof(int));
	      basic->neg_cnt = 1;
	      basic->neg[0] = head;
	      basic->pos = &(basic->neg[1]);
	      basic->pos_cnt = 0;

	    } else {
	      /* Create a fact "head." */

	      basic->head = head;
	      basic->pos_cnt = 0;
	      basic->pos = NULL;
	      basic->neg_cnt = 0;
	      basic->neg = NULL;
	    }
	  }
	}
      }
      break;

    case TYPE_WEIGHT:

      { WEIGHT_RULE *weight = scan->data.weight;

	if(!keep) {
	  if(useless(scan, table))
	    remove = -1;
	  else if(weight->bound == 0) {

	    /* The body is trivially satisfied; turn into a fact */

	    int head = weight->head;
	    int status = get_status(table, head);
	    BASIC_RULE *basic = (BASIC_RULE *)weight;

	    weight->pos_cnt = 0;
	    weight->neg_cnt = 0;
          
	    if(weight->neg) /* See input.c */
	      free(weight->neg);

	    scan->type = TYPE_BASIC;

	    if(status & MARK_INPUT) {
	      /* Create a constraint ":- not head." */

	      if(!contradiction)
		*contradiction = (*newatom)++;
              
	      basic->head = *contradiction;
	      basic->neg = (int *) malloc(sizeof(int));
	      basic->neg_cnt = 1;
	      basic->neg[0] = head;
	      basic->pos = &(basic->neg[1]);
	      basic->pos_cnt = 0;

	    } else { 
	      /* Create a fact "head." */

	      basic->head = head;
	      basic->pos_cnt = 0;
	      basic->pos = NULL;
	      basic->neg_cnt = 0;
	      basic->neg = NULL;
	    }
	  }
	}
      }
      break;

    default:
      fprintf(stderr, "%s: rule type %i not supported!\n",
              program_name, scan->type);
      exit(-1);
      break;
    }

    extra = scan->next;

    /* Update the program accordingly */
      
    if(remove) {

      if(prev)
        prev->next = extra ? extra : next;
      else
        program = extra ? extra : next;

      scan->next = NULL; /* Detach (again) */
      free_rule(scan);   /* Destructive */
    }

    if(extra) {

      while(extra->next != NULL)
        extra = extra->next;

      prev = extra;
      prev->next = next;

    } else
      if(!remove) {
        prev = scan;
        prev->next = next;
      }

    scan = next;  /* Rule in the original program */
  }

  return program;
}

/*
 * rename_head -- Rename the head of a rule
 */

void rename_head(RULE *rule, int head)
{
  switch(rule->type) {
  case TYPE_BASIC:
    { BASIC_RULE *basic = rule->data.basic;
      basic->head = head;
    }
    break;

  case TYPE_CONSTRAINT:
    { CONSTRAINT_RULE *constraint = rule->data.constraint;
      constraint->head = head;
    }
    break;

  case TYPE_CHOICE:
    { CHOICE_RULE *choice = rule->data.choice;
      if(choice->head)
	choice->head[0] = head;
    }
    break;

  case TYPE_WEIGHT:
    { WEIGHT_RULE *weight = rule->data.weight;
      weight->head = head;
    }
    break;
  default:
    fprintf(stderr, "rename_head: unspported rule type %i!\n", rule->type);
    exit(-1);
    break;
  }
}

/* --------------------- Local translation routines ------------------------ */

void tr_pos_list(int style, FILE *out, int cnt, int *pos, ATAB *table)
{
  int i = 0;

  for(i = 0 ; i < cnt; ) {
    write_atom_if_possible(style, out, pos[i], table);
    i++;
    if(style == STYLE_READABLE && i<cnt)
      fputs(", ", out);
  }

  return;
}

void tr_neg_list(int style, FILE *out, int cnt, int *neg, ATAB *table)
{
  int i = 0;

  for(i = 0 ; i < cnt; ) {
    if(style == STYLE_READABLE)
      fputs("not ", out);
    write_atom_if_possible(style, out, neg[i], table);
    i++;
    if(style == STYLE_READABLE && i<cnt)
      fputs(", ", out);
  }

  return;
}

void tr_literal_list(int style, FILE *out, char *separator,
		     int pos_cnt, int *pos,
		     int neg_cnt, int *neg,
		     int *weight, ATAB *table)
{
  int i = 0, j = 0;

  for(i=0; i<neg_cnt; i++) {
    if(style == STYLE_READABLE)
      fprintf(out, "not ");
    write_atom_if_possible(style, out, neg[i], table);
    if(weight && (style == STYLE_READABLE))
      fprintf(out, "=%i", weight[j++]);
    if(style == STYLE_READABLE)
      if(i<neg_cnt-1 || pos_cnt)
	fprintf(out, "%s", separator);
  }

  for(i=0; i<pos_cnt; i++) {
    write_atom_if_possible(style, out, pos[i], table);
    if(weight && (style == STYLE_READABLE))
      fprintf(out, "=%i", weight[j++]);
    if(style == STYLE_READABLE && i<pos_cnt-1)
       fprintf(out, "%s", separator);
  }

  if(weight && (style == STYLE_SMODELS))
    while(j<pos_cnt+neg_cnt)
      fprintf(out, " %i", weight[j++]);

  return;
}

void compress_literal_list(int style, FILE *out, char *separator,
			   int scc_pos_cnt, int *scc_pos, ATAB *table)
{
  int i = 0;

  for(i=0; i<scc_pos_cnt; i++) {
    write_atom_if_possible(style, out, scc_pos[i], table);
    if(style == STYLE_READABLE && i<scc_pos_cnt-1)
       fprintf(out, "%s", separator);
  }

  return;
}

void external_literal_list(int style, FILE *out, char *separator,
			   int scc_pos_cnt, int *scc_pos,
			   int pos_cnt, int *pos,
			   int neg_cnt, int *neg, ATAB *table)
{
  int i = 0, j=0;

  /* All negative literals as such */

  for(i=0; i<neg_cnt; i++) {
    if(style == STYLE_READABLE)
      fprintf(out, "not ");
    write_atom_if_possible(style, out, neg[i], table);
    if(style == STYLE_READABLE)
      if(i<neg_cnt-1 || pos_cnt-scc_pos_cnt>0)
	fprintf(out, "%s", separator);
  }

  /* Positive literals outside the component */

  for(i=0, j=0; i<pos_cnt; i++) {
    int atom = pos[i];

    if(atom == scc_pos[j])
      j++;
    else {
      write_atom_if_possible(style, out, atom, table);
      if(style == STYLE_READABLE && i-j<pos_cnt-scc_pos_cnt-1)
	fprintf(out, "%s", separator);
    }

  }

  return;
}

/*
 * compress_rule -- Compress the bodies of basic/choice rules
 */

void compress_rule(int style, FILE *out,
                   int atom, int scc_pos_cnt, int *scc_pos,
		   int ext_body, int index, RULE *rule, ATAB *table)
{
  int pos_cnt = get_pos_cnt(rule);
  int *pos = get_pos(rule);
  int neg_cnt = get_neg_cnt(rule);
  int *neg = get_neg(rule);

  /* Produce the compressed rule */

  if(style == STYLE_READABLE) {

    if(rule->type == TYPE_CHOICE)
      fputs("{ ", out);
    write_atom_if_possible(style, out, atom, table);
    if(rule->type == TYPE_CHOICE)
      fputs(" }", out);
    fprintf(out, " :- ");

  } else if(style == STYLE_SMODELS) {

    if(rule->type == TYPE_CHOICE)
      fprintf(out, "3 1");
    else
      fprintf(out, "1");
    write_atom_if_possible(style, out, atom, table);

  }

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", scc_pos_cnt+1, 0);

  if(style == STYLE_READABLE) {
    fprintf(out, "_eb_%i_", index);
    write_atom_if_possible(style, out, atom, table);
    fputs(", ", out);
  }

  if(pos_cnt || neg_cnt) {

    compress_literal_list(style, out,
			  style == STYLE_READABLE ? ", ": " ",
			  scc_pos_cnt, scc_pos, table);
  }

  if(style == STYLE_SMODELS)
    fprintf(out, " %i", ext_body);

  if(style == STYLE_READABLE)
    fputs(".", out);
  fputs("\n",out);

  /* Produce the external part of the body */

  if(style == STYLE_READABLE) {

    fprintf(out, "_eb_%i_", index);
    write_atom_if_possible(style, out, atom, table);
    fprintf(out, " :- ");

  } else if(style == STYLE_SMODELS)
    fprintf(out, "1 %i", ext_body);

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", pos_cnt-scc_pos_cnt+neg_cnt, neg_cnt);

  external_literal_list(style, out,
			style == STYLE_READABLE ? ", ": " ",
			scc_pos_cnt, scc_pos,
			pos_cnt, pos, neg_cnt, neg, table);

  if(style == STYLE_READABLE)
    fputs(".", out);
  fputs("\n",out);

  return;
}

/*
 * tr_wellsupp -- Detect if a rule provides well support
 */

int tr_wellsupp(int style, FILE *out, int atom, RULE *rule,
		ATAB *table, int scc, int scc_pos_cnt, int *scc_pos,
		int well_support, int index, int body_ext,
		int *contradiction, NODE *graph, int newatom)
{
  int pos_cnt = get_pos_cnt(rule);
  int *pos = get_pos(rule);
  int neg_cnt = get_neg_cnt(rule);
  int *neg = get_neg(rule);
  int i = 0, j = 0;

  if(new_symbols) {
    qdef(well_support, new_symbols);
    qstr("_ws_", new_symbols);
    qidx(index, new_symbols);
    qstr("_", new_symbols);
    qatom(atom, table, new_symbols);
  }

  if(style == STYLE_READABLE)
    fprintf(out, "\n%% Well-support:\n\n");

  switch(rule->type) {
  case TYPE_BASIC:
  case TYPE_CHOICE:

    /* Generate the rules for checking well-support
     *
     * _ws_r :- _eb_r, _acyc_scc_a_b^1, ..., _acyc_scc_a_b^m.
     * _eb_r :- b'_1, ..., b'_k, not c_1, ..., not c_l.
     *
     * and drop the rule for _eb_r if k+l<=1.
     */

    if(style == STYLE_READABLE) {

      fprintf(out, "_ws_%i_", index);
      write_atom_if_possible(style, out, atom, table);
      if(body_ext) {
	fprintf(out, " :- _eb_%i_", index);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, ", ");
      } else if(pos_cnt+neg_cnt>0)
	fprintf(out, " :- ");

    } else {

      fprintf(out, "1 %i", well_support);
      if(body_ext)
	fprintf(out, " %i 0 %i", scc_pos_cnt+1, body_ext);
      else {
	fprintf(out, " %i %i", pos_cnt+neg_cnt, neg_cnt);
	/* Negative body */
	tr_literal_list(style, out, " ", 0, NULL, neg_cnt, neg, NULL, table);
      }
    }

    /* Positive body */

    for(i=0, j=0; i<pos_cnt; i++) {
	int atom2 = pos[i];
	int acyc = acyc_find_edge(graph, atom2);

	if(atom2 == scc_pos[j]) {
	  if(style == STYLE_READABLE)
	    fprintf(out, "_acyc_%i_%i_%i", scc, atom, atom2);
	  else if(style == STYLE_SMODELS)
	    write_atom_if_possible(style, out, acyc, NULL); /* Positive */
	  if(body_ext) {
	    if(style == STYLE_READABLE && j<scc_pos_cnt-1)
	      fputs(", ", out);
	  } else {
	    if(style == STYLE_READABLE && i<pos_cnt-1)
	      fputs(", ", out);
	  }
	  j++;
	} else if(!body_ext) {
	  write_atom_if_possible(style, out, atom2, table);

	  if(style == STYLE_READABLE && i<pos_cnt-1)
	    fputs(", ", out);
	}
    }

    /* Negative body */

    if(!body_ext) {
      if(style == STYLE_READABLE) {
	if(pos_cnt && neg_cnt)
	  fputs(", ", out);
	tr_literal_list(style, out, ", ", 0, NULL, neg_cnt, neg, NULL, table);
      }
    }

    if(style == STYLE_READABLE)
      fputs(".", out);
    fputs("\n", out);
    break;

  case TYPE_WEIGHT:
  case TYPE_CONSTRAINT:
    { int *weight = NULL, bound = 0;

      if(rule->type == TYPE_WEIGHT) {
	weight = rule->data.weight->weight;
	bound = rule->data.weight->bound;
      } else
	bound = rule->data.constraint->bound;

      /* Produce modified constraint/weight rule */

      if(style == STYLE_READABLE) {
	fprintf(out, "_ws_%i_", index);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, " :- %i ", bound);
	if(rule->type == TYPE_WEIGHT)
	  fputs("[", out);
	else
	  fputs("{", out);
      } else {
	if(rule->type == TYPE_WEIGHT) {
	  fprintf(out, "5");
	  write_atom_if_possible(style, out, well_support, NULL);
	  fprintf(out, " %i %i %i", bound, pos_cnt+neg_cnt, neg_cnt);
	} else {
	  fprintf(out, "2");
	  write_atom_if_possible(style, out, well_support, NULL);
	  fprintf(out, " %i %i %i", pos_cnt+neg_cnt, neg_cnt, bound);
	}
	/* Negative body */
	tr_literal_list(style, out, " ", 0, NULL, neg_cnt, neg, NULL, table);
      }

      /* Positive body */
      
      for(i=0, j=0; i<pos_cnt; i++) {
	int atom2 = pos[i];
	int acyc = acyc_find_edge(graph, atom2);

	if(atom2 == scc_pos[j]) {
	  if(style == STYLE_READABLE)
	    fprintf(out, "_acyc_%i_%i_%i", scc, atom, atom2);
	  else if(style == STYLE_SMODELS)
	    write_atom_if_possible(style, out, acyc, NULL); /* Positive */
	  j++;
	} else
	  write_atom_if_possible(style, out, atom2, table);
	if(rule->type == TYPE_WEIGHT && style == STYLE_READABLE)
	  fprintf(out, "=%i", weight[neg_cnt+i]);
	if(style == STYLE_READABLE && i<pos_cnt-1)
	  fputs(", ", out);
      }

      if(style == STYLE_READABLE) {
	if(pos_cnt && neg_cnt)
	  fputs(", ", out);
	/* Negative body */
	tr_literal_list(style, out, ", ", 0, NULL, neg_cnt, neg, weight, table);
	if(rule->type == TYPE_WEIGHT)
	  fprintf(out, "].\n");
	else
	  fprintf(out, "}.\n");
      } else if(style == STYLE_SMODELS) {
	/* Optionally weights */
	if(rule->type == TYPE_WEIGHT)
	  for(i=0; i<neg_cnt+pos_cnt; i++)
	    fprintf(out, " %i", weight[i]);
	fprintf(out, "\n");
      }
    }
    break;
  }

  return newatom;
}

/*
 *  tr_redcheck -- Check the reduncancy of support for cardinality/weight rules
 */

int tr_redcheck(int style, FILE *out, int atom, RULE *rule,
		ATAB *table, int scc, int scc_pos_cnt, int *scc_pos,
		int index, int *contradiction,
                NODE *graph, int newatom)
{
  int pos_cnt = get_pos_cnt(rule);
  int *pos = get_pos(rule);
  int neg_cnt = get_neg_cnt(rule);
  int *neg = get_neg(rule);
  int *scc_chk = (int *)malloc(sizeof(int)*scc_pos_cnt);
  int *scc_nxt = (int *)malloc(sizeof(int)*scc_pos_cnt);
  int i = 0, j = 0;

  /* All new atoms are created locally */

  int redundancy = newatom++;

  if(new_symbols) {
    qdef(redundancy, new_symbols);
    qstr("_red_", new_symbols);
    qidx(index, new_symbols);
    qstr("_", new_symbols);
    qatom(atom, table, new_symbols);
  }

  if(style == STYLE_READABLE)
    fprintf(out, "\n%% Reduncancy for well-support:\n\n");

  switch(rule->type) {
  case TYPE_WEIGHT:
  case TYPE_CONSTRAINT:
    { int *weight = NULL, bound = 0;
      int skip = 0;

      if(scc_pos_cnt>0) skip=1; /* The first condition is to be skipped */

      if(rule->type == TYPE_WEIGHT) {
	weight = rule->data.weight->weight;
	bound = rule->data.weight->bound;
      } else
	bound = rule->data.constraint->bound;

      /* Produce modified constraint/weight rule */
      
      scc_chk[0] = 0;
      scc_nxt[0] = 0;
      for(j=1; j<scc_pos_cnt; j++) {
	  scc_chk[j] = newatom++;
	  scc_nxt[j] = newatom++;
      }

      if(style == STYLE_READABLE) {
	fprintf(out, "_red_%i_", index);
	write_atom_if_possible(style, out, atom, table);
	fprintf(out, " :- %i ", bound);
	if(rule->type == TYPE_WEIGHT)
	  fputs("[", out);
	else
	  fputs("{", out);
      } else {
	if(rule->type == TYPE_WEIGHT) {
	  fprintf(out, "5");
	  write_atom_if_possible(style, out, redundancy, NULL);
	  fprintf(out, " %i %i %i", bound, pos_cnt+neg_cnt-skip, neg_cnt);
	} else {
	  fprintf(out, "2");
	  write_atom_if_possible(style, out, redundancy, NULL);
	  fprintf(out, " %i %i %i", pos_cnt+neg_cnt-skip, neg_cnt, bound);
	}
	/* Negative body */
	tr_literal_list(style, out, " ", 0, NULL, neg_cnt, neg, NULL, table);
      }

      /* Positive body */
      
      for(i=0, j=0; i<pos_cnt; i++) {
	int atom2 = pos[i];
	int acyc = acyc_find_edge(graph, atom2);

	if(atom2 == scc_pos[j]) { /* Produce the _chk_ atom */
	  if(j>0) {
	    if(new_symbols) {
	      qdef(scc_chk[j], new_symbols);
	      qstr("_chk_", new_symbols);
	      qidx(index, new_symbols);
	      qstr("_", new_symbols);
	      qidx(j, new_symbols);
	      qstr("_", new_symbols);
	      qatom(atom, table, new_symbols);

	      qdef(scc_nxt[j], new_symbols);
	      qstr("_nxt_", new_symbols);
	      qidx(index, new_symbols);
	      qstr("_", new_symbols);
	      qidx(j, new_symbols);
	      qstr("_", new_symbols);
	      qatom(atom, table, new_symbols);
	    }
	    if(style == STYLE_READABLE) {
	      fprintf(out, "_chk_%i_%i_", index, j);
	      write_atom_if_possible(style, out, atom, table);
	    } else if(style == STYLE_SMODELS)
	      write_atom_if_possible(style, out,
				     scc_chk[j], NULL); /* Positive */
	    if(rule->type == TYPE_WEIGHT && style == STYLE_READABLE)
	      fprintf(out, "=%i", weight[neg_cnt+i]);
	    if(style == STYLE_READABLE && i<pos_cnt-skip-1)
	      fputs(", ", out);
	  } else skip=0;
	  j++;
	} else { /* Print as is */
	  write_atom_if_possible(style, out, atom2, table);
	  if(rule->type == TYPE_WEIGHT && style == STYLE_READABLE)
	    fprintf(out, "=%i", weight[neg_cnt+i]);
	  if(style == STYLE_READABLE && i<pos_cnt-skip-1)
	    fputs(", ", out);
	}
      }

      if(scc_pos_cnt>0) skip=1;

      if(style == STYLE_READABLE) {
	if(pos_cnt-skip>0 && neg_cnt)
	  fputs(", ", out);
	/* Negative body */
	tr_literal_list(style, out, ", ", 0, NULL, neg_cnt, neg, weight, table);
	if(rule->type == TYPE_WEIGHT)
	  fprintf(out, "].\n");
	else
	  fprintf(out, "}.\n");
      } else if(style == STYLE_SMODELS) {
	/* Optionally weights */
	if(rule->type == TYPE_WEIGHT) {
	  for(i=0; i<neg_cnt; i++)
	    fprintf(out, " %i", weight[i]);
	  for(i=0, j=0; i<pos_cnt; i++) {
	    if(pos[i] == scc_pos[j]) {
	      if(j>0) /* Skip the one weight with j=0 */
		fprintf(out, " %i", weight[neg_cnt+i]);
	      j++;
	    } else
	      fprintf(out, " %i", weight[neg_cnt+i]);
	  }
	}
	fprintf(out, "\n");
      }

      for(i=0, j=0; i<pos_cnt; i++) {
	int atom2 = pos[i];
	int acyc = acyc_find_edge(graph, atom2);

	if(atom2 == scc_pos[j]) {
	  if(j>0) {
	    if(style == STYLE_READABLE) {
	      fprintf(out, "_chk_%i_%i_", index, j);
	      write_atom_if_possible(style, out, atom, table);
	      fputs(" :- ", out);
	      fprintf(out, "_nxt_%i_%i_", index, j);
	      write_atom_if_possible(style, out, atom, table);
	      fputs(", ", out);
	      fprintf(out, "_acyc_%i_%i_%i", scc, atom, atom2);
	      fputs(".\n", out);

	      if(j-1>0) {
		fprintf(out, "_nxt_%i_%i_", index, j);
		write_atom_if_possible(style, out, atom, table);
		fputs(" :- ", out);
		fprintf(out, "_nxt_%i_%i_", index, j-1);
		write_atom_if_possible(style, out, atom, table);
		fputs(".\n", out);
	      }

	      fprintf(out, "_nxt_%i_%i_", index, j);
	      write_atom_if_possible(style, out, atom, table);
	      fputs(" :- ", out);
	      fprintf(out, "_acyc_%i_%i_%i", scc, atom, scc_pos[j-1]);
	      fputs(".\n", out);

	    } else if(style == STYLE_SMODELS) {
	      int prevacyc = acyc_find_edge(graph, scc_pos[j-1]);

	      fprintf(out, "1 %i 2 0 %i", scc_chk[j], scc_nxt[j]);
	      write_atom_if_possible(style, out, acyc, NULL);
	      fputs("\n", out);

	      if(j-1>0)
		fprintf(out, "1 %i 1 0 %i\n", scc_nxt[j], scc_nxt[j-1]);

	      fprintf(out, "1 %i 1 0", scc_nxt[j]);
	      write_atom_if_possible(style, out, prevacyc, NULL);
	      fputs("\n", out);
	    }
	  }

	  if(style == STYLE_READABLE) {

	    fprintf(out, "%s%i :- ", prefix, *contradiction);
	    fprintf(out, "_acyc_%i_%i_%i", scc, atom, atom2);
	    fputs(", ", out);
	    fprintf(out, "_red_%i_", index);
	    write_atom_if_possible(style, out, atom, table);
	    fputs(".\n", out);

	  } else if(style == STYLE_SMODELS) {

	    fprintf(out, "1 %i 2 0", *contradiction);
	    write_atom_if_possible(style, out, acyc, NULL);
	    write_atom_if_possible(style, out, redundancy, NULL);
	    fputs("\n", out);
	    
	  }
	  j++;
	}
      }
    }
    break;
  }

  free(scc_chk);
  free(scc_nxt);
  return newatom;
}

/*
 * tr_must_support -- Ensure that true atoms are receiving well-support
 */

void tr_must_support(int style, FILE *out, int atom, ATAB *table,
		     int supp_cnt, int *supp, int contradiction)
{
  int i = 0;

  /* Generate constraint: ":- a, not _ws_*." */

  if(style == STYLE_READABLE) {

    fprintf(out, "%% Enforce either external or internal support for ");
    write_atom_if_possible(style, out, atom, table);
    fputs(":\n\n", out);

    fprintf(out, "%s%i :- ", prefix, contradiction);
    write_atom_if_possible(style, out, atom, table);
    for(i=0; i < supp_cnt; i++) {
      fputs(", not ", out);
      fprintf(out, "_ws_%i_", i+1);
      write_atom_if_possible(style, out, atom, table);
    }
    fprintf(out, ".\n\n");

  } else if(style == STYLE_SMODELS) {
	
    fprintf(out, "1 %i %i %i",
	    contradiction, supp_cnt+1, supp_cnt);
    for(i=0; i < supp_cnt; i++)
      write_atom_if_possible(style, out, supp[i], NULL);
    write_atom_if_possible(style, out, atom, table); /* Positive */
    fputs("\n", out);
  }

  return;
}

void tr_false_atom(int style, FILE *out, int contradiction,
		   int scc, int atom1, int atom2, int atom3, ATAB *table)
{
  /* Create constraints ":- _acyc_scc_a_*, not a." */

  switch(style) {
  case STYLE_READABLE:
    fprintf(out, "%s%i :- _acyc_%i_%i_%i, not ",
	    prefix, contradiction, scc, atom1, atom2);
    write_atom_if_possible(style, out, atom1, table);	
    fputs(".\n", out);
    break;
  case STYLE_SMODELS:
    fprintf(out, "1 %i 2 1", contradiction);
    write_atom_if_possible(style, out, atom1, table); /* Negative */
    write_atom_if_possible(style, out, atom3, NULL);  /* Positive */
    fputs("\n", out);
    break;
  }


  return;
}

void tr_support(int style, FILE *out, int contradiction, int scc,
		int atom1, int atom2, int atom3, int index,
		int atom4, ATAB *table)
{
  /* Create constraints ":- _acyc_scc_a_b, ws(r)."  */

  switch(style) {
  case STYLE_READABLE:
    fprintf(out, "%s%i :- _acyc_%i_%i_%i, _ws_%i_",
	    prefix, contradiction, scc, atom1, atom2, index);
    write_atom_if_possible(style, out, atom1, table);	
    fputs(".\n", out);
    break;
  case STYLE_SMODELS:
    fprintf(out, "1 %i 2 0", contradiction);
    write_atom_if_possible(style, out, atom4, NULL);
    write_atom_if_possible(style, out, atom3, NULL);
    fputs("\n", out);
    break;
  }

  return;
}

/*
 * tr_atoms --- Translate the program atom by atom
 */

void tr_atoms(int style, FILE *out, ATAB *table, OCCTAB *occtable,
	      int weak, int *contradiction, int newatom)
{
  ATAB *scan = table;

  /* Process all atoms one by one */

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = definition(occtable, atom);
      int scc = d->scc;
      int scc_size = d->scc_size;
      RULE *r = NULL;
      int j = 0;

      if(scc_size < 2) {

	/* Go through the rules that have the atom as head */

	if(style == STYLE_READABLE && d->rule_cnt) {
	  fputs("% Nontrivial rules having ", out);
	  write_atom_if_possible(style, out, atom, table);
	  fputs(" as head:\n\n", out);
	}

	for(j=0; j < d->rule_cnt; j++) {
	  r = d->rules[j]; /* These rules remain untouched */

	  write_rule(style, out, r, table);
	}

	if(style == STYLE_READABLE && d->rule_cnt)
	  fputs("\n", out);

      } else { /* The atom is involved in a larger SCC */
	int *support = NULL;
	int *redundancy = NULL;
	int *extbody = NULL;
	int extbody_cnt = 0;
	int hasext = 0;
	NODE *newnode = new_node(atom, 0, 0, NULL);
	EDGE *e = NULL;

	if(*contradiction == 0)  /* This is created only if needed */
	  *contradiction = newatom++;

	if(!graph)
	  graph = new_graph(scc, NULL);

	/* Reserve space for new atoms related with supporting rules */

	support = (int *)malloc(sizeof(int)*(d->rule_cnt));
	extbody = (int *)malloc(sizeof(int)*(d->rule_cnt));

	/* Go through rules that have the atom as head */

	for(j=0; j < d->rule_cnt; j++) {
	  r = d->rules[j];
	  int bound = 0;
	  int wsum = 0;

	  int pos_cnt = get_pos_cnt(r);
	  int neg_cnt = get_neg_cnt(r);
	  int *pos = get_pos(r);
	  int scc_pos_cnt = 0;
	  int *scc_pos = (int *)malloc(sizeof(int)*pos_cnt);
	  int k = 0, l = 0;

	  if(style == STYLE_READABLE) {
	    fprintf(out, "%% Translation of rule #%i having the atom ",
		    j+1);
	    write_atom_if_possible(style, out, atom, table);
	    fputs(" as head:\n\n", out);
	  }

	  /* Count and record positive body literals within the same SCC */

	  for(k=0, l=0 ; k<pos_cnt; k++) {
	    int atom2 = pos[k];
	    DEF *d2 = definition(occtable, atom2);

	    if(d2->scc == scc) {
	      scc_pos_cnt++;

	      newatom = acyc_create_edge(newnode, atom2, newatom);

	      scc_pos[l] = atom2;
	      l++;
	    } else if(r->type == TYPE_WEIGHT)
	      wsum += (r->data.weight->weight)[neg_cnt+k];
	  }

	  if(scc_pos_cnt == 0 ||
	     r->type == TYPE_CONSTRAINT ||
	     r->type == TYPE_WEIGHT ||
	     (pos_cnt+neg_cnt-scc_pos_cnt <= 1)) { /* Keep the rule as is */

	    extbody[j] = 0;
	    write_rule(style, out, r, table);
	    hasext = -1;

	  } else { /* Rename the head of the rule and translate the rule */

	    extbody[j] = newatom++;
	    if(new_symbols) {
	      qdef(extbody[j], new_symbols);
	      qstr("_eb_", new_symbols);
	      qidx(j+1, new_symbols);
	      qstr("_", new_symbols);
	      qatom(atom, table, new_symbols);
	    }
	    compress_rule(style, out, atom, scc_pos_cnt, scc_pos,
			  extbody[j], j+1, r, table);
	  }

	  if(r->type == TYPE_CONSTRAINT)
	    bound = r->data.constraint->bound;
	  else if(r->type == TYPE_WEIGHT) {
	    bound = r->data.weight->bound;

	    for(k=0; k<neg_cnt; k++)
	      wsum += (r->data.weight->weight)[k];
	  }

	  /* Generate rules for support */

	  support[j] = newatom++;

	  newatom = tr_wellsupp(style, out, atom, r, table,
				scc, scc_pos_cnt, scc_pos,
				support[j], j+1, extbody[j],
				contradiction, newnode, newatom);

	  if(!weak &&
	     (r->type == TYPE_CONSTRAINT || r->type == TYPE_WEIGHT)) {
	    /* Check that the selected support is minimal */

	    newatom = tr_redcheck(style, out, atom, r, table,
				  scc, scc_pos_cnt, scc_pos,
				  j+1, contradiction,
                                  newnode, newatom);
	  }


	  if(style == STYLE_READABLE)
	    fputs("\n", out);

	  free(scc_pos);
	}

	/* Acyc constraints */

	if(!weak && style == STYLE_READABLE) {
	  fprintf(out, "%% Acyc constraints related with atom ");
	  write_atom_if_possible(style, out, atom, table);
	  fputs(":\n\n", out);
	}

	/* Create acyc constraints related with the atom itself */

	if(!weak) {
	  e = newnode->edges;
	  while(e) {
	    tr_false_atom(style, out, *contradiction,
			  scc, atom, e->node, e->atom, table);
	    e = e->next;
	  }
	}

	/* Create acyc constraints related with support */

	if(!weak)
	  for(j=0; j < d->rule_cnt; j++) {
	    r = d->rules[j];

	    int pos_cnt = get_pos_cnt(r);
	    int *pos = get_pos(r);

	    e = newnode->edges;

	    while(e) {
	      int skip = 0;
	      int l = 0;

	      for(l=0; l<pos_cnt; l++)
		if(pos[l] == e->node) {
		  skip = -1;
		  l = pos_cnt;
		}

	      if(skip)
		skip = 0;
	      else
		/* TODO: Make more aggresive for cardinality/weight rules */
		tr_support(style, out, *contradiction, scc,
			   atom, e->node, support[j], j+1,
			   e->atom, table);

	      e = e->next;
	    }
	  }

	if(!weak & style == STYLE_READABLE)
	  fputs("\n", out);

	/* Locate the right component in the graph and add the node */

	GRAPH *pg = NULL, *sg = graph;

	while(sg && (sg->id != scc)) {
	  pg = sg;
	  sg = sg->next;
	}

	if(sg) {
	  NODE *sn = sg->nodes;

	  if(sn) {
	    while(sn->next) sn = sn->next;
	    sn->next = newnode;
	  } else
	    sg->nodes = newnode;
	} else
	  pg->next = new_graph(scc, newnode);

	newnode = NULL;

	/* Enforce either external or internal support */

	tr_must_support(style, out, atom, table,
			d->rule_cnt, support, *contradiction);

	free(support);
	free(extbody);
      }
    }
    scan = scan->next;
  }
  return;
}
