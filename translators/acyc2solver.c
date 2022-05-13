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
 * ACYC2SOLVER -- Transform LP + ACYC into back-end format(s)
 *
 * (c) 2014-2015 Tomi Janhunen
 *
 * Main program and routines for atom/rule level translation
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

void _version_acyc2solver_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: acyc2solver.c,v $",
           "$Date: 2021/05/27 11:37:57 $",
           "$Revision: 1.17 $");
  _version_atom_c();
  _version_rule_c();
  _version_input_c();
  _version_scc_c();
  _version_acyc_c();
}

void usage()
{
  fprintf(stderr, "\nusage:");
  fprintf(stderr, "   acyc2solver <options> <file>\n\n");
  fprintf(stderr, "options:\n");
  fprintf(stderr, "   -h or --help -- print help message\n");
  fprintf(stderr, "   --version -- print version information\n");
  fprintf(stderr, "   -v -- verbose mode (human readable)\n");
  fprintf(stderr, "   -d -- drop optimization statements\n");
  fprintf(stderr, "   -g -- add the graph (for --pb)\n");
  fprintf(stderr, "   --bv   -- bit-vector logic\n");
  fprintf(stderr, "   --diff -- difference logic (default)\n");
  fprintf(stderr, "   --mip  -- mixed integer program\n");
  fprintf(stderr, "   --pb   -- pseudo-Boolean theory\n");

  fprintf(stderr, "\n");

  return;
}

char *zero = "zero";        /* The reference variable for "0" */
char *cost = "cost";        /* The variable for objective function */
int newatom = 0;
int newcounter = 0;
int constraint_cnt = 0;

void tr_atoms(int style, FILE *out, ATAB *table, OCCTAB *occtable);
RULE *merge_optimize_statements(RULE *statements);
void tr_optimize_statement(int style, FILE *out, RULE *statement, ATAB *table);
void tr_compute_statement(int style, FILE *out, ATAB *table);
void tr_acyc_interface(int style, FILE *out, GRAPH *graphs);
void assign_acyc_atoms(GRAPH *graphs);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL, *statements = NULL, *merged = NULL;
  RULE *scan = NULL, *prev = NULL;

  ATAB *table = NULL;
  OCCTAB *occtable = NULL;
  GRAPH *graphs = NULL;
  int number = 0;
  int size = 0;
  int style = 0, symstyle = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0;
  int option_dropt = 0;
  int option_graph = 0;
  int option_bv = 0;
  int option_diff = 0;
  int option_mip = 0;
  int option_pb = 0;

  char *arg = NULL;
  int which = 0;
  int error = 0;
  int contradiction = 0;

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
    else if(strcmp(arg, "--bv") == 0)
      option_bv = -1;
    else if(strcmp(arg, "--diff") == 0)
      option_diff = -1;
    else if(strcmp(arg, "--mip") == 0)
      option_mip = -1;
    else if(strcmp(arg, "--pb") == 0)
      option_pb = -1;
    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }
  }

  if(option_help) usage();
  if(option_version) _version_acyc2solver_c();

  if(option_help || option_version)
    exit(0);

  if(option_bv && option_diff) {
    fprintf(stderr, "%s: options --bv and --diff are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_bv && option_mip) {
    fprintf(stderr, "%s: options --bv and --mip are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_bv && option_pb) {
    fprintf(stderr, "%s: options --bv and --pb are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_diff && option_mip) {
    fprintf(stderr, "%s: options --diff and --mip are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_diff && option_pb) {
    fprintf(stderr, "%s: options --diff and --pb are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_mip && option_pb) {
    fprintf(stderr, "%s: options --mip and --pb are incompatible!\n",
	    program_name);
    error = -1;
  }

  if(option_graph && !option_pb) {
    fprintf(stderr, "%s: option -g presumes --pb!\n",
	    program_name);
    error = -1;
  }

  if(error) {
    usage();
    exit(-1);
  }

  if(!option_bv && !option_diff && !option_mip && !option_pb)
    option_diff = -1; /* Default output format */

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
  if(size == 0) {
    if(option_verbose)
      fprintf(out, "%% %s contains no atoms, hence no output!\n", file);
    else {
      if(option_bv) {
        fprintf(out, "(set-logic QF_BV)\n");
        fprintf(out, "(assert true)\n");
        fprintf(out, "(check-sat)\n");
        fprintf(out, "(exit)\n");
      }
      if(option_diff) {
        fprintf(out, "(set-logic QF_IDL)\n");
        fprintf(out, "(assert true)\n");
        fprintf(out, "(check-sat)\n");
        fprintf(out, "(exit)\n");
      }
      if(option_mip) {
	fprintf(out,
		"MINIMIZE\n\nSUBJECT TO\n  var_0 = 0\nINTEGER\n  var_0\nEND\n");
      }
      if(option_pb)
	fprintf(out, "1 >= 0;\n");
    }
    exit(0);
  }

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

  /* Extract acyc information if present */

  graphs = extract_acyc_graphs(table);
  if(graphs)
    (void) count_nodes(graphs);

  /* Check head occurrences */

  occtable = initialize_occurrences(table, 0, 0);
  compute_occurrences(program, occtable, 0, 0);

  /* Initialize numbering schemes for new atoms and variables */

  newatom = 1;     /* For body atoms */
  newcounter = 1;  /* For translating bodies of cardinality/weight rules */

  /* Produce the desired output */

  if(option_verbose) { /* Use symbolic (human readable) format */

    fprintf(out, "%% Translation of program %s and its %i atoms:\n\n",
            file, size);

    fprintf(out, "%% List of atoms:\n\n");

    write_symbols(STYLE_READABLE, out, table);

    if(graphs)
      tr_acyc_interface(STYLE_READABLE, out, graphs);

    tr_atoms(STYLE_READABLE, out, table, occtable);

    fprintf(out, "\n%% Translation of the compute statement:\n\n");

    tr_compute_statement(STYLE_READABLE, out, table);

  } else { /* !option_verbose: produce suitable back-end format */

    if(option_bv || option_diff) {
      if(option_bv) {
	fprintf(out, "(set-logic QF_BV)\n");
	style = STYLE_BV;
	symstyle = STYLE_BSYM;
      } else {
	fprintf(out, "(set-logic QF_IDL)\n");
	style = STYLE_DIFF;
	symstyle = STYLE_DSYM;
      }
      fprintf(out, "(set-info :smt-lib-version 2.0)\n");
      tr_atoms(symstyle, out, table, occtable);
      if(graphs)
	tr_acyc_interface(symstyle, out, graphs);
      if(merged)
	tr_optimize_statement(symstyle, out, merged, table);
      newatom = 1;
      newcounter = 1;
    } else if(option_mip) {
      style = STYLE_LP;
      fputs("MINIMIZE\n", out);
      if(merged)
	tr_optimize_statement(style, out, merged, table);
      else
	fputs("\n", out);
      fputs("SUBJECT TO\n", out);
    } else if(option_pb) {
      int acnt = 0;
      newatom = size+1;

      acnt = newatom;
      tr_atoms(STYLE_PCNT, out, table, occtable);
      tr_compute_statement(STYLE_PCNT, out, table);
      if(graphs) {
	GRAPH *sg = graphs;

	while(sg) {
	  assign_acyc_atoms(sg);
	  if(!option_graph)
	    constraint_cnt += sg->edge_cnt;

	  sg = sg->next;
	}
      }
      acnt = newatom-acnt;

      newatom = size+1;

      fprintf(out, "* #variable= %i #constraint= %i\n",
	      size+acnt, constraint_cnt);
      fprintf(out, "* Generated by acyc2solver --pb%s\n",
	      option_graph ? " -g": "");
      style = STYLE_PB;
      if(graphs && option_graph)
	tr_acyc_into_graph(style, out, graphs);
      if(merged) {
	fputs("min: ", out);
	tr_optimize_statement(style, out, merged, table);
      }
    }

    tr_atoms(style, out, table, occtable);
    tr_compute_statement(style, out, table);
    if(graphs &&
       !(option_pb && option_graph /* Graph is forwarded otherwise */))
      tr_acyc_interface(style, out, graphs);

    if(option_mip) {
      newatom = 1; /* Reinitialize */
      fputs("BINARY\n", out);
      tr_atoms(STYLE_BIN, out, table, occtable);
      fputs("GENERAL\n", out);
      tr_atoms(STYLE_GEN, out, table, occtable);
      if(graphs)
	tr_acyc_interface(STYLE_GEN, out, graphs);
      fputs("END\n", out);
    }

    if(option_bv || option_diff) {
      if(merged)
	tr_optimize_statement(style, out, merged, table);
      fprintf(out, "(check-sat)\n");
      fprintf(out, "(get-model)\n");
      fprintf(out, "(exit)\n");
    }
  }

  exit(0);
}

/* ------------------------- Auxiliary routines ---------------------------- */

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

/* ========================= Translate basic rules ========================= */

void tr_basic(int style, FILE *out,
	      int head,  /* Original head atom (if used) */
	      int body,  /* New body atom (otherwise) */
	      int status, BASIC_RULE *basic, ATAB *table)
{
  int pos_cnt = basic->pos_cnt;
  int *pos = basic->pos;
  int neg_cnt = basic->neg_cnt;
  int *neg = basic->neg;
  int i = 0, previous = 0;
  int shift = table->shift;

  switch(style) {
  case STYLE_READABLE:

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head) {
	write_atom(style, out, head, table);
      } else
	fprintf(out, "body_%i", body);
      fputs(" ", out);

      fputs("<-> ", out);
    } else if(status & MARK_FALSE)
      fputs("~(", out);

    if(pos_cnt+neg_cnt == 0)
      fputs("T", out);

    for(i=0; i<pos_cnt;) {
      int atom = pos[i];

      write_atom(style, out, atom, table);
      i++;
      if(i<pos_cnt)
	fputs(" & ", out);
    }

    if(pos_cnt>0 && neg_cnt>0) {
      fputs(" &", out);
      fputs(" ", out);
    }

    for(i=0; i<neg_cnt;) {
      int atom = neg[i];

      fputs("~", out);
      write_atom(style, out, atom, table);
      i++;
      if(i<neg_cnt) {
	fputs(" &", out);
	fputs(" ", out);
      }
    }

    if(status & MARK_FALSE)
      fputs(")", out);

    fputs(".\n", out);
    break;

  case STYLE_BV:
  case STYLE_DIFF:

    fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      fputs("(= ", out);
      if(head) {
	fprintf(out, "var_%i", head+shift);
      } else
	fprintf(out, "body_%i", body);
      fputs(" ", out);
    } else if(status & MARK_FALSE)
      fputs("(not ", out);

    if(pos_cnt+neg_cnt>1)
      fputs("(and ", out);
    else if(pos_cnt+neg_cnt == 0)
      fputs("true", out);

    for(i=0; i<pos_cnt;) {
      int atom = pos[i];

      fprintf(out, "var_%i", atom+shift);
      i++;
      if(i<pos_cnt)
	fputs(" ", out);
    }

    if(pos_cnt>0 && neg_cnt>0)
      fputs(" ", out);

    for(i=0; i<neg_cnt;) {
      int atom = neg[i];

      fputs("(not ", out);
      fprintf(out, "var_%i", atom+shift);
      fputs(")", out);
      i++;
      if(i<neg_cnt)
	fputs(" ", out);
    }

    if(pos_cnt+neg_cnt>1)
      fputs(")", out);
    if(status & MARK_FALSE)
      fputs(")", out);
    if(!(status & MARK_TRUE_OR_FALSE))
      fputs(")", out);
    fputs(")\n", out);
    break;

  case STYLE_PCNT:
    /* This must be in synchrony with STYLE_PB below */

    if(!(status & MARK_FALSE) && pos_cnt+neg_cnt>0) constraint_cnt++;
    constraint_cnt++;
    break;

  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x"; /* PB Competitions insist on this */

      /* For the equivalence "bd_r <-> B & -C" generate:
       *
       * sum_i b_i - sum_j c_j - |B union C| bd_r >= - |C|
       *
       * This becomes void if bd_r = 0.
       */

      if(!(status & MARK_FALSE) && pos_cnt+neg_cnt>0) {
	if(style == STYLE_LP)
	  fputs("  ", out);
	else if(pos_cnt>0)
	  fputs("1 ", out);

	for(i=0; i<pos_cnt;) {
	  int atom = pos[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<pos_cnt) {
	    if(style == STYLE_LP)
	      fputs("+ ", out);
	    else
	      fputs("+1 ", out);
	  }
	}

	if(neg_cnt>0) {
	  if(style == STYLE_LP)
	    fputs("- ", out);
	  else
	    fputs("-1 ", out);
	}

	for(i=0; i<neg_cnt;) {
	  int atom = neg[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<neg_cnt) {
	    if(style == STYLE_LP)
	      fputs("- ", out);
	    else
	      fputs("-1 ", out);
	  }
	}

	if(head) {
	  if((status & MARK_TRUE) && pos_cnt+neg_cnt>0)
	    fprintf(out, " >= %i", pos_cnt);
	  else
	    fprintf(out,
		    style == STYLE_LP ?
                    "- %i %s%i >= %i": "-%i %s%i >= %i",
		    pos_cnt+neg_cnt, varpref, head+shift, -neg_cnt);
	} else {
	  if((status & MARK_TRUE) && pos_cnt+neg_cnt>0)
	    fprintf(out, " >= %i", pos_cnt);
	  else
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i body_%i >= %i" : "-%i x%i >= %i",
		    pos_cnt+neg_cnt, body, -neg_cnt);
	}
	if(style == STYLE_PB)
	  fputs(" ;", out);
	fputs("\n", out);
      }

      /* For the equvalence "bd_r <-> B & -C" generate:
       *
       * sum_i b_i - sum_j c_j - bd_r <= |B|-1 */

      if(style == STYLE_LP)
	fputs("  ", out);
      else if(pos_cnt>0)
	fputs("-1 ", out); /* Equation multiplied by -1 */

      for(i=0; i<pos_cnt;) {
	int atom = pos[i];

	fprintf(out, "%s%i ", varpref, atom+shift);
	i++;
	if(i<pos_cnt) {
	  if(style == STYLE_LP)
	    fputs("+ ", out);
	  else
	    fputs("-1 ", out);
	}
      }

      if(neg_cnt>0) {
	if(style == STYLE_LP)
	  fputs("- ", out);
	else
	  fputs("+1 ", out);
      }

      for(i=0; i<neg_cnt;) {
	int atom = neg[i];

	fprintf(out, "%s%i ", varpref, atom+shift);
	i++;
	if(i<neg_cnt) {
	  if(style == STYLE_LP)
	    fputs("- ", out);
	  else
	    fputs("+1 ", out);
	}
      }

      if((status & MARK_FALSE) && pos_cnt+neg_cnt>0) {
	if(style == STYLE_LP)
	  fprintf(out, "<= %i", pos_cnt-1);
	else
	  fprintf(out, ">= %i", 1-pos_cnt);
      } else if((status & MARK_TRUE) && pos_cnt+neg_cnt>0) {
	if(style == STYLE_LP)
	  fprintf(out, "<= %i", pos_cnt);
	else
	  fprintf(out, ">= %i", -pos_cnt);
      } else {
	if(head)
	  fprintf(out,
		  style == STYLE_LP ?
		  "- %s%i <= %i": "+1 %s%i >= %i",
		  varpref, head+shift,
		  style == STYLE_LP ? pos_cnt-1 : 1-pos_cnt);
	else
	  fprintf(out,
		  style == STYLE_LP ?
		  "- body_%i <= %i" : "+1 x%i >= %i",
		  body, style == STYLE_LP ? pos_cnt-1 : 1-pos_cnt);
      }
      if(style == STYLE_PB)
	fputs(" ;", out);
      fputs("\n", out);
    }
    break;
  }

  return;
}

/* ====================== Translate constraint rules ====================== */

void tr_constraint(int style, FILE *out,
                   int head,  /* Original head atom (if used) */
                   int body,  /* New body atom (otherwise) */
		   int status, CONSTRAINT_RULE *constraint, ATAB *table)
{
  int pos_cnt = constraint->pos_cnt;
  int *pos = constraint->pos;
  int neg_cnt = constraint->neg_cnt;
  int *neg = constraint->neg;
  int bound = constraint->bound;
  int i = 0, previous = 0;
  int shift = table->shift;
  int bits = 0;

  switch(style) {
  case STYLE_READABLE:

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	write_atom(style, out, head, table);
      else
	fprintf(out, "body_%i", body);
      fputs(" <-> ", out);
    } else if(status & MARK_FALSE)
      fputs("~ ", out);

    if(pos_cnt+neg_cnt == 0)
      fputs("T", out);
    else {
      fprintf(out, "%i { ", bound);

      for(i=0; i<pos_cnt;) {
        int atom = pos[i];

        write_atom(style, out, atom, table);
        i++;
        if(i<pos_cnt)
          fputs(", ", out);
      }

      if(pos_cnt>0 && neg_cnt>0)
        fputs(", ", out);

      for(i=0; i<neg_cnt;) {
        int atom = neg[i];

        fputs("~", out);
        write_atom(style, out, atom, table);

        i++;
        if(i<neg_cnt)
          fputs(" , ", out);
      }
      fputs(" }", out);
    }
    fputs(".\n", out);
    break;

  case STYLE_BV:

    bits = base2log(pos_cnt+neg_cnt+1);
    previous = 0;

    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i (bvadd w_%i (_ bv1 %i)))",
		newcounter, previous, bits);
      else
	fprintf(out, "(= w_%i (_ bv1 %i))",
		newcounter, bits);
      fputs("))\n", out);

      fprintf(out, "(assert (=> (not var_%i) ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i (_ bv0 %i))", newcounter, bits);
      fputs("))\n", out);

      previous = newcounter++;
    }
    
    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i (bvadd w_%i (_ bv1 %i)))",
		newcounter, previous, bits);
      else
	fprintf(out, "(= w_%i (_ bv1 %i))", newcounter, bits);
      fputs("))\n", out);

      fprintf(out, "(assert (=> var_%i ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i (_ bv0 %i))", newcounter, bits);
      fputs("))\n", out);

      previous = newcounter++;
    }

    /* Generate the definition for the head/body atom */

    fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	fprintf(out, "(= var_%i ", head+shift);
      else
	fprintf(out, "(= body_%i ", body);
    } else if(status & MARK_FALSE)
      fputs("(not ", out);

    if(previous) /* Check the bound */
      fprintf(out, "(bvult (_ bv%i %i) w_%i)", bound-1, bits, previous);
    else { /* The body is empty */
      if(0 >= bound)
        fputs("true", out);
      else
        fputs("false", out);
    }
    if(!(status & MARK_TRUE_OR_FALSE) || (status & MARK_FALSE))
      fputs(")", out);
    fputs(")\n", out);
    break;

  case STYLE_DIFF:

    previous = 0;
    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= (- w_%i w_%i) 1)", newcounter, previous);
      else
	fprintf(out, "(= (- w_%i %s) 1)", newcounter, zero);
      fputs("))\n", out);

      fprintf(out, "(assert (=> (not var_%i) ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i %s)", newcounter, zero);
      fputs("))\n", out);

      previous = newcounter++;
    }

    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= (- w_%i w_%i) 1)", newcounter, previous);
      else
	fprintf(out, "(= (- w_%i %s) 1)", newcounter, zero);
      fputs("))\n", out);

      fprintf(out, "(assert (=> var_%i ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i %s)", newcounter, zero);
      fputs("))\n", out);

      previous = newcounter++;
    }

    /* Generate the definition for the head/body atom */

    fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	fprintf(out, "(= var_%i ", head+shift);
      else
	fprintf(out, "(= body_%i ", body);
    } else if(status & MARK_FALSE)
      fputs("(not ", out);

    if(previous) /* Check the bound */
      fprintf(out, "(>= (- w_%i %s) %i)", previous, zero, bound);
    else { /* The body is empty */
      if(0 >= bound)
        fputs("true", out);
      else
        fputs("false", out);
    }
    if(!(status & MARK_TRUE_OR_FALSE) || (status & MARK_FALSE))
      fputs(")", out);
    fputs(")\n", out);
    break;

  case STYLE_PCNT:
    /* Must be kept in synchrony with STYLE_PB below */

    constraint_cnt++;
    if(!(status & MARK_TRUE)) constraint_cnt++;
    break;

  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x";

      /* For the equivalence "bd_r <-> bound { B, -C }" generate:
       *
       * sum_i b_i - sum_j c_j - bound x bd_r >= - |C|
       *
       * Becomes void if bd_r = 0.
       */
      
      if(style == STYLE_LP)
	fputs("  ", out);
      else if(pos_cnt>0)
	fputs("1 ", out);

      for(i=0; i<pos_cnt;) {
	int atom = pos[i];

	fprintf(out, "%s%i ", varpref, atom+shift);
	i++;
	if(i<pos_cnt) {
	  if(style == STYLE_LP)
	    fputs("+ ", out);
	  else
	    fputs("+1 ", out);
	}
      }

      if(neg_cnt>0) {
	if(style == STYLE_LP)
	  fputs("- ", out);
	else
	  fputs("-1 ", out);
      }

      for(i=0; i<neg_cnt;) {
	int atom = neg[i];

	fprintf(out, "%s%i ", varpref, atom+shift);
	i++;
	if(i<neg_cnt) {
	  if(style == STYLE_LP)
	    fputs("- ", out);
	  else
	    fputs("-1 ", out);
	}
      }

      if((status & MARK_FALSE) && pos_cnt+neg_cnt>0)
	fprintf(out, " >= %i", -neg_cnt);
      else if((status & MARK_TRUE) && pos_cnt+neg_cnt>0)
	fprintf(out, " >= %i", bound-neg_cnt);
      else {
	if(head)
	  fprintf(out,
		  style == STYLE_LP ?
		  "- %i %s%i >= %i" : "-%i %s%i >= %i",
		  bound, varpref, head+shift, -neg_cnt);
	else
	  fprintf(out,
		  style == STYLE_LP ?
		  "- %i body_%i >= %i" : "-%i x%i >= %i",
		  bound, body, -neg_cnt);
      }
      if(style == STYLE_PB)
	fputs(" ;", out);
      fputs("\n", out);

      /* For the equvalence "bd_r <-> bound { B, -C }" generate:
       *
       * sum_i b_i - sum_j c_j - (|B|+|C|+1-bound) bd_r <= bound-|C|-1
       *
       * Becomes void if bd_r = 1.
       */

      if(!(status & MARK_TRUE)) {
	if(style == STYLE_LP)
	  fputs("  ", out);
	else if(pos_cnt>0)
	  fputs("-1 ", out); /* Equation multiplied by -1 */

	for(i=0; i<pos_cnt;) {
	  int atom = pos[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<pos_cnt) {
	    if(style == STYLE_LP)
	      fputs("+ ", out);
	    else
	      fputs("-1 ", out);
	  }
	}

	if(neg_cnt>0) {
	  if(style == STYLE_LP)
	    fputs("- ", out);
	  else
	    fputs("+1 ", out);
	}

	for(i=0; i<neg_cnt;) {
	  int atom = neg[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<neg_cnt) {
	    if(style == STYLE_LP)
	      fputs("- ", out);
	    else
	      fputs("+1 ", out);
	  }
	}

	if((status & MARK_FALSE) && pos_cnt+neg_cnt>0) {
	  if(style == STYLE_LP)
	    fprintf(out, " <= %i", bound-neg_cnt-1);
	  else
	    fprintf(out, " >= %i", 1-bound+neg_cnt);
	} else {
	  if(head)
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i %s%i <= %i" : "%+i %s%i >= %i",
		    pos_cnt+neg_cnt+1-bound, varpref, head+shift,
		    style == STYLE_LP ? bound-neg_cnt-1 : 1-bound+neg_cnt);
	  else
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i body_%i <= %i" : "%+i x%i >= %i",
		    pos_cnt+neg_cnt+1-bound, body,
		    style == STYLE_LP ? bound-neg_cnt-1 : 1-bound+neg_cnt);
	}
	if(style == STYLE_PB)
	  fputs(" ;", out);
	fputs("\n", out);
      }
    }
    break;
  }

  return;
}

/* ======================== Translate choice rules ======================== */

void tr_choice(int style, FILE *out,
	       int head,  /* Original head atom (if used) */
	       int body,  /* New body atom (otherwise) */
	       int status, CHOICE_RULE *choice, ATAB *table)
{
  int pos_cnt = choice->pos_cnt;
  int *pos = choice->pos;
  int neg_cnt = choice->neg_cnt;
  int *neg = choice->neg;
  int i = 0, previous = 0;
  int shift = table->shift;

  switch(style) {
  case STYLE_READABLE:

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	write_atom(style, out, head, table);
      else
	fprintf(out, "body_%i", body);

      fputs(" -> ", out);
    }

    if(!(status & MARK_FALSE)) {
      if(pos_cnt+neg_cnt == 0)
	fputs("T", out);

      for(i=0; i<pos_cnt;) {
	int atom = pos[i];

	write_atom(style, out, atom, table);
	i++;
	if(i<pos_cnt)
	  fputs(" & ", out);
      }

      if(pos_cnt>0 && neg_cnt>0)
	fputs(" & ", out);

      for(i=0; i<neg_cnt;) {
	int atom = neg[i];

	fputs("~", out);
	write_atom(style, out, atom, table);
	i++;
	if(i<neg_cnt)
	  fputs(" & ", out);
      }
      fputs(".\n", out);
    }
    break;

  case STYLE_BV:
  case STYLE_DIFF:

    if(!(status & MARK_FALSE))
      fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      fputs("(=> ", out);
      if(head)
	fprintf(out, "var_%i", head+shift);
      else
	fprintf(out, "body_%i", body);
      fputs(" ", out);
    }

    if(!(status & MARK_FALSE)) {
      if(pos_cnt+neg_cnt>1)
	fputs("(and ", out);
      else if(pos_cnt+neg_cnt == 0)
	fputs("true", out);

      for(i=0; i<pos_cnt;) {
	int atom = pos[i];

	fprintf(out, "var_%i", atom+shift);
	i++;
	if(i<pos_cnt)
	  fputs(" ", out);
      }

      if(pos_cnt>0 && neg_cnt>0)
	fputs(" ", out);

      for(i=0; i<neg_cnt;) {
	int atom = neg[i];

	fputs("(not ", out);
	fprintf(out, "var_%i", atom+shift);
	fputs(")", out);
	i++;
	if(i<neg_cnt)
	  fputs(" ", out);
      }

      if(pos_cnt+neg_cnt>1)
	fputs(")", out);
    }

    if(!(status & MARK_TRUE_OR_FALSE))
      fputs(")", out);
    if(!(status & MARK_FALSE))
      fputs(")\n", out);
    break;

  case STYLE_PCNT:
    if(!(status & MARK_FALSE))
      constraint_cnt++;
    break;

  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x";

      /* For the implication "bd_r -> B & -C" generate:
       *
       * sum_i b_i - sum_j c_j - |B union C| bd_r >= - |C|
       *
       * Becomes void if bd_r = 0.
       */

      if(!(status & MARK_FALSE)) {
	if(style == STYLE_LP)
	  fputs("  ", out);
	else if(pos_cnt>0)
	  fputs("1 ", out);

	for(i=0; i<pos_cnt;) {
	  int atom = pos[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<pos_cnt) {
	    if(style == STYLE_LP)
	      fputs("+ ", out);
	    else
	      fputs("+1 ", out);
	  }
	}

	if(neg_cnt>0) {
	  if(style == STYLE_LP)
	    fputs("- ", out);
	  else
	    fputs("-1 ", out);
	}

	for(i=0; i<neg_cnt;) {
	  int atom = neg[i];

	  fprintf(out, "%s%i ", varpref, atom+shift);
	  i++;
	  if(i<neg_cnt) {
	    if(style == STYLE_LP)
	      fputs("- ", out);
	    else
	      fputs("-1 ", out);
	  }
	}

	if((status & MARK_TRUE) && pos_cnt+neg_cnt>0)
	  fprintf(out, " >= %i", pos_cnt);
	else {
	  if(head)
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i %s%i >= %i" : "-%i %s%i >= %i",
		    pos_cnt+neg_cnt, varpref, head+shift, -neg_cnt);
	  else
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i body_%i >= %i" : "-%i x%i >= %i",
		    pos_cnt+neg_cnt, body, -neg_cnt);
	}
	if(style == STYLE_PB)
	  fputs(" ;", out);
	fputs("\n", out);
      }
    }
    break;
  }

  return;
}

/* ======================== Translate weight rules ======================== */

void tr_weight(int style, FILE *out,
               int head,  /* Original head atom (if used) */
               int body,  /* New body atom (otherwise) */
               int status, WEIGHT_RULE *weight, ATAB *table)
{
  int pos_cnt = weight->pos_cnt;
  int *pos = weight->pos;
  int neg_cnt = weight->neg_cnt;
  int *neg = weight->pos;
  int bound = weight->bound;
  int *weights = weight->weight;
  int shift = table->shift;
  int sum = 0, pos_sum = 0, neg_sum = 0;
  int i = 0, previous = 0;
  int bits = 0;

  switch(style) {
  case STYLE_READABLE:

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	write_atom(style, out, head, table);
      else
	fprintf(out, "body_%i", body);
      fputs(" <-> ", out);
    } else if(status & MARK_FALSE)
      fputs("~", out);

    if(pos_cnt+neg_cnt == 0)
      fputs("T", out);
    else {
      fprintf(out, "%i [ ", bound);

      weights = &weight->weight[neg_cnt];

      for(i=0; i<pos_cnt;) {
        int atom = pos[i];

        write_atom(style, out, atom, table);
        fprintf(out, "=%i", *(weights++));
        i++;
        if(i<pos_cnt)
          fputs(", ", out);
      }

      if(pos_cnt>0 && neg_cnt>0)
        fputs(", ", out);

      weights = weight->weight;

      for(i=0; i<neg_cnt;) {
        int atom = neg[i];

        fputs("~", out);
        write_atom(style, out, atom, table);
        fprintf(out, "=%i", *(weights++));
        i++;
        if(i<neg_cnt)
          fputs(" , ", out);
      }
      fputs(" ]", out);
    }
    fputs(".\n", out);
    break;

  case STYLE_BV:

    for(i=0; i<pos_cnt+neg_cnt; i++)
      sum += weights[i];
    bits = base2log(sum+1);
    previous = 0;

    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i ", pos[i]+shift);

      if(previous)
	fprintf(out, "(= w_%i (bvadd w_%i (_ bv%i %i)))",
		newcounter, previous, *weights++, bits);
      else
	fprintf(out, "(= w_%i (_ bv%i %i))",
		newcounter, *weights++, bits);
      fputs("))\n", out);

      fprintf(out, "(assert (=> (not var_%i) ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i (_ bv0 %i))", newcounter, bits);
      fputs("))\n", out);

      previous = newcounter++;
    }
    
    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i (bvadd w_%i (_ bv%i %i)))",
		newcounter, previous, *weights++, bits);
      else
	fprintf(out, "(= w_%i (_ bv%i %i))",
		newcounter, *weights++, bits);
      fputs("))\n", out);

      fprintf(out, "(assert (=> var_%i ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i (_ bv0 %i))", newcounter, bits);
      fputs("))\n", out);

      previous = newcounter++;
    }

    /* Generate the definition for the head/body atom */

    fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	fprintf(out, "(= var_%i ", head+shift);
      else
	fprintf(out, "(= body_%i ", body);
    } else if(status & MARK_FALSE)
      fputs("(not ", out);

    if(previous)
      fprintf(out, "(bvult (_ bv%i %i) w_%i)", bound-1, bits, previous);
    else { /* The body is empty */
      if(0 >= bound)
        fputs("true", out);
      else
        fputs("false", out);
    }
    if(!(status & MARK_TRUE_OR_FALSE) || (status & MARK_FALSE))
      fputs(")", out);
    fprintf(out, ")\n");
    break;

  case STYLE_DIFF:

    previous = 0;
    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= (- w_%i w_%i) %i)",
		newcounter, previous, weights[neg_cnt+i]);
      else
	fprintf(out, "(= (- w_%i %s) %i)",
		newcounter, zero, weights[neg_cnt+i]);
      fputs("))\n", out);

      fprintf(out, "(assert (=> (not var_%i) ", pos[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i %s)", newcounter, zero);
      fputs("))\n", out);

      previous = newcounter++;
    }

    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= (- w_%i w_%i) %i)",
		newcounter, previous, weights[i]);
      else
	fprintf(out, "(= (- w_%i %s) %i)",
		newcounter, zero, weights[i]);
      fputs(")\n", out);

      fprintf(out, "  (=> var_%i ", neg[i]+shift);
      if(previous)
	fprintf(out, "(= w_%i w_%i)", newcounter, previous);
      else
	fprintf(out, "(= w_%i %s)", newcounter, zero);
      fputs("))\n", out);

      previous = newcounter++;
    }

    /* Generate the definition for the head/body atom */

    fputs("(assert ", out);

    if(!(status & MARK_TRUE_OR_FALSE)) {
      if(head)
	fprintf(out, "(= var_%i ", head+shift);
      else
	fprintf(out, "(= body_%i ", body);
    } else if(status & MARK_FALSE)
      fputs("(not ", out);

    if(previous)
      fprintf(out, "(>= (- w_%i %s) %i)", previous, zero, bound);
    else { /* The body is empty */
      if(0 >= bound)
        fputs("true", out);
      else
        fputs("false", out);
    }
    if(!(status & MARK_TRUE_OR_FALSE) || (status & MARK_FALSE))
      fputs(")", out);
    fprintf(out, ")\n");
    break;

  case STYLE_PCNT:
    constraint_cnt++;
    if(!(status & MARK_TRUE))
      constraint_cnt++;
    break;

  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x";

      /* For the equivalence "bd_r <-> bound [ B=W_B, -C=W_C ]" generate:
       *
       * sum_i (w_i x b_i) - sum_j (w_j x c_j) - bound x bd_r >= - sum W_C
       *
       * Becomes void if bd_r = 0.
       */

      if(style == STYLE_LP)
	fputs("  ", out);
      weights = &weight->weight[neg_cnt];

      for(i=0; i<pos_cnt;) {
	int atom = pos[i];

	if(style == STYLE_PB)
	  fputs("+", out);
	fprintf(out, "%i %s%i ", *weights, varpref, atom+shift);
	pos_sum += *(weights++);
	i++;
	if(i<pos_cnt && style == STYLE_LP)
	  fputs("+ ", out);
      }

      if(neg_cnt>0 && style == STYLE_LP)
	  fputs("- ", out);

      weights = weight->weight;

      for(i=0; i<neg_cnt;) {
	int atom = neg[i];

	if(style == STYLE_PB)
	  fputs("-", out);
	fprintf(out, "%i %s%i ", *weights, varpref, atom+shift);
	neg_sum += *(weights++);
	i++;
	if(i<neg_cnt && style == STYLE_LP)
	  fputs("- ", out);
      }

      if((status & MARK_FALSE) && pos_cnt+neg_cnt>0)
	fprintf(out, " >= %i", -neg_sum);
      else if((status & MARK_TRUE) && pos_cnt+neg_cnt>0)
	fprintf(out, " >= %i", bound-neg_sum);
      else {
	if(head)
	  fprintf(out,
		  style == STYLE_LP ?
		  "- %i %s%i >= %i": "-%i %s%i >= %i",
		  bound, varpref, head+shift, -neg_sum);
	else
	  fprintf(out,
		  style == STYLE_LP ?
		  "- %i body_%i >= %i" : "-%i x%i >= %i",
		  bound, body, -neg_sum);
      }
      if(style == STYLE_PB)
	fputs(" ;", out);
      fputs("\n", out);

      /* For the equvalence "bd_r <-> bound [ B=W_B, -C=W_C ]" generate:
       *
       * sum_i (w_i x b_i) - sum_j (w_j x c_j)
       * - (sum W_B + sum W_C + 1 - bound) bd_r <= bound - sum W_C - 1
       *
       * Becomes void if bd_r = 1.
       */

      if(!(status & MARK_TRUE)) {
	if(style == STYLE_LP)
	  fputs("  ", out);

	weights = &weight->weight[neg_cnt];

	for(i=0; i<pos_cnt;) {
	  int atom = pos[i];

	  if(style == STYLE_PB)
	    fputs("-", out); /* Eq multiplied by -1 */
	  fprintf(out, "%i %s%i ", *(weights++), varpref, atom+shift);
	  i++;
	  if(i<pos_cnt && style == STYLE_LP)
	      fputs("+ ", out);
	}

	if(neg_cnt>0 && style == STYLE_LP)
	    fputs("- ", out);

	weights = weight->weight;

	for(i=0; i<neg_cnt;) {
	  int atom = neg[i];

	  if(style == STYLE_PB)
	    fputs("+", out);
	  fprintf(out, "%i %s%i ", *(weights++), varpref, atom+shift);
	  i++;
	  if(i<neg_cnt && style == STYLE_LP)
	      fputs("- ", out);
	}

	if((status & MARK_FALSE) && pos_cnt+neg_cnt>0) {
	  if(style == STYLE_LP)
	    fprintf(out, " <= %i", bound-neg_sum-1);
	  else
	    fprintf(out, " >= %i", 1-bound+neg_sum);
	} else {
	  if(head)
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i %s%i <= %i" : "%+i %s%i >= %i",
		    pos_sum+neg_sum+1-bound, varpref,
		    head+shift,
		    style == STYLE_LP ? bound-neg_sum-1 : 1-bound+neg_sum);
	  else
	    fprintf(out,
		    style == STYLE_LP ?
		    "- %i body_%i <= %i" : "%+i x%i >= %i",
		    pos_sum+neg_sum+1-bound, body,
		    style == STYLE_LP ? bound-neg_sum-1 : 1-bound+neg_sum);
	}
	if(style == STYLE_PB)
	  fputs(" ;", out);
	fputs("\n", out);
      }
    }
    break;
  }

  return;
}

/*
 * form_definition -- Form the equivalence defining the atom
 */

int form_definition(int style, FILE *out, int atom, int status,
		    int shift, int cnt, ATAB *table, int newatom)
{
  int j = 0;

  /* Simplification is done if the atom is known to be true */

  switch(style) {
  case STYLE_READABLE:

    if(!(status & MARK_TRUE)) {
      write_atom(style, out, atom, table);
      fputs(" <-> ", out);
    }
    for(j=0; j < cnt;) {
      fprintf(out, "body_%i", newatom+j);

      if(++j < cnt)
	fputs(" | ", out);
    }
    fputs(".\n", out);
    break;

  case STYLE_BV:
  case STYLE_DIFF:

    fputs("(assert ", out);
    if(!(status & MARK_TRUE))
      fprintf(out, "(= var_%i ", atom+shift);
    fputs("(or ", out);
    for(j=0; j < cnt;) {
      fprintf(out, "body_%i", newatom+j);

      if(++j < cnt)
	fputs(" ", out);
    }
    fputs(")", out);
    if(!(status & MARK_TRUE))
      fputs(")", out);
    fputs(")\n", out);
    break;

  case STYLE_PCNT:
    /* Must be kept in synchrony with STYLE_PB below */

    if(!(status & MARK_TRUE)) constraint_cnt++;
    constraint_cnt++;
    break;

  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x";

      /* It is being assumed that cnt>0 */

      if(!(status & MARK_TRUE)) {
	if(style == STYLE_LP)
	  fputs("  ", out);
	else
	  fputs("-1 ", out); /* This equation multiplied by -1 */
	for(j=0; j < cnt;) {
	  fprintf(out, style == STYLE_LP ? "body_%i" : "x%i", newatom+j);

	  if(++j < cnt)
	    fputs(style == STYLE_LP ? " + " : " -1 ", out);
	}
	fprintf(out,
		style == STYLE_LP ?
		" - %i %s%i <= 0" : " +%i %s%i >= 0",
		cnt, varpref, atom+shift);
	if(style == STYLE_PB)
	  fputs(" ;", out);
	fputs("\n", out);
      }

      if(style == STYLE_LP)
	fputs("  ", out);
      else
	fputs("1 ", out);
      for(j=0; j < cnt;) {
	fprintf(out, style == STYLE_LP ? "body_%i" : "x%i", newatom+j);

	if(++j < cnt)
	  fputs(style == STYLE_LP ? " + " : " +1 ", out);
      }
      if(status & MARK_TRUE)
	fputs(" >= 1", out);
      else
	fprintf(out,
		style == STYLE_LP ?
		" - %s%i >=0" : " -1 %s%i >=0",
		varpref, atom+shift);
      if(style == STYLE_PB)
	fputs(" ;", out);
      fputs("\n", out);
    }
    break;
  }

  return newatom+cnt;
}

/*
 * form_completion -- Form Clark's completion
 */

int form_completion(int style, FILE *out, DEF *d, int atom,
		    int status, int shift, ATAB *table)
{
  int j = 0, zero_used = 0;
  RULE *r = NULL;

  switch(style) {
  case STYLE_DSYM:
    /* Declare symbols needed in the QF_IDL formula */

    if(d->rule_cnt>1 && !(status & MARK_FALSE)) {
      /* New atoms denoting rule bodies */

      for(j=0; j < d->rule_cnt; j++)
	fprintf(out, "(declare-fun body_%i () Bool)\n", newatom+j);

      newatom += d->rule_cnt;
    }

    if(d->rule_cnt>0) {  /* New variables for cardinality/weight rules */

      for(j=0; j < d->rule_cnt; j++) {
        r = d->rules[j];

        if(r->type == TYPE_CONSTRAINT || r->type == TYPE_WEIGHT) {
          int k = 0, cnt = 0;

          cnt = get_pos_cnt(r) + get_neg_cnt(r);

          for(k=0; k<cnt; k++) {
	    fprintf(out, "(declare-fun w_%i () Int)\n", newcounter+k);
            zero_used = -1;
          }

          newcounter += cnt;
        }
      }
    }
    break;

  case STYLE_BSYM:

    /* Declare symbols needed in the QF_BV formula */

    if(d->rule_cnt>1 && !(status & MARK_FALSE)) {
      /* New atoms denoting rule bodies */

      for(j=0; j < d->rule_cnt; j++)
	fprintf(out, "(declare-fun body_%i () Bool)\n", newatom+j);
	
      newatom += d->rule_cnt;
    }

    if(d->rule_cnt>0) {  /* New variables for cardinality/weight rules */

      for(j=0; j < d->rule_cnt; j++) {
        r = d->rules[j];

	if((r->type != TYPE_CONSTRAINT) && (r->type != TYPE_WEIGHT))
	  continue;

	int k = 0, cnt = get_pos_cnt(r)+get_neg_cnt(r), sum = 0;

	if(r->type == TYPE_CONSTRAINT)
	  sum = cnt;
	else {
	  int *weights = r->data.weight->weight;
	  for(k=0; k<cnt; k++)
	    sum += weights[k];
	}

	int bits = base2log(sum+1);

	for(k=0; k<cnt; k++) {
	  fprintf(out, "(declare-fun w_%i () (_ BitVec %i))\n",
		  newcounter+k, bits);
	  zero_used = -1;
	}
	newcounter += cnt;
      }
    }
    break;

  case STYLE_BIN: /* Declare binary variables (MIP) */

    if(d->rule_cnt>1 && !(status & MARK_FALSE)) {

      /* New atoms denoting rule bodies */

      for(j=0; j < d->rule_cnt; j++)
	fprintf(out, "  body_%i\n", newatom+j);

      newatom += d->rule_cnt;
    }
    break;

  case STYLE_GEN: /* Declare general variables (MIP) */
    break;

  case STYLE_PCNT:
    if(d->rule_cnt>1 && !(status & MARK_FALSE))
      newatom += d->rule_cnt;

    /* Precalculate the number of constraints in synchrony with STYLE_PB */

    if(d->rule_cnt == 0) {

      if(!(status & MARK_INPUT) && !(status & MARK_FALSE))
	constraint_cnt++;

    } else if(d->rule_cnt == 1) {

      r = d->rules[0];  /* Unique defining rule */

      switch(r->type) {
      case TYPE_BASIC:
	tr_basic(style, out, atom, 0, status, r->data.basic, table);
	break;

      case TYPE_CONSTRAINT:
	tr_constraint(style, out, atom, 0, status, r->data.constraint, table);
	break;

      case TYPE_CHOICE:
	tr_choice(style, out, atom, 0, status, r->data.choice, table);
	break;

      case TYPE_WEIGHT:
	tr_weight(style, out, atom, 0, status, r->data.weight, table);
	break;
      }

    } else {

      /* Scan the entire definition */

      for(j=0; j < d->rule_cnt; j++) {
	r = d->rules[j];

	switch(r->type) {
	case TYPE_BASIC:
	  if(status & MARK_FALSE)
	    tr_basic(style, out, atom, 0, status, r->data.basic, table);
	  else
	    tr_basic(style, out, 0, newatom+j, 0, r->data.basic, table);
	  break;

	case TYPE_CONSTRAINT:
	  if(status & MARK_FALSE)
	    tr_constraint(style, out, atom, 0,
			  status, r->data.constraint, table);
	  else
	    tr_constraint(style, out, 0, newatom+j,
			  0, r->data.constraint, table);
	  break;

	case TYPE_CHOICE:
	  if(status & MARK_FALSE)
	    tr_choice(style, out, atom, 0, status, r->data.choice, table);
	  else
	    tr_choice(style, out, 0, newatom+j, 0, r->data.choice, table);
	  break;

	case TYPE_WEIGHT:
	  if(status & MARK_FALSE)
	    tr_weight(style, out, atom, 0, status, r->data.weight, table);
	  else
	    tr_weight(style, out, 0, newatom+j, 0, r->data.weight, table);
	  break;
	}
      }

      if(!(status & MARK_FALSE))
	newatom = form_definition(style, out, atom, status, shift,
				  d->rule_cnt, table, newatom);
    }
    break;

  case STYLE_READABLE:
  case STYLE_BV:
  case STYLE_DIFF:
  case STYLE_LP:
  case STYLE_PB:

    if(d->rule_cnt == 0) {

      if(!(status & MARK_INPUT)       /* Must be allowed to vary */
	 && !(status & MARK_FALSE)) { /* Falsified by the compute statement */

	/* Falsify the atom unconditionally */

	if(style == STYLE_BV || style == STYLE_DIFF)
	  fprintf(out, "(assert (not var_%i))\n", atom+shift);
	else if(style == STYLE_LP)
	  fprintf(out, "  var_%i = 0\n", atom+shift);
	else if(style == STYLE_PB)
	  fprintf(out, "1 x%i = 0 ;\n", atom+shift);
	else {
	  fputs("~", out);
	  write_atom(style, out, atom, table);
	  fputs(".\n", out);
	}
      }

    } else if(d->rule_cnt == 1) {

      r = d->rules[0];

      /* Make the head equivalent to the unique rule body */

      switch(r->type) {
      case TYPE_BASIC:
	tr_basic(style, out, atom, 0, status, r->data.basic, table);
	r->data.basic->head = 0;   /* The atom denotes the body */
	break;

      case TYPE_CONSTRAINT:
	tr_constraint(style, out, atom, 0, status, r->data.constraint, table);
	r->data.constraint->head = 0;   /* The atom denotes the body */
	break;

      case TYPE_CHOICE:
	tr_choice(style, out, atom, 0, status, r->data.choice, table);
	r->data.choice->head[0] = 0;  /* The atom denotes the body */
	break;

      case TYPE_WEIGHT:
	tr_weight(style, out, atom, 0, status, r->data.weight, table);
	r->data.weight->head = 0;   /* The atom denotes the body */
	break;
      }

    } else {

      /* Make the head equivalent to a disjunction of its rule bodies */

      for(j=0; j < d->rule_cnt; j++) {
	r = d->rules[j];

	switch(r->type) {
	case TYPE_BASIC:
	  if(status & MARK_FALSE)
	    tr_basic(style, out, atom, 0, status, r->data.basic, table);
	  else {
	    tr_basic(style, out, 0, newatom+j, 0, r->data.basic, table);
	    r->data.basic->head = newatom+j;
	  }
	  break;

	case TYPE_CONSTRAINT:
	  if(status & MARK_FALSE)
	    tr_constraint(style, out, atom, 0,
			  status, r->data.constraint, table);
	  else {
	    tr_constraint(style, out, 0, newatom+j,
			  0, r->data.constraint, table);
	    r->data.constraint->head = newatom+j;
	  }
	  break;

	case TYPE_CHOICE:
	  if(status & MARK_FALSE)
	    tr_choice(style, out, atom, 0, status, r->data.choice, table);
	  else {
	    tr_choice(style, out, 0, newatom+j, 0, r->data.choice, table);
	    r->data.choice->head[0] = newatom+j;
	  }
	  break;

	case TYPE_WEIGHT:
	  if(status & MARK_FALSE)
	    tr_weight(style, out, atom, 0, status, r->data.weight, table);
	  else {
	    tr_weight(style, out, 0, newatom+j, 0, r->data.weight, table);
	    r->data.weight->head = newatom+j;
	  }
	  break;
	}
      }

      /* Generate "a <-> body_1 | ... | body_n." */

      if(!(status & MARK_FALSE))
	newatom = form_definition(style, out, atom, status, shift,
				  d->rule_cnt, table, newatom);
    }
    break;
  }

  return zero_used;
}

/*
 * tr_atoms --- Translate the program atom by atom
 */

void tr_atoms(int style, FILE *out, ATAB *table, OCCTAB *occtable)
{
  int zero_used = 0;
  ATAB *scan = table;

  /* Process all atoms one by one */

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int shift = scan->shift;
    int *statuses = scan->statuses;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = definition(occtable, atom);
      int scc = d->scc;
      int scc_size = d->scc_size;
      int status = statuses[i];
      RULE *r = NULL;
      int j = 0;

      /* Form Clark's completion for this atom */

      switch(style) {
      case STYLE_BSYM:
      case STYLE_DSYM:
	fprintf(out, "(declare-fun var_%i () Bool)\n", atom+shift);
	break;

      case STYLE_BIN:
	fprintf(out, "  var_%i\n", atom+shift);
	break;

      case STYLE_GEN:
	break;

      case STYLE_PCNT:
	break;

      case STYLE_READABLE:
        fputs("\n% Translation of atom ", out);
        write_atom(style, out, atom, table);
        fputs(":\n\n", out);
	break;
      }

      zero_used |=
	form_completion(style, out, d, atom, status, shift, table);
    }
    scan = scan->next;
  }
  if(zero_used) {
    if(style == STYLE_DSYM)
      fprintf(out, "(declare-fun %s () Int)\n", zero);
  }
  return;
}

/*
 * tr_optimize_statement -- Translate optimization statements
 */

void tr_optimize_statement(int style, FILE *out, RULE *statement, ATAB *table)
{
  int i = 0, shift = table->shift;
  OPTIMIZE_RULE *opt = statement->data.optimize;
  int pos_cnt = opt->pos_cnt;
  int *pos = opt->pos;
  int neg_cnt = opt->neg_cnt;
  int *neg = opt->neg;
  int *weights = opt->weight;
  int sum = 0, bits = 0;

  if(pos_cnt+neg_cnt == 0)
    return;

  if(style == STYLE_BSYM || style == STYLE_BV) {

    for(i=0; i<pos_cnt+neg_cnt; i++)
      sum += weights[i];

    bits = base2log(sum+1);
  }

  switch(style) {
  case STYLE_LP:
  case STYLE_PB:

    { char *varpref = NULL;

      if(style == STYLE_LP)
	varpref = "var_";
      else
	varpref = "x";

      /* For an optimization statement [ B=W_B, -C=W_C ]" generate:
       *
       * sum_i (w_i x b_i) - sum_j (w_j x c_j) */

      if(style == STYLE_LP)
	fputs("  ", out);

      for(i=0; i<pos_cnt; ) {
	if(style == STYLE_PB)
	  fputs("+", out);
	fprintf(out, "%i %s%i ", weights[neg_cnt+i], varpref, pos[i]+shift);
	
	i++;
	if(i<pos_cnt && style == STYLE_LP)
	    fputs("+ ", out);
      }

      if(neg_cnt>0 && style == STYLE_LP)
	fputs("- ", out);

      for(i=0; i<neg_cnt;) {
	if(style == STYLE_PB)
	  fputs("-", out);
	fprintf(out, "%i %s%i ", weights[i], varpref, neg[i]+shift);
	i++;
	if(i<neg_cnt && style == STYLE_LP)
	  fputs("- ", out);
      }
      if(style == STYLE_PB)
	fputs(";", out); 
      fputs("\n", out); 
    }
    break;

  case STYLE_BSYM:

    fprintf(out, "(declare-fun %s () (_ BitVec %i))\n", cost, bits);
    for(i=0; i<pos_cnt+neg_cnt; i++)
      fprintf(out, "(declare-fun %s_%i () (_ BitVec %i))\n",
	      cost, i+1, bits);
    break;

  case STYLE_DSYM:

    fprintf(out, "(declare-fun %s () Int)\n", cost);
    for(i=0; i<pos_cnt+neg_cnt; i++)
      fprintf(out, "(declare-fun %s_%i () Int)\n", cost, i+1);
    break;

  case STYLE_BV:

    if(pos_cnt+neg_cnt == 0)
      fprintf(out, "(assert (= %s (_ bv 0 1)))\n", cost);
    else if(pos_cnt+neg_cnt == 1)
      fprintf(out, "(assert (= %s %s_1))\n", cost, cost);
    else { /* pos_cnt+neg_cnt >= 2 and adding becomes necessary */
      fprintf(out, "(assert (= %s ", cost);
      for(i=0; i<pos_cnt+neg_cnt-1; i++)
	fprintf(out, "(bvadd cost_%i ", i+1);
      fprintf(out, "cost_%i", i+1);
      for(i=0; i<pos_cnt+neg_cnt-1; i++)
	fputs(")", out);
      fputs("))\n", out);
    }	  

    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i (= cost_%i (_ bv%i %i))))\n",
	      pos[i]+shift, i+1, weights[neg_cnt+i], bits);
      fprintf(out, "(assert (=> (not var_%i) (= cost_%i (_ bv0 %i))))\n",
	      pos[i]+shift, i+1, bits);
    }

    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) (= cost_%i (_ bv%i %i))))\n",
	      neg[i]+shift, pos_cnt+i+1, weights[i], bits);
      fprintf(out, "(assert (=> var_%i (= cost_%i (_ bv0 %i))))\n",
	      neg[i]+shift, pos_cnt+i+1, bits);
    }
    break;

  case STYLE_DIFF:
    fprintf(out, "(assert (= %s (+", cost);
    for(i=0; i<pos_cnt+neg_cnt; i++)
      fprintf(out, " cost_%i", i+1);
    fputs(")))\n", out);
	  
    for(i=0; i<pos_cnt; i++) {
      fprintf(out, "(assert (=> var_%i (= cost_%i %i)))\n",
	      pos[i]+shift, i+1, weights[neg_cnt+i]);
      fprintf(out, "(assert (=> (not var_%i) (= cost_%i 0)))\n",
	      pos[i]+shift, i+1);
    }

    for(i=0; i<neg_cnt; i++) {
      fprintf(out, "(assert (=> (not var_%i) (= cost_%i %i)))\n",
	      neg[i]+shift, pos_cnt+i+1, weights[i]);
      fprintf(out, "(assert (=> var_%i (= cost_%i 0)))\n",
	      neg[i]+shift, pos_cnt+i+1);
    }
    break;

  case STYLE_READABLE:
    write_rule(style, out, statement, table);	
    fputs("\n", out); 
    break;
  }

  return;
}

/*
 * tr_compute_statement -- Translate a compute statement
 */

void tr_compute_statement(int style, FILE *out, ATAB *table)
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

      switch(style) {
      case STYLE_READABLE:
        if(status & MARK_TRUE) {
          write_atom(style, out, atom, table);
          fputs(".\n", out);
        }
        if(status & MARK_FALSE) {
          fprintf(out, "~");
          write_atom(style, out, atom, table);
          fputs(".\n", out);
        }
        break;

      case STYLE_BV:
      case STYLE_DIFF:
        if(status & MARK_TRUE)
          fprintf(out, "(assert var_%i)\n", atom+shift);
        if(status & MARK_FALSE)
          fprintf(out, "(assert (not var_%i))\n", atom+shift);
        break;

      case STYLE_PCNT:
	/* Must be kept in synchrony with STYLE_PB below */

	if(status & MARK_TRUE)
	  constraint_cnt++;
	if(status & MARK_FALSE)
	  constraint_cnt++;
	break;

      case STYLE_LP:
      case STYLE_PB:
        if(status & MARK_TRUE) {
	  if(style == STYLE_LP)
	    fprintf(out, "  var_%i = 1\n", atom+shift);
	  else
	    fprintf(out, "1 x%i = 1 ;\n", atom+shift);
	}
        if(status & MARK_FALSE) {
	  if(style == STYLE_LP)
	    fprintf(out, "  var_%i = 0\n", atom+shift);
	  else
	    fprintf(out, "1 x%i = 0 ;\n", atom+shift);
	}
        break;
      }
    }
    table = table->next;
  }
  return;
}

/*
 * assign_acyc_atoms -- Assign atoms involved in acyc constraints
 */

void assign_acyc_atoms(GRAPH *graphs)
{
  GRAPH *sg = graphs;
  int bits = 0, cnt = 0;

  while(sg) {
    NODE *node = sg->nodes;
    int bits = base2log(sg->node_cnt+1);

    while(node) {
      node -> vec = newatom;
      newatom += bits;
      
      node = node->next;
    }
    
    sg = sg -> next;
  }

  return;
}

/*
 * tr_acyc_interface -- Create constraints related with acyc information
 */

void tr_acyc_interface(int style, FILE *out, GRAPH *graphs)
{
  GRAPH *sg = graphs;
  int bits = 0, i = 0, w = 0;

  while(sg) {
    NODE *node = sg->nodes;

    while(node) {
      EDGE *edge = node->edges;

      if(style == STYLE_DSYM)
	fprintf(out, "(declare-fun acyc_%i () Int)\n", node->node);
      else if(style == STYLE_BSYM) {
	bits = base2log(sg->node_cnt+1);
	fprintf(out, "(declare-fun acyc_%i () (_ BitVec %i))\n",
		node->node, bits);
      } else if(style == STYLE_GEN)
	fprintf(out, "  acyc_%i\n", node->node);
      else 
	while(edge) {
	  switch(style) {
	  case STYLE_BV:
	    bits = base2log(sg->node_cnt+1);
	    fprintf(out, "(assert (=> var_%i (bvult acyc_%i acyc_%i)))\n",
		    edge->atom, edge->node, node->node);
	    break;
	  case STYLE_DIFF:
	    fprintf(out, "(assert (=> var_%i (> acyc_%i acyc_%i)))\n",
		    edge->atom, node->node, edge->node);
	    break;
	  case STYLE_LP:
	    fprintf(out, "  acyc_%i - acyc_%i - %i var_%i >= %i\n",
		    node->node, edge->node, sg->node_cnt,
		    edge->atom, 1-(sg->node_cnt));
	    break;
	  case STYLE_PB:
	    bits = base2log(sg->node_cnt+1);
	    w = 1;
	    for(i=0; i<bits; ) {
	      fprintf(out, "%i x%i", w, node->vec+i);
	      w *= 2;
	      i++;
	      if(i<bits)
		fputs(" +", out);
	    }
	    fputs(" -", out);
	    w = 1;
	    for(i=0; i<bits; ) {
	      fprintf(out, "%i x%i", w,
		      acyc_find_node(edge->node, sg->nodes)->vec+i);
	      w *= 2;
	      i++;
	      if(i<bits)
		fputs(" -", out);
	    }
	    fprintf(out, " -%i x%i >= %i ;\n",
		    sg->node_cnt, edge->atom, 1-(sg->node_cnt));
	    break;
	  }
	  edge = edge->next;
	}

      node = node->next;
    }
    sg = sg->next;
  }

  return;
}
