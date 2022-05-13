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
 * scc.c -- Computation of Strongly Connected Components (SCCs) etc
 *
 * (c) 2004-2008, 2015 Tomi Janhunen
 */

#include <stdlib.h>
#include <stdio.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"
#include "scc.h"

void _version_scc_c()
{
  _version("$RCSfile: scc.c,v $",
	   "$Date: 2021/05/27 11:40:56 $",
	   "$Revision: 1.17 $");
}

/*
 * scc_set/clear -- Set parameters for SCC computation
 */

int scc_flags = 0;

void scc_set(int mask)
{
  scc_flags |= mask;
}

void scc_clear(int mask)
{
  scc_flags ^= mask;
}

/* --------------------------------------------------------------------------*/

/*
 * initialize_occurrences --- Form an occurrence table
 */

OCCTAB *initialize_occurrences(ATAB *table,
			       int pb,  /* Positive bodies? */
			       int nb)  /* Negative bodies? */
{
  OCCTAB *rvalue = (OCCTAB *)malloc(sizeof(OCCTAB));
  OCCTAB *occtab = rvalue;
  
  while(table) {
    int count = table->count;
    int offset = table->offset;
    SYMBOL **names = table->names;
    int *statuses = table->statuses;
    int *others = table->others;
    int i = 0;

    occtab->count = count;
    occtab->offset = offset;
    occtab->atoms = table;

    /* Head occurrences */

    occtab->def = (DEF *)malloc(sizeof(DEF)*(count+1));

    for(i=1; i<=count; i++) {
      DEF *d = &(occtab->def)[i];

      d->rule_cnt = 0;
      d->rules = NULL;
      d->scc = 0;
      d->scc_size = 0;
      d->visited = 0;
      d->status = (statuses[i] & (MARK_INPUT|MARK_CHOICE));
      if(names[i])
	d->status |= MARK_VISIBLE;
      if(others)
	d->other = others[i];
    }

    /* Occurrences in positive bodies */

    if(pb) {
      occtab->pbody = (OCC *)malloc(sizeof(OCC)*(count+1));

      for(i=1; i<=count; i++) {
	OCC *p = &(occtab->pbody)[i];

	p->rule_cnt = 0;
	p->rules = NULL;
      }

    } else
      occtab->pbody = NULL;

    /* Occurrences in negative bodies */

    if(nb) {
      occtab->nbody = (OCC *)malloc(sizeof(OCC)*(count+1));

      for(i=1; i<=count; i++) {
	OCC *n = &(occtab->nbody)[i];

	n->rule_cnt = 0;
	n->rules = NULL;
      }

    } else
      occtab->nbody = NULL;

    /* Process the next piece (if any) */

    if(table = table->next) {
      occtab->next = (OCCTAB *)malloc(sizeof(OCCTAB));
      occtab = occtab->next;
    } else
      occtab->next = NULL;
  }

  return rvalue;
}

void compute_occurrences(RULE *program, OCCTAB *occtab,
			 int prune, int special_atom)
{
  RULE *scan = program;
  OCCTAB *pass = occtab;

  /* ------ Count occurrences of atoms ------ */

  while(scan) {

    switch(scan->type) {
    case TYPE_CHOICE:
    case TYPE_DISJUNCTIVE:
      { int *heads = get_heads(scan);
        int cnt = get_head_cnt(scan);
        int i = 0;

	for(i=0; i<cnt; i++) {
	  DEF *d = definition(occtab, heads[i]);
	  
	  if(!(d->status & prune)) d->rule_cnt++;
	}
      }
      break;
      
    case TYPE_BASIC:
    case TYPE_CONSTRAINT:
    case TYPE_WEIGHT:
      { int head = get_head(scan);
        DEF *d = definition(occtab, head);
      
        if(!(d->status & prune)) d->rule_cnt++;
      }
      break;

    case TYPE_INTEGRITY:
    case TYPE_OPTIMIZE:
    case TYPE_CLAUSE:
      /* Headless rules are reported under special atom */
      { DEF *d = NULL;

        if(special_atom){ 
          d = definition(occtab, special_atom);

          if(!(d->status & prune)) d->rule_cnt++;
        }
      }
      break;

    default:
      fprintf(stderr, "compute_occurrences: unsupported rule type %i!\n",
	      scan->type);
      exit(-1);
    }

    if(occtab->pbody) {
      int *pos = get_pos(scan);
      int cnt = get_pos_cnt(scan);
      int i = 0;

      for(i=0; i<cnt; i++) {
        DEF *d = definition(occtab, pos[i]);
	OCC *p = pbody_occs(occtab, pos[i]);

	if(!(d->status & prune))
	  p->rule_cnt++;
      }

    }
    if(occtab->nbody) {
      int *neg = get_neg(scan);
      int cnt = get_neg_cnt(scan);
      int i = 0;

      for(i=0; i<cnt; i++) {
	DEF *d = definition(occtab, neg[i]);
	OCC *n = nbody_occs(occtab, neg[i]);

	if(!(d->status & prune))
	  n->rule_cnt++;
      }
    }

    scan = scan->next;
  }

  /* ------ Allocate memory for pointers referring to rules ------ */

  while(pass) {
    int count = pass->count;
    int i = 0;

    for(i=1; i<=count; i++) {
      DEF *d = &(pass->def)[i];

      if(d->rule_cnt) {
	d->rules = (RULE **)malloc(sizeof(RULE *)*(d->rule_cnt));
	d->rule_cnt = 0;
      }

      if(pass->pbody) {
	OCC *p = &(pass->pbody)[i];

	if(p->rule_cnt) {
	  p->rules = (RULE **)malloc(sizeof(RULE *)*(p->rule_cnt));
	  p->rule_cnt = 0;
	}
      }

      if(pass->nbody) {
	OCC *n = &(pass->nbody)[i];

	if(n->rule_cnt) {
	  n->rules = (RULE **)malloc(sizeof(RULE *)*(n->rule_cnt));
	  n->rule_cnt = 0;
	}
      }
    }

    pass = pass->next;
  }

  /* ----- Collect occurrences of atoms ------ */

  scan = program;

  while(scan) {
    int type = scan->type;
    int head = 0;

    switch(scan->type) {
    case TYPE_CHOICE:
    case TYPE_DISJUNCTIVE:
      { int *heads = get_heads(scan);
        int cnt = get_head_cnt(scan);
        int i = 0;

        for(i=0; i<cnt; i++) {
	  DEF *d = definition(occtab, heads[i]);

  	  if(!(d->status & prune))
	    d->rules[d->rule_cnt++] = scan;
        }
      }
      break;

    case TYPE_BASIC:
    case TYPE_CONSTRAINT:
    case TYPE_WEIGHT:
      { int head = get_head(scan);
        DEF *d = definition(occtab, head);
      
        if(!(d->status & prune))
	 d->rules[d->rule_cnt++] = scan;
      }
      break;

    case TYPE_INTEGRITY:
    case TYPE_OPTIMIZE:
    case TYPE_CLAUSE:
      /* Headless rules are collected under a special atom */
      { DEF *d = NULL;

        if(special_atom) {
	  d = definition(occtab, special_atom);

	  if(!(d->status & prune))
	    d->rules[d->rule_cnt++] = scan;
	}
      }
      break;

    default:
      /* Never entered */
      break;
    }

    if(occtab->pbody) {
      int *pos = get_pos(scan);
      int cnt = get_pos_cnt(scan);
      int i = 0;

      for(i=0; i<cnt; i++) {
	DEF *d = definition(occtab, pos[i]);
	OCC *p = pbody_occs(occtab, pos[i]);

	if(!(d->status & prune))
	  p->rules[p->rule_cnt++] = scan;
      }

    }
    if(occtab->nbody) {
      int *neg = get_neg(scan);
      int cnt = get_neg_cnt(scan);
      int i = 0;

      for(i=0; i<cnt; i++) {
	DEF *d = definition(occtab, neg[i]);
	OCC *n = nbody_occs(occtab, neg[i]);

	if(!(d->status & prune))
	  n->rules[n->rule_cnt++] = scan;
      }
    }

    scan = scan->next;
  }

  return;
}

/*
 * free_occurrences --- Release memory taken by an occurrence table
 */

void free_occurrences(OCCTAB *occtab)
{
  OCCTAB *table = occtab;

  while(table) {
    OCCTAB *delete = table;

    free(occtab->def);

    if(occtab->pbody)
      free(occtab->pbody);

    if(occtab->nbody)
      free(occtab->nbody);

    table = table->next;

    delete->next = NULL;
    free(delete);
  }

  return;
}

DEF *definition(OCCTAB *occtab, int atom)
{
  while(occtab) {
    int count = occtab->count;
    int offset = occtab->offset;

    if(atom > offset && atom <= offset+count)
      return &(occtab->def)[atom-offset];

    occtab = occtab->next;
  }
  return NULL;
}

OCC *pbody_occs(OCCTAB *occtab, int atom)
{
  while(occtab) {
    int count = occtab->count;
    int offset = occtab->offset;

    if(atom > offset && atom <= offset+count)
      return &(occtab->pbody)[atom-offset];

    occtab = occtab->next;
  }
  return NULL;
}

OCC *nbody_occs(OCCTAB *occtab, int atom)
{
  while(occtab) {
    int count = occtab->count;
    int offset = occtab->offset;

    if(atom > offset && atom <= offset+count)
      return &(occtab->nbody)[atom-offset];

    occtab = occtab->next;
  }
  return NULL;
}

/* ------ Adopting Sedgewick's representation of Tarjan's algorithm: ------- */

int visit(int atom, int *next, int max_atom, ASTACK **stack, OCCTAB *occtab);

int count_on(ASTACK *stack, int atom)
{
  int rvalue = 0;

  if(stack) {
    int atom2 = stack->atom;

    while(stack && atom != atom2) {
      rvalue++;
      if(stack = stack->under)
	atom2 = stack->atom;
    }
  }

  return rvalue;
}

void visit_list(int *first, int cnt, int *next, int *min, int max_atom,
		int mask, ASTACK **stack, OCCTAB *occtab)
{
  int i = 0;

  for(i=0; i<cnt; i++) {
    int atom = first[i];
    DEF *h = definition(occtab, atom);
    int rvalue = h->visited;

    h->status |= mask;

    if(rvalue == 0)
      rvalue = visit(atom, next, max_atom, stack, occtab);

    if(rvalue < *min) *min = rvalue;
  }

  return;
}

int visit(int atom, int *next, int max_atom, ASTACK **stack, OCCTAB *occtab)
{
  DEF *h = definition(occtab, atom);
  int min = ++(*next);
  int i = 0;

  h->visited = min;

  *stack = push(atom, 0, NULL, *stack);

  /* Traverse atoms on which this one depends positively
     (by default) and also negatively (optional) */

  for(i=0; i < h->rule_cnt; i++) {
    RULE *r = h->rules[i];
    int *first = NULL;
    int cnt = 0;

    first = get_pos(r);
    cnt = get_pos_cnt(r);
    if(cnt && ((h->status & MARK_CHOICE) == 0 || (scc_flags & SCC_SKIP_CHOICE) == 0))
      visit_list(first, cnt, next, &min, max_atom,
		 MARK_POSOCC, stack, occtab);

    if(scc_flags & SCC_NEG) {
      first = get_neg(r);
      cnt = get_neg_cnt(r);

      if(cnt)
	visit_list(first, cnt, next, &min, max_atom,
		   MARK_NEGOCC, stack, occtab);

    }
  }

  /* Unwind a SCC from the stack */

  if(h->visited == min) {
    int size = count_on(*stack, atom)+1;
    int atom2 = 0;
    *stack = pop(&atom2, NULL, NULL, *stack);

    h->scc = min;
    h->scc_size = size;
    h->visited = max_atom+1;

    while(atom2 != atom) {
      DEF *h2 = definition(occtab, atom2);

      h2->scc = min;
      h2->scc_size = size;
      h2->visited = max_atom+1;

      *stack = pop(&atom2, NULL, NULL, *stack);
    }
  }

  return min;
}

/*
 * compute_sccs -- Compute SCCs for the program
 */

void compute_sccs(OCCTAB *occtab, int max_atom)
{
  int next = 0;           /* Next free component number */
  ASTACK *stack = NULL;   /* Global stack to be used by visit */
  OCCTAB *scan = occtab;

  /* Visit all atoms that have head occurrences */

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = &(scan->def)[i];

      if(d->rule_cnt>0 && d->visited == 0)
	visit(atom, &next, max_atom, &stack, occtab);

    }
    scan = scan->next;
  }

  return;
}

/* ------------------------------------------------------------------------- */

void revisit(int atom, int scc, int max_atom, ASTACK **stack, OCCTAB *occtab);

void revisit_list(int *atoms, int cnt, int scc, int max_atom,
		  ASTACK **stack, OCCTAB *occtab)
{
  int i = 0;

  for(i=0; i<cnt; i++) {
    int atom = atoms[i];
    DEF *h = definition(occtab, atom);

    if((scc == h->scc) && (h->visited == max_atom+1))
      revisit(atom, scc, max_atom, stack, occtab);
  }

  return;
}

void revisit(int atom, int scc, int max_atom, ASTACK **stack, OCCTAB *occtab)
{
  DEF *d = definition(occtab, atom);
  int i = 0;

  d->visited = 0;

  *stack = push(atom, 0, NULL, *stack);

  /* Revisit any unvisited atoms in the same SCC */

  for(i=0; i < d->rule_cnt; i++) {
    RULE *r = d->rules[i];
    int *first = NULL;
    int cnt = 0;

    first = get_pos(r);
    cnt = get_pos_cnt(r);
    if(cnt)
      revisit_list(first, cnt, scc, max_atom, stack, occtab);

    if(scc_flags & SCC_NEG) {
      first = get_neg(r);
      cnt = get_neg_cnt(r);
      if(cnt)
	revisit_list(first, cnt, scc, max_atom, stack, occtab);
    }
  }

  return;
}

int border_rule_cnt(int atom, DEF *d, OCCTAB *occtab)
{
  int scc = d->scc;
  int cnt = d->rule_cnt;
  RULE **rules = d->rules;
  int i = 0;
  int rvalue = 0;
  
  for(i=0; i<cnt; i++) {
    RULE *r = rules[i];
    int j = 0;
    int pos_cnt = get_pos_cnt(r);
    int *pos = get_pos(r);
    int same = 0;

    while(j<pos_cnt && !same) {
      int atom2 = pos[j];
      DEF *d2 = definition(occtab, atom2);

      if(scc == d2->scc) same++;
      j++;
    }

    if(!same)
      rvalue++;
  }

  return rvalue;
}

/*
 * compute_borders -- Find border atoms that critically link SCCs together
 */

void compute_borders(OCCTAB *occtab, int max_atom)
{
  ASTACK *stack = NULL; /* Stack to be used by revisit */

  /* Revisit all atoms that have head occurrences */

  while(occtab) {
    int count = occtab->count;
    int offset = occtab->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = &(occtab->def)[i];
      int border_size = 0;

      /* Visit any unvisited atoms that have defining rules */

      if(d->rule_cnt>0 && d->visited == max_atom+1) {
	int atom2 = 0;
	int border_size = 0;
	int cnt = 0;
	ASTACK *stack2 = NULL;
	DEF *d2 = NULL;
	int number = 1; /* Start of local numbering */

	revisit(atom, d->scc, max_atom, &stack, occtab);

	/* Unwind the SCC from stack to stack2 */

	while(atom != atom2) {
	  stack = pop(&atom2, NULL, NULL, stack);
	  d2 = definition(occtab, atom2);

	  if((cnt = border_rule_cnt(atom2, d2, occtab))>0) {
	    border_size++;
	    d2->status |= MARK_BORDER;
	    if(cnt == 1) d2->status |= MARK_UNIQUE;
	  }

	  stack2 = push(atom2, 0, NULL, stack2);
	}

	while(stack2) {
          /* Produce local numbering for border atoms */

	  stack2 = pop(&atom2, NULL, NULL, stack2);
	  d2 = definition(occtab, atom2);

	  d2->border_size = border_size;
	  d2->other = (d2->status & MARK_BORDER ? number++ : 0);

	}

	/* Both stacks are now emtpy */
      }
    }
    occtab = occtab->next;
  }

  return;
}

/* ------------------------------------------------------------------------- */

void scc_revisit(int atom, int scc, int max_atom,
		 ASTACK **stack, OCCTAB *occtab);

void revisit_same(int *atoms, int cnt, int scc, int max_atom,
		  ASTACK **stack, OCCTAB *occtab)
{
  int i = 0;

  for(i=0; i<cnt; i++) {
    int atom = atoms[i];
    DEF *d = definition(occtab, atom);

    /* Revisit positively/negatively interdependent atoms in the same SCC */

    if(scc == d->scc
       && d->visited == max_atom+1)
      scc_revisit(atom, scc, max_atom, stack, occtab);
  }

  return;
}

void revisit_hidden(int *atoms, int cnt, int scc, int max_atom,
		    ASTACK **stack, OCCTAB *occtab)
{
  int i = 0;

  for(i=0; i<cnt; i++) {
    int atom = atoms[i];
    DEF *d = definition(occtab, atom);
    ATAB *a = find_atom(occtab->atoms, atom);

    /* Follow hidden atoms to SCCs in which they are defined */

    if((a->names)[atom-(a->offset)] == NULL
       && scc != d->scc
       && d->visited == max_atom+1)
      scc_revisit(atom, d->scc, max_atom, stack, occtab);
  }

  return;
}

void revisit_occurrences(int atom, int scc, int max_atom,
			 ASTACK **stack, OCCTAB *occtab)
{
  OCC *p = pbody_occs(occtab, atom);
  OCC *n = nbody_occs(occtab, atom);
  int i = 0, cnt = 0;
  RULE **rules = NULL;

  /* Positive occurrences */

  cnt = p->rule_cnt;
  rules = p->rules;

  for(i=0 ; i<cnt; i++) {
    RULE *r = rules[i];
    int head_cnt = get_head_cnt(r);
    int *heads = get_heads(r);
    int j = 0;

    if(head_cnt)
      for(j=0; j<head_cnt; j++) {
	int atom2 = heads[j];
	DEF *d2 = definition(occtab, atom2);

	if(scc != d2->scc
	   && d2->visited == max_atom+1)
	  scc_revisit(atom2, d2->scc, max_atom, stack, occtab);
	    
      }
  }

  /* Negative occurrences */

  cnt = n->rule_cnt;
  rules = n->rules;

  for(i=0 ; i<cnt; i++) {
    RULE *r = rules[i];
    int head_cnt = get_head_cnt(r);
    int *heads = get_heads(r);
    int j = 0;

    if(head_cnt)
      for(j=0; j<head_cnt; j++) {
	int atom2 = heads[j];
	DEF *d2 = definition(occtab, atom2);

	if(scc != d2->scc
	   && d2->visited == max_atom+1)
	  scc_revisit(atom2, d2->scc, max_atom, stack, occtab);
	    
      }
  }

  return;
}

void scc_revisit(int atom, int scc, int max_atom,
		 ASTACK **stack, OCCTAB *occtab)
{
  DEF *d = definition(occtab, atom);
  ATAB *a = find_atom(occtab->atoms, atom);
  int i = 0;

  d->visited = 0;

  *stack = push(atom, 0, NULL, *stack);

  for(i=0; i < d->rule_cnt; i++) {
    RULE *r = d->rules[i];
    int *first = NULL;
    int cnt = 0;

    first = get_pos(r);
    cnt = get_pos_cnt(r);
    if(cnt) {
      revisit_same(first, cnt, scc, max_atom, stack, occtab);
      revisit_hidden(first, cnt, scc, max_atom, stack, occtab);
    }

    first = get_neg(r);
    cnt = get_neg_cnt(r);
    if(cnt) {
      if(scc_flags & SCC_NEG)
	revisit_same(first, cnt, scc, max_atom, stack, occtab);
      revisit_hidden(first, cnt, scc, max_atom, stack, occtab);
    }
  }

  if((a->names)[atom-(a->offset)] == NULL)
    revisit_occurrences(atom, scc, max_atom, stack, occtab);

  return;
}

/*
 * merge_sccs -- Merge sccs that have joint hidden atoms
 */

void merge_sccs(OCCTAB *occtab, int max_atom)
{
  ASTACK *stack = NULL;   /* Stack to be used by revisit */
  ASTACK *stack2 = NULL;  /* Temporary stack for unwinding */
  OCCTAB *scan = occtab;
  
  /* Revisit all atoms that have head occurrences */

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int i = 0;

    for(i=1; i<=count; i++) {
      int atom = i+offset;
      DEF *d = &(scan->def)[i];

      /* Visit any unvisited atoms that have defining rules */

      if(d->rule_cnt>0 && d->visited == max_atom+1) {

	int atom2 = 0;
	int joint_scc = d->scc; /* Initial value to be minimized */
	int scc_size = 0;
	DEF *d2 = NULL;

	scc_revisit(atom, d->scc, max_atom, &stack, occtab);

	/* Unwind the SCC from stack to stack2 */

	while(atom != atom2) {
	  stack = pop(&atom2, NULL, NULL, stack);
	  d2 = definition(occtab, atom2);
	  int scc = d2->scc;

	  if(scc<joint_scc) joint_scc = scc;

	  stack2 = push(atom2, 0, NULL, stack2);
	  scc_size++;
	}

	while(stack2) {
          /* Join SCCs by assigning the joint SCC number */

	  stack2 = pop(&atom2, NULL, NULL, stack2);
	  d2 = definition(occtab, atom2);

	  d2->scc = joint_scc;
	  d2->scc_size = scc_size;
	}

	/* Both stacks are now emtpy */
      }
    }
    scan = scan->next;
  }

  return;
}
