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
 * acyc.c -- Routines related with acyclicity constraints
 *
 * (c) 2014 Tomi Janhunen
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <limits.h>

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

#include "acyc.h"

void _version_acyc_c()
{
  _version("$RCSfile: acyc.c,v $",
           "$Date: 2021/05/27 11:13:13 $",
           "$Revision: 1.11 $");
}

int base2log(int n)
{
  int result = 0;

  n--;
  while(n)
    n=n/2, result++;
  return result;
}

EDGE *new_edge(int end, int atom, int vec)
{
  EDGE *new = (EDGE *)malloc(sizeof(EDGE));
  new->node = end;
  new->atom = atom;
  new->vec = vec;
  new->next = NULL;

  return new;
}

NODE *new_node(int node, int renumber, int vec, EDGE *edges)
{ 
  NODE *new = (NODE *)malloc(sizeof(NODE));
  new->node = node;
  new->renumber = renumber;
  new->vec = vec;
  new->edges = edges;
  new->next = NULL;

  return new;
}

GRAPH *new_graph(int grid, NODE *nodes)
{ 
  GRAPH *new = (GRAPH *)malloc(sizeof(GRAPH));
  new->id = grid;
  new->node_cnt = 0;
  new->edge_cnt = 0;
  new->nodes = nodes;
  new->next = NULL;

  return new;
}

NODE *insert_edge(int atom, int node1, int node2, NODE *graph)
{
  NODE *prev = NULL;
  NODE *scan = graph;
  EDGE *prev2 = NULL;
  EDGE *scan2 = NULL;

  while(scan && (scan->node !=node1)) {
    prev = scan;
    scan = scan->next;
  }

  if(scan) { /* Insert it to the list of successors */
    prev2 = NULL;
    scan2 = scan->edges;

    while(scan2 && (scan2->node !=node2)) {
      prev2 = scan2;
      scan2 = scan2->next;
    }

    if(scan2) /* An earlier occurrence was found */
      return graph;
    else {
      EDGE *newedge = new_edge(node2, atom, 0);
      newedge->next = NULL;
      if(prev2)
	prev2->next = newedge;
    }

  } else { /* Create a new entry */
    EDGE *newedge = new_edge(node2, atom, 0);
    NODE *new = new_node(node1, 0, 0, newedge);

    if(prev)
      prev->next = new;
    else
      graph = new;
  }

  return graph;
}

int acyc_create_edge(NODE *node, int end, int newatom)
{
  EDGE *prev = NULL;
  EDGE *edge = node->edges;

  while(edge && (edge->node != end)) {
    prev = edge;
    edge = edge->next;
  }

  if(!edge) {
    edge = new_edge(end, newatom++, 0);
    if(prev)
      prev->next = edge;
    else
      node->edges = edge;
  }

  return newatom;
}

int acyc_find_edge(NODE *node, int end)
{
  EDGE *edge = node->edges;

  while(edge && edge->node != end)
    edge = edge->next;

  return edge ? edge->atom : 0;
}

int count_nodes(GRAPH *graph)
{
  int cnt = 0;

  while(graph) {
    NODE *node = graph->nodes;
    int saved = cnt;
    int ecnt = 0;

    while(node) {
      EDGE *edge = node->edges;
      
      node->renumber = ++cnt;

      while(edge) {
	ecnt++;
	edge = edge->next;
      }

      node = node->next;
    }

    graph->node_cnt = cnt - saved;
    graph->edge_cnt = ecnt;
    graph = graph->next;
  }

  return cnt;
}

int allocate_vectors(NODE *graph, int flavor, int len, int newatom)
{
  NODE *node = graph;

  while(node) {
    EDGE *edge = node->edges;

    node->vec = newatom;
    newatom += len;
      
    if(flavor == FL_ACYC_BIN)
      while(edge) {
	edge->vec = newatom;
	newatom += len;

	edge = edge->next;
      }

    node = node->next;
  }

  return newatom;
}

NODE *acyc_find_node(int node, NODE *graph)
{
  NODE *scan = graph;
  
  while(scan) {
    if(scan->node == node)
      return scan;
    scan = scan -> next;
  }

  return NULL;
}

void print_nodes(int style, FILE *out, NODE *node)
{
  while(node) {
    EDGE *edge = node->edges;
    int cnt = 0;

    while(edge) {
      cnt++;
      edge = edge->next;
    }
    switch(style) {
    case STYLE_DIMACS:
      fputs("c ", out);
      break;
    case STYLE_PB:
      fputs("* ", out);
      break;
    default:
      fputs("% ", out);
      break;
    }
    fprintf(out, "node %i %i\n", node->renumber, cnt);

    node = node->next;
  }

  return;
}

void print_edges(int style, FILE *out, NODE *nodes)
{
  NODE *scan = nodes;

  while(scan) {
    EDGE *edge = scan->edges;

    while(edge) {
      NODE *orig = acyc_find_node(edge->node, nodes);
      if(orig) {
	switch(style) {
	case STYLE_DIMACS:
	  fputs("c ", out);
	  break;
	case STYLE_PB:
	  fputs("* ", out);
	  break;
	default:
	  fputs("% ", out);
	  break;
	}
	fprintf(out, "arc %s%i %i %i\n", style == STYLE_PB ? "x" : "",
		edge->atom, scan->renumber, orig->renumber);
      }
      edge = edge->next;
    }

    scan = scan->next;
  }

  return;
}

GRAPH *extract_acyc_graphs(ATAB *table)
{
  int nodecnt = 0;
  GRAPH *graphs = NULL;

  while(table) {
    int count = table->count;
    int offset = table->offset;
    SYMBOL **names = table->names;
    int i = 0;
  
    for(i=1; i<=count; i++) {
      int atom = i+offset;
      SYMBOL *name = names[i];
      int grid = 0;              /* Component id */
      int atom1 = 0, atom2 = 0;  /* Original dependent atoms */
      
      if(name && name->name) {
	if(strncmp(name->name, "_acyc_", 6)==0)
	  if(sscanf(name->name, "_acyc_%i_%i_%i",
		    &grid, &atom1, &atom2) == 3) {
	    GRAPH *prev = NULL;
	    GRAPH *scan = graphs;

	    while(scan && scan->id != grid) {
	      prev = scan;
	      scan = scan->next;
	    }
	    if(scan)
	      scan->nodes = insert_edge(atom, atom1, atom2, scan->nodes);
	    else {
	      GRAPH *new = (GRAPH *)malloc(sizeof(GRAPH));
	      new->id = grid;
	      new->node_cnt = 0;
	      new->nodes = insert_edge(atom, atom1, atom2, NULL);
	      new->next = NULL;

	      if(prev)
		prev->next = new;
	      else
		graphs = new;
	    }
	  }
      }
    }
    table = table->next;
  }

  return graphs;
}


void tr_acyc_into_graph(int style, FILE *out, GRAPH *graphs)
{
  int nodecnt = count_nodes(graphs);
  GRAPH *scan = graphs;

  switch(style) {
  case STYLE_DIMACS:
    fprintf(out, "c graph %i\n", nodecnt);
    break;
  case STYLE_PB:
    fprintf(out, "* graph %i\n", nodecnt);
    break;
  default:
    fprintf(out, "%% The graph has %i nodes:\n", nodecnt);
  }

  while(scan) {
    NODE *nodes = scan->nodes;

    print_nodes(style, out, nodes);
    scan = scan->next;
  }

  scan = graphs;

  while(scan) {
    NODE *nodes = scan->nodes;
    
    print_edges(style, out, nodes);
    
    scan = scan->next;
  }

  switch(style) {
  case STYLE_DIMACS:
    fprintf(out, "c endgraph\n");
    break;
  case STYLE_PB:
    fprintf(out, "* endgraph\n");
    break;
  default:
    break;
  }

  return;
}

int acyc_cnf_size(GRAPH *graph, int flavor, int *clause_cnt, int newatom)
{
  (void) count_nodes(graph);

  while(graph) {
    int bits = 0;
    
    if(flavor == FL_ACYC_BIN)
      bits = base2log(graph->node_cnt+2);
    else
      bits = graph->node_cnt;

    newatom = allocate_vectors(graph->nodes, flavor, bits, newatom);

    if(flavor == FL_ACYC_BIN)
      *(clause_cnt) += (6*bits-2)*(graph->edge_cnt);
    else
      *(clause_cnt) += 2*bits*(graph->edge_cnt);

    graph = graph->next;
  }

  return newatom;
}

void tr_edge_un_cnf(int style, FILE *out, int weight_sum,
		    int grid, int xnode, int ynode, int bits,
	            int xvec, int yvec, int lvec, int acyc)
{
  int i = 0;

  if(style == STYLE_READABLE) {
    int len = strlen("_acyc___")+3*log(INT_MAX)+1;
    char *acycname = (char *)malloc(len);

    sprintf(acycname, "_acyc_%i_%i_%i", grid, xnode, ynode);

    fprintf(out, "%% Primitive _lt_%i_%i with %i values:\n",
	    xnode, ynode, bits);

    fprintf(out, "-_one_%i_%i | -%s", bits-1, xnode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);
    fprintf(out, "_one_0_%i | -%s", ynode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);

    for(i=1; i<bits; i++) {
      fprintf(out, "_one_%i_%i | -_one_%i_%i | -%s",
	      i-1, xnode, i, xnode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
      fprintf(out, "_one_%i_%i | _one_%i_%i | -_one_%i_%i | -%s",
	      i, ynode, i, xnode, i-1, xnode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
    }

  } else if(style == STYLE_DIMACS) {

    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "%i -%i 0\n", yvec, acyc);
    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "-%i -%i 0\n", xvec+bits-1, acyc);

    for(i=1; i<bits; i++) {
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "%i -%i -%i 0\n", xvec+i-1, xvec+i, acyc);
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "%i %i -%i -%i 0\n", yvec+i, xvec+i, xvec+i-1, acyc);
    }
  }

  return;
}

void tr_edge_bin_cnf(int style, FILE *out, int weight_sum,
		     int grid, int xnode, int ynode, int bits,
		     int xvec, int yvec, int lvec, int acyc)
{
  int i = 0;

  if(style == STYLE_READABLE) {
    int len = strlen("_acyc___")+3*log(INT_MAX)+1;
    char *acycname = (char *)malloc(len);

    sprintf(acycname, "_acyc_%i_%i_%i", grid, xnode, ynode);

    fprintf(out, "%% Primitive _lt_%i_%i with %i bits:\n",
	    xnode, ynode, bits);

    fprintf(out, "_lt_0_%i_%i | _one_0_%i | -_one_0_%i | -%s",
	    xnode, ynode, xnode, ynode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);
    fprintf(out, "-_lt_0_%i_%i | -_one_0_%i | -%s",
	    xnode, ynode, xnode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);
    fprintf(out, "-_lt_0_%i_%i | _one_0_%i | -%s",
	    xnode, ynode, ynode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);

    for(i=1; i<bits; i++) {
      fprintf(out, "_lt_%i_%i_%i | _one_%i_%i | -_one_%i_%i | -%s",
	      i, xnode, ynode, i, xnode, i, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
      fprintf(out,
        "_lt_%i_%i_%i | _one_%i_%i | _one_%i_%i | _lt_%i_%i_%i | -%s",
	i, xnode, ynode, i, xnode, i, ynode, i-1, xnode, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
      fprintf(out,
        "_lt_%i_%i_%i | -_one_%i_%i | -_one_%i_%i | _lt_%i_%i_%i | -%s",
	i, xnode, ynode, i, xnode, i, ynode, i-1, xnode, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);

      fprintf(out, "-_lt_%i_%i_%i | -_one_%i_%i | _one_%i_%i | -%s",
	      i, xnode, ynode, i, xnode, i, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
      fprintf(out, "-_lt_%i_%i_%i | -_one_%i_%i | _lt_%i_%i_%i | -%s",
	      i, xnode, ynode, i, xnode, i-1, xnode, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
      fprintf(out, "-_lt_%i_%i_%i | _one_%i_%i | _lt_%i_%i_%i | -%s",
	      i, xnode, ynode, i, ynode, i-1, xnode, ynode, acycname);
      if(weight_sum)
	fprintf(out, " = %i.\n", weight_sum);
      else
	fputs(".\n", out);
    }

    fprintf(out, "_lt_%i_%i_%i | -%s", bits-1, xnode, ynode, acycname);
    if(weight_sum)
      fprintf(out, " = %i.\n", weight_sum);
    else
      fputs(".\n", out);

  } else if(style == STYLE_DIMACS) {

    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "%i %i -%i -%i 0\n", lvec, xvec, yvec, acyc);
    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "-%i -%i -%i 0\n", lvec, xvec, acyc);
    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "-%i %i -%i 0\n", lvec, yvec, acyc);

    for(i=1; i<bits; i++) {
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "%i %i -%i -%i 0\n",
	      lvec+i, xvec+i, yvec+i, acyc);
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "%i %i %i %i -%i 0\n",
	      lvec+i, xvec+i, yvec+i, lvec+i-1, acyc);
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "%i -%i -%i %i -%i 0\n",
	      lvec+i, xvec+i, yvec+i, lvec+i-1, acyc);

      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "-%i -%i %i -%i 0\n",
	      lvec+i, xvec+i, yvec+i, acyc);
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "-%i -%i %i -%i 0\n",
	      lvec+i, xvec+i, lvec+i-1, acyc);
      if(weight_sum)
	fprintf(out, "%i ", weight_sum);
      fprintf(out, "-%i %i %i -%i 0\n",
	      lvec+i, yvec+i, lvec+i-1, acyc);
    }

    if(weight_sum)
      fprintf(out, "%i ", weight_sum);
    fprintf(out, "%i -%i 0\n", lvec+bits-1, acyc);
 }

  return;
}

void tr_nodes_into_cnf(int style, int flavor, FILE *out,
		       int grid, NODE *graph, int bits, int weight_sum)
{
  NODE *node = graph;

  while(node) {
    EDGE *edge = node->edges;

    while(edge) {
      NODE *end = acyc_find_node(edge->node, graph);

      switch(flavor) {
      case FL_ACYC_UN:
	tr_edge_un_cnf(style, out, weight_sum,
                       grid, node->node, edge->node, bits,
		       node->vec, end->vec, edge->vec, edge->atom);
	break;

      case FL_ACYC_BIN:
	tr_edge_bin_cnf(style, out, weight_sum,
			grid, node->node, edge->node, bits,
			node->vec, end->vec, edge->vec, edge->atom);
	break;

      default:
	fprintf(stderr, "acyc: unsupported flavor %i!\n", flavor);
	exit(-1);
      }

      edge = edge->next;
    }

    node = node->next;
  }

  return;
}

void tr_acyc_into_cnf(int style, int flavor, FILE *out,
		      GRAPH *graph, int weight_sum)
{
  while(graph) {
    int bits = 0;

    if(flavor == FL_ACYC_BIN)
      bits = base2log(graph->node_cnt+2);
    else
      bits = graph->node_cnt;

    tr_nodes_into_cnf(style, flavor, out, graph->id,
		      graph->nodes, bits, weight_sum);

    graph = graph->next;
  }

  return;
}

/*
 * tr_acyc_symbols -- Declare the atoms related with acyclicity check
 */

void tr_acyc_symbols(int style, FILE *out, GRAPH *graph)
{
  GRAPH *sg = graph;

  while(sg) {
    int grid = sg->id;
    NODE *node = sg->nodes;
    
    while(node) {
      EDGE *edge = node->edges;

      while(edge) {
	switch(style) {
	case STYLE_READABLE:
	  fprintf(out, "%% _%i = _acyc_%i_%i_%i\n",
		  edge->atom, grid, node->node, edge->node);
	  break;
	case STYLE_SMODELS:
	  fprintf(out, "%i _acyc_%i_%i_%i\n",
		  edge->atom, grid, node->node, edge->node);
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

/*
 * tr_acyc_external -- Deaclare acyclicity atoms as externals
 */

void tr_acyc_external(int style, FILE *out, GRAPH *graph)
{
  GRAPH *sg = graph;

  if(style == STYLE_READABLE)
    fprintf(out, "{ ");

  while(sg) {
    int grid = sg->id;
    NODE *node = sg->nodes;
    
    while(node) {
      EDGE *edge = node->edges;

      while(edge) {

	switch(style) {
	case STYLE_READABLE:
	  fprintf(out, "_acyc_%i_%i_%i", grid, node->node, edge->node);
	  break;
	case STYLE_SMODELS:
	  fprintf(out, "%i\n", edge->atom);
	  break;
	}
	edge = edge->next;
	if(edge && style == STYLE_READABLE)
	  fputs(", ", out);
      }
      node = node->next;
      if(node && style == STYLE_READABLE)
	fputs(", ", out);
    }
    sg = sg->next;
    if(sg && style == STYLE_READABLE)
      fputs(", ", out);
  }

  if(style == STYLE_READABLE)
    fprintf(out, " }.\n\n");

  return;
}

/*
 * tr_acyc_choices -- Choice rules for acyclicity atoms
 */

void tr_acyc_choices(int style, FILE *out,  GRAPH *graph, ATAB *table)
{
  GRAPH *sg = graph;

  while(sg) {
    int grid = sg->id;
    NODE *node = sg->nodes;
    
    while(node) {
      EDGE *edge = node->edges;

      while(edge) {

	switch(style) {
	case STYLE_READABLE:
	  fprintf(out, "{ _acyc_%i_%i_%i } :- ", grid, node->node, edge->node);
	  write_atom(style, out, edge->node, table);
	  fputs(".\n", out);
	  break;
	case STYLE_SMODELS:
	  fprintf(out, "3 1 %i 1 0 %i\n", edge->atom, edge->node);
	  break;
	}

	edge = edge->next;
      }
      node = node->next;
    }
    sg = sg->next;
  }

  if(style == STYLE_READABLE)
    fprintf(out, "\n");

  return;
}

