/* asptranslate -- Translation-Based ASP under ASPTOOLS

   Copyright (C) 2023 Tomi Janhunen

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
 * Definitions related to acyclicity constraints
 *
 * (c) 2014-2015, 2023 Tomi Janhunen
 */

#define _ACYC_H_RCSFILE  "$RCSfile: acyc.h,v $"
#define _ACYC_H_DATE     "$Date: 2023/02/25 14:03:00 $"
#define _ACYC_H_REVISION "$Revision: 1.7 $"

extern void _version_acyc_c();

typedef struct edge {
  int node;             /* End node */
  int atom;             /* Atom labeling this edge */
  int vec;              /* Vector of atoms associated with this edge */
  struct edge *next;    /* Next edge */
} EDGE;

typedef struct node {
  int node;             /* Start node */
  int renumber;         /* For renumbering the nodes */
  int vec;              /* Vector of atoms associated with this node */
  struct edge *edges;   /* Edges starting from this node */
  struct node *next;    /* Next node in this graph */
} NODE;

typedef struct graph {
  int id;               /* Identifier */
  int node_cnt;         /* Node count */
  int edge_cnt;         /* Edge count */
  struct node *nodes;   /* Nodes of the graph */
  struct graph *next;   /* Next graph in this collection */
} GRAPH;

#define FL_ACYC_UN  1
#define FL_ACYC_BIN 2

#define STYLE_BV    6   /* QF_BV internal format */
#define STYLE_BSYM  7   /* Symbol declarations in QF_BV */
#define STYLE_DIFF  8   /* QF_IDL internal format */
#define STYLE_DSYM  9   /* Symbol declarations in QF_IDL */
#define STYLE_LP   10   /* Linear programming format */
#define STYLE_BIN  11   /* Declaration of binary variables */
#define STYLE_GEN  12   /* Declaration of general integer variables */
#define STYLE_PB   13   /* Pseudo-Boolean format */
#define STYLE_PCNT 14   /* Count constraints in Pseudo-Boolean format */

extern int base2log(int number);
extern NODE *new_node(int node, int renumber, int vec, EDGE *edges);
extern GRAPH *new_graph(int grid, NODE *nodes);

extern GRAPH *extract_acyc_graphs(ATAB *table);
int acyc_create_edge(NODE *node, int endnode, int newatom);
int acyc_find_edge(NODE *node, int endnode);
extern int count_nodes(GRAPH *graph);
NODE *acyc_find_node(int node, NODE *graph);

extern void tr_acyc_into_graph(int style, FILE *out, GRAPH *graphs);
extern int acyc_cnf_size(GRAPH *graphs, int flavor,
			 int *clause_cnt, int newatom);
extern void tr_acyc_into_cnf(int style, int flavor, FILE *out,
			     GRAPH *graphs, int weight_sum);
extern void tr_acyc_symbols(int style, FILE *out, GRAPH *graph, int symbols);
extern void tr_acyc_external(int style, FILE *out, GRAPH *graph);
extern void tr_acyc_choices(int style, FILE *out, GRAPH *graph, ATAB*table);
