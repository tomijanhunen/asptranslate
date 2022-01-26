/* lp2normal2 -- Normalizer for smodels programs (under ASPTOOLS)

   Copyright (C) 2022 Jori Bomanson / Tomi Janhunen

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
 * LP2NORMAL2 -- Normalize SMODELS programs
 *
 * (c) 2014 Jori Bomansson
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>   // for UCHAR_MAX I think
#include <assert.h>
#include <math.h>     // for pow

#include "expression.h"

/******************************************************************************
 *
 */

#define STACK_SIZE          1000
#define ENCODE(c)           ((char) (128 + (unsigned int) (c)))
#define ENCODETOINT(c)      ((int) (unsigned char) (ENCODE(c)))
#define DECODE(c)           ((char) (((unsigned int) (c)) - 128))
#define IS_ENCODED(c)       (128 <= ((unsigned int) (c)))
#define ORIGIN_IMPLICIT     (' ')
#define ORIGIN_IDENTITY     (321321)
#define ORIGIN_CONSTANT     (123123)

#define CODE1C(x)           ((unsigned int) (x))
#define CODE2C(x, y)        (CODE1C(x) + UCHAR_MAX * CODE1C(y))
#define CODE3C(x, y, z)     (CODE1C(x) + UCHAR_MAX * CODE2C(y, z))

#define CODE1(x)            (CODE1C((x)[0]))
#define CODE2(x)            (CODE2C((x)[0], (x)[1]))
#define CODE3(x)            (CODE3C((x)[0], (x)[1], (x)[2]))

#define OP_PRINT_STREAM     (stderr)
#define ERRPREFIX           "expression error: "

static int precedences[UCHAR_MAX];

static void
init_precedence()
{
  int *p  = precedences;
  int c   = 0;
  p[':']  = c;
  p[';']  = c++;
  p['=']  = c++;
  p[ENCODETOINT('o')] = c++;
  p[ENCODETOINT('a')] = c++;
  p[ENCODETOINT('n')] = c++;
  p['<']  = c;
  p['>']  = c;
  p[ENCODETOINT('<')] = c;
  p[ENCODETOINT('>')] = c;
  p[ENCODETOINT('=')] = c;
  p[ENCODETOINT('!')] = c++;
  p['+']  = c;
  p['-']  = c++;
  p['*']  = c;
  p['/']  = c++;
  //p['!']  = c;
  p['^']  = c++;
  p[ENCODETOINT('l')]  = c++;
  p['e']  = c++;
  p[ORIGIN_IMPLICIT] = c++;
}

static int
get_precedence(char c)
{
  return precedences[(int) (unsigned char) c];
}

/******************************************************************************
 * For Convenience
 */

static int
f(int *vars, EXPRESSION *self)
{
  assert(NULL != self);
  return self->eval_on_rhs(vars, self);
}

static int
g(int *vars, EXPRESSION *self)
{
  assert(NULL != self);
  return self->eval_on_lhs(vars, self);
}

static int
apply_exit(int *vars, EXPRESSION *self)
{
  fprintf(stderr, ERRPREFIX "This '%c' is not supposed to be evaluated\n",
          self->origin);
  exit(-1);
}

/******************************************************************************
 * c Operation Implementations
 */

#define BINOP(x, y) \
static int \
b_##x(int *vars, EXPRESSION *self) \
{ \
  return f(vars, self->a) y f(vars, self->b); \
}

BINOP(plus, +)
BINOP(minus, -)
BINOP(times, *)
BINOP(over, /)
BINOP(lt, <)
BINOP(gt, >)
BINOP(le, <=)
BINOP(ge, >=)
BINOP(eq, ==)
BINOP(ne, !=)
BINOP(and, &&)
BINOP(or, ||)

/******************************************************************************
 * More complex operators
 */

static int
b_power(int *vars, EXPRESSION *self)
{
  return (int) pow((double) f(vars, self->a), (double) f(vars, self->b));
}

// Not truly binary
static int
b_log(int *vars, EXPRESSION *self)
{
  return (int) log2((double) f(vars, self->b));
}

static int
b_sci(int *vars, EXPRESSION *self)
{
  return f(vars, self->a) * (int) pow(10.0, (double) f(vars, self->b));
}

/******************************************************************************
 * Variables and constants
 */

static int
z_get_variable(int *vars, EXPRESSION *self)
{
  return vars[self->constant];
}

//static int
//u_get_dynamic_variable(int *vars, EXPRESSION *self)
//{
//  return vars[g(vars, self->a)];
//}

static int
z_get_constant(int *vars, EXPRESSION *self)
{
  return self->constant;
}

/******************************************************************************
 * Hack-ish stuff
 */

//static int
//u_set_variable(int *vars, EXPRESSION *self)
//{
//  return vars[self->constant] = f(vars, self->a);
//}

static int
b_set_dynamic_variable(int *vars, EXPRESSION *self)
{
  int key = g(vars, self->a);
  assert((0 <= key) && (key < EXPRESSION_VARS_SIZE));
  return vars[key] = f(vars, self->b);
}

static int
b_cat_dec(int *vars, EXPRESSION *self)
{
  return 10 * f(vars, self->a) + f(vars, self->b);
}

static int
b_semicolon(int *vars, EXPRESSION *self)
{
  (void) f(vars, self->a);
  return f(vars, self->b);
}

static int
b_print(int *vars, EXPRESSION *self)
{
  (void) f(vars, self->a);
  int r = f(vars, self->b);
  fprintf(OP_PRINT_STREAM, "%i = ", r);
  expression_fprint(OP_PRINT_STREAM, self->b);
  fprintf(OP_PRINT_STREAM, "\n");
  return r;
}

/******************************************************************************
 * Left hand side
 */

static int
z_illegal_operator_lhs(int *vars, EXPRESSION *self)
{
  fprintf(stderr, ERRPREFIX "operator '%c' and expression \"", self->origin);
  expression_fprint(stderr, self);
  fprintf(stderr, "\" are wrongly on the left hand side of an assignment.\n");
  exit(-1);
}

static int
z_illegal_operand_lhs(int *vars, EXPRESSION *self)
{
  fprintf(stderr, ERRPREFIX "operand \"");
  expression_fprint(stderr, self);
  fprintf(stderr, "\" is wrongly on the left hand side of an assignment.\n");
  exit(-1);
}

/******************************************************************************
 * Functions relating operators to functions
 */

static expression_function
get_operator_eval_on_rhs(char c)
{
  switch(c) {
  case ':' : return b_print;
  case ';' : return b_semicolon;
  case '=' : return b_set_dynamic_variable;
  case '+' : return b_plus;
  case '-' : return b_minus;
  case '*' : return b_times;
  case '/' : return b_over;
  case '^' : return b_power;
  case '<' : return b_lt;
  case '>' : return b_gt;
  case 'e' : return b_sci;
  case ENCODE('<') : return b_le;
  case ENCODE('>') : return b_ge;
  case ENCODE('n') : /* fall through */ //return u_not;
  case ENCODE('=') : return b_eq;
  case ENCODE('!') : return b_ne;
  case ENCODE('a') : return b_and;
  case ENCODE('o') : return b_or;
  case ENCODE('l') : return b_log;
  case ORIGIN_IMPLICIT : return b_cat_dec;
  }
  fprintf(stderr, ERRPREFIX "unrecognized operator '%c'\n", c);
  exit(-1);
}

static expression_function
get_operator_eval_on_lhs(char c)
{
  switch(c) {
    default : return z_illegal_operator_lhs;
  }
}

/******************************************************************************
 * Shunting Yard
 */

static char *
squish(char *s)
{
  int n   = strlen(s);  /* remaining input length */
  int m   = 0;          /* accumulated output length */

  char *x = malloc((n + 1) * sizeof(char));

  int i;
  int inc;

  for(i = 0; s[i] != '\0'; i += inc, n -= inc) {
    int code;

    switch((n < 3 ? n : 3)) {
    case 3 :

      switch(CODE3(&s[i])) {
      case CODE3C('a', 'n', 'd') :
      case CODE3C('n', 'o', 't') :
      case CODE3C('l', 'o', 'g') :
        inc = 3;
        x[m++] = ENCODE(s[i]);
        continue;
      }
      /* fall through */

    case 2 :

      switch(CODE2(&s[i])) {
      case CODE2C('o', 'r') :
      case CODE2C('=', '=') :
      case CODE2C('!', '=') :
      case CODE2C('<', '=') :
      case CODE2C('>', '=') :
        inc = 2;
        x[m++] = ENCODE(s[i]);
        continue;
      }
    }

    inc = 1;

    if(isspace(s[i])) {
      continue;
    }

    x[m++] = s[i];
  }

  x[m] = '\0';
  return x;
}

static void
process_stacked_operator(
    int *stackcp, EXPRESSION **stackv,
    int *queuecp, EXPRESSION **queuev)
{
  assert(1 <= *stackcp);
  EXPRESSION *e = stackv[--(*stackcp)];
  assert(NULL != e);

  if(*queuecp < 2) {
    fprintf(stderr, ERRPREFIX "too few operands for '%c'\n", e->origin);
    exit(-1);
  }

  e->b = queuev[--(*queuecp)];
  e->a = queuev[*queuecp - 1];

  queuev[*queuecp - 1] = e;
}

static void
process_closing_parenthesis(
    int *stackcp, EXPRESSION **stackv,
    int *queuecp, EXPRESSION **queuev)
{
  /* pop until '(' */
  while((0 < *stackcp) && (NULL != stackv[*stackcp - 1]))
    process_stacked_operator(stackcp, stackv, queuecp, queuev);

  if(0 == *stackcp) {
    fprintf(stderr, ERRPREFIX "missing '('\n");
    exit(-1);
  }

  /* remove the left parenthesis */
  (*stackcp)--;
}

static void
process_operator_lightly(int *stackcp, EXPRESSION **stackv, char c)
{
  /* push new operator */
  EXPRESSION *e  = malloc(sizeof(EXPRESSION));
  e->origin      = c;
  e->a           = NULL;
  e->b           = NULL;
  e->eval_on_rhs = get_operator_eval_on_rhs(c);
  e->eval_on_lhs = get_operator_eval_on_lhs(c);
  stackv[(*stackcp)++] = e;
}

static void
process_operator(
    int *stackcp, EXPRESSION **stackv,
    int *queuecp, EXPRESSION **queuev,
    char c, int left_assoc)
{
  if(left_assoc) {
    left_assoc = (left_assoc ? 1 : 0);
    /* pop until a lower precedence operator is encountered */
    int p = get_precedence(c);
    while((0 < *stackcp)
        && (NULL != stackv[*stackcp - 1])
        && (p < get_precedence(stackv[*stackcp - 1]->origin) + left_assoc))
      process_stacked_operator(stackcp, stackv, queuecp, queuev);
  }

  process_operator_lightly(stackcp, stackv, c);
}

static void
process_operand(int *queuecp, EXPRESSION **queuev, char c, int origin)
{
  EXPRESSION *e  = malloc(sizeof(EXPRESSION));
  e->origin      = origin;
  e->a           = NULL;
  e->b           = NULL;

  if(isdigit(c)) {
    e->eval_on_rhs = z_get_constant;
    e->eval_on_lhs = z_illegal_operand_lhs;
    e->constant = (int) (c - '0');
  }
  else if(isalpha(c)) {
    e->eval_on_rhs = z_get_variable;
    e->eval_on_lhs = z_get_constant;
    e->constant = (int) c;
  }
  else {
    fprintf(stderr, ERRPREFIX "unkown '%c' (%u)\n", c, (unsigned int) c);
    exit(-1);
  }

  queuev[(*queuecp)++] = e;
}

/*
 * Determine if an expression is constant.
 * If this returns true, the expression does not reference variables.
 */
static int
is_constant_expression(EXPRESSION *e)
{
  return ((NULL != e) && (z_get_constant == e->eval_on_rhs));
}

/*
 * Check for errors in and simplify an expression
 */
static EXPRESSION *
postprocess_expression(EXPRESSION *e)
{
  if (NULL == e) {
    return NULL;
  }

  /* Recurse */
  e->a = postprocess_expression(e->a);
  e->b = postprocess_expression(e->b);

  /* Simplify */
  if(is_constant_expression(e->a) && is_constant_expression(e->b)) {

    e->constant    = f(NULL, e);
    e->origin      = ORIGIN_CONSTANT;
    e->eval_on_rhs = z_get_constant;
    e->eval_on_lhs = z_illegal_operand_lhs;

    free(e->a);
    free(e->b);
    e->a = NULL;
    e->b = NULL;
  }
  else if(ORIGIN_IMPLICIT == e->origin) {

    fprintf(stderr, ERRPREFIX "the string \"");
    expression_fprint(stderr, e);
    fprintf(stderr, "\" is currently interpreted as \"(");
    expression_fprint(stderr, e->a);
    fprintf(stderr, ")(");
    expression_fprint(stderr, e->b);
    fprintf(stderr, ")\" and is not allowed\n");
    exit(-1);
  }

  return e;
}

/*
 * Parse an expression out of a string expression
 */
EXPRESSION *
expression_create(char *s)
{
  char *x = squish(s);
  EXPRESSION *stackv[STACK_SIZE];
  EXPRESSION *queuev[STACK_SIZE];
  int stackc = 0;
  int queuec = 0;
  int was_operand = 0;
  int want_operand = 1;
  int i;

  if(get_precedence('*') == 0) {
    init_precedence();
  }

#ifdef DEBUG
  fprintf(stderr, "expression \"%s\", squished: \"%s\"\n", s, x);
#endif

  for(i = 0; x[i] != 0; i++) {

    int is_operand = 0;
    int allow_left = 1;   /* allow left & right associativity */
    int allow_right = 1;
    char c = x[i];

    switch (c) {

    case '(' :

      stackv[stackc++] = NULL;
      want_operand = 1;
      break;

    case ')' :

      process_closing_parenthesis(&stackc, stackv, &queuec, queuev);
      want_operand = 0;
      break;

    /* unary operators */
    case ENCODE('n') :
    case ENCODE('l') : want_operand = 1; /* fall through */

    /* unary and binary operators */
    case '+' :
    case '-' :
    case ';' :
    case ':' :

      if(want_operand) {
        /* Mimic a unary operator by adding an implicit identity operand */
        process_operand(&queuec, queuev, '0', ORIGIN_IDENTITY);
        want_operand = 0;
      } else {
        allow_right = 0;
      }
      /* fall through */

    /* binary operators */
    case '=' : allow_left = !allow_right; /* fall through */
    case '*' :
    case '/' :
    case '^' :
    case '<' :
    case '>' :
    case 'e' :
    case ENCODE('<') :
    case ENCODE('>') :
    case ENCODE('=') :
    case ENCODE('!') :
    case ENCODE('a') :
    case ENCODE('o') :

      if(want_operand) {
        fprintf(stderr, ERRPREFIX "expected an operand before '%c' in \"%s\"\n",
                c, s);
        exit(-1);
      }

      process_operator(&stackc, stackv, &queuec, queuev, c, allow_left);
      want_operand = 1;
      break;

    default :

      if(was_operand) {
        /* Combine consecutive operands with an implicit operator */
        process_operator(&stackc, stackv, &queuec, queuev, ORIGIN_IMPLICIT, 1);
      }
      process_operand(&queuec, queuev, c, (int) c);
      is_operand = 1;
      want_operand = 0;
      break;
    }

    was_operand = is_operand;
  }

  while((0 < stackc) && (NULL != stackv[stackc - 1])) {
    process_stacked_operator(&stackc, stackv, &queuec, queuev);
  }

  if(0 < stackc) {
    fprintf(stderr, ERRPREFIX "extra '('\n");
    exit(-1);
  }

  if(0 == queuec) {
    fprintf(stderr, ERRPREFIX "expected something, got \"%s\"\n", s);
    exit(-1);
  }

  if(1 < queuec) {
    fprintf(stderr, ERRPREFIX "expected a single expression, got\n");
    for(i = 0; i < queuec; i++) {
      fprintf(stderr, "\t");
      expression_fprint(stderr, queuev[i]);
      fprintf(stderr, "\n");
    }
    exit(-1);
  }

  free(x);
  return postprocess_expression(queuev[0]);
}

static int
fprint_operand_origin(FILE *out, EXPRESSION *e)
{
  int c = e->origin;
  int n = 0;

  switch(c) {
    case ORIGIN_IDENTITY :
      /* Skip */
      break; // TODO: Skip whitespace caused by the corresponding operator
    case ORIGIN_CONSTANT :
      n = fprintf(out, "%i", e->constant);
      break;
    default :
      n = (EOF == fputc(c, out) ? 0 : 1);
  }

  return n;
}

static int
fprint_operator_origin(FILE *out, EXPRESSION *e)
{
  char c = e->origin;
  int n = 0;

  if(' ' == c) {
    return n;
  }

  n += (EOF == fputc(' ', out) ? 0 : 1);
  if(IS_ENCODED(c)) {
    switch(DECODE(c)) {
      case 'a' :
        n += (EOF == fputs("and", out) ? 0 : 3);
        break;
      case 'n' :
        n += (EOF == fputs("not", out) ? 0 : 3);
        break;
      case 'o' :
        n += (EOF == fputs("or", out) ? 0 : 2);
        break;
      case 'l' :
        n += (EOF == fputs("log", out) ? 0 : 3);
        break;
      default :
        n += (EOF == fputc(DECODE(c), out) ? 0 : 1);
        n += (EOF == fputc('=', out) ? 0 : 1);
    }
  }
  else {
    n += (EOF == fputc(c, out) ? 0 : 1);
  }
  n += (EOF == fputc(' ', out) ? 0 : 1);

  return n;
}

int
expression_fprint(FILE *out, EXPRESSION *e)
{
  int n = 0;

  if(NULL == e->a) {
    n = fprint_operand_origin(out, e);
  }
  else {
    // TODO: Take better care of EOFs
    n += fprintf(out, "(");
    n += expression_fprint(out, e->a);
    n += fprint_operator_origin(out, e);
    n += expression_fprint(out, e->b);
    n += fprintf(out, ")");
  }

  return n;
}

void
expression_free(EXPRESSION *e)
{
  if(NULL != e->a) expression_free(e->a);
  if(NULL != e->b) expression_free(e->b);
  free(e);
}

int
expression_eval(EXPRESSION *e, int *vars)
{
  return e->eval_on_rhs(vars, e);
}
