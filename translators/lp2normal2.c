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
 * (c) 2009-2010 Tomi Janhunen, 2013-2015 Jori Bomanson
 *
 * Main program and routines for rule level translation
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <libgen.h>
#include <limits.h>
#include <math.h>
#include <time.h>
#include <unistd.h>
#include <inttypes.h>   /* for uint64_t */
#include <ctype.h>      /* for isdigit */

#include "version.h"
#include "symbol.h"
#include "atom.h"
#include "rule.h"
#include "io.h"

/* Configuration and includes specific to this project */

#define DEBUG_WQ                  ((DEBUG) && 0)
#define DEBUG_WQ_CNT              ((DEBUG) && 0)
#define DEBUG_DIV                 ((DEBUG) && 0)
#define DEBUG_OPT_EMPTY           ((DEBUG) && 0)

#include "prime.h"
#include "condflags.h"

#include "intarray.h"

#include "common.h"
#include "args.h"
#include "litint.h"
#include "unarysort.h"
#include "simplification.h"
#include "robdd.h"
#include "plan.h"
#include "implyaux.h"

/* Configuration specific to this source file */

#define ORDER_DESCENDING          0
#define ORDER_ASCENDING           1

#define USE_WRONG_BUT_OK_DIVISOR_COST_ESTIMATE  0

#define SYMBOL_MAX_LEN            512

#define BACKPROPAGATE_STATUSES    1

#define ERROR_ON_MISSING_CH_HEAD  0

void _version_lp2normal2_c()
{
  fprintf(stderr, "%s: version information:\n", program_name);
  _version("$RCSfile: lp2normal2.c,v $",
	   "$Date: 2021/05/27 10:42:49 $",
	   "$Revision: 1.14 $");
  _version_atom_c();
  _version_input_c();
  _version_rule_c();
  _version_symbol_c();
}

void short_usage()
{
  FILE *f = stdout;
  fprintf(f, "\n");
  fprintf(f, "usage:   %s <options> [<file>]\n", program_name);
  fprintf(f, "\n");
  fprintf(f, "Basic Options:\n");
  fprintf(f, "   -h or --help[=(1|2)] -- Print [2=long] help message\n");
  fprintf(f, "   --version -- Print version information\n");
  fprintf(f, "   -v  -- Verbose mode (human readable)\n");
  fprintf(f, "   -r  -- Raw translation without simplification\n");
  fprintf(f, "   -R  -- Do only what is omitted in -r\n");
  fprintf(f, "   -s<seed> -- Set the seed for drawing random numbers\n");
  fprintf(f, "\n");
  fprintf(f, "Choice Rule Options:\n");
  fprintf(f, "   -k  -- Keep choice rules\n");
  fprintf(f, "   -e  -- Make atoms in bodyless choice rules external\n");
  fprintf(f, "   -E  -- Treat external atoms as one choice rule\n");
  fprintf(f, "\n");
  fprintf(f, "Cardinality Rule Options:\n");
  fprintf(f, "   -ck or -kc -- Keep as is\n");
  fprintf(f, "   -cR -- Keep after simplification\n");
  fprintf(f, "   -sc -- Shuffle body literals\n");
  fprintf(f, "   -cc -- Use an automatically chosen translation\n");
  fprintf(f, "   -ca -- Sum with a sequence of adders\n");
  fprintf(f, "   -cb -- Use a binary translation\n");
  fprintf(f, "   -cu -- Use a unary translation\n");
  fprintf(f, "   -ct -- Totalize\n");
  fprintf(f, "   -ch -- Sort with an odd-even merge-sorter\n");
  fprintf(f, "   -cs -- Select with mergers\n");
  fprintf(f, "   -cn -- Count sequentially in unary\n");
  fprintf(f, "\n");
  fprintf(f, "Weight Rule Options:\n");
  fprintf(f, "   -wk or -kw -- Keep as is\n");
  fprintf(f, "   -wR -- Keep after simplification\n");
  fprintf(f, "   -wm -- Decompose into bits\n");
  fprintf(f, "   -ws -- Stretch to a cardinality rule by repetition\n");
  fprintf(f, "   -wa -- Sum with a sequence of adders\n");
  fprintf(f, "   -wu -- Sum in a mixed radix base with mergers\n");
  fprintf(f, "   -wq -- Sum in a mixed radix base with shared mergers\n");
  fprintf(f, "   -we -- Do an exponentially sized case analysis\n");
  fprintf(f, "   -wb -- Check with a reduced ordered BDD\n");
  fprintf(f, "   -wz -- Count sequentially in unary\n");
  fprintf(f, "\n");
  fprintf(f, "Optimization Rule Options:\n");
  fprintf(f, "   -ok or ko -- Keep as is\n");
  fprintf(f, "   -om -- Merge all into one lexicographically\n");
  fprintf(f, "   -ob -- Optimize the sum in binary with a weight rule\n");
  fprintf(f, "   -oqn -- Optimize the sum in a mixed radix base\n");
  fprintf(f, "   -ox -- Optimize the sum in unary\n");
  fprintf(f, "   -od<bound> -- Turn into a weight integrity rule\n");
  fprintf(f, "\n");
}

void long_usage()
{
  FILE *f = stdout;
  fprintf(f, "\n");
  fprintf(f, "usage:   %s <options> [<file>]\n", program_name);
  fprintf(f, "\n");
  fprintf(f, "General Options:\n");
  fprintf(f, "\n");
  fprintf(f, "   -h or --help[=(1|2)] -- Print [2=long] help message\n");
  fprintf(f, "   --version -- Print version information\n");
  fprintf(f, "   -v  -- Verbose mode (human readable)\n");
  fprintf(f, "   -r  -- Raw translation without simplification\n");
  fprintf(f, "   -R  -- Do only what is omitted in -r\n");
  fprintf(f, "   -s<seed> -- Set the seed for drawing random numbers\n");
  fprintf(f, "   -d(l|u)+<bound>\n");
  fprintf(f, "       -- Give soft bounds to radices in -wu, -wq, -oq\n");
  fprintf(f, "          l -- preferring that <bound> <= any radix\n");
  fprintf(f, "          u -- preferring that <bound> >= any radix\n");
  fprintf(f, "   <option>-if <condition>\n");
  fprintf(f, "       -- Apply <option> if <condition> is met, where\n");
  fprintf(f, "          <option>    -- specifies a translation\n");
  fprintf(f, "          <condition> -- is expressed in terms of\n");
  fprintf(f, "               n -- the number of body literals\n");
  fprintf(f, "               k -- the bound\n");
  fprintf(f, "               w -- the sum of all weights\n");
  //fprintf(f, "         (NYI) a -- an estimate of created atom count\n");
  //fprintf(f, "         (NYI) r -- an estimate of created rule count\n");
  fprintf(f, "               d -- call depth starting from 0\n");
  fprintf(f, "          ... using + - * ^ / < > = ; ( )\n");
  fprintf(f, "                    <= >= != == 0-9 and or not log\n");
  fprintf(f, "          NOTE: For each rule, only the first satisfied\n");
  fprintf(f, "                option specific to its type is used\n");
  fprintf(f, "\n");
  fprintf(f, "Choice Rule Options:\n");
  fprintf(f, "\n");
  fprintf(f, "   -k  -- Keep choice rules\n");
  fprintf(f, "   -e  -- Make atoms in bodyless choice rules external\n");
  fprintf(f, "   -E  -- Treat external atoms as one choice rule\n");
  fprintf(f, "   --aux-choice=(yes|no)\n");
  fprintf(f, "       -- Do or do not use choices on auxiliary atoms\n");
  fprintf(f, "\n");
  fprintf(f, "Cardinality Rule Options:\n");
  fprintf(f, "\n");
  fprintf(f, "   -ck or -kc -- Keep as is\n");
  fprintf(f, "   -cR -- Keep after simplification\n");
  fprintf(f, "   -sc -- Shuffle body literals\n");
  /*fprintf(f, "          ... and then use -cc / -c.*\n");*/
  fprintf(f, "   -cc -- Use an automatically chosen translation\n");
  fprintf(f, "   -ca -- Sum with a sequence of adders\n");
  fprintf(f, "   -cb -- Use a binary translation\n");
  fprintf(f, "   -cu -- Use a unary translation\n");
  fprintf(f, "   -cn -- Count sequentially in unary\n");
  fprintf(f, "   -c(h|t)(w|e)* -- Sort with mergers\n");
  fprintf(f, "          h -- using odd-even mergers\n");
  fprintf(f, "          t -- using \"totalizer\" mergers\n");
  fprintf(f, "          w -- by sorting pairwise sorted pairs\n");
  fprintf(f, "          e -- by splitting input along powers of two\n");
  fprintf(f, "   -cs(o|a)? -- Select with mergers\n");
  fprintf(f, "          o -- by OR'ing 2 mirrored selectors\n");
  fprintf(f, "          a -- by AND'ing 2 mirrored selectors\n");
  fprintf(f, "          ... using -cc / -c(c|n|x|t).*\n");
  fprintf(f, "\n");
  fprintf(f, "Weight Rule Options:\n");
  fprintf(f, "\n");
  fprintf(f, "   -wk or -kw -- Keep as is\n");
  fprintf(f, "   -wR -- Keep after simplification\n");
  fprintf(f, "   -wm -- Decompose into bits\n");
  /*fprintf(f, "          ... and then use -wq / -w.*\n");*/
  fprintf(f, "   -wp(a|d|r) -- Order body literals by weights\n");
  fprintf(f, "          a -- in ascending order\n");
  fprintf(f, "          d -- in descending order\n");
  fprintf(f, "          r -- randomly\n");
  /*fprintf(f, "          ... and then use -wq / -w.*\n");*/
  fprintf(f, "   -ws -- Stretch to a cardinality rule by repetition\n");
  fprintf(f, "          ... and then use -cc / -c.*\n");
  fprintf(f, "   -we -- Do an exponentially sized case analysis\n");
  fprintf(f, "   -wb -- Check with a reduced ordered BDD\n");
  fprintf(f, "   -wz -- Count sequentially in unary\n");
  fprintf(f, "   -wa -- Sum with a sequence of adders\n");
  fprintf(f, "   -wu -- Sum in a mixed radix base with mergers\n");
  fprintf(f, "          ... using -ws / -w(s|b|z)\n");
  fprintf(f, "   -wq(i|s|p)*\n");
  fprintf(f, "       -- Sum in a mixed radix base with shared mergers\n");
  fprintf(f, "          i -- almost independently with little sharing\n");
  fprintf(f, "          s -- without a preliminary grouping phase\n");
  fprintf(f, "          p -- and print a dot file to standard error\n");
  fprintf(f, "          ... using -cc / -c(c|n|x|t|y).*\n");
  fprintf(f, "\n");
  fprintf(f, "Optimization Rule Options:\n");
  fprintf(f, "\n");
  fprintf(f, "   -ok or ko -- Keep as is\n");
  fprintf(f, "   -om -- Merge all into one lexicographically\n");
  /*fprintf(f, "          ... and then use -ok / -o.*\n");*/
  fprintf(f, "   -ob -- Optimize the sum in binary with a weight rule\n");
  fprintf(f, "          ... using -wq / -w.*\n");
  fprintf(f, "   -oq(n|h)(M|i|s|p)*\n");
  fprintf(f, "       -- Optimize the sum in a mixed radix base\n");
  fprintf(f, "          n -- using negation to impose uniqueness\n");
  fprintf(f, "          h -- using a non-unique representation\n");
  fprintf(f, "          M -- and write the result in many statements\n");
  fprintf(f, "          * -- see -wq\n");
  fprintf(f, "   -ox(u)? -- Optimize the sum in unary\n");
  fprintf(f, "          u -- using only unit weights\n");
  fprintf(f, "          ... using -ws / -w(s|b|z)\n");
  fprintf(f, "   -o(l|u)+(s)?<bound> -- Give bounds to -ox\n");
  fprintf(f, "          l -- s.t. <bound> <= any optimization value\n");
  fprintf(f, "          u -- s.t. <bound> >= any optimization value\n");
  fprintf(f, "          s -- assume the bound without enforcing it\n");
  fprintf(f, "   -of(%%o|%%i|%%a|%%w|[^%%])*\n");
  fprintf(f, "       -- Specify a naming format for added atoms\n");
  fprintf(f, "          %%o -- statement number\n");
  fprintf(f, "          %%i -- index within statement\n");
  fprintf(f, "          %%a -- atom number\n");
  fprintf(f, "          %%w -- weight\n");
  fprintf(f, "   -od<bound> -- Turn into a weight integrity rule\n");
  fprintf(f, "\n");
  fprintf(f, "Notes:\n");
  fprintf(f, "\n");
  fprintf(f, "   * The default command line is\n");
  fprintf(f, "     lp2normal2 -cc -wq --aux-choice=no\n");
  fprintf(f, "\n");
  fprintf(f, "   * Strings of the form \"... .* <x> / <y>\" denote\n");
  fprintf(f, "     that the option being described depends on choices\n");
  fprintf(f, "     between options that match the pattern <y>, and\n");
  fprintf(f, "     that by default <x> is considered to be chosen\n");
  fprintf(f, "\n");
  fprintf(f, "   * These dependencies are mostly transitive with the\n");
  fprintf(f, "     exception that the combinations -wu -ws and\n");
  fprintf(f, "     -ox -ws depend only on -c(c|n|x|t|y).*\n");
  fprintf(f, "\n");
}

void normalize_program(ARGS *args, RULE *program);

RULE *extract_rules_by_type(RULE **program, int type);

void merge_and_normalize_optimize_statements(ARGS *args, RULE *statements);

int produce_atom_with_status(ATAB *table, int mask, int *newatom);

void normalize_input(ARGS *args);

void output_unary_weight_sorter(ARGS *args, int bound, int *res,
                                int tot_cnt, int *mix, int *weight,
                                int *startatom);

int main(int argc, char **argv)
{
  char *file = NULL;
  FILE *in = NULL;
  FILE *out = stdout;
  RULE *program = NULL;
  RULE *optimize_statements = NULL;
  char *optimize_format = "";
  int optimize_lb = 0, optimize_ub = INT_MAX;
  int radix_lb = 0, radix_ub = INT_MAX;

  ATAB *table = NULL;       /* For the original program */

  /* Conditional flavors for cardinalities, weights, and optimize statements */

  CONDFLAGS *condmflavors = condflags_create();
  CONDFLAGS *condcflavors = condflags_create();
  CONDFLAGS *condwflavors = condflags_create();
  CONDFLAGS *condoflavors = condflags_create();

  int seed = 0;
  int size = 0, number = 0;

  int option_help = 0;
  int option_version = 0;
  int option_verbose = 0; 
  int option_noexternal = 0;
  int which = 0;
  int error = 0;
  uint64_t flavors = 0;
  int i = 0;
  int have_cond = 0;

  program_name = argv[0];

  /* Process options */

  for(which=1; which<argc; which+=1 + have_cond) {
    char *arg       = argv[which];
    char *condition = "1";
    size_t n        = strlen(arg);
    int cond_cnt    = 0;  /* progress counter */

    /* Process conditional aspects */

    have_cond = ((3 < n) && (strcmp(&arg[n - 3], "-if") == 0));
    if(have_cond) {

      if(which + 1 < argc)
        condition = argv[which + 1];
      else {
        error = -2;
        fprintf(stderr, "%s: missing a condition for %s\n",
                program_name, arg);
        error = -2;
      }

      arg[n - 3]  = '\0';
      cond_cnt = condflags_size(condmflavors)
               + condflags_size(condcflavors)
               + condflags_size(condwflavors)
               + condflags_size(condoflavors);
    }

      /* ---- General ---- */

    if(strcmp(arg, "-h") == 0
       || strcmp(arg, "--help") == 0
       || strcmp(arg, "--help=1") == 0)
      option_help = -1;
    else if(strcmp(arg, "--help=2") == 0)
      option_help = -2;
    else if(strcmp(arg, "--version") == 0)
      option_version = -1;
    else if(strcmp(arg, "-v") == 0)
      option_verbose = -1;
    else if(strcmp(arg, "-r") == 0)
      flavors |= FL_RAW;
    else if(strcmp(arg, "-R") == 0)
      flavors |= FL_ANTIRAW;
    else if((strncmp(arg, "-s", 2) == 0) && !(strcmp(arg, "-sc") == 0))
      seed = atoi(arg+2);
    else if((strncmp(arg, "-dl", 3) == 0) || (strncmp(arg, "-du", 3) == 0)) {

      int lower = 0, upper = 0;

      for(i = 2; !error && (arg[i] != '\0') && !isdigit(arg[i]); i++)
        if(arg[i] == 'l')
          lower = 1;
        else if(arg[i] == 'u')
          upper = 1;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -2;
        }

      if(isdigit(arg[i])) {
        int bound = atoi(&arg[i]);
        if(lower) 
          radix_lb = bound;
        if(upper)
          radix_ub = bound;
      } else {
        fprintf(stderr, "%s: -d%c must end in <bound>\n",
                program_name, arg[2]);
        error = -2;
      }

    }

      /* ---- Choices ---- */

    else if(strcmp(arg, "-k") == 0)
      flavors |= FL_KEEP_CH;
    else if(strcmp(arg, "-e") == 0)
      flavors |= FL_CH_EXTERNAL;
    else if(strcmp(arg, "-E") == 0)
      option_noexternal = 1;
    else if(strncmp(arg, "--aux-choice=", 13) == 0) {

      char *argarg = arg + 13;
      if(strcmp(argarg, "yes") == 0) {
        flavors |= FL_CH_AUX;
      } else if(strcmp(argarg, "no") == 0) {
        /* Do nothing */;
      } else {
        fprintf(stderr, "%s: unkown parameter %s in option %s\n",
                program_name, argarg, arg);
        error = -2;
      }

    }

      /* ---- Cardinalities ---- */

    else if((strcmp(arg, "-kc") == 0) || (strcmp(arg, "-ck") == 0))
      flavors |= FL_KEEP_CO;
    else if(strcmp(arg, "-cR") == 0)
      condflags_add_str(condcflavors, condition, FL_ANTIRAW);
    else if(strcmp(arg, "-sc") == 0)
      flavors |= FL_SHUFFLE_CO;
    else if(strcmp(arg, "-cc") == 0) {
      condflags_add_str(condmflavors, condition, FL_CO_AUTO);
      condflags_add_str(condcflavors, condition, FL_CO_AUTO);
    } else if(strcmp(arg, "-ca") == 0)
      condflags_add_str(condcflavors, condition, FL_ADDER);
    else if(strcmp(arg, "-cb") == 0)
      condflags_add_str(condcflavors, condition, FL_BINARY);
    else if(strcmp(arg, "-cu") == 0)
      condflags_add_str(condcflavors, condition, FL_UNARY);
    else if(strcmp(arg, "-cn") == 0)
      condflags_add_str(condcflavors, condition, FL_CO_SEQ_SORT);
    else if((strncmp(arg, "-c", 2) == 0)
            && ((arg[2] == 't') || (arg[2] == 'h'))) {

      uint64_t f = 0;
      for(i = 2; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 't')
          f |= FL_CO_TOTALIZE;
        else if(arg[i] == 'h')
          f |= FL_CO_OE_MERGE; 
        else if(arg[i] == 'w')
          f |= FL_CO_REC_SORT_PW;
        else if(arg[i] == 'e')
          f |= FL_CO_REC_SORT_EXP2;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      condflags_add_str(condmflavors, condition, f);
      condflags_add_str(condcflavors, condition, f);

    } else if(strncmp(arg, "-cs", 3) == 0) {

      uint64_t f = 0;
      f |= FL_CO_SELECT;
      for(i = 3; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 'o')
          f |= FL_CO_SELECT_O2;
        else if(arg[i] == 'a')
          f |= FL_CO_SELECT_A2;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      condflags_add_str(condcflavors, condition, f);

    }

      /* ---- Weights ---- */

    else if((strcmp(arg, "-kw") == 0) || (strcmp(arg, "-wk") == 0))
      flavors |= FL_KEEP_WT;
    else if(strcmp(arg, "-wR") == 0)
      condflags_add_str(condwflavors, condition, FL_ANTIRAW);
    else if(strcmp(arg, "-wm") == 0)
      flavors |= FL_WT_BIT_DECOMPOSE;

    else if(strncmp(arg, "-wp", 3) == 0) {

      uint64_t f = 0;
      for(i = 3; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 'a')
          f |= FL_WT_ORDER_ASCENDING;
        else if(arg[i] == 'd')
          f |= FL_WT_ORDER_DESCENDING;
        else if(arg[i] == 'r')
          f |= FL_WT_ORDER_RANDOM;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      if(i <= 3) {
        fprintf(stderr, "%s: -wp requires one more character\n", program_name);
        error = -2;
      }
      flavors |= f;

    }
    else if(strcmp(arg, "-ws") == 0)
      condflags_add_str(condwflavors, condition, FL_WT_STRETCH);
    else if(strcmp(arg, "-we") == 0)
      condflags_add_str(condwflavors, condition, FL_WT_EXP);
    else if(strcmp(arg, "-wb") == 0)
      condflags_add_str(condwflavors, condition, FL_ROBDD);
    else if(strcmp(arg, "-wz") == 0)
      condflags_add_str(condwflavors, condition, FL_WT_SEQ_SORT);
    else if(strcmp(arg, "-wa") == 0)
      condflags_add_str(condwflavors, condition, FL_WT_ADDER);
    else if(strcmp(arg, "-wu") == 0)
      condflags_add_str(condwflavors, condition, FL_WT_MIX_UNR);
    else if(strncmp(arg, "-wq", 3) == 0) {

      uint64_t f = FL_WT_PLAN;
      for(i = 3; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 'i')
          f |= FL_WT_PLAN_INDEPENDENT;
        else if(arg[i] == 's')
          f |= FL_WT_PLAN_FAMILY_SINGLETON;
        else if(arg[i] == 'p')
          f |= FL_WT_PLAN_DOT;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      condflags_add_str(condwflavors, condition, f);

    }

      /* ---- Optimizations ---- */

    else if((strcmp(arg, "-ko") == 0) || (strcmp(arg, "-ok") == 0))
      condflags_add_str(condoflavors, condition, FL_KEEP_OPT);
    else if(strcmp(arg, "-om") == 0)
      flavors |= FL_OPT_MERGE;
    else if(strncmp(arg, "-ob", 3) == 0)
      condflags_add_str(condoflavors, condition, FL_OPT_WEIGHT | FL_OPT_OPT);
    else if((strncmp(arg, "-oq", 3) == 0)
              && ((arg[3] == 'n') || (arg[3] == 'h'))) {

      uint64_t f = FL_OPT_PLAN;
      for(i = 3; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 'n')
          f |= FL_OPT_PLAN_NEG;
        else if(arg[i] == 'h')
          f |= FL_OPT_PLAN_HALF;
        else if(arg[i] == 'M')
          f |= FL_OPT_PLAN_MANY;
        else if(arg[i] == 'i')
          f |= FL_OPT_PLAN_INDEPENDENT;
        else if(arg[i] == 's')
          f |= FL_OPT_PLAN_FAMILY_SINGLETON;
        else if(arg[i] == 'p')
          f |= FL_OPT_PLAN_DOT;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      if((f & FL_OPT_PLAN_HALF) && (f & FL_OPT_PLAN_MANY)) {
        fprintf(stderr, "%s: character %c has no effect in option %s\n",
                program_name, 'M', arg);
        error = -1;
      }
      condflags_add_str(condoflavors, condition, f);

    }
    else if(strncmp(arg, "-ox", 3) == 0) {

      uint64_t f = FL_OPT_SORT;
      for(i = 3; !error && (arg[i] != '\0'); i++)
        if(arg[i] == 'u')
          f |= FL_OPT_SORT_UNIT;
        else if(arg[i] == 'r')  /* undocumented (by intention) */
          f |= FL_OPT_SORT_RULE;
        else if(arg[i] == 'c')  /* undocumented (by intention) */
          f |= FL_OPT_SORT_INTEGRITY;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -1;
        }
      condflags_add_str(condoflavors, condition, f);

    } else if((strncmp(arg, "-ol", 3) == 0) || (strncmp(arg, "-ou", 3) == 0)) {

      int integrity = 1, lower = 0, upper = 0;

      for(i = 2; !error && (arg[i] != '\0') && !isdigit(arg[i]); i++)
        if(arg[i] == 'l')
          lower = 1;
        else if(arg[i] == 'u')
          upper = 1;
        else if(arg[i] == 's')
          integrity = 0;
        else {
          fprintf(stderr, "%s: unkown character %c in option %s\n",
                  program_name, arg[i], arg);
          error = -2;
        }

      if(integrity) {
        if(lower)
          flavors |= FL_OPT_SORT_LB_INTEGRITY;
        if(upper)
          flavors |= FL_OPT_SORT_UB_INTEGRITY;
      }

      if(isdigit(arg[i])) {
        int bound = atoi(&arg[i]);
        if(lower) 
          optimize_lb = bound;
        if(upper)
          optimize_ub = bound;
      } else {
        fprintf(stderr, "%s: -o%c must end in <bound>\n",
                program_name, arg[2]);
        error = -2;
      }

    }
    else if(strncmp(arg, "-of", 3) == 0)
      optimize_format = arg + 3;
    else if(strncmp(arg, "-od", 3) == 0) {

      flavors |= FL_OPT_DECISION;
      if(isdigit(arg[3])) {
        optimize_ub = atoi(&arg[3]);
      } else {
        fprintf(stderr, "%s: -od must end in <bound>\n", program_name);
        error = -2;
      }

    }

      /* ---- Rest ---- */

    else if(file == NULL)
      file = arg;
    else {
      fprintf(stderr, "%s: unknown argument %s\n", program_name, arg);
      error = -1;
    }

    /* Check that if there was a condition, it was also used */

    if(have_cond) {
      if(cond_cnt == (condflags_size(condmflavors)
                    + condflags_size(condcflavors)
                    + condflags_size(condwflavors)
                    + condflags_size(condoflavors))) {
        fprintf(stderr, "%s: conditions are not supported for %s\n",
                program_name, arg);
        error = -3;
      }
    }

  }

  if(option_help == -1) short_usage();
  if(option_help == -2) long_usage();
  if(option_version) _version_lp2normal2_c();

  if(option_help || option_version)
    exit(0);

  /* Do some sanity checking */

  if((flavors & FL_CH_EXTERNAL)
      && (flavors & FL_OPT_WEIGHT)
      && (*optimize_format == '\0')) {
    fprintf(stderr, "%s: together options -e and -ob require -of\n",
            program_name);
    error = -2;
  }

  if(error) {
    if(error == -1)
      short_usage();
    if(error == -2)
      long_usage();
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

  size = table_size(table);
  
  if(seed == 0)
    seed = time(NULL) + (int)getpid();
  srand(seed);

  /* Store unconditional flavors */

  condflags_add_uncond(condmflavors, flavors);
  condflags_add_uncond(condcflavors, flavors);
  condflags_add_uncond(condwflavors, flavors);
  condflags_add_uncond(condoflavors, flavors);

  /* Package some arguments and state into an ARGS object */

  ARGS args;
  args.style = (option_verbose ? STYLE_READABLE : STYLE_SMODELS);
  args.out = out;
  args.table = table;
  args.flavors = flavors;  /* This assignment here should be unnecessary */
  args.condmflavors = condmflavors;
  args.condcflavors = condcflavors;
  args.condwflavors = condwflavors;
  args.condoflavors = condoflavors;
  args.conddepth = 0;      /* This assignment here should be unnecessary */
  args.newatom = size + 1;
  args.newrule = 0;
  args.newopt = 0;
  args.falsity = produce_atom_with_status(table, MARK_FALSE, &args.newatom);
  args.optimize_lb = optimize_lb;
  args.optimize_ub = optimize_ub;
  args.radix_lb = radix_lb;
  args.radix_ub = radix_ub;
  args.optimize_format = optimize_format;

  if(args.falsity < 0) {
    /* read_compute_statement should exit if this is about to happen */
    fprintf(stderr, "%s: missing a false atom!\n", program_name);
    exit(-1);
  }

  /* Extract optimize statements */

  if(flavors & FL_OPT_MERGE)
    optimize_statements = extract_rules_by_type(&program, TYPE_OPTIMIZE);

  if(BACKPROPAGATE_STATUSES)  /* TODO: Consider checking for not raw */
    backpropagate_statuses(&program, table);

  /* Produce the desired output */

  if(option_verbose) {

    fprintf(out, "%% Program '%s' normalized:\n\n", basename(file));
    normalize_program(&args, program);

    if(optimize_statements)
      merge_and_normalize_optimize_statements(&args, optimize_statements);

    if(option_noexternal)
      normalize_input(&args);

    fprintf(out, "\n");

    fprintf(out, "compute { ");
    write_compute_statement(STYLE_READABLE, out, table, MARK_TRUE_OR_FALSE);
    fprintf(out, " }.\n\n");

    if(!option_noexternal)
      write_input(STYLE_READABLE, out, table);

    fprintf(out, "%% The symbols of '%s' (%i symbols):\n\n",
            basename(file), size);  // TODO: Increase by the new symbol count
    write_symbols(STYLE_READABLE, out, table);

    fprintf(out, "\n");

  } else {

    normalize_program(&args, program);

    if(optimize_statements)
      merge_and_normalize_optimize_statements(&args, optimize_statements);

    if(option_noexternal)
      normalize_input(&args);
      //write_input(STYLE_SMODELS, out, table);

    fprintf(out, "0\n");

    write_symbols(STYLE_SMODELS, out, table);
    fprintf(out, "0\n");

    fprintf(out, "B+\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_TRUE);
    fprintf(out, "0\n");

    fprintf(out, "B-\n");
    write_compute_statement(STYLE_SMODELS, out, table, MARK_FALSE);
    fprintf(out, "0\n");

    if(!option_noexternal) {
      fprintf(out, "E\n");
      write_compute_statement(STYLE_SMODELS, out, table, MARK_INPUT);
      fprintf(out, "0\n");
    }

    fprintf(out, "%i\n", number);
  }

  condflags_free(condmflavors);
  condflags_free(condcflavors);
  condflags_free(condwflavors);
  condflags_free(condoflavors);

  exit(0);
}

/* ---------------------- Miscellaneous ----------------------------------- */

/* gcd -- Calculate the greatest common divisor */

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

int int_ceil_log(int x)
{
  int i, j;
  for(j = 1, i = 0; j < x; i++, j <<= 1);
  return i;
}

/* ---------------------- Conditional Flavors ----------------------------- */

// TODO: Provide output size estimates

void choose_flavors_for_arguments(ARGS *args, CONDFLAGS *f, int k, int n, int w)
{
  condflags_set(f, 'k', k);
  condflags_set(f, 'n', n);
  condflags_set(f, 'w', w);
  condflags_set(f, 'd', args->conddepth);
  args->flavors = condflags_eval(f);
}

void choose_flavors_for_constraint(ARGS *args, RULE *rule)
{
  CONSTRAINT_RULE *c  = rule->data.constraint;
  int n               = c->pos_cnt + c->neg_cnt;

  args->conddepth = 0;
  choose_flavors_for_arguments(args, args->condcflavors,
                             c->bound, n, n);
}

void choose_flavors_for_weight(ARGS *args, RULE *rule)
{
  WEIGHT_RULE *w  = rule->data.weight;
  int n           = w->pos_cnt + w->neg_cnt;

  args->conddepth = 0;
  choose_flavors_for_arguments(args, args->condwflavors,
                             w->bound, n, int_array_sum(n, w->weight));
}

void choose_flavors_for_optimize(ARGS *args, RULE *rule)
{
  OPTIMIZE_RULE *o  = rule->data.optimize;
  int n             = o->pos_cnt + o->neg_cnt;

  args->conddepth = 0;
  choose_flavors_for_arguments(args, args->condoflavors,
                             0, n, int_array_sum(n, o->weight));
}

uint64_t replace_flavors_for_unary_merger(ARGS *args, int bound,
                                          int leftn, int rightn)
{
  uint64_t s  = args->flavors;
  int n       = leftn + rightn;

  args->conddepth++;
  choose_flavors_for_arguments(args, args->condmflavors, bound, n, n);

  return s;
}

uint64_t replace_flavors_for_unary_sorter(ARGS *args, int bound, int n)
{
  uint64_t s = args->flavors;

  args->conddepth++;
  choose_flavors_for_arguments(args, args->condcflavors, bound, n, n);

  return s;
}

uint64_t replace_flavors_for_unary_weight_sorter(ARGS *args, int bound,
                                                 int n, int wsum)
{
  uint64_t s = args->flavors;

  args->conddepth++;
  choose_flavors_for_arguments(args, args->condwflavors, bound, n, wsum);

  return s;
}

void restore_flavors(ARGS *args, uint64_t saved_flavors)
{
  args->flavors = saved_flavors;
  args->conddepth--;
}

/* ---------------------- Shuffling Routines ------------------------------ */

void shuffle_literals(int ncnt, int pcnt, int *table) {
  int i, temp, random;
  
  for (i=0; i<ncnt; i++) {
    random = rand() % ncnt;
    temp = *(table + i);
    *(table + i) = *(table + random);
    *(table + random) = temp;
  }

  for (i=0; i<pcnt; i++) {
    random = rand() % pcnt;
    temp = *(table + ncnt + i);
    *(table + ncnt + i) = *(table + ncnt + random);
    *(table + ncnt + random) = temp;
  }
}

void shuffle_literals_plus_weights(int ncnt, int pcnt, int *table) {
  int i, temp, random;
  
  for (i=0; i<ncnt; i++) {
    random = rand() % ncnt;
    
    temp = *(table + i);
    *(table+i) = *(table + random);
    *(table+random) = temp;
    
    temp = *(table + ncnt + pcnt + i);
    *(table + ncnt + pcnt + i) = *(table + ncnt + pcnt + random);
    *(table + ncnt + pcnt + random) = temp;
  }
  
  for (i=0; i<pcnt; i++) {
    random = rand() % pcnt;
    
    temp = *(table + ncnt + i);
    *(table + ncnt + i) = *(table + ncnt + random);
    *(table + ncnt + random) = temp;
    
    temp = *(table + 2*ncnt + pcnt + i);
    *(table + 2*ncnt + pcnt + i) = *(table + 2*ncnt + pcnt + random);
    *(table + 2*ncnt + pcnt + random) = temp;
  }
  
}

/* ---------------------- atom.c Additions -------------------------------- */

/*
 * Look for an atom with the given status
 */

int find_atom_with_status(ATAB *table, int mask)
{
  while(table) {
    int *statuses = table->statuses;
    int count = table->count;
    int offset = table->offset;
    int atom;
    for(atom = 1; atom <= count; atom++)
      if(statuses[atom - offset] & mask)
        return atom;
    table = table->next;
  }
  return -1;
}

/*
 * Set the status of an atom, and add the atom to the atom table if necessary
 */

void set_status_safe(ATAB *table, int atom, int mask)
{
  if (!set_status(table, atom, mask)) {

    /* Extend symbol table to cover the missing atom */

    ATAB *piece = extend_table(table, 1, atom - 1);
    piece->statuses[1] |= mask;
  }
}

ATAB *extend_table_with_array(ATAB *table, int count, int *array)
{
  int min = int_array_min(count, array);
  int max = int_array_max(count, array);
  return extend_table(table, max - min + 1, min - 1);
}

/*
 * Look up or add an atom with the given status
 */

int produce_atom_with_status(ATAB *table, int mask, int *newatom)
{
  int atom = find_atom_with_status(table, mask);
  if(0 <= atom)
    return atom;
  atom = (*newatom)++;
  set_status_safe(table, atom, mask);
  return atom;
}

/* --------------------------- Local Routines ------------------------------ */

int rename_negative(int style, FILE *out,
		    int neg_cnt, int *neg,
		    ATAB *table, int newatom)
{
  int i = 0;

  for(i=0; i<neg_cnt; i++) {
    int head = newatom++;
    output_normal(style, out, head, 0, NULL, 1, &neg[i], table);
    neg[i] = head;
  }

  return newatom;
}

int remove_negative_literals(int style, FILE *out, RULE *rule,
			 ATAB *table, int newatom)
{
  switch(rule->type) {
  case TYPE_BASIC:
    { BASIC_RULE *basic = rule->data.basic;

      newatom = rename_negative(style, out,
 			        basic->neg_cnt, basic->neg,
			        table, newatom);
      /* See input.c */
      basic->pos = basic->neg;
      basic->pos_cnt += basic->neg_cnt;
      basic->neg_cnt = 0;
    }
    break;

  case TYPE_CONSTRAINT:
    { CONSTRAINT_RULE *constraint = rule->data.constraint;

      newatom = rename_negative(style, out,
 			        constraint->neg_cnt, constraint->neg,
			        table, newatom);
      /* See input.c */
      constraint->pos = constraint->neg;
      constraint->pos_cnt += constraint->neg_cnt;
      constraint->neg_cnt = 0;
    }
    break;

  case TYPE_CHOICE:
    { CHOICE_RULE *choice = rule->data.choice;

      newatom = rename_negative(style, out,
 			        choice->neg_cnt, choice->neg,
			        table, newatom);
      /* See input.c */
      choice->pos = choice->neg;
      choice->pos_cnt += choice->neg_cnt;
      choice->neg_cnt = 0;
    }
    break;

  case TYPE_WEIGHT:
    { WEIGHT_RULE *weight = rule->data.weight;

      newatom = rename_negative(style, out,
 			        weight->neg_cnt, weight->neg,
			        table, newatom);
      /* See input.c */
      weight->pos = weight->neg;
      weight->pos_cnt += weight->neg_cnt;
      weight->neg_cnt = 0;
    }
    break;

  case TYPE_DISJUNCTIVE:
    { DISJUNCTIVE_RULE *disjunctive = rule->data.disjunctive;

      newatom = rename_negative(style, out,
 			        disjunctive->neg_cnt, disjunctive->neg,
			        table, newatom);
      /* See input.c */
      disjunctive->pos = disjunctive->neg;
      disjunctive->pos_cnt += disjunctive->neg_cnt;
      disjunctive->neg_cnt = 0;
    }
    break;

  default:
    fprintf(stderr, "%s: rule type %i not supported!\n",
	    program_name, rule->type);
    exit(-1);
  }

  return newatom;
}

/*
 * output_atom -- Write a (new) atom in an appropriate style
 */

void output_atom(int style, FILE *out, int atom, ATAB *table)
{
  ATAB *piece = find_atom(table, atom);

  if(style != STYLE_READABLE && style != STYLE_SMODELS) {
      fprintf(stderr, "%s: unknown style %i for _%i\n",
	      program_name, style, atom);
      exit(-1);
  }

  if(piece) {
    /* The atom is within the scope of the symbol table */

    int offset = piece->offset;
    int shift = piece->shift;
    SYMBOL **names = piece->names;
    SYMBOL *name = names[atom-offset];

    if(style == STYLE_READABLE) {

      if(name)
	write_name(out, name, piece->prefix, piece->postfix);
      else
	fprintf(out, "_%i", atom+shift);

    } else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom+shift);

  } else {
    /* The atom is new atom outside the scope of the symbol table */

    if(style == STYLE_READABLE)
      fprintf(out, "_%i", atom);
    else if(style == STYLE_SMODELS)
      fprintf(out, " %i", atom);

  }

  return;
}

/*
 * output_literal_list -- Output lists of positive and negative literals
 */

void output_literal_list(int style, FILE *out, char *separator,
			 int pos_cnt, int *pos,
			 int neg_cnt, int *neg,
			 ATAB *table)
{
  int *scan = NULL;
  int *last = NULL;

  for(scan = neg, last = &neg[neg_cnt];
      scan != last; ) {
    if(style == STYLE_READABLE)
      fprintf(out, "not ");
    output_atom(style, out, *scan, table);
    scan++;
    if(style == STYLE_READABLE)
      if(scan != last || pos_cnt)
	fputs(separator, out);
  }

  for(scan = pos, last = &pos[pos_cnt];
      scan != last; ) {
    output_atom(style, out, *scan, table);
    scan++;
    if(style == STYLE_READABLE)
      if(scan != last)
	fputs(separator, out);
  }

  return;
}

/*
 * output_normal -- Print a normal rule (as a basic rule)
 */

void output_normal(int style, FILE *out,
		   int head, int pos_cnt, int *pos, int neg_cnt, int *neg,
		   ATAB *table)
{
  if(style == STYLE_SMODELS)
    fprintf(out, "1");

  output_atom(style, out, head, table);

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", (pos_cnt+neg_cnt), neg_cnt);

  if(pos_cnt || neg_cnt) {
    if(style == STYLE_READABLE)
      fprintf(out, " :- ");

    output_literal_list(style, out, ", ",
			pos_cnt, pos,
			neg_cnt, neg, table);
  }

  if(style == STYLE_READABLE)
    fprintf(out, ".");
  fprintf(out, "\n");

  return;
}

/*
 * output_normal_cond -- Output a normal rule with potential extra conditions
 */

void output_normal_cond(int style, FILE *out, int head,
			int pos_cnt, int *pos, int pos_cond,
			int neg_cnt, int *neg, int neg_cond,
			ATAB *table)
{
  int *new_pos = NULL, *new_neg = NULL;
  
  if(pos_cond) {
    int i = 0;

    new_pos = (int *)malloc((pos_cnt+1)*sizeof(int));

    for(i = 0; i<pos_cnt; i++)
      new_pos[i] = pos[i];
    new_pos[pos_cnt] = pos_cond;

  } else
    new_pos = pos;

  if(neg_cond) {
    int i = 0;

    new_neg = (int *)malloc((neg_cnt+1)*sizeof(int));

    for(i = 0; i<neg_cnt; i++)
      new_neg[i] = neg[i];
    new_neg[neg_cnt] = neg_cond;

  } else
    new_neg = neg;

  output_normal(style, out, head,
		pos_cond ? pos_cnt+1 : pos_cnt, new_pos,
		neg_cond ? neg_cnt+1 : neg_cnt, new_neg,
		table);

  if(pos_cond) free(new_pos);
  if(neg_cond) free(new_neg);

  return;
}

/*
 * output_literal_rules -- Output a rule for each literal
 */

void output_literal_rules(int style, FILE *out,
			  RULE *rule, ATAB *table)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt;
  int neg_cnt = constraint->neg_cnt;
  int *scan = NULL, *last = NULL;

  if(pos_cnt)
    for(scan = constraint->pos, last = &scan[pos_cnt]; scan != last; scan++)
      output_normal(style, out, constraint->head, 1, scan, 0, NULL, table);

  if(neg_cnt)
    for(scan = constraint->neg, last = &scan[neg_cnt]; scan != last; scan++)
      output_normal(style, out, constraint->head, 0, NULL, 1, scan, table);

  return;
}

/*
 * output_literal_pair_rules -- Output a rule for each literal pair
 */

void output_literal_pair_rules(int style, FILE *out,
			       RULE *rule, ATAB *table)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt;
  int neg_cnt = constraint->neg_cnt;
  int *scan = NULL, *last = NULL;

  if(pos_cnt)
    for(scan = constraint->pos, last = &scan[pos_cnt];
	scan != last; scan++) {
      int *scan2 = NULL, *last2 = NULL;
      int new_pos[2] = {0, 0};

      new_pos[0] = *scan;

      for(scan2 = constraint->pos, last2 = &scan2[pos_cnt];
	  scan2 != last2; scan2++) {

	if(scan < scan2) {
	  new_pos[1] = *scan2;

	  output_normal(style, out, constraint->head,
			2, new_pos, 0, NULL, table);
	}
      }

      if(scan < constraint->neg)
	for(scan2 = constraint->neg, last2 = &scan2[neg_cnt];
	    scan2 != last2; scan2++)
	  output_normal(style, out, constraint->head,
			1, scan, 1, scan2, table);
    }

  if(neg_cnt)
    for(scan = constraint->neg, last = &scan[neg_cnt];
	scan != last; scan++) {
      int *scan2 = NULL, *last2 = NULL;
      int new_neg[2] = {0, 0};

      if(scan<constraint->pos)
	for(scan2 = constraint->pos, last2 = &scan2[pos_cnt];
	    scan2 != last2; scan2++)
	  output_normal(style, out, constraint->head,
			1, scan2, 1, scan, table);

      new_neg[0] = *scan;

      for(scan2 = constraint->neg, last2 = &scan2[neg_cnt];
	  scan2 != last2; scan2++) {

	if(scan < scan2) {
	  new_neg[1] = *scan2;
	    
	  output_normal(style, out, constraint->head,
			0, NULL, 2, new_neg, table);
	}
      }
    }

  return;
}

/* ---------------------- Simple Output Functions ------------------------- */

/*
 * a copy of write_literal_list from output.c (but not io.h)
 */

void output_weighted_literal_list(int style, FILE *out, char *separator,
			          int pos_cnt, int *pos,
			          int neg_cnt, int *neg,
			          int *weight, ATAB *table)
{
  int *scan = NULL;
  int *last = NULL;
  int *wscan = weight;
  int *wlast = &weight[pos_cnt+neg_cnt];

  for(scan = neg, last = &neg[neg_cnt];
      scan != last; ) {
    if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
      fprintf(out, "not ");
    output_atom(style, out, *scan, table);
    if(wscan && (style == STYLE_READABLE))
      fprintf(out, "=%i", *(wscan++));
    scan++;
    if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
      if(scan != last || pos_cnt)
	fprintf(out, "%s", separator);
  }

  for(scan = pos, last = &pos[pos_cnt];
      scan != last; ) {
    output_atom(style, out, *scan, table);
    if(wscan && (style == STYLE_READABLE))
      fprintf(out, "=%i", *(wscan++));
    scan++;
    if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
      if(scan != last)
	fprintf(out, "%s", separator);
  }

  if(wscan && (style == STYLE_SMODELS))
    while(wscan != wlast)
      fprintf(out, " %i", *(wscan++));

  return;
}

/*
 * like write_weight in output.c, but accepts a head atom out of table
 */

void output_weight(int style, FILE *out, RULE *rule, ATAB *table)
{
  int pos_cnt = 0;
  int neg_cnt = 0;
  int bound = 0;

  WEIGHT_RULE *weight = rule->data.weight;

  if(style == STYLE_SMODELS)
    fprintf(out, "5");

  output_atom(style, out, weight->head, table);

  pos_cnt = weight->pos_cnt;
  neg_cnt = weight->neg_cnt;
  bound = weight->bound;

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i %i", bound, (pos_cnt+neg_cnt), neg_cnt);

  if(style == STYLE_READABLE)
    fprintf(out, " :- %i [", bound);

  if(pos_cnt || neg_cnt)
    output_weighted_literal_list(style, out, ", ",
		                 pos_cnt, weight->pos,
		                 neg_cnt, weight->neg,
		                 weight->weight, table);

  if(style == STYLE_READABLE)
    fprintf(out, "].");
  fprintf(out, "\n");

  return;
}

/*
 * like write_constraint in output.c but accepts out of table atoms
 */

void output_optimize(int style, FILE *out, RULE *rule, ATAB *table)
{
  int pos_cnt = 0;
  int neg_cnt = 0;

  OPTIMIZE_RULE *optimize = rule->data.optimize;

  if(style == STYLE_SMODELS)
    fprintf(out, "6 0");

  pos_cnt = optimize->pos_cnt;
  neg_cnt = optimize->neg_cnt;

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", (pos_cnt+neg_cnt), neg_cnt);

  if(pos_cnt || neg_cnt) {
    if(style == STYLE_READABLE)
      fprintf(out, "minimize [");

    output_weighted_literal_list(style, out, ", ",
		        pos_cnt, optimize->pos,
		        neg_cnt, optimize->neg,
		        optimize->weight, table);
  }

  if(style == STYLE_READABLE)
    fprintf(out, "].");
  fprintf(out, "\n");

  return;
}

/*
 * like write_choice in output.c but accepts out of table atoms
 */

void output_choice(int style, FILE *out, RULE *rule, ATAB *table)
{
  int head_cnt = 0;
  int pos_cnt = 0;
  int neg_cnt = 0;
  char *separator = ", ";

  CHOICE_RULE *choice = rule->data.choice;
  head_cnt = choice->head_cnt;
  pos_cnt = choice->pos_cnt;
  neg_cnt = choice->neg_cnt;

  if(style == STYLE_SMODELS)
    fprintf(out, "3 %i", head_cnt);
  else if(style == STYLE_READABLE)
    fprintf(out, "{");

  if(style == STYLE_GNT)
    separator = " | ";
  else if(style == STYLE_DLV)
    separator = " v ";

  output_literal_list(style, out, separator,
		      head_cnt, choice->head,
		      0, NULL,
		      table);

  if(style == STYLE_READABLE)
    fprintf(out, "}");

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", (pos_cnt+neg_cnt), neg_cnt);

  if(pos_cnt || neg_cnt) {
    if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
      fprintf(out, " :- ");

    output_literal_list(style, out, ", ",
		        pos_cnt, choice->pos,
		        neg_cnt, choice->neg,
		        table);
  }

  if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
    fprintf(out, ".");
  fprintf(out, "\n");

  return;
}

/*
 * like write_constraint in output.c, but accepts a head atom out of table
 */

void output_constraint(int style, FILE *out, RULE *rule, ATAB *table)
{
  int pos_cnt = 0;
  int neg_cnt = 0;
  int bound = 0;

  CONSTRAINT_RULE *constraint = rule->data.constraint;

  if(style == STYLE_SMODELS)
    fprintf(out, "2");

  output_atom(style, out, constraint->head, table);

  pos_cnt = constraint->pos_cnt;
  neg_cnt = constraint->neg_cnt;
  bound = constraint->bound;

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i %i", (pos_cnt+neg_cnt), neg_cnt, bound);

  if(style == STYLE_READABLE)
    fprintf(out, " :- %i {", bound);

  if(pos_cnt || neg_cnt)
    output_literal_list(style, out, ", ",
		        pos_cnt, constraint->pos,
		        neg_cnt, constraint->neg,
		        table);

  if(style == STYLE_READABLE)
    fprintf(out, "}.");

  fprintf(out, "\n");

  return;
}

/*
 * like write_disjunctive in output.c but accepts out of table atoms
 */

void output_disjunctive(int style, FILE *out, RULE *rule, ATAB *table)
{
  int head_cnt = 0;
  int pos_cnt = 0;
  int neg_cnt = 0;
  char *separator = " | ";

  DISJUNCTIVE_RULE *disjunctive = rule->data.disjunctive;
  head_cnt = disjunctive->head_cnt;
  pos_cnt = disjunctive->pos_cnt;
  neg_cnt = disjunctive->neg_cnt;

  if(style == STYLE_SMODELS)
    fprintf(out, "8 %i", head_cnt);

  if(style == STYLE_GNT)
    separator = " | ";
  else if(style == STYLE_DLV)
    separator = " v ";

  output_literal_list(style, out, separator,
		      head_cnt, disjunctive->head,
		      0, NULL,
		      table);

  if(style == STYLE_SMODELS)
    fprintf(out, " %i %i", (pos_cnt+neg_cnt), neg_cnt);

  if(pos_cnt || neg_cnt) {
    if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
      fprintf(out, " :- ");

    output_literal_list(style, out, ", ",
		        pos_cnt, disjunctive->pos,
		        neg_cnt, disjunctive->neg,
		        table);
  }

  if(style == STYLE_READABLE || style == STYLE_GNT || style == STYLE_DLV)
    fprintf(out, ".");
  fprintf(out, "\n");

  return;
}

/* ------------------------------------------------------------------------- */

/*
 * output_counting_chain -- Count atoms up to two using a chain
 */

int output_counting_chain(int style, FILE *out, RULE *rule,
			  ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt;
  int *scan = NULL, *last = NULL;
  int previous = newatom++;
      
  if(pos_cnt) {

    /* Generate: f_1 :- l_1. */

    output_normal(style, out,
		  previous, 1, constraint->pos, 0, NULL, table);

    scan = constraint->pos;

    for(last = &scan[pos_cnt], scan=&scan[1]; scan != last; scan++) {
      int new_pos[2] = {0, 0};

      /* For i>1: a :- f_(i-1), l_i. */

      new_pos[0] = previous;
      new_pos[1] = *scan;
      output_normal(style, out, constraint->head,
		    2, new_pos, 0, NULL, table);

      /* For i>1: f_i :- f_(i-1). */

      output_normal(style, out, newatom, 1, &previous, 0, NULL, table);
      previous = newatom++;

      /* For i>1: f_i :- l_i. */

      output_normal(style, out, previous, 1, scan, 0, NULL, table);
    }
  }

  if(neg_cnt) {

    if(!pos_cnt)   /* Generate: f_1 :- l_1. */
      output_normal(style, out,
		    previous, 0, NULL, 1, constraint->neg, table);

    scan = constraint->neg;

    for(last = &scan[neg_cnt], scan = (pos_cnt ? &scan[0] : &scan[1]);
	scan != last; scan++) {

      /* For i>1: a :- f_(i-1), l_i. */

      output_normal(style, out, constraint->head,
		    1, &previous, 1, scan, table);

      /* For i>1: f_i :- f_(i-1). */

      output_normal(style, out, newatom, 1, &previous, 0, NULL, table);
      previous = newatom++;

      /* For i>1: f_i :- l_i. */

      output_normal(style, out, previous, 0, NULL, 1, scan, table);
    }
  }

  return newatom;
}

/*
 * output_counting_triangle -- Count atoms up to k using a triangular structure
 */

int output_counting_triangle(int style, FILE *out, RULE *rule,
			     ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *intermediate = (int *)malloc((pos_cnt+neg_cnt)*sizeof(int));
  int i = 0, j = 0;

  for(i=0; i < bound; i++) {   /* Levels i = 0..bound-1 */

    if(neg_cnt)
      for(j=pos_cnt+(neg_cnt-1); (i>pos_cnt-1?i:pos_cnt)<=j; j--) {

	intermediate[j] = newatom++;

	if(i>0)
	  /* Generate: d(i,j) :- d(i-1,j-1), l_j. */
	  output_normal(style, out, intermediate[j],
			1, &intermediate[j-1],
			1, &constraint->neg[j-pos_cnt], table);
	else
	  /* Generate: d(i,j) :- l_j. */
	  output_normal(style, out, intermediate[j],
			0, NULL, 1, &constraint->neg[j-pos_cnt], table);

	if(j<pos_cnt+(neg_cnt-1))
	  /* Generate: d(i,j+1) :- d(i,j). */
	  output_normal(style, out, intermediate[j+1],
			1, &intermediate[j], 0, NULL, table);
      }

    if(pos_cnt)
      for(j=pos_cnt-1; i<=j; j--) {

	intermediate[j] = newatom++;

	if(i>0) {  /* Generate: d(i,j) :- d(i-1,j-1), l_j. */
	  int new_pos[2] = {0, 0};

	  new_pos[0] = intermediate[j-1];
	  new_pos[1] = constraint->pos[j];

	  output_normal(style, out, intermediate[j],
			2, new_pos, 0, NULL, table);

	} else /* Generate: d(i,j) :- l_j. */
	  output_normal(style, out, intermediate[j],
			1, &constraint->pos[j], 0, NULL, table);

	/* Generate: d(i,j+1) :- d(i,j). */

	if(j<pos_cnt+(neg_cnt-1))
	  output_normal(style, out, intermediate[j+1],
			1, &intermediate[j], 0, NULL, table);
      }
  }

  /* Derive the head atom */

  output_normal(style, out, constraint->head,
		1, &intermediate[pos_cnt+neg_cnt-1], 0, NULL, table);

  free(intermediate);

  return newatom;
}

/*
 * output_counting_net -- Count atoms up to k using a net structure
 */

int output_counting_net(int style, FILE *out, RULE *rule,
			ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int cnt = pos_cnt + neg_cnt;
  int *values = (int *)malloc(cnt*sizeof(int));
  int *intermediate = (int *)malloc(cnt*sizeof(int));
  int i = 0, head = 0;

  for(i=0; i<cnt; i++) {
    if(i<pos_cnt)
      values[i] = constraint->pos[i];
    else { /* We have to rename negative literals */
      head = newatom++;

      output_normal(style, out, head, 0, NULL,
		    1, &(constraint->neg[i-pos_cnt]), table);

      values[i] = head;
    }
    intermediate[i] = 0;
  }

  while(bound != 1) {

    /* Output XORs: xor(i) :- l(i-1), not l(i).  xor(i) :- l(i), not l(i-1). */

    for(i=0; i<cnt; i++) {
      if(i == 0)
	/* Just copy the first entry */
	intermediate[i] = values[i];
      else if(i != cnt-1 || (bound & 1)){
	head = newatom++;

	output_normal(style, out, head,
		      1, &values[i], 1, &intermediate[i-1], table);
	output_normal(style, out, head,
		      1, &intermediate[i-1], 1, &values[i], table);
	intermediate[i] = head;
      } else
	/* Last entry not needed */
	intermediate[i] = 0;
    }

    /* Output ANDs: and(i) :- l(i), l(i+1). */

    for(i=0; i<cnt-1; i++) {
	head = newatom++;
	int pos[2] = {0, 0};
	
	pos[0] = intermediate[i];
	pos[1] = values[i+1];

	output_normal(style, out, head, 2, pos, 0, NULL, table);
	values[i] = head;
      }
    values[cnt-1] = intermediate[cnt-1];

    if(bound & 1)
      bound++;
    else
      cnt--;

    bound >>= 1;
  }

  /* Derive the head atom */

  for(i=0; i<cnt; i++)
    output_normal(style, out, constraint->head,
		  1, &values[i], 0, NULL, table);

  return newatom;
}

/*
 * output_counting_grid -- Count atoms up to k using a grid structure
 */

int output_counting_grid(int style, FILE *out, RULE *rule,
			 ATAB *table, int newatom)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int *intermediate =
    (int *)malloc((pos_cnt+neg_cnt-bound+1)*sizeof(int));
  int i = 0, j = 0;

  for(i=0; i < constraint->bound; i++)      /* Levels i = 0..bound-1 */
    for(j=0; j<=pos_cnt+neg_cnt-bound; j++) {
      int new_head = newatom++;
      int lit = pos_cnt+neg_cnt-j-i-1;      /* Which (diagonal) literal */

      if(pos_cnt && lit<pos_cnt) {
	/* A positive literal l is used */

	if(i>0) {  /* Generate: d(j,i) :- d(j,i-1), l_lit. */
	  int new_pos[2] = {0, 0};

	  new_pos[0] = intermediate[j];
	  new_pos[1] = constraint->pos[lit];

	  output_normal(style, out, new_head,
			2, new_pos, 0, NULL, table);

	} else /* Generate: d(j,i) :- l_lit. */
	  output_normal(style, out, new_head,
			1, &constraint->pos[lit], 0, NULL, table);

	intermediate[j] = new_head;

	if(j > 0)
	  /* Generate: d(j,i) :- d(j-1,i). */
	  output_normal(style, out, new_head,
			1, &intermediate[j-1], 0, NULL, table);
      }

      if(neg_cnt && lit>=pos_cnt && lit<pos_cnt+neg_cnt) {
	/* A negative literal l is used */

	if(i>0)
	  /* Generate: d(j,i) :- d(j,i-1), l_lit. */
	  output_normal(style, out, new_head,
			1, &intermediate[j],
			1, &constraint->neg[lit-pos_cnt], table);

	else /* Generate: d(j,i) :- l_lit. */
	  output_normal(style, out, new_head,
			0, NULL, 1, &constraint->neg[lit-pos_cnt], table);

	intermediate[j] = new_head;

	if(j > 0)
	  /* Generate: d(j,i) :- d(j-1,i). */
	  output_normal(style, out, new_head,
			1, &intermediate[j-1], 0, NULL, table);
      }
    }

  /* Derive the head atom */

  output_normal(style, out, constraint->head,
		1, &intermediate[pos_cnt+neg_cnt-bound], 0, NULL, table);

  free(intermediate);

  return newatom;
}

/* ------------------------- Some Debugging Functions --------------------- */

#if 1
// TODO: Possibly use #if DEBUG

char *
ma2s(int atom)
{
  if(SMX_IS_TRUE(atom))
    return "T";
  if(SMX_IS_FALSE(atom))
    return "F";
  if(SMX_IS_DONT_CARE(atom))
    return "X";
  if(SMX_IS_WANTED(atom))
    return "W";
  if(SMX_IS_SPECIAL(atom))
    return "S";
  static char *buf[40];
  char *const prefix = (MIX_IS_POS(atom) ? "" : "~");
  static int i = 39;
  if(++i == 40) i = 0;
  if(buf[i] == NULL) buf[i] = malloc(64 * sizeof(char));
  sprintf(buf[i], "%s%i", prefix, MIX_GET_ATOM(atom));
  return buf[i];
}

/* Array to string functions for easy debugging. */

char *
a2sb(int c, int stride, int *a, char *buf)
{
  int i;
  int p;
  p = sprintf(buf, "[");
  for(i = 0; i < c; i++) {
    if(i > 0)
      p += sprintf(&buf[p], ", ");
    p += sprintf(&buf[p], "%s", ma2s(a[stride * i]));
  }
  sprintf(&buf[p], "]");
  return buf;
}

char *
a2y(int c, int stride, int *a)
{
  static char *buf[10];
  static int i = 9;
  const int n = 128;
  if(++i == 10) i = 0;
  if(buf[i] == NULL) buf[i] = malloc(n * sizeof(char));
  if((c < 0) || (n <= (11 + 2) * (c + stride - 1) / stride)) {
    sprintf(buf[i], "[ ... %i elements ... ]", c);
    return buf[i];
  }
  return a2sb(c, stride, a, buf[i]);
}

char *
a2x(int c, int *a)
{
  return a2y(c, 1, a);
}

#endif

/* --------------------- Weight Ordering ---------------------------------- */

/* for sorting atoms or anything else by their weights */

typedef struct weighted_index {
  int weight;
  int index;
} WINDEX;

/* for qsort */ 

int compare_weighted_index_descending(const void *a, const void *b) 
{ 
  const WINDEX *wia = (const WINDEX *)a;
  const WINDEX *wib = (const WINDEX *)b;
  return wib->weight - wia->weight; 
} 

/* for qsort */ 

int compare_weighted_index_ascending(const void *a, const void *b) 
{ 
  const WINDEX *wia = (const WINDEX *)a;
  const WINDEX *wib = (const WINDEX *)b;
  return wia->weight - wib->weight; 
} 

/*
 *
 */

void sort_weighted_array_in_place(int cnt, int *body, int *weight, int order)
{
  WINDEX * const wi = (WINDEX *)malloc(cnt * sizeof(WINDEX));
  int i;

  /* Store the weights in the weighted index array */
  for(i = 0; i < cnt; i++) {
    wi[i].index = body[i];
    wi[i].weight = weight[i];
  }

  /* Sort the weighted indices */
  qsort(wi, cnt, sizeof(WINDEX),
        (order == ORDER_DESCENDING
         ? compare_weighted_index_descending
         : compare_weighted_index_ascending));

  /* Transfer the now ordered data back */
  for(i = 0; i < cnt; i++) {
    body[i] = wi[i].index;
    weight[i] = wi[i].weight;
  }

  free(wi);
}

/*
 *
 */

void permute_weighted_array_in_place(ARGS *args, int cnt, int *body,
                                     int *weight)
{
  if(args->flavors & FL_WT_ORDER_ASCENDING)
    sort_weighted_array_in_place(cnt, body, weight, ORDER_ASCENDING);
  else if(args->flavors & FL_WT_ORDER_DESCENDING)
    sort_weighted_array_in_place(cnt, body, weight, ORDER_DESCENDING);
  else if(args->flavors & FL_WT_ORDER_RANDOM)
    shuffle_literals_plus_weights(0, cnt, body);
}

/*
 *
 */

void permute_weight_rule_in_place(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;

  if(args->flavors & (FL_WT_ORDER_ASCENDING | FL_WT_ORDER_DESCENDING)) {

    const int order = (args->flavors & FL_WT_ORDER_ASCENDING
                       ? ORDER_ASCENDING
                       : ORDER_DESCENDING);

    sort_weighted_array_in_place(weight->neg_cnt, weight->neg,
                                 weight->weight, order);

    sort_weighted_array_in_place(weight->pos_cnt, weight->pos,
                                 &weight->weight[weight->neg_cnt], order);

  } else if(args->flavors & FL_WT_ORDER_RANDOM)

    shuffle_literals_plus_weights(weight->neg_cnt,
                                  weight->pos_cnt,
                                  weight->neg);
}

/* 
 * sort_body_descending -- Take input separated by polarity and output mixed
 *                         literals sorted in descendig order
 */

void sort_body_descending(int pos_cnt, int *pos, int neg_cnt, int *neg,
                          int *weight, int *sorted_body, int *sorted_weight)
{
  const int tot_cnt = neg_cnt + pos_cnt;
  int i;

  for(i = 0; i < neg_cnt; i++)
    sorted_body[i] = MIX_GET_NEG(neg[i]);

  for(i = 0; i < pos_cnt; i++)
    sorted_body[neg_cnt + i] = pos[i];

  for(i = 0; i < tot_cnt; i++)
    sorted_weight[i] = weight[i];

  sort_weighted_array_in_place(tot_cnt, sorted_body, sorted_weight,
                             ORDER_DESCENDING);
}

/* ========================= Unary Mixed Radix Sorting Network ============ */

/*
 *
 */

int get_weight_residue_overflow(int bound, int residue_sum, int divisor)
{
  const int bound_residue = bound % divisor;

  const int a = 1 + (residue_sum - bound_residue + divisor - 1) / divisor;
  const int b = (bound / divisor) + 1; 

  return (a < b ? a : b);
}

/*
 *
 */

double estimate_sorting_cost(double n)
{
#if USE_WRONG_BUT_OK_DIVISOR_COST_ESTIMATE
  return n;
#else
  return n * exp2(log2(n));
#endif
}

/*
 *
 */

int estimate_quotient_cost(int cnt, int *w, int div, int overflow)
{
#if USE_WRONG_BUT_OK_DIVISOR_COST_ESTIMATE
  return -(int) lround(0.50 * (double) cnt * log2((double) div)) + overflow;
#else

  const int w_sum = int_array_sum(cnt, w);
  const double w_avg = (double) w_sum / (double) cnt;
  const double a_levels = log2(w_avg / (double) div);
  const double a_lvl_bits = 0.50 * (double) cnt;

  return
    (int) lround(estimate_sorting_cost(a_lvl_bits + overflow)
                 + (a_levels - 1) * estimate_sorting_cost(1.5 * a_lvl_bits));
#endif
}

/*
 * TODO: Explain
 */

int estimate_divisor_cost(int bound, int cnt, int *w, int div)
{
  const int residue_sum = int_array_sum_residues(cnt, w, div);
  const int overflow = get_weight_residue_overflow(bound, residue_sum, div);
  const int quotient_cost = estimate_quotient_cost(cnt, w, div, overflow);

  return estimate_sorting_cost(residue_sum) + quotient_cost;
}

/*
 *
 */

int improve_divisor(int best_div, int cnt, int *w)
{
  int i, divmul;

  /* Compute the gcd of the weights after being divided */

  for(divmul = w[0] / best_div, i = 1; i < cnt; i++)
    divmul = gcd(divmul, w[i] / best_div);

  divmul = (divmul ? divmul : 1);

  return best_div * divmul;
}

/*
 * Heuristically choose a (prime) number to divide an array with so as to
 * minimize a (hard coded) cost function defined on the quotients and residues.
 *
 * REQUIRES: w_max == max(w[0], ..., w[cnt - 1])
 * ENSURES:  w[0] / r + ... + w[cnt - 1] / r <= max_residue_sum
 */

int pick_divisor(int bound, int cnt, int *w, int w_max, int lb, int ub,
                 int max_residue_sum)
{
  const int lim = MIN(bound, MIN(w_max, ub)) + 1;
  int i;

  /* Initialize with the given lower bound, or 2 */

  int best_div = MAX(lb, 2);
  int init_rsum = int_array_sum_residues(cnt, w, best_div);
  int best_cost = estimate_divisor_cost(bound, cnt, w, best_div);

  if(max_residue_sum < init_rsum) {
    best_div = 2;
    best_cost = estimate_divisor_cost(bound, cnt, w, best_div);
  }

  /* Go through primes up to the limit */

  for(i = 0; (i < PRIME_COUNT) && (prime_array[i] < lim); i++) {

    if(prime_array[i] <= best_div)
      continue;

    const int div = prime_array[i];
    const int rsum = int_array_sum_residues(cnt, w, div);
    const int cost = estimate_divisor_cost(bound, cnt, w, div);

    if((cost < best_cost) && (rsum <= max_residue_sum)) {
      best_cost = cost;
      best_div = div;
    }
  }

  const int r = improve_divisor(best_div, cnt, w);
#if DEBUG_DIV
  fprintf(stderr, "%% Chose divisor %i (lb=%i, ub=%i)\n", r, lb, ub);
#endif
  return r;
}

/* ========================= Weight Counter =============================== */

/*
 * WARNING: Changes the literal and weight int arrays of the rule
 */

void output_mixed_radix_weight_counter(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;
  const int neg_cnt = weight->neg_cnt, pos_cnt = weight->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt, head = weight->head;
  int * const mix = weight->neg, * const w = weight->weight;
  int bound = weight->bound;

  const int max_space = RADIX_MAX_BLOWUP(args->radix_ub, tot_cnt);
  int * const carry = (int *)malloc(2 * max_space * sizeof(int));
  int * const merge = (int *)malloc(2 * max_space * sizeof(int));
  int * const sort  = (int *)malloc(max_space * sizeof(int));
  int * const tmpv  = (int *)malloc(max_space * sizeof(int));
  int * const tmpw  = (int *)malloc(max_space * sizeof(int));
  int *source;
  int div, source_cnt, carry_cnt = 0, startatom = args->newatom;
  int i, j;

  litint_from_neg(neg_cnt, mix);
  permute_weighted_array_in_place(args, tot_cnt, mix, w);

  const int w_max_i = int_array_max_index(tot_cnt, w);

  /**/

  for(;; bound = (bound / div) + ((bound % div) != 0)) {

    int merge_cnt, sort_cnt = 0, tmp_cnt = 0;
    div = pick_divisor(bound, tot_cnt, w, w[w_max_i],
                       args->radix_lb, args->radix_ub, max_space);

    /* Collect literals belonging to the current bucket */

    for(i = 0; i < tot_cnt; i++) {
      j = w[i] % div;
      if(j) {
        tmpv[tmp_cnt] = mix[i];
        tmpw[tmp_cnt] = j;
        tmp_cnt++;
        sort_cnt += j;
      }
    }

    for(i = 0; i < tot_cnt; i++) /* Divide the weights for the next round */
      w[i] /= div;

    const int tcond = (w[w_max_i] == 0); /* Check for the last iteration */

    if(sort_cnt) {  /* Sort the current bucket */
      int_array_fill(sort_cnt, sort, SMX_WANTED);
      output_unary_weight_sorter(args, sort_cnt, sort,
                                 tmp_cnt, tmpv, tmpw, &startatom);
    }

    /* Merge the current bucket with any carried literals */

    merge_cnt = (carry_cnt && sort_cnt ? carry_cnt + sort_cnt : 0);

    if(merge_cnt) { /* Merge previous carries and current sorted input */

      if(tcond) { /* We want to know only one output */

        for(i = 0; i < merge_cnt; i++)
          merge[i] = SMX_DONT_CARE;
        merge[bound - 1] = SMX_WANTED;

      } else /* We want to know roughly a 'div':th of everything */

        for(i = 0; i < merge_cnt; i++)
          merge[i] = ((i - (bound + div - 1)) % div
                     ? SMX_DONT_CARE
                     : SMX_WANTED);

      output_unary_merger(args,
                          merge_cnt, merge,
                          carry_cnt, carry,
                          sort_cnt, sort,
                          0, startatom);
    }

    if(sort_cnt == 0) {
      source_cnt = carry_cnt;
      source     = carry;
    } else if(carry_cnt == 0) {
      source_cnt = sort_cnt;
      source     = sort;
    } else {
      source_cnt = merge_cnt;
      source     = merge;
    }

    /* Check terminal condition */

    if(tcond)
      break;

    /* Carry roughly every 'div':th output */

    for(j = 0, i = (bound + div - 1) % div; i < source_cnt; i += div, j++)
      carry[j] = source[i];

    carry_cnt = j;
  }

  /* Derive the head from the output */

  litint_output_normal(args, head, 1, &source[bound - 1]);

  free(carry);
  free(merge);
  free(sort);
  free(tmpv);
  free(tmpw);
}

/* ========================= Misc ========================================= */

/*
 * decompose_weight -- Decompose a weight rule by bits 
 */

RULE *decompose_weight(RULE *rule)
{
  int i, j;

  WEIGHT_RULE * const weight = rule->data.weight;
  int * const neg = weight->neg;
  const int neg_cnt = weight->neg_cnt;
  const int pos_cnt = weight->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt;
  int * const w = weight->weight;

  RULE * const new = (RULE *)malloc(sizeof(RULE));;
  WEIGHT_RULE * const dec = (WEIGHT_RULE *)malloc(sizeof(WEIGHT_RULE));

  /* Count the total number of bits in weights */

  int bit_count = 0;

  for(i = 0; i < neg_cnt; i++) {
    int x = w[i];
    while(x) {
      bit_count += (x & 1);
      x >>= 1;
    }
  }

  const int neg_bit_count = bit_count;

  for(i = neg_cnt; i < tot_cnt; i++) {
    int x = w[i];
    while(x) {
      bit_count += (x & 1);
      x >>= 1;
    }
  }

  /* Decompose the rule */

  int * const new_neg = (int *)malloc(2 * bit_count * sizeof(int));
  int * const new_pos = &new_neg[neg_bit_count];
  int * const new_weight = &new_neg[bit_count];

  j = 0;

  for(i = 0; i < tot_cnt; i++) {
    const int x = w[i];
    const int y = neg[i];
    int b;
    for(b = 1; b <= x; b <<= 1) {
      if(x & b) {
        new_neg[j] = y;
        new_weight[j] = b;
        j++;
      }
    }
  }

#if DEBUG
  if(j != bit_count)
    fprintf(stderr, "AAARGH: j = %i, bit_count = %i\n", j, bit_count);
#endif

  /* Package the rule */

  new->type = TYPE_WEIGHT;
  new->data.weight = dec;
  new->next = NULL;

  dec->head = weight->head;
  dec->bound = weight->bound;
  dec->neg_cnt = neg_bit_count;
  dec->neg = new_neg;
  dec->pos_cnt = bit_count - neg_bit_count;
  dec->pos = new_pos;
  dec->weight = new_weight;

  return new;
}

/* ========================= Weighted Unary Constructions ================= */

/*
 * Output a unary weight sorter implemented with a constraint sorter
 */

void output_stretched_unary_weight_sorter(ARGS *args, int bound, int *res,
                                          int tot_cnt, int *mix, int *weight, 
                                          int *startatom)
{
  const int new_cnt = int_array_sum(tot_cnt, weight);
  int * const tmp = (int *)malloc(new_cnt * sizeof(int));
  int i, j, tmp_cnt = 0;

  for(i = 0; i < tot_cnt; i++)
    for(j = weight[i]; j; j--)
      tmp[tmp_cnt++] = mix[i];

  output_unary_sorter(args, bound, res, tmp_cnt, tmp, startatom);

  free(tmp);
}

/*
 * Output a unary weight sorter
 * NOTE: See cardinality_to_weight_body for how the output may be condensed
 */

void output_unary_weight_sorter(ARGS *args, int bound, int *res,
                                int tot_cnt, int *mix, int *weight,
                                int *startatom)
{
  uint64_t saved_flavors
    = replace_flavors_for_unary_weight_sorter(args, bound, tot_cnt,
                                              int_array_sum(tot_cnt, weight));

  if(args->flavors & FL_WT_SEQ_SORT) {

    output_sequential_unary_weight_sorter(args, bound, res,
                                          tot_cnt, mix, weight);

    *startatom = MAX(*startatom, args->newatom);

  } else if(args->flavors & FL_ROBDD) {

    int *alt_res = (int *)malloc(bound * sizeof(int));
    int *alt_bounds = (int *)malloc(bound * sizeof(int));
    int i, res_cnt = 0;

    for(res_cnt = i = 0; i < bound; i++)
      if(SMX_IS_WANTED(res[i])) {
        alt_res[res_cnt] = SMX_WANTED;
        alt_bounds[res_cnt] = i + 1;
        res_cnt++;
      }

    output_bdd_sorter(args, res_cnt, alt_bounds, alt_res,
                      tot_cnt, mix, weight);

    for(i = 0; i < res_cnt; i++)
      res[alt_bounds[i] - 1] = alt_res[i];

    free(alt_res);
    free(alt_bounds);

    *startatom = MAX(*startatom, args->newatom);

  } else /* if(args->flavors & FL_WT_STRETCH) */

    output_stretched_unary_weight_sorter(args, bound, res,
                                         tot_cnt, mix, weight, startatom);

  restore_flavors(args, saved_flavors);
}

/*
 * Encode a weight rule by taking the bound-th digit of a unary weight sorter
 */

void output_unary_weight_tester(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight_rule = rule->data.weight;
  const int neg_cnt = weight_rule->neg_cnt, pos_cnt = weight_rule->pos_cnt;
  const int tot_cnt = neg_cnt + pos_cnt, bound = weight_rule->bound;
  int * const mix = weight_rule->neg, *const w = weight_rule->weight;
  int * res = (int *)malloc(bound * sizeof(int));
  int i, startatom = args->newatom;

  litint_from_neg(neg_cnt, mix);
  permute_weighted_array_in_place(args, tot_cnt, mix, w);

  /* Specify that we want to know the last element only */

  for(i = 0; i < bound - 1; i++)
    res[i] = SMX_DONT_CARE;

  res[bound - 1] = SMX_WANTED;

  /* Output a sorter */

  output_unary_weight_sorter(args, bound, res, tot_cnt, mix,
                             w, &startatom);

  /* Derive the head from the sorted output */

  litint_output_normal(args, weight_rule->head, 1, &res[bound - 1]);

  free(res);
}

/* ========================= SYMBOLIC TRANSLATION ========================= */

/*
 * output_symbolic_and -- Calculate conjunction symbolically
 */

int output_symbolic_and(int style, FILE *out, int x, int y,
			int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x<0) {             /* x is true */
    if(y<0) {           /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y == 0) { /* y is false */
      /* No rules needed */
      answer = 0;
    } else {            /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x == 0) {   /* x is false */
    /* No rules needed */
    answer = 0;
  } else {              /* x is an atom */
    if(y<0) {           /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y == 0)   /* y is false */
      /* No rules needed */
      answer = 0;
    else {              /* y is an atom */
      if(x != y) {
	int pos[2] = {0, 0};

	pos[0] = x<y ? x : y;
	pos[1] = x<y ? y : x;

	output_normal_cond(style, out, answer = (*newatom)++,
			   2, pos, pos_cond, 0, NULL, neg_cond, table);
      } else { /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     1, &x, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional atom */
	  answer = x;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_or -- Calculate disjunction symbolically
 */

int output_symbolic_or(int style, FILE *out, int x, int y,
		       int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x == 0) {        /* x is false */
    if(y == 0)        /* y is false */
      /* No rules needed */
      answer = 0;
    else if(y<0) {    /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {          /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else 
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x < 0) {  /* x is true */
    if(pos_cond || neg_cond)
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 0, NULL, neg_cond, table);
    else
      /* Propagate an unconditional value */
      answer = -1;
  } else {            /* x is an atom */
    if(y == 0) {      /* y is false */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y < 0) {   /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {            /* y is an atom */
      if(x != y) {
	answer = (*newatom)++;
	output_normal_cond(style, out, answer,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
	output_normal_cond(style, out, answer,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      } else {        /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     1, &x, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional atom */
	  answer = x;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_eq -- Calculate equivalence symbolically
 */

int output_symbolic_eq(int style, FILE *out, int x, int y,
		       int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x < 0) {           /* x is true */
    if(y < 0) {         /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y == 0) { /* y is false */
      /* No rules needed */
      answer = 0;
    } else {            /* y is an atom */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x == 0) {   /* x is false */
    if(y < 0) {
      /* No rules are needed */
      answer = 0;
    } else if(y == 0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond,
			 1, &y, neg_cond, table);

  } else {             /* x is an atom */
    if(y < 0) {        /* y is true */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y == 0) {  /* y is false */
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &x, neg_cond, table);
    } else {           /* y is an atom */
      if(x != y) {
	int body[2] = {0, 0};

	body[0] = x<y ? x : y;
	body[1] = x<y ? y : x;
	answer = (*newatom)++;

	output_normal_cond(style, out, answer,
			   2, body, pos_cond, 0, NULL, neg_cond, table);
	output_normal_cond(style, out, answer,
			   0, NULL, pos_cond, 2, body, neg_cond, table);
      } else { /* Atoms are the same */
	if(pos_cond || neg_cond)
	  output_normal_cond(style, out, answer = (*newatom)++,
			     0, NULL, pos_cond, 0, NULL, neg_cond, table);
	else
	  /* Propagate an unconditional value */
	  answer = -1;
      }
    }
  }

  return answer;
}

/*
 * output_symbolic_excl -- Calculate exclusion symbolically
 */

int output_symbolic_excl(int style, FILE *out, int x, int y,
			 int pos_cond, int neg_cond, ATAB *table, int *newatom)
{
  int answer = 0;

  if(x == 0) {         /* x is false */
    if(y == 0) {
      /* No rules are needed */
      answer = 0;
    } else if(y<0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &y, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = y;
    }
  } else if(x < 0) {   /* x is true */
    if(y == 0) {       /* y is false */
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   0, NULL, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional value */
	answer = -1;
    } else if(y < 0) { /* y is true */
      /* No rules are needed */
      answer = 0;
    } else {           /* y is an atom */
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &y, neg_cond, table);
    }
  } else {             /* x is an atom */
    if(y == 0) {
      if(pos_cond || neg_cond)
	output_normal_cond(style, out, answer = (*newatom)++,
			   1, &x, pos_cond, 0, NULL, neg_cond, table);
      else
	/* Propagate an unconditional atom */
	answer = x;
    } else if(y < 0) {
      output_normal_cond(style, out, answer = (*newatom)++,
			 0, NULL, pos_cond, 1, &x, neg_cond, table);
    } else {
      if(x != y) {
	answer = (*newatom)++;
	output_normal_cond(style, out, answer,
			   1, &x, pos_cond, 1, &y, neg_cond, table);
	output_normal_cond(style, out, answer,
			   1, &y, pos_cond, 1, &x, neg_cond, table);
      } else /* Atoms are the same */
	/* No rules needed */
	/* Propagate an unconditional value */
	answer = 0;
    }
  }

  return answer;
}

/*
 * output_symbolic_adder_seq -- Produce a sequence of adders symbolically
 */

int output_symbolic_adder_seq(int style, FILE *out,
			      int bound,
			      int neg_cnt, int *neg,
			      int pos_cnt, int *pos,
			      int *weights, int bits,
			      ATAB *table, int *newatom)
{
  int i = 0, j = 0, answer = 0;
  int *sum = (int *)malloc(bits*sizeof(int));
  int *carry = (int *)malloc(bits*sizeof(int));
  int *gte = NULL;

  /* Initialize vectors */

  for(j=0; j<bits; j++) {
    sum[j] = 0;    /* False */
    carry[j] = 0;  /* False */
  }

  for(i=0; i<neg_cnt+pos_cnt; i++) { /* Process literals one by one */
    int neg_cond = i<neg_cnt ? neg[i] : 0;
    int pos_cond = i<neg_cnt ? 0 : pos[i-neg_cnt];
    int weight = weights[i];

    for(j=0; j<bits; j++) {
      int sum_bit = 0, carry_bit = 0;

      if(weight & 1) {

	sum_bit =
	  output_symbolic_eq(style, out, sum[j], j>0 ? carry[j-1] : 0,
			     pos_cond, neg_cond, table, newatom);

	if(sum[j]>0) /* Copy the value */
	  output_normal_cond(style, out, sum_bit,
			     1, &sum[j], neg_cond, 0, NULL, pos_cond, table);

	carry_bit =
	  output_symbolic_or(style, out, sum[j], j>0 ? carry[j-1] : 0,
			     pos_cond, neg_cond, table, newatom);

      } else {

	sum_bit =
	  output_symbolic_excl(style, out, sum[j], j>0 ? carry[j-1] : 0,
			       pos_cond, neg_cond, table, newatom);

	if(sum[j]>0) /* Copy the value */
	  output_normal_cond(style, out, sum_bit,
			     1, &sum[j], neg_cond, 0, NULL, pos_cond, table);

	carry_bit =
	  output_symbolic_and(style, out, sum[j], j>0 ? carry[j-1] : 0,
			      pos_cond, neg_cond, table, newatom);
      }	

      sum[j] = sum_bit;
      carry[j] = carry_bit;

      weight >>= 1;
    }
  }

  /* Test the outcome, sum[bits-1]...sum[0], against bound */

  gte = carry; /* To be reused */

  for(j = 0; j<bits; j++) {
    if(j == 0) {
      if(bound & 1)
	gte[j] = sum[j];
      else
	gte[j] = -1;  /* True */

    } else { /* j > 0 */
      if(bound & 1)
	gte[j] =
	  output_symbolic_and(style, out, sum[j], gte[j-1],
			      0, 0, table, newatom);
      else
	gte[j] =
	  output_symbolic_or(style, out, sum[j], gte[j-1],
			     0, 0, table, newatom);
    }
    bound >>= 1;
  }

  answer = gte[bits-1];

  free(sum);
  free(gte);

  return answer;
}

/* ======================== NORMALIZATION ROUTINES ======================== */

/*
 * normalize_basic -- Produce the normalized version of a basic rule
 */

void normalize_basic(ARGS *args, RULE *rule)
{
  BASIC_RULE *basic = rule->data.basic;

  args_output_normal(args, basic->head,
                      basic->pos_cnt, basic->pos,
                      basic->neg_cnt, basic->neg);
}

/*
 * normalize_constraint -- Produce the normalized version of a constraint rule
 */

void normalize_constraint(ARGS *args, RULE *rule, int is_top_level)
{
  CONSTRAINT_RULE *constraint = rule->data.constraint;
  int pos_cnt = constraint->pos_cnt,
      neg_cnt = constraint->neg_cnt,
      bound = constraint->bound;
  int style = args->style;
  FILE *out = args->out;
  ATAB *table = args->table;
  uint64_t flavors = args->flavors;
  int newatom = args->newatom;
  int savedatom = newatom;          /* for try_add_aux_choice */

  if(flavors & FL_SHUFFLE_CO)
    shuffle_literals(rule->data.constraint->neg_cnt,
                     rule->data.constraint->pos_cnt,
                     rule->data.constraint->neg);

  if(flavors & FL_KEEP_CO) {
    output_constraint(style, out, rule, table);
    return;
  }

  /* Handle special cases first */

  if(bound == 0) {

    /* The body is trivially satisfied; so create a fact */

    output_normal(style, out, constraint->head, 0, NULL, 0, NULL, table);

  } else if(bound == 1 && pos_cnt+neg_cnt>1) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */

    /* The rule corresponds to (pos_cnt+neg_cnt) basic rules
       of the following form: a :- l.*/

    output_literal_rules(style, out, rule, table);

  } else if(bound == 2 && pos_cnt+neg_cnt>2) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */
    
    if(pos_cnt+neg_cnt < 7)

      /* The rule corresponds to (pos_cnt+neg_cnt over 2) basic rules
         of the following form: a :- l_1, l_2. */

      output_literal_pair_rules(style, out, rule, table);

    else

      /* The rule corresponds to 3*(pos_cnt+neg_cnt)-2 basic rules */

      newatom = output_counting_chain(style, out, rule, table, newatom);

  } else if(bound == pos_cnt+neg_cnt) {

    if(flavors & FL_RAW) goto raw; /* Do full translation anyway */

    /* The rule corresponds to a single basic rule */

    output_normal(style, out, constraint->head,
		  pos_cnt, constraint->pos, neg_cnt, constraint->neg, table);

  } else if(bound < pos_cnt+neg_cnt) {

    /* Handle the general case: 2 < bound < pos_cnt+neg_cnt */

  raw:

    /* Evaluate conditional flavors now */

    choose_flavors_for_constraint(args, rule);
    flavors = args->flavors;

    if(flavors & FL_ANTIRAW) {

      output_constraint(style, out, rule, table);

    } else if(flavors & FL_ADDER) {
      int cnt = neg_cnt+pos_cnt, test = 0, bits = 0;
      int *weights = (int *)malloc(cnt*sizeof(int));
      int i = 0;

      /* Have to do this for the soundness of stable models: */
      newatom = remove_negative_literals(style, out, rule, table, newatom);

      for(i=0; i<cnt; i++)
        weights[i] = 1;

      while(cnt)
        bits++, cnt >>= 1;

      test = output_symbolic_adder_seq(style, out, bound, 0, NULL,
                                       constraint->pos_cnt, constraint->pos,
                                       weights, bits, table, &newatom);

      output_normal(style, out, constraint->head, 1, &test, 0, NULL, table);

    } else if(flavors & FL_BINARY) {

      /* The rule corresponds to a total of
         3*(pos_cnt+neg_cnt)*log_2(bound) basic rules */

      newatom = output_counting_net(style, out, rule, table, newatom);

    } else if(flavors & FL_UNARY) {

      /* The rule corresponds to a total of
         2*(pos_cnt+neg_cnt)*bound - bound^2 + 1 basic rules */

      newatom = remove_negative_literals(style, out, rule, table, newatom);
      newatom = output_counting_triangle(style, out, rule, table, newatom);

    }

    else /* if(flavors & FL_CO_UNARY_SORT) */ {

      output_unary_sorter_tester(args, rule);
      newatom = args->newatom;

    }

#if 0
    else /* The rule corresponds to a total of
            2*(pos_cnt+neg_cnt)*bound - 2*bound^2 + bound + 1 basic rules */

      newatom = output_counting_grid(style, out, rule, table, newatom);
#endif
  }

  args->newatom = newatom;

  if(is_top_level)
    try_add_aux_choice(args, constraint->head, savedatom, newatom);
}

/*
 * normalize_choice -- Produce the normalized version of a choice rule
 */

void normalize_choice(ARGS *args, RULE *rule)
{
  CHOICE_RULE *choice = rule->data.choice;
  int head_cnt = choice->head_cnt;
  int pos_cnt = choice->pos_cnt;
  int neg_cnt = choice->neg_cnt;
  int *scan = NULL;
  int *last = NULL;
  int body = 0;

  if(head_cnt == 0)
    return;

  /* Check FL_KEEP_CH, then FL_CH_EXTERNAL and finally FL_ANTIRAW */

  if(args->flavors & FL_KEEP_CH) {
    args_output_choice(args, rule);
    return;
  }

  if((args->flavors & FL_CH_EXTERNAL) && (pos_cnt == 0) && (neg_cnt == 0)) {

    /* Mark the head atoms as (external) input */

#if 1
    if(set_statuses(args->table, head_cnt, choice->head, MARK_INPUT))
      return;
#if ERROR_ON_MISSING_CH_HEAD
    else
      error("choice rule head atom is missing a symbol table entry");
#endif
#else
    /* This alone is not better than the above, because if the above fails the
     * head contains atoms without names and this will not fix that */
    set_statuses_safe(args->table, head_cnt, choice->head, MARK_INPUT);
    return;
#endif
  }

  if(args->flavors & FL_ANTIRAW) {
    args_output_choice(args, rule);
    return;
  }

  if(head_cnt>1 && pos_cnt+neg_cnt>0) {
    
    /* Create a shorthand for the body to avoid
       unnecessary (quadratic) copying of the body */

    body = args->newatom++;
    args_output_normal(args, body,
                        pos_cnt, choice->pos,
                        neg_cnt, choice->neg);
  }

  /* Process head atoms in order */

  for(scan = choice->head, last = &scan[head_cnt]; scan != last; ) {
    int head = *scan++;
    int neg_head = args->newatom++;

    /* Create a basic rule for deriving this head atom */

    if(body)
      args_output_normal(args, head, 1, &body, 1, &neg_head);
    else {
      int *new_neg = (int *)malloc((neg_cnt+1)*sizeof(int));

      memcpy(new_neg, choice->neg, neg_cnt*sizeof(int));
      new_neg[neg_cnt] = neg_head;

      args_output_normal(args, head,
                          pos_cnt, choice->pos,
                          neg_cnt + 1, new_neg);

      free(new_neg);
    }

    /* Create a basic rule for deriving the complement of this head atom */

    args_output_normal(args, neg_head, 0, NULL, 1, &head);
  }
}

void normalize_choice_head(ARGS *args, int head_cnt, int *head)
{
  RULE chrule;
  CHOICE_RULE choice;
  choice.head_cnt = head_cnt;
  choice.pos_cnt  = 0;
  choice.neg_cnt  = 0;
  choice.head     = head;
  choice.pos      = NULL;
  choice.neg      = NULL;
  chrule.data.choice = &choice;
  normalize_choice(args, &chrule);
}

/*
 * Gather atoms with given status into a choice rule
 *
 * This is based on write_input in output.c
 */

void gather_table_atoms(ATAB *table, int mask, int *pcount, int **patoms)
{
  ATAB *scan = table;
  int head_count = 0;
  int i = 0;

  /* Count head atoms */

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int shift = scan->shift;
    SYMBOL **names = scan->names;
    int *statuses = scan->statuses;

    for(i=1; i<=count; i++)
      if(names[i] && (statuses[i] & mask))
        head_count++;

    scan = scan->next;
  }

  int *atoms = malloc(head_count * sizeof(*atoms));
  scan = table;
  i = 0;

  while(scan) {
    int count = scan->count;
    int offset = scan->offset;
    int shift = scan->shift;
    SYMBOL **names = scan->names;
    int *statuses = scan->statuses;
    int j = 0;

    for(j=1; j<=count; j++) {
      int atom = j+offset;

      if(names[j] && (statuses[j] & mask))
        atoms[i++] = atom;
    }

    scan = scan->next;
  }

  *pcount = head_count;
  *patoms = atoms;
}

/* Normalize input atoms stored in the table */

void normalize_input(ARGS *args)
{
  int head_cnt = 0, *head = NULL;
  uint64_t s = args->flavors;

  /* Disable the option for turning choice atoms into external/input atoms */
  args->flavors &= ~FL_CH_EXTERNAL;

  gather_table_atoms(args->table, MARK_INPUT, &head_cnt, &head);
  normalize_choice_head(args, head_cnt, head);
  free(head);

  args->flavors = s;
}

/*
 * normalize_disjunctive -- Copy proper disjunctive rules as is
 */

void normalize_disjunctive(ARGS *args, RULE *rule)
{
  DISJUNCTIVE_RULE *disjunctive = rule->data.disjunctive;

  args_output_disjunctive(args, rule);
}

/* ------------------------------------------------------------------------ */

/*
 * Repeat non-unary weight atoms to make a constraint rule
 */

RULE *stretch_weight(RULE *rule)
{
  int i, j, k;
  int neg_sum = 0, pos_sum = 0;
  int sum;
  WEIGHT_RULE *weight = rule->data.weight;
  int neg_cnt = weight->neg_cnt, pos_cnt = weight->pos_cnt;
  int *neg = weight->neg, *pos = weight->pos;
  int cnt = neg_cnt + pos_cnt;
  int *w = weight->weight;
  RULE *new;
  CONSTRAINT_RULE *constraint;

  /* Compute negative and positive sums that will be the new atom counts */

  for(i = 0; i < neg_cnt; i++)
    neg_sum += w[i];
  for(; i < cnt; i++)
    pos_sum += w[i];

  sum = neg_sum + pos_sum;

  /* Create new negative and positive arrays */

  int * const new_neg = (int *)malloc(sum * sizeof(int));
  int * const new_pos = &new_neg[neg_sum];

  for(k = i = 0; i < neg_cnt; i++)
    for(j = 0; j < w[i]; j++, k++)
      new_neg[k] = neg[i];

  for(k = i = 0; i < pos_cnt; i++)
    for(j = 0; j < w[neg_cnt + i]; j++, k++)
      new_pos[k] = pos[i];

  /* Return a new constraint rule */

  new = (RULE *)malloc(sizeof(RULE));
  constraint = (CONSTRAINT_RULE *)malloc(sizeof(CONSTRAINT_RULE));

  new->type = TYPE_CONSTRAINT;
  new->data.constraint = constraint;
  new->next = NULL;

  constraint->head = weight->head;
  constraint->bound = weight->bound;
  constraint->neg_cnt = neg_sum;
  constraint->neg = new_neg;
  constraint->pos_cnt = pos_sum;
  constraint->pos = new_pos;
  return new;
}

/*
 *
 */

void normalize_weight_as_constraint(ARGS *args, RULE *rule)
{
  RULE * const new = stretch_weight(rule);
  CONSTRAINT_RULE * const constraint = new->data.constraint;
  normalize_constraint(args, new, 0);
  free(constraint->neg);
  free(constraint);
  free(new);
}

/*
 * is_weight_rule_cardinality -- Check if a weight rule is really a constraint
 */

int is_weight_rule_cardinality(RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;
  const int cnt = weight->neg_cnt + weight->pos_cnt;
  int * const w = weight->weight;
  int r = 1;
  int i;

  // TODO: Check if they are all equal, not necessarily one
  // EDIT: We might not actually need that, considering how this is used
  for (i = 0; (i < cnt) && r; i++)
    r = (w[i] == 1);

  return r;
}

/* ------------------------------------------------------------------------ */

/*
 * Like exponential_basic_count, but with the sum of weights specified
 */

int exponential_basic_count_sub(int bound, int sum, int cnt, int *weight,
                                int limit)
{
  int basic_cnt;

  /* Base cases */
  
  if(bound <= 0)
    return 1;
  if(cnt == 0)
    return 0;
  if(sum < bound)
    return 0;
  if(bound == sum)
    return 1;

  /* Branching */

  basic_cnt
    = 1 + exponential_basic_count_sub(bound - weight[0], sum - weight[0],
                                      cnt - 1, &weight[1], limit - 1);

  if(limit <= basic_cnt)
    return limit;

  return basic_cnt + exponential_basic_count_sub(bound, sum - weight[0],
                                                 cnt - 1, &weight[1],
                                                 limit - basic_cnt);
}

/*
 * Count the number of basic rules output by the exponential weight
 * translation if that count is below a given number and otherwise
 * return something no less than that number
 */

int exponential_basic_count(int bound, int cnt, int *weight, int limit)
{
  return exponential_basic_count_sub(bound, int_array_sum(cnt, weight),
                                     cnt, weight, limit);
}

/*
 * Real implementation of output_exponential
 */

void output_exponential_sub(ARGS *args, 
                            int head,
                            int bound, int sum,
                            int neg_cnt, int *neg,
                            int pos_cnt, int *pos,
                            int *weight)
{
  int i;
  int asnormal;
  int only_with;
  int use_pos = !neg_cnt;
  int use_neg = !use_pos;

  /* Base cases */

  if(bound <= 0) {
    args_output_normal(args, head, 0, NULL, 0, NULL);
    return;
  }

  if(!neg_cnt && !pos_cnt)
    return;

  if(sum < bound)
    return;

  /* See if the rest can be ouput directly */

  asnormal = 1;

  if(bound != sum)
    for(i = 0; i < neg_cnt + pos_cnt && asnormal; i++)
      if(bound <= sum - weight[i])
        asnormal = 0;

  if(asnormal) {
    args_output_normal(args, head, pos_cnt, pos, neg_cnt, neg);
    return;
  }

  /* Branching */

  if(bound <= weight[0])

    args_output_normal(args, head, use_pos, pos, use_neg, neg);

  else {

    /* Branch with the current literal */

    only_with = args->newatom++;

    if(use_neg)
      args_output_normal(args, head, 1, &only_with, 1, neg);
    else {
      int buf[2];
      buf[0] = *pos;
      buf[1] = only_with;
      args_output_normal(args, head, 2, buf, 0, NULL);
    }

    output_exponential_sub(args, only_with,
                           bound - weight[0], sum - weight[0],
                           neg_cnt - use_neg, &neg[use_neg],
                           pos_cnt - use_pos, &pos[use_pos],
                           &weight[1]);
  }

  /* Branch without caring about the current literal */

  output_exponential_sub(args, head,
                         bound, sum - weight[0],
                         neg_cnt - use_neg, &neg[use_neg],
                         pos_cnt - use_pos, &pos[use_pos],
                         &weight[1]);
}

/*
 * output_exponential -- Translate weight exponentially
 */

void output_exponential(ARGS *args, RULE *rule)
{
  WEIGHT_RULE * const weight = rule->data.weight;
  const int cnt = weight->neg_cnt + weight->pos_cnt;

  output_exponential_sub(args, weight->head, weight->bound,
                         int_array_sum(cnt, weight->weight),
                         weight->neg_cnt, weight->neg,
                         weight->pos_cnt, weight->pos,
                         weight->weight);
}

/*
 * normalize_weight -- Produce the normalized version of a weight rule
 */

int normalize_weight(int style, FILE *out, RULE *rule,
		     ATAB *table, uint64_t flavors, int newatom)
{
  int head = 0, pos_cnt = 0, neg_cnt = 0, bound = 0;
  int sum = 0, bits = 0, test = 0;
  int i = 0;

  WEIGHT_RULE *weight = rule->data.weight;

  /* Perform preliminary simplifications */

  sum = simplify_weight_more(style, out, rule, table, flavors);
  if (!sum)
    return newatom;

  /* Now (0 < bound < sum) holds and the body is non-empty */

  newatom = remove_negative_literals(style, out, rule, table, newatom);

  bound = weight->bound;
  head = weight->head;
  pos_cnt = weight->pos_cnt;
  neg_cnt = weight->neg_cnt;

  /* Handle the general case */

  i = sum;

  while(i>0)
    bits++, i >>= 1;

  test = output_symbolic_adder_seq(style, out, bound,
				   neg_cnt, weight->neg,
				   pos_cnt, weight->pos,
				   weight->weight, bits,
				   table, &newatom);

  output_normal(style, out, head, 1, &test, 0, NULL, table);

  return newatom;
}

/*
 *
 */

void free_weight_rule(RULE *rule)
{
  free(rule->data.weight->neg); /* includes ->pos and ->weight, see input.c */
  free(rule->data.weight);
  free(rule);
}

/* ------------------------------------------------------------------------- */

/*
 *
 */

void normalize_weight_2(ARGS *args, RULE *rule, int is_top_level)
{
  uint64_t flavors = args->flavors;
  int decompose_please = (flavors & FL_WT_BIT_DECOMPOSE);
  int savedatom = args->newatom;    /* for try_add_aux_choice */

  if(flavors & FL_KEEP_WT) {
    permute_weight_rule_in_place(args, rule);
    args_output_weight(args, rule);
    return;
  }

  if(!(flavors & FL_RAW)) {

    if(simplify_weight_2(args, rule) < 0)
      return; /* Nothing was left of the rule after simplification */

    if(is_weight_rule_cardinality(rule)) {
      normalize_weight_as_constraint(args, rule);
      goto end;
    }
  }

  if(decompose_please)

    rule = decompose_weight(rule);

  /* Evaluate conditional flavors now */

  choose_flavors_for_weight(args, rule);
  flavors = args->flavors;

  if(flavors & FL_ANTIRAW) {

    /* Skip translations */

    permute_weight_rule_in_place(args, rule);
    args_output_weight(args, rule);

  } else {

    if(flavors & FL_WT_ADDER) {

      permute_weight_rule_in_place(args, rule);
      args->newatom = normalize_weight(args->style, args->out, rule,
                                        args->table, flavors, args->newatom);

    } else if(flavors & FL_WT_MIX_UNR)

      output_mixed_radix_weight_counter(args, rule);

    else if(flavors & FL_WT_STRETCH) {

      permute_weight_rule_in_place(args, rule);
      normalize_weight_as_constraint(args, rule);

    } else if(flavors & FL_WT_EXP) {

      permute_weight_rule_in_place(args, rule);
      output_exponential(args, rule);

    } else if(flavors & FL_ROBDD)

      output_bdd(args, rule);

    else if(flavors & FL_WT_UNARY_SORT)

      output_unary_weight_tester(args, rule);

    else /* if(flavors & FL_WT_PLAN) */

      output_planned_weight_counter(args, rule);
  }

  if(decompose_please)
    free_weight_rule(rule);

end:
  if(is_top_level)
    try_add_aux_choice(args, rule->data.weight->head, savedatom, args->newatom);
}

/* ---------------------- Optimize Statements ----------------------------- */

/*
 * Find a symbol matching a formatted optimization atom name
 */

SYMBOL *find_optimize_format_symbol(char *optimize_format, int opt_num,
                                    int index, int atom, int weight)
{
  char *from = NULL;
  char *to = NULL;
  char p = '\0';

  char buffer[SYMBOL_MAX_LEN];
  int i = 0;
  int n = SYMBOL_MAX_LEN;

  for(from = to = optimize_format; (i < n) && (*to != '\0'); to++) {

    char c = *to;
    int inc = 0;

    if(c == '%') {
      if(from < to) {
        inc = MIN(n - i - 1, (int) (to - from));
        snprintf(&buffer[i], inc + 1, "%s", from);
      }
      from = to + 2;
    } else if(p == '%') {
      switch(c) { // TODO: Add 0 and 1 indexed variants
        case 'o' : inc = snprintf(&buffer[i], n - i, "%i", opt_num); break;
        case 'i' : inc = snprintf(&buffer[i], n - i, "%i", index);   break;
        case 'a' : inc = snprintf(&buffer[i], n - i, "%i", atom);    break;
        case 'w' : inc = snprintf(&buffer[i], n - i, "%i", weight);  break;
        default  : from -= 2;
      }
      inc = MIN(n - i - 1, inc);
    }

    p = c;
    i += inc;
  }

  if((i < n) && (from < to))
    snprintf(&buffer[i], MIN(n - i, (int) (to - from + 1)), "%s", from);

  buffer[i] = '\0';
  return find_symbol(buffer);
}

/*
 * Give optimize atoms formatted names
 */

void add_optimize_format_names(ARGS *args, int cnt, int *atoms, int *weights)
{
  ATAB *piece = extend_table_with_array(args->table, cnt, atoms);
  int opt_num = args->newopt++;
  int i;

  for(i = 0; i < cnt; i++)
    piece->names[atoms[i] - piece->offset]
      = find_optimize_format_symbol(args->optimize_format, opt_num, i,
                                    atoms[i], weights[i]);
}

int is_optimize_empty(RULE *rule)
{
  const int r = !int_array_or(rule->data.optimize->neg_cnt
                          + rule->data.optimize->pos_cnt,
                          rule->data.optimize->weight);
#if DEBUG_OPT_EMPTY
  fprintf(stderr, "%% is_optimize_empty(%s, %s, %s) -> %i\n",
          a2x(rule->data.optimize->neg_cnt, rule->data.optimize->neg),
          a2x(rule->data.optimize->pos_cnt, rule->data.optimize->pos),
          a2x(rule->data.optimize->neg_cnt
              + rule->data.optimize->pos_cnt,
              rule->data.optimize->weight),
          r);
#endif
  return r;
}

/*
 * Convert a cardinality rule body into a weight rule body by combining runs of
 * literals into one
 * NOTE: body must have capacity for 2*cnt literals
 */

int cardinality_to_weight_body(int cnt, int *body)
{
  int i, s = 0, new_cnt = 0, *weights = &body[cnt];
  for(i = 1; i < cnt; i++)
    if(body[s] != body[i]) {
      weights[new_cnt] = i - s;
      body[new_cnt] = body[s];
      new_cnt++;
      s = i;
    }
  weights[new_cnt] = i - s;
  body[new_cnt] = body[s];
  new_cnt++;

  int_array_copy(new_cnt, &body[new_cnt], weights);

  return new_cnt;
}

/*
 * Sort optimize statement literals in place
 */

void sort_optimize(ARGS *args, RULE *rule)
{
  OPTIMIZE_RULE * const optimize = rule->data.optimize;
  const int tot_cnt = optimize->neg_cnt + optimize->pos_cnt;

  /* Compute upper and lower bounds to be used with this rule, excluding and
     including any padding required to express any requested integrity
     constraints or to leave room for offset facts */

  const int wsum = int_array_sum(tot_cnt, optimize->weight);

  const int bound_lo = MAX(0, args->optimize_lb);
  const int bound_up = MIN(wsum, args->optimize_ub);

  const int integrity_lo = (args->flavors & FL_OPT_SORT_LB_INTEGRITY ? 1 : 0);
  const int integrity_up = (args->flavors & FL_OPT_SORT_UB_INTEGRITY ? 1 : 0);

  const int wanted_lo = MAX(args->optimize_lb - integrity_lo, 0);
  const int wanted_hi = MIN(args->optimize_ub + integrity_up, wsum);

  const int padding_lo = bound_lo - wanted_lo;
  const int padding_up = wanted_hi - bound_up;

  const int output_lo = bound_lo - (bound_lo ? 1 : 0);
  const int output_up = bound_up;

  if(bound_up < bound_lo) {
    litint_output_normal(args, args->falsity, 0, NULL);
    return;
  }

  int *res = (int *)malloc(2 * output_up * sizeof(int));
  int i, new_cnt, body[2], startatom = args->newatom;

  /* Prepare the input and result arrays for a sorter and then output it */

  litint_from_neg(optimize->neg_cnt, optimize->neg);
  permute_weighted_array_in_place(args, tot_cnt, optimize->neg,
                                  optimize->weight);

  int_array_fill(wanted_lo, res, SMX_DONT_CARE);
  int_array_fill(wanted_hi - wanted_lo, &res[wanted_lo], SMX_WANTED);

  output_unary_weight_sorter(args, wanted_hi, res,
                             tot_cnt, optimize->neg, optimize->weight,
                             &startatom);

  free(optimize->neg);  /* This frees pos & weight as well */

  /* Take care of constraints and prepare for optimization value offsets */

  if(padding_lo)        /* Add a constraint to enforce the lower bound */
    litint_output_normal_1(args, args->falsity, MIX_COMPLEMENT(res[wanted_lo]));
  else if(bound_lo)     /* Add a dummy "fact" used to offset optimize values */
    res[output_lo] = MIX_GET_NEG(args->falsity);

  if(padding_up)        /* Add a constraint to enforce the upper bound */
    litint_output_normal_1(args, args->falsity, res[bound_up]);

  /* Compute new count and reposition res */

  new_cnt = output_up - output_lo;
  if(0 < output_lo)
    int_array_copy(new_cnt, res, &res[output_lo]);

  /* Add weights to the result and possibly try to compress it */

  if(args->flavors & FL_OPT_SORT_UNIT)
    int_array_fill(new_cnt, &res[new_cnt], 1);
  else
    new_cnt = cardinality_to_weight_body(new_cnt, res);

  /* Take care of offsetting optimization values */

  if(bound_lo)
    res[new_cnt] = bound_lo;

  if(new_cnt != output_up)
    res = realloc(res, 2 * new_cnt * sizeof(int));

  /* Give names to new atoms */

  if(*args->optimize_format != '\0') {
    litint_rename_neg(args, new_cnt, res);
    add_optimize_format_names(args, new_cnt, res, &res[new_cnt]);
  }

  /* Add rules or constraints saying the result must be sorted */

  if(args->flavors & FL_OPT_SORT_RULE)
    for(i = MAX(wanted_lo - output_lo, 0); i < new_cnt - 1; i++)
      litint_output_normal_1(args, res[i], res[i + 1]);
  else if(args->flavors & FL_OPT_SORT_INTEGRITY) {
    for(i = MAX(wanted_lo - output_lo, 0); i < new_cnt - 1; i++) {
      body[0] = MIX_COMPLEMENT(res[i]);
      body[1] = res[i + 1];
      litint_output_normal(args, args->falsity, 2, body);
    }
  }

  /* Package everything back into the rule and output it */

  litint_to_optimize(new_cnt, res, optimize);
  args_output_optimize(args, rule);
}

/*
 *
 */

void normalize_optimize_as_weight(ARGS *args, RULE *rule)
{
  OPTIMIZE_RULE *optimize = rule->data.optimize;
  RULE *new;
  WEIGHT_RULE *weight;
  int total_weight, bit_cnt;
  int neg_cnt = optimize->neg_cnt, pos_cnt = optimize->pos_cnt;
  int *opt_neg = optimize->neg, *opt_pos = optimize->pos;
  int *opt_weight = optimize->weight;
  int *new_neg, *new_pos, *new_bit, *new_weight;
  int i, b;

  /* Allocate a new weight rule */

  new = (RULE *)malloc(sizeof(RULE));
  weight = (WEIGHT_RULE *)malloc(sizeof(WEIGHT_RULE));

  new->type = TYPE_WEIGHT;
  new->data.weight = weight;
  new->next = NULL;

  /* Count the number of bits needed */

  for(total_weight = 0, i = 0; i < neg_cnt+pos_cnt; i++)
    total_weight += opt_weight[i];

  /* + 1 compensates for the effective use of a proper upper bound */

  bit_cnt = int_ceil_log(total_weight + 1);

  new_neg = (int *)malloc(2 * (neg_cnt+bit_cnt+pos_cnt) * sizeof(int));
  new_bit = &new_neg[neg_cnt];
  new_pos = &new_bit[bit_cnt];
  new_weight = &new_pos[pos_cnt];

  weight->neg = new_neg;
  weight->pos = new_pos;
  weight->weight = new_weight;
  weight->neg_cnt = neg_cnt + bit_cnt;
  weight->pos_cnt = pos_cnt;
  weight->head = args->falsity;

  /* Copy negative atoms and their respective weights */

  for(i = 0; i < neg_cnt; i++) {
    new_neg[i] = opt_neg[i];
    new_weight[i] = opt_weight[i];
  }

  /* Insert new bound bit atoms (as negative literals) */

  for(b = 1, i = 0; i < bit_cnt; i++, b <<= 1) {
    new_bit[i] = args->newatom++;
    new_weight[neg_cnt+i] = b;
  }

  /* Set the bound to be the sum of the bit weights + 1 */

  weight->bound = b;

  /* Copy positive atoms and their respective weights */

  for(i = 0; i < pos_cnt; i++) {
    new_pos[i] = opt_pos[i];
    new_weight[neg_cnt+bit_cnt+i] = opt_weight[neg_cnt+i];
  }

  if(*args->optimize_format != '\0') {

    /* Name the bit atoms so that normalize_choice will work properly */

    ATAB *piece = extend_table(args->table, bit_cnt, new_bit[0] - 1);
    int opt_num = args->newopt++;

    for(i = 0; i < bit_cnt; i++)
      piece->names[i + 1]
        = find_optimize_format_symbol(args->optimize_format, opt_num, i,
                                      new_bit[i], new_weight[neg_cnt + i]);
  }

  /* Output a choice rule for the optimize bits */

  normalize_choice_head(args, bit_cnt, new_bit);

  /* Output a replacement optimization rule if wanted */

  if(args->flavors & FL_OPT_OPT) {

    /* Reuse the optimize rule, and loan the new weight rule */

    optimize->pos_cnt = bit_cnt;
    optimize->neg_cnt = 0;
    optimize->pos = new_bit;
    optimize->weight = &new_weight[neg_cnt];
    args_output_optimize(args, rule);
    optimize->pos_cnt = pos_cnt;
    optimize->neg_cnt = neg_cnt;
    optimize->pos = opt_pos;
    optimize->weight = opt_weight;
  }

  /* Normalize the constructed weight rule */

  normalize_weight_2(args, new, 0);

  /* Clean up */

  free(new_neg);
  free(weight);
  free(new);
}

/*
 * Replace minimization with an upper bound
 * WARNING: This changes the type of the given rule from optimize to weight
 */

void decide_optimize(ARGS *args, RULE *rule)
{
  OPTIMIZE_RULE optimize = *rule->data.optimize;
  WEIGHT_RULE *weight = rule->data.weight;
  int bound = args->optimize_ub + 1;

  /* Convert the rule in place to a weight rule */

  rule->type = TYPE_WEIGHT;

  weight->weight  = optimize.weight;
  weight->bound   = bound;
  weight->head    = args->falsity;
  weight->neg     = optimize.neg;
  weight->pos     = optimize.pos;
  weight->neg_cnt = optimize.neg_cnt;
  weight->pos_cnt = optimize.pos_cnt;

  /* Continue normalizing the weight rule */

  normalize_weight_2(args, rule, 0);
}

/*
 * Remove and return rules of a given type from a program
 */

RULE *extract_rules_by_type(RULE **program, int type)
{
  RULE **prevnext = program;
  RULE *scan = *program;
  RULE *opt_first = NULL;
  RULE *opt_last = NULL;

  while(scan) {
    if(scan->type == type) {

      if(!opt_first)
        opt_first = scan;
      else
        opt_last->next = scan;

      opt_last = scan;
      *prevnext = scan->next;
      scan->next = NULL;
      scan = *prevnext;

    } else {

      prevnext = &scan->next;
      scan = scan->next;
    }
  }

  return opt_first;
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

    int div = int_array_gcd(o->neg_cnt + o->pos_cnt, o->weight);

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

/*
 * normalize_optimize -- Normalize an optimization statement
 */

void normalize_optimize(ARGS *args, RULE *rule, int is_top_level)
{
  int savedatom = args->newatom;    /* for add_aux_choice */
  choose_flavors_for_optimize(args, rule);

  if((args->flavors & (FL_KEEP_OPT | FL_ANTIRAW)) || is_optimize_empty(rule))
    args_output_optimize(args, rule);

  else if(args->flavors & FL_OPT_WEIGHT)
    normalize_optimize_as_weight(args, rule);

  else if(args->flavors & FL_OPT_SORT)
    sort_optimize(args, rule);

  else if(args->flavors & FL_OPT_PLAN)
    plan_optimize(args, rule);

  else if(args->flavors & FL_OPT_DECISION)
    decide_optimize(args, rule);

  else
    args_output_optimize(args, rule);

  if(is_top_level)
    add_aux_choice(args, savedatom, args->newatom);
}

/*
 *
 */

void merge_and_normalize_optimize_statements(ARGS *args, RULE *statements)
{
  RULE *rule = merge_optimize_statements(statements);

  normalize_optimize(args, rule, 1);

  free(rule->data.optimize->neg);
  free(rule->data.optimize);
  free(rule);
}

/* ------------------------------------------------------------------------- */

/*
 * normalize_rule --- Produce the normalized version of a rule
 */

void normalize_rule(ARGS *args, RULE *rule)
{
  switch(rule->type) {
  case TYPE_BASIC:

    normalize_basic(args, rule);
    break;

  case TYPE_CONSTRAINT:

    normalize_constraint(args, rule, 1);
    break;

  case TYPE_CHOICE:

    normalize_choice(args, rule);
    break;

  case TYPE_WEIGHT:

    normalize_weight_2(args, rule, 1);
    break;

  case TYPE_OPTIMIZE:

    normalize_optimize(args, rule, 1);
    break;

  case TYPE_DISJUNCTIVE:

    normalize_disjunctive(args, rule);
    break;

  default:
    fprintf(stderr, "%s: rule type %i not supported!\n",
	    program_name, rule->type);
    exit(-1);
  }
}

/*
 * normalize_rule --- Produce the normalized version of an entire program
 */

void normalize_program(ARGS *args, RULE *program)
{
  while(program) {
    normalize_rule(args, program);

    program = program->next;
  }
}

/* vim: set tabstop=2 shiftwidth=2 softtabstop=2 expandtab: */
