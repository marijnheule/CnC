/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>

#include "march.h"
#include "cube.h"
#include "common.h"
#include "equivalence.h"
#include "lookahead.h"
#include "parser.h"
#include "preselect.h"
#include "progressBar.h"
#include "resolvent.h"
#include "solver.h"
#include "memory.h"

void handleUNSAT () {
  if (quiet_mode == 0) {
    printf ("c main():: nodeCount: %i\n", nodeCount);
    printf ("c main():: time=%f\n", ((float)(clock()))/CLOCKS_PER_SEC); }
  if (mode == PLAIN_MODE) {
    printf( "s UNSATISFIABLE\n" ); }
  else { printUNSAT (); }
  disposeFormula();
  exit (EXIT_CODE_UNSAT); }

int main (int argc, char** argv) {
  int result   = UNKNOWN;
  int exitcode = EXIT_CODE_UNKNOWN;

  if (argc < 2) {
    printf ("c input file missing, usage: ./march_cu DIMACS-file.cnf\n");
    printf ("c run using -h for help\n");
    return EXIT_CODE_ERROR; }

  hardLimit  = 0; // no hard limit
  seed       = 0; // no initial seed
  quiet_mode = 0;
  cut_depth  = 0;
  cut_var    = 0;
  cubeLimit  = 0;
  strcpy (cubesFile, "/tmp/cubes.icnf");

  h_min      = H_MIN;
  h_max      = H_MAX;
  h_bin      = H_BIN;
  h_dec      = H_DEC;
  sl_iter    = SL_ITER;
  dl_iter    = DL_ITER;
//  mode       = PLAIN_MODE;
  mode       = CUBE_MODE;
  sharp_mode = 0;

  gah        = GAH;
  addWFR     = WFR;
  addIMP     = IMP;

#ifdef SCHUR
  dl_iter    = 0;
#endif

  cweight  = 8200;
  downexp  = 0.3;
  fraction = 0.02;

  int i;
  for (i = 1; i < argc; i++)
    if (strcmp (argv[i], "-h") == 0) {
      printf("c march_cu help\n");
      printf("c USAGE: ./march_cu <input-file> [options]\n\n");
      printf("   where input may be in (uncompressed) DIMACS.\n\n");
      printf("c OPTIONS:\n\n");
      printf("   -h            prints this help message\n");
      printf("   -p            plain / no cube mode\n");
//      printf("   -c <file>     parse cube from <file>    (default:             no cube)\n");
      printf("   -d <int>      set a static cutoff depth (default: %4.0f, dynamic depth)\n", (float) cut_depth);
      printf("   -n <int>      set a static cutoff vars  (default: %4.0f, dynamic depth)\n", (float) cut_var);
      printf("   -e <float>    set a down exponent       (default: %4.2f,   fast cubing)\n", downexp);
      printf("   -f <float>    set a down fraction       (default: %4.2f,   fast cubing)\n", fraction);
      printf("   -l <int>      limit the number of cubes (default: %4.0f,      no limit)\n", (float) cubeLimit);
      printf("   -s <int>      seed for heuristics       (default: %4.0f,     no random)\n", (float) seed);
      printf("   -#            #SAT preprocessing only\n\n");
//      printf("   -v            more verbose output\n\n");
      printf("c OPTIONAL LOOKAHEAD TECHNIQUES (option will negate the default):\n\n");
      printf("   -gah          global autarky heuristic  (default: %s)\n",  (GAH)?"on":"off");
      printf("   -imp          add both implications     (default: %s)\n",  (IMP)?"on":"off");
      printf("   -wfr          add windfall resolvents   (default: %s)\n\n",(WFR)?"on":"off");
      printf("c OUTPUT OPTIONS:\n\n");
      printf("   -o <file>     emit the cubes to <file>  (default: %s)\n", cubesFile);
      printf("   -q            turn on quiet mode        (set default output to stdout)\n");
      printf("   -cnf          add the cnf to the cubes\n\n");
      printf("c MAGIC CONSTANTS:\n\n");
      printf("   -bin <float>  binary clause weight      (default: %6.2f)\n", H_BIN);
      printf("   -dec <float>  size exponential decay    (default: %6.2f)\n", H_DEC);
      printf("   -min <float>  minimum heuristic value   (default: %6.2f)\n", H_MIN);
      printf("   -max <float>  maximum heuristic value   (default: %6.2f)\n", H_MAX);
      printf("   -sli <int>    singlelook iterations     (default: %6.0f)\n", (float) SL_ITER);
      printf("   -dli <int>    doublelook iterations     (default: %6.0f)\n", (float) DL_ITER);
      return EXIT_CODE_UNKNOWN; }

  for (i = 2; i < argc; i++) {
    if (strcmp(argv[i], "-o"  ) == 0) { strcpy (cubesFile, argv[i+1]); }
    if (strcmp(argv[i], "-p"  ) == 0) { mode = PLAIN_MODE;             }
    if (strcmp(argv[i], "-#"  ) == 0) { sharp_mode = 1;                }
    if (strcmp(argv[i], "-q"  ) == 0) { quiet_mode = 1;                }
    if (strcmp(argv[i], "-d"  ) == 0) { cut_depth  = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-n"  ) == 0) { cut_var    = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-l"  ) == 0) { cubeLimit  = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-L"  ) == 0) { hardLimit  = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-s"  ) == 0) { seed       = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-gah") == 0) { gah       ^= 1;                }
    if (strcmp(argv[i], "-imp") == 0) { addIMP    ^= 1;                }
    if (strcmp(argv[i], "-wfr") == 0) { addWFR    ^= 1;                }
    if (strcmp(argv[i], "-min") == 0) { h_min      = atof (argv[i+1]); }
    if (strcmp(argv[i], "-max") == 0) { h_max      = atof (argv[i+1]); }
    if (strcmp(argv[i], "-bin") == 0) { h_bin      = atof (argv[i+1]); }
    if (strcmp(argv[i], "-dec") == 0) { h_dec      = atof (argv[i+1]); }
    if (strcmp(argv[i], "-sli") == 0) { sl_iter    = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-dli") == 0) { dl_iter    = strtoul (argv[i+1], NULL, 10); }
    if (strcmp(argv[i], "-e"  ) == 0) { downexp    = atof (argv[i+1]); }
    if (strcmp(argv[i], "-f"  ) == 0) { fraction   = atof (argv[i+1]); } }

  if ((mode != PLAIN_MODE) && (quiet_mode == 0)) {
    printf("c down fraction = %.3f and down exponent = %.3f\n", (float) fraction, (float) downexp);
    printf("c cubes are emitted to %s\n", cubesFile); }

  if (seed) srand (seed);

  if (!cut_var && !cut_depth) dynamic = 1;

  /***** Parsing... *******/
  runParser (argv[1]);

#ifdef SIMPLE_EQ
	if (equivalence_reasoning() == UNSAT) handleUNSAT();
#endif
        for (i = 0; i < nrofclauses; i++)
          if (Clength[i] > 3) {
            kSAT_flag = 1; break; }

        if (quiet_mode == 0) {
          if (kSAT_flag) {
            printf("c clause-length heuristic with magic constants: bin = %.2f and dec = %.2f\n", h_bin, h_dec); }
	  else {
            printf("c literal-weight heuristic with magic constants: min = %.2f, bin = %.2f, and max = %.2f\n", h_min, h_bin, h_max); } }

#ifndef TERNARYLOOK
#ifdef RESOLVENTLOOK
	if (resolvent_look() == UNSAT) handleUNSAT();
#endif
#endif
        if (kSAT_flag)         allocate_big_clauses_datastructures();

	depth                 = 0;   // to solver.c ?
        nodeCount             = 0;
        lookAheadCount        = 0;
        unitResolveCount      = 0;
	necessary_assignments = 0;

        int* status;
        status = (int*) malloc (sizeof (int) * (2 * nrofvars + 1));
        for (i = 0; i <= 2* nrofvars; i++) status[i] = 0;
        status += nrofvars;

        for (i = 0; i < nrofclauses; i++) {
          if (Clength[i] == 2) {
            if (!status[Cv[i][0]]) { status[Cv[i][0]] = Cv[i][1]; }
            else                   { status[Cv[i][0]] = nrofvars + 1;     }
            if (!status[Cv[i][1]]) { status[Cv[i][1]] = Cv[i][0]; }
            else                   { status[Cv[i][1]] = nrofvars + 1;     } }
          if (Clength[i] > 2) {
            int j;
            for (j = 0; j < Clength[i]; j++)
              status[Cv[i][j]] = nrofvars + 1; } }
     if (sharp_mode == 1) {
        int count = 0, out = 0;
        for (i = 1; i <= nrofvars; i++) {
          if (status[i] && status[i] == -status[-i]) {
            status[status[ i]] = nrofvars + 1;
            status[status[-i]] = nrofvars + 1;
            if (count == 0) printf("c free #SAT variables:");
            count++; out += 2;
            printf(" %i", i);
          }
          if (!status[i] && !status[-i] && !timeAssignments[i]) {
            if (count == 0) printf("c free #SAT variables:");
            count++; out += 1;
            printf(" %i", i);
          }
        }
        if (count) printf("\nc number free #SAT variables: %i\n", count);
        if (out == freevars) printf("c all remaing variables are free #SAT: 2^%i solutions\n", count);
     }


	if (initSolver ())
	{
#ifdef TIMEOUT
		printf ("c timeout = %i seconds\n", TIMEOUT);
#endif
#ifdef PROGRESS_BAR
		pb_init (6);
#endif
#ifdef DISTRIBUTION
		result = distribution_branching();
#else
#ifdef SUPER_LINEAR
		result = super_linear_branching();
#else
		result = march_solve_rec();
#endif
#endif

#ifdef PROGRESS_BAR
		pb_dispose();
#endif
	}
	else
	{
		printf( "c main():: conflict caused by unary equivalence clause found.\n" );
		result = UNSAT;
	}
        if (quiet_mode == 0) {
#ifdef CUBE
          nodeCount = getNodes ();
#endif
          printf ("c main():: nodeCount: %i\n", nodeCount);
          printf ("c main():: dead ends in main: %i\n", mainDead);
          printf ("c main():: lookAheadCount: %lli\n", lookAheadCount);
          printf ("c main():: unitResolveCount: %i\n", unitResolveCount);
          printf ("c time = %.2f seconds\n", ((float)(clock()))/CLOCKS_PER_SEC);
          printf ("c main():: necessary_assignments: %i\n", necessary_assignments); }

#ifdef COUNT_SAT
	printf ("c main():: found %i solutions\n", count_sat);
	if (count_sat > 0) result = SAT;
#endif

	switch (result)
	{
	    case SAT:
		printf( "s SATISFIABLE\n" );
#ifndef COUNT_SAT
                if (quiet_mode == 0)
		  printSolution (original_nrofvars);
#endif
		exitcode = EXIT_CODE_SAT;
		break;

	    case UNSAT:
               if (mode == PLAIN_MODE) {
                 printf ("s UNSATISFIABLE\n");
  	         exitcode = EXIT_CODE_UNSAT; }
               else {

            printDecisionTree (); }
	       break;

	    default:
		printf( "s UNKNOWN\n" );
		exitcode = EXIT_CODE_UNKNOWN;
            printDecisionTree ();
        }

	disposeSolver();

	disposeFormula();

        return exitcode;
}

void runParser (char* fname) {
  FILE* in;

  if ((in = fopen (fname, "r")) == NULL) {
    printf ("c runParser():: input file could not be opened!\n");
    exit (EXIT_CODE_ERROR); }

  if (!initFormula (in)) {
    printf ("c runParser():: p-line not found in input, but required by DIMACS format!\n");
    fclose (in);
    exit (EXIT_CODE_ERROR); }

  if (!parseCNF(in)) {
    printf ("c runParser():: parse error in input!\n");
    fclose (in);
    exit (EXIT_CODE_ERROR); }

  fclose (in);

  init_equivalence();

  if (simplify_formula () == UNSAT) {
    if (quiet_mode == 0) {
      printf ("c runParser():: conflicting unary clauses, so instance is unsatisfiable!\n");
      printf( "c time = %.2f seconds\n", ((float)(clock()))/CLOCKS_PER_SEC ); }
    printUNSAT ();
    printf ("s UNSATISFIABLE\n");
    disposeFormula ();
    exit (EXIT_CODE_UNSAT); }
}
