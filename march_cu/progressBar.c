/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]

   This file contains the code for the progress bar
*/

#include <stdio.h>
#include <stdlib.h>

#include "progressBar.h"
#include "common.h"

int pb_count, pb_best, pb_granularity, pb_currentDepth, pb_branchCounted;

void pb_init (int granularity) {
  if (quiet_mode) return;

  if (granularity < 1 || granularity > 6)
    exit (EXIT_CODE_ERROR);

  pb_granularity = granularity - 1;
  pb_currentDepth = 0;
  pb_branchCounted = 0;
  pb_count = 0;
  pb_best  = 10000;

  printf ("c |");
  int i; for (i = 0; i < (1 << granularity); i++) printf("-");
  printf ("|");
  fflush (stdout); }

void pb_reset () {
  pb_currentDepth = 0;
  pb_branchCounted = 0;
  pb_count = 0;
#ifdef DISTRIBUTION
  printf ("| (");
  if ((jump_depth >= 10) && (target_rights < 10)) printf(" ");
  printf ("%i/%i) NodeCount: %i\nc |", target_rights, jump_depth, nodeCount);
#else
  printf ("| NodeCount: %i\nc |", nodeCount);
#endif
  int i; for (i = 0; i < (1 << (pb_granularity+1)); i++) printf("-");
  printf ("|");
  fflush (stdout); }

void pb_dispose () {
  if (quiet_mode) return;
  pb_update ();
  printf ("\nc\n"); }

void pb_update () {
  if (quiet_mode) return;
  printf( "\rc |" );
  int i; for( i = 0; i < pb_count; i++) printf ("*");
  fflush (stdout); }

void pb_descend () {
  if (quiet_mode) return;
  pb_branchCounted = 0;
  pb_currentDepth++; }

void pb_climb () {
  if (quiet_mode) return;
  pb_currentDepth--;

  if (pb_currentDepth < pb_best) {
    if (pb_best == 6) {
      printf( "c |" );
      int i; for (i = 0; i < (1 << (pb_granularity + 1)); i++) printf("-");
      printf ("|");
      fflush (stdout); pb_best = 5; }

    if (pb_best >= 6) {
      pb_best = pb_currentDepth;
    printf("\rc");
//      printf("\rc rough runtime estimate: %f seconds\n", pow(pb_best, 2) * ((float)(clock()))/CLOCKS_PER_SEC );
    }
  }

  if ((pb_currentDepth == pb_granularity) || (pb_currentDepth < pb_granularity && !pb_branchCounted)) {
    pb_branchCounted = 1;
    pb_count += 1 << (pb_granularity - pb_currentDepth);
    pb_update (); }
}

