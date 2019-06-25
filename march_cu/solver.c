/* MARCH Satisfiability Solver

   Copyright (C) Marijn Heule

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
*/


//#define BACKJUMP

//#define LOCAL_AUTARKY
//#define DETECT_COMPONENTS
//#define COMPENSATION_RESOLVENTS

#define SAT_INCREASE	1000

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <math.h>

#include "common.h"
#include "cube.h"
#include "distribution.h"
#include "solver.h"
#include "equivalence.h"
#include "preselect.h"
#include "memory.h"
#include "lookahead.h"
#include "progressBar.h"
#include "parser.h"
#include "microsat.h"


#define CONTINUE	1
#define FINISHED	0

#define IS_REDUCED_TIMP( __a, __b )	((timeAssignments[__a] < NARY_MAX) && (timeAssignments[__b] == (NARY_MAX+1)) )

#ifdef DISTRIBUTION
  #define LEFT_CHILD	 records[record_index].child[branch_literal > 0]
  #define RIGHT_CHILD	 records[record_index].child[branch_literal < 0]
#endif

struct solver CDCL;

int sl_depth;

int *tmpEqImpSize;

int *var_weight;

int *TernaryImpTable, *TernaryImpLast;
int current_bImp_stamp, *bImp_stamps;

int *newbistack, *newbistackp, newbistackSize;
int *substack,   *substackp,   substackSize;

int analyze_autarky();

int nrofforced;

unsigned long long solution_bin = 0;
unsigned int solution_bits = 63;

int discrepancies = 0;

float first_time;
#ifdef DISTRIBUTION
int skip_flag = 0;
int first_depth = 20;
#endif
#ifdef SUBTREE_SIZE
int path_length;
#endif
#ifdef CUT_OFF
int last_SAT_bin = -1;
#endif
#ifdef BACKJUMP
int backjump_literal = 0;
#endif

int currentNodeNumber = 1;
int UNSATflag = 0;

#ifdef CUBE
//int refute_compensation;
int size_flag;
FILE *output;
int current_Dnode;
#endif

#define STAMP_IMPLICATIONS( _nrval ) \
{ \
    bImp = BIMP_START(_nrval); \
    current_bImp_stamp++; \
    bImp_stamps[ _nrval ] = current_bImp_stamp; \
    for (i = BIMP_ELEMENTS; --i; ) \
	bImp_stamps[ *(bImp++) ] = current_bImp_stamp; \
}

void push_stack_blocks () {
  PUSH (      r, STACK_BLOCK);
  PUSH (    imp, STACK_BLOCK);
  PUSH (   bieq, STACK_BLOCK);
  PUSH (subsume, STACK_BLOCK);
  current_node_stamp++; }

#ifdef PROGRESS_BAR
#define NODE_START( ) \
{ \
  push_stack_blocks( ); \
  pb_descend( ); \
}
#define NODE_END( ) \
{ \
  backtrack(); \
  pb_climb(); \
}
#else
#define NODE_START( ) \
{ \
	push_stack_blocks( ); \
}
#define NODE_END( ) \
{ \
	backtrack(); \
}
#endif \

int recursive_solve () {
  int _result = 0;

  depth++;
  PUSH (r, STACK_BLOCK);
  _result = march_solve_rec ();
  depth--;

  return _result; }

#define UPDATE_BIN( ) \
{\
    if( depth <= solution_bits ) solution_bin ^= (unsigned long long) 1 << (solution_bits - depth); \
}

/*
	----------------------------------------------------
	------------[ initializing and freeing ]------------
	----------------------------------------------------
*/
void clearTernaryImpReduction( ) {
  int i;
  for (i = 1; i <= nrofvars; i++) {
    TernaryImpReduction[  i ] = 0;
    TernaryImpReduction[ -i ] = 0; } }

void fill_ternary_implication_arrays () {
  int i, j;
  for (i = 0; i < nrofclauses; i++)
    if (Clength[ i ] == 3) {
      for (j = 0; j < 3; j++) {
        int lit = Cv[i][j];
        TernaryImp[lit][ tmpTernaryImpSize[lit]++ ] = Cv[i][(j+1)%3 ];
        TernaryImp[lit][ tmpTernaryImpSize[lit]++ ] = Cv[i][(j+2)%3 ]; } }

  for (i = -nrofvars; i <= nrofvars; i++)
    TernaryImpSize[ i ] = tmpTernaryImpSize[ i ] / 2; }

int initSolver()
{
	int i, j, _tmp;

	decisions = (int*) malloc( sizeof(int) * (nrofvars + 1) );

        var_weight    = (int*) malloc (sizeof(int) * (nrofvars + 1) );

	/* initialise global counters */
#ifdef CUBE
	current_Dnode = 1;
	init_assumptions();

	part_free  = nrofvars;
	conflicts  = 0;
        free_th    = 0;
	nr_cubes   = 0;
#endif
	current_node_stamp = 1;
	lookDead 	   = 0;
	mainDead 	   = 0;
#ifdef COUNT_SAT
	count_sat	   = 0;
#endif
       solution_bin = 0;
       solution_bits = 63;
#ifdef DISTRIBUTION
       first_time = 0;
       skip_flag = 0;
       first_depth = 20;
#endif
       currentNodeNumber = 1;
       UNSATflag = 0;

	/* allocate recursion stack */
	/* tree is max. nrofvars deep and we thus have max. nrofvars STACK_BLOCKS
		 -> 2 * nrofvars should be enough for everyone :)
	*/
	INIT_ARRAY( r       , 3 * nrofvars + 1   );

	INIT_ARRAY( imp     , INITIAL_ARRAY_SIZE );
	INIT_ARRAY( subsume , INITIAL_ARRAY_SIZE );
	INIT_ARRAY( bieq    , INITIAL_ARRAY_SIZE );
	INIT_ARRAY( newbi   , INITIAL_ARRAY_SIZE );
	INIT_ARRAY( sub     , INITIAL_ARRAY_SIZE );

	MALLOC_OFFSET( bImp_satisfied, int, nrofvars, 2 );
	MALLOC_OFFSET( bImp_start,     int, nrofvars, 2 );
	MALLOC_OFFSET( bImp_stamps,    int, nrofvars, 0 );
	MALLOC_OFFSET( node_stamps, tstamp, nrofvars, 0 );

	tmpEqImpSize  = (int*) malloc( sizeof(int) * (nrofvars+1) );

	init_lookahead();
	init_preselection();
#ifdef DISTRIBUTION
	init_direction();
#endif

        for (i = 1; i <= nrofvars; i++) var_weight[i] = 0;

	for( i = 0; i < nrofclauses; i++ )
          for( j = 0; j < Clength[i]; j++ )
            var_weight[ abs(Cv[ i ][ j ]) ]++;

	tmpTernaryImpSize = (int* ) malloc( sizeof(int ) * ( 2*nrofvars+1 ) );
#ifdef TERNARYLOOK
        TernaryImp 	  = (int**) malloc( sizeof(int*) * ( 2*nrofvars+1 ) );
        TernaryImpSize 	  = (int* ) malloc( sizeof(int ) * ( 2*nrofvars+1 ) );

        for( i = 0; i <= 2 * nrofvars; i++ ) {
	    tmpTernaryImpSize[ i ] = 0;
	    TernaryImpSize   [ i ] = 0; }

	for( i = 0; i < nrofclauses; i++ )
	    if( Clength[ i ] == 3 )
		for( j = 0; j < 3; j++ )
		    TernaryImpSize[ Cv[ i ][ j ] + nrofvars ]++;

        for( i = 0; i <= 2 * nrofvars; i++ )
	    TernaryImp[ i ] = (int*) malloc(sizeof(int)*(4*TernaryImpSize[i]+4));

        tmpTernaryImpSize 	+= nrofvars;
        TernaryImp 		+= nrofvars;
	TernaryImpSize 		+= nrofvars;

	fill_ternary_implication_arrays();

        for( i = -nrofvars; i <= nrofvars; i++ )
	    tmpTernaryImpSize[ i ] = 4 * TernaryImpSize[ i ] + 2;

	while (AddTernaryResolvents());

        for (i = -nrofvars; i <= nrofvars; i++)
	  free( TernaryImp[ i ] );

	FREE_OFFSET( TernaryImp     );
	FREE_OFFSET( TernaryImpSize );
#else
        tmpTernaryImpSize 	+= nrofvars;
#endif
	/* initialise global datastructures */

        if (gah) {
	  MALLOC_OFFSET( TernaryImpReduction, int, nrofvars, 0 );

	  if (kSAT_flag) {
	    int _nrofliterals = 0;

	    for( i = 0; i < nrofbigclauses; ++i )
		_nrofliterals += clause_length[ i ];

	    clause_reduction = (int*) malloc(sizeof (int) * nrofbigclauses);
	    clause_red_depth = (int*) malloc(sizeof (int) * nrofbigclauses);
	    big_global_table = (int*) malloc(sizeof (int) * _nrofliterals );
	    clause_SAT_flag  = (int*) malloc(sizeof (int) * nrofbigclauses);

	    MALLOC_OFFSET( big_to_binary, int*, nrofvars, NULL );
	    MALLOC_OFFSET( btb_size,      int , nrofvars,    0 );

	    for( i = 0; i < nrofbigclauses; ++i )
	    {
		clause_reduction[ i ] =  0;
		clause_red_depth[ i ] =  nrofvars;
		clause_SAT_flag [ i ] =  0;
	    }

	    int tmp = 0;
            for( i = 1; i <= nrofvars; i++ )
            {
                big_to_binary[  i ] = (int*) &big_global_table[ tmp ];
                tmp += big_occ[  i ];

                big_to_binary[ -i ] = (int*) &big_global_table[ tmp ];
                tmp += big_occ[ -i ];

            }
	    assert( tmp == _nrofliterals );
          }
	}

        TernaryImp 	= (int**) malloc( sizeof(int*) * ( 2*nrofvars+1 ) );
        TernaryImpSize 	= (int* ) malloc( sizeof(int ) * ( 2*nrofvars+1 ) );
        TernaryImpLast 	= (int* ) malloc( sizeof(int ) * ( 2*nrofvars+1 ) );
        TernaryImpTable	= (int* ) malloc( sizeof(int ) * ( 6*nrofclauses+1 ) );

	TernaryImp	       += nrofvars;
	TernaryImpSize	       += nrofvars;
	TernaryImpLast	       += nrofvars;

	if (simplify_formula() == UNSAT) return UNSAT;

	for (i = -nrofvars; i <= nrofvars; i++) {
	    tmpTernaryImpSize[ i ] = 0;
	    TernaryImpSize   [ i ] = 0;
	    bImp_satisfied   [ i ] = 2;	}

	for (i = 0; i < nrofclauses; i++)
	  if (Clength[ i ] == 3)
	    for (j = 0; j < 3; j++)
	      TernaryImpSize[ Cv[ i ][ j ] ]++;

	_tmp = 0;
        for (i = -nrofvars; i <= nrofvars; i++) {
	    TernaryImp[ i ]     = TernaryImpTable + 2 * _tmp;
            _tmp               += TernaryImpSize[ i ];
	    TernaryImpLast[ i ] = TernaryImpSize[ i ]; }

	fill_ternary_implication_arrays();

	rebuild_BinaryImp();

	init_freevars();

	for (i = 0; i < nrofceq ; i++)
	    assert (CeqSizes[ i ] != 1);
#ifdef EQ
	for (i = 0; i < nrofceq ; i++)
	    if( CeqSizes[ i ] == 2 )
            	DPLL_propagate_binary_equivalence( i );
#endif
#ifdef DETECT_COMPONENTS
	init_localbranching();
#endif
#ifdef CUT_OFF
	solution_bits = CUT_OFF - 1;
#endif
	push_stack_blocks();

        trailSize = 0;
        trail = (int*) malloc (sizeof(int) * nrofvars);

        initCDCL (&CDCL, nrofvars, nrofclauses);

        for (i = 0; i < nrofclauses; i++) {
          if (Clength[i] > 1)
            addClause (&CDCL, Cv[i], Clength[i], 1); }

	return 1;
}

void disposeSolver () {
  if (kSAT_flag) {
    free_big_clauses_datastructures();

    if (gah) {
      FREE( clause_reduction );
      FREE( big_global_table );
      FREE( clause_red_depth );
      FREE( clause_SAT_flag );

      FREE_OFFSET( big_to_binary );
      FREE_OFFSET( btb_size ); } }

  free_BinaryImp();

  dispose_lookahead();
  dispose_preselection();
  dispose_freevars();

  FREE_OFFSET( TernaryImp        );
  FREE_OFFSET( TernaryImpSize    );
  FREE_OFFSET( tmpTernaryImpSize );
  FREE_OFFSET( bImp_stamps       );
  FREE_OFFSET( bImp_satisfied    );
  FREE_OFFSET( node_stamps       );

  FREE( tmpEqImpSize );
  FREE( impstack );
  FREE( rstack );
}

int propagate_forced_literals() {
  int _freevars = freevars;

  if (IFIUP( 0, FIX_FORCED_LITERALS ) == UNSAT) return UNSAT;

  nrofforced = _freevars - freevars;
  percentage_forced = 100.0 * nrofforced / (double) _freevars;

  return SAT; }

int super_linear_branching () {
  sl_depth = 1;

  while (1) {
    int _result = march_solve_rec();
    if (_result != UNSAT)
      return _result;
#ifdef TIMEOUT
    if (((int) clock()) / TIMEOUT > CLOCKS_PER_SEC) return UNKNOWN;
#endif
    pb_reset ();
    sl_depth++; }

  return UNSAT; }

// only used for distribution branching
int distribution_branching () {
  int _result;

  target_rights  = 0;
  current_rights = 0;
  current_record = 0;

  first_time = (float) clock();

  do {
    assert (target_rights <= jump_depth);

#ifdef SUBTREE_SIZE
	    path_length = 1;
#endif
    _result = march_solve_rec();
    if( _result != UNSAT )
	return _result;

#ifdef TIMEOUT
  if (((int) clock()) / TIMEOUT > CLOCKS_PER_SEC)
    return UNKNOWN;
#endif
#ifndef CUT_OFF
    pb_reset();
#endif
    target_rights++;

    current_record = 1;

  } while (records[1].UNSAT_flag == 0);

  return UNSAT; }

// only used for distribution branching
int skip_node () {
  if (depth < jump_depth)
    if ((target_rights < current_rights) ||
	(target_rights >= (current_rights + jump_depth - depth)) )
      return 1;
  return 0; }

void printConflict () {
  if (kSAT_flag) {
    int i, *_rstackp = rstack;

    printf ("c at depth %i add conflict: ", depth);
    while (_rstackp < rstackp) {
      i = *(_rstackp++);

      if (timeAssignments[ i ] >= NARY_MAX) {
        if ((TernaryImpReduction[ i ] + TernaryImpReduction[ -i ]) != 0) {
          if (timeAssignments[ i ] & 1) printf ("%i ",  i);
          else 				printf ("%i ", -i); }
        else { printf("* "); } } }
  printf ("\n\n"); } }

void refuteNode () {
  Dnode_setType (current_Dnode, REFUTED_DNODE);
  conflicts++; }

int march_solve_rec() {
  if (nrofclauses == 0) return SAT;

  int branch_literal = 0, _result, _percentage_forced;
  int skip_left = 0, skip_right = 0, top_flag = 0;

  if (hardLimit && conflicts >= hardLimit) return UNKNOWN;

  nodeCount++;
#ifdef CUBE
 if (mode == CUBE_MODE) {
  Dnode_init (current_Dnode);
  Dnode_setWeight (current_Dnode, freevars);

//   int v, w;
//   w = 0;
/*
   if (nodeCount > 5)
   for (v = 1; v <= nrofvars; v++) {
//     printf("c weight[%i] = %i\n", v, var_weight[v]);
//     if (IS_FIXED(v)) {
     if (IS_NOT_FIXED(v)) {
//       w += (var_weight[v]);
       w += BinaryImp[  v ][ 0 ] - bImp_satisfied[  v ];
       w += BinaryImp[ -v ][ 0 ] - bImp_satisfied[ -v ];
//       w += (var_weight[v] > 0);
    }
   }
*/
/*
  if (depth)  // why is this required ?!?
   for (v = 1; v <= 168; v++)
     if (IS_FIXED(v)) w++;
*/
//  printf("c weight = %i, depth = %i\n", w, depth);
//  printf("c freevars: %i, free_th: %.3f\n", freevars, free_th);

//        if (w + 2 * depth > 100)
//        if (freevars < 15000 + depth * 80)  // huge
//        if (freevars < 4800 + depth * 10)  // buildroot
//        if (freevars < 3000)  // buildroot
//        if (freevars < free_th)  // new default
      if ((cut_depth && (depth == cut_depth)) || (dynamic && (freevars < free_th)) || (cut_var && (freevars < cut_var)))
      {
	nodeCount--;
	nr_cubes++;
	Dnode_setType (current_Dnode, CUBE_DNODE);

        free_th *= (1.0 - pow(fraction, pow(depth, downexp)));
//        free_th *= (1.0 - pow(fraction, depth));
	return UNSAT; }
 }
#endif
#ifdef DISTRIBUTION
	int record_index = current_record;

	top_flag = TOP_OF_TREE;

	if (fix_recorded_literals (record_index) == UNSAT)
	    return UNSAT;

	if (record_index == 0) record_index = init_new_record ();
#endif
#ifdef SUPER_LINEAR
	if (depth < sl_depth) subtree_size = 0;
	else if (subtree_size == SL_MAX) return UNSAT;
	else	subtree_size++;
#endif
#ifdef TIMEOUT
	if (((int) clock()) / TIMEOUT > CLOCKS_PER_SEC) return UNKNOWN;
#endif
#ifdef SUBTREE_SIZE
	path_length++;
#endif
#ifdef CUT_OFF
	if (depth <= CUT_OFF) last_SAT_bin = -1;

        if (solution_bin == last_SAT_bin) {
#ifdef DISTRIBUTION
	    records[ record_index ].UNSAT_flag = 1;
#endif
            return UNSAT;
	}
#endif
#ifdef DETECT_COMPONENTS
	determine_components();
#endif
#ifdef DISTRIBUTION
	branch_literal = records[record_index].branch_literal;

	if (branch_literal != 0) dist_acc_flag = 1;
	else
#endif
/*
      if (mode == PLAIN_MODE) {
        resetAssumptions (&CDCL);
        int t; for (t = 0; t < trailSize; t++)
          assume (&CDCL, trail[t]);
        int result = solve (&CDCL, 1000);
        if (result == SAT) { int i;
         for (i = 1; i <= nrofvars; i++) {
             if (getModel (&CDCL, i) == 1) { FIX (i, MAX  ); }
            else                          { FIX (i, MAX+1); } }
          return SAT; }
        if (result == UNSAT) return UNSAT;
      }
*/
	do
	{
#ifdef LOCAL_AUTARKY
	    int _depth = analyze_autarky ();
	    if (_depth == 0)
	      printf ("c global autarky found at depth %i\n", depth);
	    else if (_depth != depth)
	      printf ("c autarky found at depth %i (from %i)\n", depth, _depth);
#endif
//	    printf("node %i @ depth %i\n", nodeCount, depth );

	    if (ConstructCandidatesSet () == 0) {
	      if (depth > 0) {
		if (checkSolution() == SAT) {
//#ifdef CUBE
//  		    refuteNode ();
//                    return UNSAT;
//#else
                    if (sharp_mode == 1) {
                      refuteNode ();
                      return UNSAT; }
                    return verifySolution();
//#endif
	        } }
	    	if (PreselectAll() == 0) {


//#ifdef CUBE
//  		    refuteNode ();
//                    return UNSAT;
//#else
                    if (sharp_mode == 1) {
                      refuteNode ();
                      return UNSAT; }
		    return verifySolution ();
//#endif
                } }
	    else  ConstructPreselectedSet ();

            int _freevars = freevars;
	    if (lookahead () == UNSAT) {
	    	lookDead++;
#ifdef CUBE
		refuteNode();
                free_th = _freevars;
#endif
	    	return UNSAT; }

	    if (propagate_forced_literals() == UNSAT) {
#ifdef CUBE
		refuteNode ();
                free_th = _freevars;
#endif
		return UNSAT; }

	    branch_literal = get_signedBranchVariable();
#ifdef FLIP_BIAS
	    branch_literal *= -1;
#endif
//	    printf("c branch literal %i", branch_literal );
	}
	while( (percentage_forced > 50.0) || (branch_literal == 0) );

	_percentage_forced = percentage_forced;

	if (gah && depth == 0) {
	    int i; for (i = 1; i <= nrofvars; i++) {
		TernaryImpReduction[  i ] = 0;
		TernaryImpReduction[ -i ] = 0;

		if( kSAT_flag ) {
		    btb_size[  i ] = 0;
		    btb_size[ -i ] = 0; } }

	    if( kSAT_flag )
		for( i = 0; i < nrofbigclauses; ++i )
		    clause_reduction[ i ] = 0;
	}
	NODE_START();
#ifdef BLOCK_PRESELECT
	set_block_stamps (branch_literal);
#endif

#ifdef DISTRIBUTION
	if( top_flag ) {
	    branch_literal *= -1;

	    current_rights++;
	    UPDATE_BIN(); }
	skip_left = skip_node();
#endif
	discrepancies++;

//        printf ("c making decision %i at depth %i\n", branch_literal, depth);
        trailSize = depth + 1;
        trail[trailSize - 1] = branch_literal;
#ifdef CUBE
	int tmp_Dnode = current_Dnode;
	current_Dnode = Dnode_left (current_Dnode);
	Dnode_setDecision (current_Dnode, branch_literal);
#endif
	if ((skip_left==0) && IFIUP (branch_literal, FIX_BRANCH_VARIABLE))
	{

#ifdef DISTRIBUTION
	    current_record = LEFT_CHILD;
#endif

	    _result = recursive_solve();
#ifdef DISTRIBUTION
	    LEFT_CHILD = current_record;
#endif

	    if (_result == SAT || _result == UNKNOWN) return _result; }
	else {
#ifdef DISTRIBUTION
		if( (LEFT_CHILD != 0)  && records[ LEFT_CHILD ].UNSAT_flag == 0 )
		{
		    records[ LEFT_CHILD ].UNSAT_flag = 1;
//		    printf("c left child %i UNSAT by parent!\n", LEFT_CHILD );
		}
#endif
		PUSH( r, STACK_BLOCK );}
#ifdef CUBE
	current_Dnode = tmp_Dnode;
#endif
	discrepancies--;

	NODE_END();

#ifdef BACKJUMP
	if (backjump_literal != 0)
	  if (timeAssignments[backjump_literal] >= NARY_MAX) {
//		printf("backjumping at depth %i due to literal %i\n", depth, backjump_literal );
		return UNSAT; }
	backjump_literal = 0;
#endif

#ifdef DISTRIBUTION
	if( top_flag )
	{
	    current_rights--;
	    UPDATE_BIN();
	}
#endif
	percentage_forced = _percentage_forced;

	if(gah && depth == 0 )
	  if( kSAT_flag )
	  {
	    int i;
	    for( i = 1; i <= nrofvars; ++i )
	    {
		assert( TernaryImpReduction[  i ] == 0 );
		assert( TernaryImpReduction[ -i ] == 0 );

		assert( btb_size[  i ] == 0 );
		assert( btb_size[ -i ] == 0 );
	    }

	    for( i = 0; i < nrofbigclauses; ++i )
	    {
		clause_red_depth[ i ] = nrofvars;
		clause_SAT_flag[ i ]  = 0;
	    }
	  }

	  if( kSAT_flag )
	  {
	    int i;
	    for( i = 1; i <= nrofvars; ++i )
	    {
		assert( TernaryImpReduction[  i ] >= 0 );
		assert( TernaryImpReduction[ -i ] >= 0 );

		assert( btb_size[  i ] >= 0 );
		assert( btb_size[ -i ] >= 0 );
	    }
	  }

	NODE_START();
#ifdef BLOCK_PRESELECT
	set_block_stamps (branch_literal);
#endif
        if( top_flag == 0 )
	{
#ifdef DISTRIBUTION
	    current_rights++;
#endif
	    UPDATE_BIN();
	}
#ifdef DISTRIBUTION
	skip_right = skip_node();
#endif

//        printf ("c making decision %i at depth %i\n", -branch_literal, depth);
        trailSize = depth + 1;
        trail[trailSize - 1] = -branch_literal;
#ifdef CUBE
	tmp_Dnode = current_Dnode;
	current_Dnode = Dnode_right (current_Dnode);
	Dnode_setDecision (current_Dnode, -branch_literal);
#endif
	if ((skip_right == 0) && IFIUP (-branch_literal, FIX_BRANCH_VARIABLE))
	{

#ifdef DISTRIBUTION
	    current_record = RIGHT_CHILD;
#endif
	    _result = recursive_solve();
#ifdef DISTRIBUTION
	    RIGHT_CHILD = current_record;
#endif
	    if( _result == SAT || _result == UNKNOWN ) return _result;}
	else {
#ifdef DISTRIBUTION
		if( (RIGHT_CHILD != 0) && records[ RIGHT_CHILD ].UNSAT_flag == 0 )
		{
		    records[ RIGHT_CHILD ].UNSAT_flag = 1;
		}
#endif
		PUSH( r, STACK_BLOCK );}
#ifdef CUBE
	current_Dnode = tmp_Dnode;
#endif
	NODE_END();

	if( top_flag == 0 )
	{
#ifdef DISTRIBUTION
	    current_rights--;
#endif
	    UPDATE_BIN();
	}

#ifdef SUBTREE_SIZE
	if( (skip_flag == 0) && (jump_depth == 0)  && (current_rights == 0) )
	{
	    int subtree = path_length - depth;

	    if( jump_depth >= 30 ) jump_depth = 999;

	    if( subtree >     SUBTREE_SIZE )
	    {
	        jump_depth = depth;

	        while( subtree > 2*SUBTREE_SIZE )
	        {
		   jump_depth++;
		   subtree = subtree / 2;
	        }

	        if( jump_depth >= 20 ) jump_depth = 999;

	        skip_flag = 1;
	    }
	}
#endif
#ifdef DISTRIBUTION
	record_node (record_index, branch_literal, skip_left, skip_right);
	current_record = record_index;
#endif

#ifdef BACKJUMP
	if (kSAT_flag) {
	  int *_rstackp = rstackp, nrval;

	  while (--_rstackp > rstack) {
            nrval = *_rstackp;
            if ((TernaryImpReduction[ nrval ] + TernaryImpReduction[ -nrval ]) != 0) {
              backjump_literal = nrval;
              break; } } }
#endif

//	printConflict();

	return UNSAT;
}

int IFIUP (const int nrval, const int forced_or_branch_flag) {

	int i, *_forced_literal_array, _forced_literals, *local_fixstackp;

	local_fixstackp = rstackp;
	end_fixstackp   = rstackp;

	currentTimeStamp = BARY_MAX;

	current_bImp_stamp = 1;

	for (i = nrofvars; i >= 1;  i--) {
	    bImp_stamps[  i ] = 0;
	    bImp_stamps[ -i ] = 0; }

	if (forced_or_branch_flag == FIX_BRANCH_VARIABLE) {
	     decisions[ depth ] = nrval; }

	if (forced_or_branch_flag == FIX_FORCED_LITERALS) {
	   get_forced_literals (&_forced_literal_array, &_forced_literals);
	   for (i = 0; i < _forced_literals; i++)
	      	if (look_fix_binary_implications(*(_forced_literal_array++)) == UNSAT )
		    { MainDead( local_fixstackp ); return UNSAT; }
	}
#ifdef DISTRIBUTION
	else if (forced_or_branch_flag == FIX_RECORDED_LITERALS) {
	   get_recorded_literals( &_forced_literal_array, &_forced_literals );
	   for (i = 0; i < _forced_literals; i++)
	      	if (look_fix_binary_implications (*(_forced_literal_array++)) == UNSAT )
		    { MainDead (local_fixstackp); return UNSAT; }
	}
#endif
	else {
	 	if (look_fix_binary_implications (nrval) == UNSAT)
    		    { MainDead (local_fixstackp); return UNSAT; }
	}

	while (local_fixstackp < end_fixstackp)
		if (DPLL_update_datastructures (*(local_fixstackp++)) == UNSAT )
		    { MainDead (local_fixstackp); return UNSAT; }

	rstackp = end_fixstackp;
	return SAT;
}

void reduce_big_occurences (const int clause_index, const int nrval) {
#ifdef HIDIFF
  HiRemoveClause (clause_index);
#endif
  int *literals = clause_list[clause_index];
  while (*literals != LAST_LITERAL) {
    int lit =  *(literals++);
    if (lit != nrval) {
      int *clauseSet = clause_set[lit];
      while (1) {
//        assert (*clauseSet != LAST_CLAUSE);
        if (*(clauseSet++) == clause_index) {
          clauseSet[ -1 ] = clause_set[ lit ][ big_occ[ lit ] - 1 ];
          clause_set[ lit ][ big_occ[ lit ] - 1 ] = LAST_CLAUSE;
          break; } }
       big_occ[lit]--; } } }

int DPLL_update_datastructures( const int nrval )
{
	int i, *bImp;
#ifdef EQ
	int nr, ceqidx;
	nr = NR( nrval );
        PUSH( sub, STACK_BLOCK );
#endif
	FIX( nrval, NARY_MAX );

//	diff[  nrval ] = 0;
//	diff[ -nrval ] = 0;

#ifdef TIMEOUT
	if( ((int) clock()) / TIMEOUT > CLOCKS_PER_SEC)
	    return UNKNOWN;
#endif
	unitResolveCount++;
	reduce_freevars( nrval );

        bImp = BIMP_START(-nrval);
        for (i = BIMP_ELEMENTS; --i;)
            bImp_satisfied[ -(*(bImp++)) ]++;

	// Update eager datastructures
	if( kSAT_flag == 0 ) {
          if (gah) {
            int *tImp = TernaryImp[nrval] + 2 * TernaryImpSize[nrval];
            for (i = TernaryImpLast[nrval] - TernaryImpSize[nrval]; i--; ) {
	      int lit1 = *(tImp++);
	      int lit2 = *(tImp++);

	      if (IS_REDUCED_TIMP(lit1, lit2))
                TernaryImpReduction[lit1]--;
	      else if( IS_REDUCED_TIMP(lit2, lit1))
                TernaryImpReduction[lit2]--; } }

	  remove_satisfied_implications( nrval);
	  remove_satisfied_implications(-nrval);

          if (gah) {
            int *tImp = TernaryImp[-nrval];
            for (i = tmpTernaryImpSize[-nrval]; i--;) {
	      TernaryImpReduction[*(tImp++)]++;
	      TernaryImpReduction[*(tImp++)]++; } }
	}
	else {
	  int *clauseSet, clause_index;

	  // REMOVE SATISFIED CLAUSES
	  clauseSet = clause_set[ nrval ];
	  while( *clauseSet != LAST_CLAUSE )
	  {
	    clause_index = *(clauseSet++);

	    // if clause is not satisfied
	    if( clause_length[ clause_index ] < SAT_INCREASE - 2 )
	    {
              if (gah) {
		// if clause is already been reduced
		if( clause_reduction[ clause_index ] > 0 )
		{
                    int *literals = clause_list[ clause_index ];
                    while( *literals != LAST_LITERAL )
			TernaryImpReduction[ *(literals++) ]--;
		}
		clause_SAT_flag[ clause_index ] = 1; }
              reduce_big_occurences( clause_index, nrval );
	    }
	    clause_length[ clause_index ] += SAT_INCREASE;
	  }
          if (gah) {
  	    for( i = 0; i < btb_size[ nrval ]; ++i ) {
	      // decrease literal reduction
              int *literals = clause_list[ big_to_binary[ nrval ][ i ] ], flag = 0;
              while( *literals != LAST_LITERAL )
              {
		if( timeAssignments[ *(literals++) ] == NARY_MAX )
		{
		    if( flag == 1 ) { flag = 0; break; }
		    flag = 1;
		}
              }

	      if( flag == 1 )
	      {
		clause_SAT_flag[  big_to_binary[ nrval ][ i ] ] = 1;
		literals = clause_list[ big_to_binary[ nrval ][ i ] ];
	    	while( *literals != LAST_LITERAL )
	            TernaryImpReduction[ *(literals++) ]--;
	      }
	    }
          }
	}

#ifdef EQ
        if (gah) {
	  tmpEqImpSize[ nr ] = Veq[ nr ][ 0 ];
	  for (i = 1; i < Veq[ nr ][0]; i++) {
            ceqidx = Veq[ nr ][i];
            int j; for( j = 0; j < CeqSizes[ ceqidx ]; j++ )
                TernaryImpReduction[ Ceq[ceqidx][j] ]++; } }
#endif
	if( kSAT_flag )
	{
	  int UNSAT_flag, *clauseSet, clause_index;
	  int first_lit, *literals, lit;

	  // REMOVE UNSATISFIED LITERALS
	  UNSAT_flag = 0;
	  clauseSet = clause_set[ -nrval ];
	  while( *clauseSet != LAST_CLAUSE )
	  {
	    clause_index = *(clauseSet++);
            if (gah) {
	      // if clause is for the first time reduced
	      if( clause_reduction[ clause_index ] == 0 )
	      {
                int *literals = clause_list[ clause_index ];
                while( *literals != LAST_LITERAL )
		    TernaryImpReduction[ *(literals++) ]++;

		clause_red_depth[ clause_index ] = depth;
	      }
	      clause_reduction[ clause_index ]++; }
	    clause_length[ clause_index ]--;
#ifdef HIDIFF
	    HiRemoveLiteral( clause_index, nrval );
#endif
            if(  clause_length[ clause_index ] == 2 )
            {
              if (gah) {
                int *literals = clause_list[ clause_index ];
                while( *literals != LAST_LITERAL )
                {
                    lit = *(literals)++;
		    if( timeAssignments[ lit ] < NARY_MAX )
			big_to_binary[ lit ][ btb_size[ lit ]++ ] = clause_index;
		}
              }
		reduce_big_occurences( clause_index, -nrval );
		clause_length[ clause_index ] = SAT_INCREASE;

	        if( UNSAT_flag == 0 )
	        {
                    first_lit = 0;
                    literals = clause_list[ clause_index ];
                    while( *literals != LAST_LITERAL )
                    {
                        lit = *(literals)++;
                        if( IS_NOT_FIXED( lit ) )
                        {
                            if( first_lit == 0 ) first_lit = lit;
                            else
			    {
				UNSAT_flag = !DPLL_add_binary_implications( first_lit, lit );
				goto next_clause;
			    }
                        }
                        else if( !FIXED_ON_COMPLEMENT(lit) ) goto next_clause;
                    }

                    if( first_lit != 0 )  UNSAT_flag = !look_fix_binary_implications( first_lit );
                    else                  UNSAT_flag = 1;
                }
                next_clause:;
	    }
	  }

	  if( UNSAT_flag ) return UNSAT;
	}

	if( kSAT_flag == 0 )
	{
	    int *tImp = TernaryImp[ -nrval ];
            for( i = tmpTernaryImpSize[ -nrval ] - 1; i >= 0; i-- )
	    {
		int lit1 = *(tImp++);
		int lit2 = *(tImp++);
                if( DPLL_add_binary_implications( lit1, lit2 ) == UNSAT )
            	    return UNSAT;
	    }
	}

#ifdef EQ
        while( Veq[ nr ][ 0 ] > 1 )
        {
            ceqidx = Veq[ nr ][ 1 ];

            fixEq( nr, 1, SGN(nrval));
            PUSH( sub, nrval );

            if( CeqSizes[ ceqidx ] == 2 )
	    {
            	if ( DPLL_propagate_binary_equivalence( ceqidx ) == UNSAT )
               	    return UNSAT;
	    }
	    else if( CeqSizes[ ceqidx ] == 1 )
            {
            	if( look_fix_binary_implications(Ceq[ceqidx][0]*CeqValues[ceqidx]) == UNSAT )
                    return UNSAT;
            }
        }

        while( newbistackp != newbistack )
        {
            POP( newbi, ceqidx );
            if( CeqSizes[ ceqidx ] == 2 )
            	if ( DPLL_propagate_binary_equivalence( ceqidx ) == UNSAT )
                    return UNSAT;
        }
#endif
	return SAT;
}

void swap_ternary_implications (const int nrval, const int lit1, const int lit2) {
  int *tImp = TernaryImp[nrval];
  int last = --TernaryImpSize[nrval];
  int i; for (i = last - 1; i >= 0; i--)
    if ((tImp[2*i] == lit1) && (tImp[2*i + 1] == lit2)) {
      tImp[2*i  ] = tImp[2*last  ]; tImp[2*last  ] = lit1;
      tImp[2*i+1] = tImp[2*last+1]; tImp[2*last+1] = lit2;
      return; } }

void remove_satisfied_implications (const int nrval) {
  int *tImp = TernaryImp[nrval];

  int i; for( i = TernaryImpSize[ nrval ] - 1; i >= 0; i-- ) {
    int lit1 = *(tImp++);
    int lit2 = *(tImp++);

    swap_ternary_implications (lit1, lit2, nrval);
    swap_ternary_implications (lit2, nrval, lit1); }

  tmpTernaryImpSize[nrval] = TernaryImpSize[nrval];
  TernaryImpSize   [nrval] = 0; }

int DPLL_propagate_binary_equivalence( const int bieq )
{
        int i, j, ceqsubst;
        int lit1, lit2;
        int value;

        lit1 = Ceq[ bieq ][ 0 ];
        lit2 = Ceq[ bieq ][ 1 ];
        value = CeqValues[ bieq ];

        for( i = 1; i < Veq[ lit1 ][ 0 ]; i++ )
        {
            ceqsubst = Veq[ lit1 ][ i ];
            for( j = 1; j < Veq[ lit2 ][ 0 ]; j++ )
            {
            	if( ceqsubst == Veq[ lit2 ][ j ] )
                {
                    fixEq( lit1, i, 1);
                    PUSH( sub, lit1 );

                    fixEq( lit2, j, value);
                    PUSH( sub, lit2 * value );

                    if( CeqSizes[ ceqsubst ] == 0 )
                       	if (CeqValues[ ceqsubst ] == -1 )
                            return UNSAT;

                    if( CeqSizes[ ceqsubst ] == 1 )
                      	if( !look_fix_binary_implications(Ceq[ceqsubst][0] * CeqValues[ceqsubst]) )
                    	    return UNSAT;

                    if( CeqSizes[ ceqsubst ] == 2 )
                     	PUSH( newbi, ceqsubst );

		    i--;
                    break;
                }
            }
        }

        if( (DPLL_add_binary_implications( lit1, -lit2 * value ) &&
	     DPLL_add_binary_implications( -lit1, lit2 * value )) == UNSAT )
                return UNSAT;

        return SAT;
}

int DPLL_add_compensation_resolvents( const int lit1, const int lit2 ) {
  int i, *bImp = BIMP_START (lit2);

  CHECK_NODE_STAMP (-lit1);
  CHECK_BIMP_UPPERBOUND (-lit1, BinaryImp[lit2][0]);

  for (i = BIMP_ELEMENTS; --i;) {
    int lit = *(bImp++);
    if (IS_FIXED(lit)) continue;
    if (bImp_stamps[-lit] == current_bImp_stamp)
      return look_fix_binary_implications (lit1);
#ifdef COMPENSATION_RESOLVENTS
    if (bImp_stamps[lit] != current_bImp_stamp) {
      CHECK_NODE_STAMP (-lit);
      CHECK_BIMP_BOUND (-lit);
      ADD_BINARY_IMPLICATIONS (lit, lit1); }
#endif
  }
  return UNKNOWN; }

int DPLL_add_binary_implications( int lit1, int lit2 )
{
	int i, *bImp;

	if( IS_FIXED(lit1) )
	{
	    if( !FIXED_ON_COMPLEMENT(lit1) )	return SAT;
	    else if( IS_FIXED(lit2) )
		    return( !FIXED_ON_COMPLEMENT(lit2) );
	    else    return look_fix_binary_implications(lit2);
	}
	else if( IS_FIXED(lit2) )
	{
	    if( !FIXED_ON_COMPLEMENT(lit2) )	return SAT;
	    else    return look_fix_binary_implications(lit1);
	}

#ifdef BIEQ
	while( (VeqDepends[ NR(lit1) ] != INDEPENDENT) &&
	    (VeqDepends[ NR(lit1) ] != EQUIVALENT) )
		lit1 = VeqDepends[ NR(lit1) ] * SGN(lit1);

	while( (VeqDepends[ NR(lit2) ] != INDEPENDENT) &&
	    (VeqDepends[ NR(lit2) ] != EQUIVALENT) )
		lit2 = VeqDepends[ NR(lit2) ] * SGN(lit2);

	if( lit1 == -lit2 ) return SAT;
	if( lit1 ==  lit2 ) return look_fix_binary_implications(lit1);
#endif

	STAMP_IMPLICATIONS( -lit1 );
	if( bImp_stamps[ -lit2 ] == current_bImp_stamp )
	    return look_fix_binary_implications( lit1 );
	if( bImp_stamps[lit2] != current_bImp_stamp )
	{
	    int _result;

	    bImp_stamps[ BinaryImp[-lit1][ BinaryImp[-lit1][0] - 1] ] = current_bImp_stamp;

	    _result = DPLL_add_compensation_resolvents( lit1, lit2 );
	    if( _result != UNKNOWN )
		return _result;

	    STAMP_IMPLICATIONS( -lit2 );
	    if( bImp_stamps[ -lit1 ] == current_bImp_stamp )
	    	return look_fix_binary_implications( lit2 );

	    _result = DPLL_add_compensation_resolvents( lit2, lit1 );
	    if( _result != UNKNOWN )
		return _result;

	    ADD_BINARY_IMPLICATIONS( lit1, lit2 );
	}
	return SAT;
}

int autarky_stamp( const int nrval )
{
	int i, *tImp, lit1, lit2, flag = 0;

	tImp = TernaryImp[ -nrval ];
	for( i = tmpTernaryImpSize[ -nrval ]; i--; )
	{
	    lit1 = *(tImp++);
	    lit2 = *(tImp++);

	    if( IS_NOT_FIXED(lit1) && IS_NOT_FIXED(lit2) )
	    {
		flag = 1;
		if( VeqDepends[ NR(lit1) ] == DUMMY )
		    autarky_stamp( lit1 );
		else
		    TernaryImpReduction[ lit1 ]++;

		if( VeqDepends[ NR(lit2) ] == DUMMY )
		    autarky_stamp( lit2 );
		else
		TernaryImpReduction[ lit2 ]++;
	    }
	}
	return flag;
}

int analyze_autarky () {
  int i, j, k, _depth;

  if (depth == 0) return 0;

  for (i = 1; i <= nrofvars; i++) {
    TernaryImpReduction[  i ] = 0;
    TernaryImpReduction[ -i ] = 0; }

  int new_bImp_flag = 0;
  int *_rstackp = rstackp;
  for (_depth = depth; _depth > 0; _depth--) {
    for (k = 1 ; k <= 2; k++)
      while (*(--_rstackp) != STACK_BLOCK) {
        int nrval = *(_rstackp);
        if (autarky_stamp (nrval) == 1)
          new_bImp_flag = 1;

        for (j = 1; j < tmpEqImpSize[NR(nrval)]; j++) {
          int ceqsubst = Veq[NR(nrval)][j];
          for (i = 0; Ceq[ceqsubst][i] != NR(nrval); i++) {
            new_bImp_flag = 1;
            TernaryImpReduction[ Ceq[ceqsubst][i] ]++; } } }
    if (new_bImp_flag == 1) break; }
  return _depth; }

void backtrack() {
  int nrval, varnr, size;

  while( !( *( rstackp - 1 ) == STACK_BLOCK ) ) {
    POP_BACKTRACK_RECURSION_STACK }
  POP_RECURSION_STACK_TO_DEV_NULL

  while( !( *( subsumestackp - 1 ) == STACK_BLOCK ) ) {
    POP( subsume, nrval );
    TernaryImpSize[ TernaryImp[nrval][ 2*TernaryImpSize[nrval]   ] ]++;
    TernaryImpSize[ TernaryImp[nrval][ 2*TernaryImpSize[nrval]+1 ] ]++;
    TernaryImpSize[ nrval ]++; }
  subsumestackp--;

  while( !( *( rstackp - 1 ) == STACK_BLOCK ) ) {
    POP_BACKTRACK_RECURSION_STACK }
  POP_RECURSION_STACK_TO_DEV_NULL

  while( !( *( bieqstackp - 1 ) == STACK_BLOCK ) ) {
    POP( bieq, varnr );
    VeqDepends[ varnr ] = INDEPENDENT; }
  bieqstackp--;

  while( !( *( impstackp - 1 ) == STACK_BLOCK ) ) {
    POP( imp, size );
    POP( imp, nrval );
    BinaryImp[ nrval ][ 0 ] = size; }
  impstackp--; }

void MainDead (int *local_fixstackp) {
  mainDead++;

  while (end_fixstackp > local_fixstackp) {
    int nrval = *(--end_fixstackp);
    UNFIX( nrval ); }
  rstackp = end_fixstackp;

#ifdef CUBE
  refuteNode ();
  if (free_th < freevars) free_th = freevars;
#endif
}

void restore_big_occurences (const int clause_index, const int nrval) {
#ifdef HIDIFF
  HiAddClause (clause_index);
#endif
  int *clause = clause_list[ clause_index ];
  while (*clause != LAST_LITERAL) {
    int lit = *(clause++);
    if (lit != nrval) {
      clause_set[ lit ][ big_occ[ lit ] ] = clause_index;
      big_occ[ lit ]++; } } }

void restore_implication_arrays (const int nrval) {
  int i, *bImp;
#ifdef EQ
  int var;
  while( !( *( substackp - 1 ) == STACK_BLOCK ) ) {
    POP( sub, var );
    int ceqsubst = Veq[ NR(var) ][ Veq[ NR(var) ][ 0 ]++ ];
    CeqValues[ ceqsubst ] *= SGN(var);
    CeqSizes[ ceqsubst ]++; }

  substackp--;
  if (gah) {
    for (i = 1; i < Veq[NR(nrval)][0]; i++) {
    int ceqsubst = Veq[NR(nrval)][i];
    int j; for( j = 0; j < CeqSizes[ceqsubst]; j++ )
      TernaryImpReduction[ Ceq[ceqsubst][j] ]--; } }
#endif
//  printf("UNFIXING %i\n", nrval );

  if (kSAT_flag) {
    int* clauseSet = clause_set[ nrval ];
    while (*clauseSet != LAST_CLAUSE) {
      int clause_index = *(clauseSet++);
      clause_length[ clause_index ] -= SAT_INCREASE;

      if (clause_length[ clause_index ] < SAT_INCREASE - 2) {
        restore_big_occurences( clause_index, nrval );
        if (gah) {
          clause_SAT_flag[ clause_index ] = 0;
          if (clause_reduction[ clause_index ] > 0 ) {
            int *clause = clause_list[ clause_index ];
            while (*clause != LAST_LITERAL)
	      TernaryImpReduction[ *(clause++) ]++; } } } }

    if (gah) {
      for (i = 0; i < btb_size[ nrval ]; ++i) {
	// decrease literal reduction
        int flag = 0;
        int *literals = clause_list[ big_to_binary[ nrval ][ i ] ];
        while( *literals != LAST_LITERAL ) {
	  if (timeAssignments[ *(literals++) ] == NARY_MAX ) {
            if (flag == 1) { flag = 0; break; }
              flag = 1; } }

	if (flag == 1) {
	  clause_SAT_flag[ big_to_binary[ nrval ][ i ] ] = 0;
	  literals = clause_list[ big_to_binary[ nrval ][ i ] ];
          while (*literals != LAST_LITERAL)
	    TernaryImpReduction[ *(literals++) ]++; } } }

    clauseSet = clause_set[ -nrval ];
    while (*clauseSet != LAST_CLAUSE) {
      int clause_index = *(clauseSet++);
      if (clause_length[ clause_index ] == SAT_INCREASE) {
        restore_big_occurences( clause_index, -nrval );
	clause_length[ clause_index ] = 2;
        if (gah) {
          int *literals = clause_list[ clause_index ];
          while (*literals != LAST_LITERAL) {
            int lit = *(literals)++;
            if (timeAssignments[ lit ] < NARY_MAX)
              btb_size[ lit ]--; } } }

    if (gah) {
      clause_reduction[ clause_index ]--;

      // if clause is restored to original length
      if (clause_reduction[ clause_index ] == 0) {
	// decrease literal reduction array
        int *literals = clause_list[ clause_index ];
        while (*literals != LAST_LITERAL)
          TernaryImpReduction[ *(literals++) ]--;
        clause_red_depth[ clause_index ] = nrofvars; } }
#ifdef HIDIFF
    HiAddLiteral( clause_index, nrval );
#endif
    clause_length[ clause_index ]++; } }

  if (kSAT_flag == 0) {
    /* restore all literals that were removed due to fixing of nrval */
    int *tImp = TernaryImp[ -nrval ];
    for (i = TernaryImpSize[ -nrval ] = tmpTernaryImpSize[ -nrval ]; i--;) {
      TernaryImpSize[ *(tImp++) ]++;
      TernaryImpSize[ *(tImp++) ]++; }

    if (gah) {
      tImp = TernaryImp[ -nrval ];
      for (i = tmpTernaryImpSize[ -nrval ]; i--;) {
	 TernaryImpReduction[ *(tImp++) ]--;
	 TernaryImpReduction[ *(tImp++) ]--; } }

    /* restore all clauses that were removed due to fixing of nrval */
    tImp = TernaryImp[ nrval ];
    for (i = TernaryImpSize[ nrval ] = tmpTernaryImpSize[ nrval ]; i--;) {
      TernaryImpSize[ *(tImp++) ]++;
      TernaryImpSize[ *(tImp++) ]++; }

    if (gah) {
      tImp = TernaryImp[ nrval ] + 2 * TernaryImpSize[ nrval ];
      for (i = TernaryImpLast[ nrval ] - TernaryImpSize[ nrval ]; i--;) {
        int lit1 = *(tImp++);
        int lit2 = *(tImp++);
        if      (IS_REDUCED_TIMP(lit1, lit2)) TernaryImpReduction[lit1]++;
        else if (IS_REDUCED_TIMP(lit2, lit1)) TernaryImpReduction[lit2]++; } } }

  bImp = BIMP_START(-nrval);
  for (i = BIMP_ELEMENTS; --i;)
    bImp_satisfied[-(*(bImp++))]--;

  freevars++;
  UNFIX (nrval); }

int checkSolution () {
  int i, *sizes;

  if (kSAT_flag) sizes = big_occ;
  else           sizes = TernaryImpSize;

  for (i = 1; i <= original_nrofvars; i++)
    if (IS_NOT_FIXED(i)) {
      if (sizes[ i] > 0) { return UNSAT; }
      if (sizes[-i] > 0) { return UNSAT; }
      if (BinaryImp[ i][0] > bImp_satisfied[ i]) { return UNSAT; }
      if (BinaryImp[-i][0] > bImp_satisfied[-i]) { return UNSAT; } }

  return SAT; }

int verifySolution()
{
	int i, j, satisfied, dollars;
#ifndef CUT_OFF
	unsigned long long mask = 0xffffffffffffffffLLU;

	dollars = solution_bits - depth;
	if( dollars < 1 ) dollars = 1;

	printf("\nc |" );
	for( i = solution_bits; i >= dollars; i-- )
	{
#ifdef DISTRIBUTION
	    if( solution_bits - i == jump_depth ) printf(".");
#endif
#ifdef SUPER_LINEAR
	    if( solution_bits - i == sl_depth ) printf(".");
#endif
	    if( ((solution_bin & mask) >> i) > 0 ) printf("1");
	    else printf("0");
	    mask = mask >> 1;
	}

	for( i = solution_bits - depth; i >= 2; i-- )
	   printf("$");

	printf("|\n");
#else
        printf("s %i\n", solution_bin + 1);
	fflush( stdout );

        last_SAT_bin = solution_bin;

        return UNSAT;
#endif
#ifdef COUNT_SAT
	count_sat++;
	return UNSAT;
#endif
	do
	{ fixDependedEquivalences(); }
	while (dependantsExists());

	/* check all 3-clauses */

	for( i = 0; i < nrofclauses; i++ )
	{
	    satisfied = 0;
	    if( Clength[ i ] == 0 ) continue;

	    for( j = 0; j < Clength[ i ]; j++ )
		if( timeAssignments[ Cv[ i ][ j ] ] == VARMAX ) satisfied = 1;

  	    if( !satisfied )
	    {
	 	printf("\nc clause %i: ", i);
		for( j = 0; j < Clength[ i ]; j++ )
	  	    printf("%i [%i] ", Cv[i][j], IS_FIXED(Cv[i][j]) );
		printf("not satisfied yet\n");
		return UNKNOWN;
	    }
	}

#ifdef EQ
        for( i = 0; i < nrofceq; i++ )
        {
      	    int value = CeqValues[ i ];
            for( j = 0; j < CeqSizes[ i ]; j++ )
            	value *= EQSGN( Ceq[ i ][ j ] );
            if( value == -1 )
            {
                printf("c eq-clause %i is not satisfied yet\n", i);
            	return UNKNOWN;
            }
        }
#endif
	return SAT;
}

void printSolution (const int orignrofvars) {
  printf ("v");
  int i; for (i = 1; i <= orignrofvars; i++) {
    if      (timeAssignments[i] ==  VARMAX   ) printf(" %i",  i);
    else if (timeAssignments[i] == (VARMAX+1)) printf(" %i", -i); }
  printf(" 0\n");

  int pos = 0, neg = 0;

  for (i = 1; i <= orignrofvars; i++) {
    if      (timeAssignments[i] ==  VARMAX   ) pos++;
    else if (timeAssignments[i] == (VARMAX+1)) neg++; }

  if (pos) {
    int rows    = (neg + pos) / pos;

    if (rows > 1 && (neg % pos == 0)) {
      printf ("c\nc detected coloring problem\nc\n");
      int j; for (j = 1; j <= rows; j++) {
        printf ("c color %i :: ", j);
        for (i = j; i <= orignrofvars; i += rows)
          if (timeAssignments[ i ] ==  VARMAX) printf (" %i", (i+rows-1) / rows);
        printf("\n"); } } }
}
