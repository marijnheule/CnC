/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#define ROOTSIZE		1
#define ROOTACC			5
#define RECORDSIZE		100
#define ACCURACY		2

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>

#include "common.h"
#include "lookahead.h"
#include "doublelook.h"
#include "equivalence.h"
#include "tree.h"
#include "solver.h"


/* global look-ahead variables */
int new_binaries, *NBCounter, *failed_DL_stamp;
float weighted_new_binaries, *WNBCounter;

#ifdef DL_DECREASE
double DL_decrease;
#endif

float *EqDiff;

int (*look_IUP        ) (const int nrval, int *local_fixstackp);
int look_IUP_w_eq_3SAT  (const int nrval, int *local_fixstackp);
int look_IUP_w_eq_kSAT  (const int nrval, int *local_fixstackp);
int look_IUP_wo_eq_3SAT (const int nrval, int *local_fixstackp);
int look_IUP_wo_eq_kSAT (const int nrval, int *local_fixstackp);

int tree_lookahead();
int serial_lookahead();

int lookahead () {
  look_fixstackp = rstackp;
  end_fixstackp  = look_fixstackp;

  int _result;
#ifdef INTELLOOK
  _result = tree_lookahead();
#else
  _result = serial_lookahead();
#endif
  if (kSAT_flag)
    restore_big_clauses (end_fixstackp, rstackp);

  return _result; }

void init_lookahead () {
  int i, longest_clause = 0;

  for (i = 0; i < nrofclauses; i++)
    if (longest_clause < Clength[ i ])
      longest_clause = Clength[ i ];

        if (quiet_mode == 0)
  	  printf("c init_lookahead: longest clause has size %i\n", longest_clause);

	size_diff = (float*) malloc(sizeof(float) * longest_clause );
	size_diff[ 0 ] = 0.0;
	size_diff[ 1 ] = 0.0;
	size_diff[ 2 ] = h_bin;

	for (i = 3; i < longest_clause; i++)
	  size_diff[ i ] = size_diff[i-1] * h_dec;
	currentTimeStamp = 0;

        lookaheadArray = (int*) malloc( sizeof( int ) * 2 * nrofvars );

#ifdef DL_STATIC
	DL_trigger = DL_STATIC;
#else
	DL_trigger = 0.0;
#endif
#ifdef DL_VARMULT
	DL_trigger = freevars * DL_VARMULT * 0.01;
#endif
	forced_literal_array = (int*)  malloc( sizeof(int) * (nrofvars+1) );
	treeArray = (struct treeNode*) malloc( sizeof(struct treeNode) * (2*nrofvars+1) );

	MALLOC_OFFSET( EqDiff,        float, nrofvars,   0 );
	MALLOC_OFFSET( diff,          float, nrofvars,   1 );
	MALLOC_OFFSET( diff_tmp,      float, nrofvars,   1 );
	MALLOC_OFFSET( NBCounter,       int, nrofvars,   0 );
	MALLOC_OFFSET( WNBCounter,    float, nrofvars, 0.0 );
	MALLOC_OFFSET( failed_DL_stamp, int, nrofvars,   0 );

	INIT_ARRAY( look_fix, nrofvars );
	INIT_ARRAY( look_res, nrofvars );

	diff_table = (float* ) malloc( sizeof(float ) * 100 * (2*nrofvars+1) );
	diff_depth = (float**) malloc( sizeof(float*) * 100                  );
	for( i = 0; i < 100; i++ )
	    diff_depth[ i ] = diff_table + (i * (2*nrofvars+1) + nrofvars);

	_diff     = diff;
	_diff_tmp = diff_tmp;

	init_tree();

	non_tautological_equivalences = check_non_tautological_equivalences();

#ifdef EQ
	if (non_tautological_equivalences) {
       	    lengthWeight = (double *) malloc (sizeof(double) * (100000));
	    lengthWeight[ 0 ] = 0.0;
	    lengthWeight[ 1 ] = 0.0;

	    int i; for( i = 2; i < 100; i++ )
#ifdef QXBASE
 	        lengthWeight[ i ] = QXCONST * 0.5 * pow(0.6 + QXBASE * 0.01, i);
#else
	        lengthWeight[ i ] = 0.0;
#endif
	    for( i = 100; i < 100000; i++ ) lengthWeight[i] = 0.0;
	}
#endif

#ifdef EQ
  if (non_tautological_equivalences) {
    if (kSAT_flag) look_IUP = &look_IUP_w_eq_kSAT;
    else           look_IUP = &look_IUP_w_eq_3SAT; }
  else
#endif
  if (kSAT_flag)   look_IUP = &look_IUP_wo_eq_kSAT;
  else             look_IUP = &look_IUP_wo_eq_3SAT;

  if (dl_iter != 0) init_doublelook();
}

void dispose_lookahead () {
  dispose_tree();
  FREE (treeArray);
  FREE (size_diff);
#ifdef EQ
  FREE (lengthWeight);
#endif
  FREE_OFFSET( EqDiff          );
//  FREE_OFFSET( diff            );
//  FREE_OFFSET( diff_tmp        );
  FREE_OFFSET( NBCounter       );
  FREE_OFFSET( WNBCounter      );
  FREE_OFFSET( failed_DL_stamp );

  FREE( diff_table           );
  FREE( diff_depth           );
  FREE( lookaheadArray       );
  FREE( look_fixstack        );
  FREE( look_resstack        );
  FREE( forced_literal_array ); }

void look_IUP_end (const int nrval) {
  if (look_resstackp > look_resstack)
    add_resolvents (nrval);
#ifdef LOOK_SUBSUME
  if (currentTimeStamp != LOOK_MAX)
    lookahead_subsume (-nrval);
#endif
}

int look_IUP_with_eq (const int nrval, int *local_stackp) {
  while( local_stackp < end_fixstackp ) {
    int imp = *(local_stackp++);

    if (kSAT_flag) {
      if (look_fix_big_clauses (imp) == UNSAT) {
        end_fixstackp = local_stackp;
        return UNSAT; } }
      else {
	if (look_fix_ternary_implications (imp) == UNSAT)
          return UNSAT; }
 	if (look_fix_equivalences (imp) == UNSAT) {
	  end_fixstackp = local_stackp;
	  return UNSAT; } }

  look_IUP_end (nrval);
  return SAT; }

int look_IUP_w_eq_3SAT (const int nrval, int *local_stackp) {
  while (local_stackp < end_fixstackp) {
    int imp = *(local_stackp++);
    if (look_fix_ternary_implications (imp) == UNSAT)
      return UNSAT;

    if (look_fix_equivalences (imp) == UNSAT) {
      end_fixstackp = local_stackp;
      return UNSAT; } }

  look_IUP_end (nrval);
  return SAT; }

int look_IUP_w_eq_kSAT (const int nrval, int *local_stackp) {
  while( local_stackp < end_fixstackp ) {
    int imp = *(local_stackp++);
    if (look_fix_big_clauses (imp) == UNSAT) {
      end_fixstackp = local_stackp;
      return UNSAT; }

     if (look_fix_equivalences (imp) == UNSAT) {
       end_fixstackp = local_stackp;
       return UNSAT; } }

  look_IUP_end (nrval);
  return SAT; }

int look_IUP_wo_eq_3SAT (const int nrval, int *local_stackp) {
  while (local_stackp < end_fixstackp)
    if (look_fix_ternary_implications (*(local_stackp++)) == UNSAT)
      return UNSAT;

  look_IUP_end (nrval);
  return SAT; }

int look_IUP_wo_eq_kSAT (const int lit, int *local_stackp) {
  while (local_stackp < end_fixstackp)
    if (look_fix_big_clauses (*(local_stackp++)) == UNSAT) {
      end_fixstackp = local_stackp;
      return UNSAT; }

  look_IUP_end (lit);
  return SAT; }

void look_backtrack () {
  int *tail_stackp = end_fixstackp;

  do {
    if (tail_stackp == rstackp)        break;
    if (IS_FIXED( *(tail_stackp - 1))) break;
    tail_stackp--; }
  while (1);

  restore_big_clauses( end_fixstackp, tail_stackp ); }


int add_windfall_resolvent (const int lit) {
  if (addWFR) {
    *look_resstackp++ = lit; }

//  compensate_for_reduction (lit);
  return look_fix_binary_implications (lit); }

int look_IFIUP (const int lit) {
  int *local_stackp;

  /* reset counters and stacks */

  new_binaries          =   0;
  weighted_new_binaries = 0.0;

  if (kSAT_flag) look_backtrack ();
  else end_fixstackp  = look_fixstackp;

  local_stackp   = end_fixstackp;
  look_resstackp = look_resstack;

  if (look_fix_binary_implications (lit) == UNSAT) {
    end_fixstackp  = local_stackp;
    return UNSAT; }

  return look_IUP (lit, local_stackp); }

int look_fix_binary_implications (const int lit) {
  int *local_fixstackp = end_fixstackp;

  if (IS_FIXED(lit))
    return (FIXED_ON_COMPLEMENT(lit) == UNSAT);

  FIX(lit, currentTimeStamp);
  *(end_fixstackp++) = lit;

  while (local_fixstackp < end_fixstackp) {
    int *bImp = BIMP_START( *(local_fixstackp++) );
    int i; for (i = BIMP_ELEMENTS; --i;) {
      int lit1 = *(bImp++);

      if (IS_FIXED(lit1)) {
        if (FIXED_ON_COMPLEMENT(lit1)) return UNSAT; }
      else {
        FIX(lit1, currentTimeStamp);
        *(end_fixstackp++) = lit1; } } }

  return SAT; }

int look_fix_ternary_implications( const int nrval )
{
        int i, *tImp = TernaryImp[ -nrval ];

        for( i = TernaryImpSize[ -nrval ]; i > 0; i-- )
        {
            int lit1 = *(tImp++);
            int lit2 = *(tImp++);

	    if( IS_FIXED(lit1) )
	    {
	   	if( FIXED_ON_COMPLEMENT(lit1) )
		{
		    if( IS_FIXED(lit2) )
		    {
			if( FIXED_ON_COMPLEMENT(lit2) ) 	         return UNSAT;
		    }
		    else if (add_windfall_resolvent( lit2 ) == UNSAT ) return UNSAT;
	   	}
	    }
	    else if( IS_FIXED(lit2) )
	    {
	   	if( FIXED_ON_COMPLEMENT(lit2) )
   		    if (add_windfall_resolvent( lit1 ) == UNSAT )     return UNSAT;
	    }
	    else
	    {
#ifndef EVAL_VAR
	        new_binaries++;
#endif
		weighted_new_binaries += diff[ lit1 ] * diff[ lit2 ];
	    }
	}
#ifdef EVAL_VAR
	new_binaries++;
#endif
	return SAT;
}

int look_fix_big_clauses (const int nrval) {
        int *clauseSet = clause_set[ -nrval ];
        while( *clauseSet != LAST_CLAUSE )
        {
            int clause_index = *(clauseSet++);
            clause_length[ clause_index ]--;
#ifndef EVAL_VAR
	    new_binaries++;
#endif
#ifndef HIDIFF
  #ifdef SCHUR
  	    weighted_new_binaries += clause_weight[ clause_index ] * size_diff[ clause_length[ clause_index ] ];
  #else
  	    weighted_new_binaries += size_diff[ clause_length[ clause_index ] ];
  #endif
#endif
	    if (clause_length[ clause_index ] <= 1)
	    {
            	int* literals = clause_list[ clause_index ];
                while( *literals != LAST_LITERAL )
                {
		    int lit = *(literals)++;
                    if( IS_NOT_FIXED( lit ) )
		    {
		        if (add_windfall_resolvent( lit ) == SAT )
			    goto next_clause;
			break;
		    }
		    else if( !FIXED_ON_COMPLEMENT(lit) )
			goto next_clause;
		}
		while( *clauseSet != LAST_CLAUSE )
            	    clause_length[ *(clauseSet++) ]--;

		return UNSAT;
	    }

	    next_clause:;
	}
#ifdef HIDIFF
	weighted_new_binaries += hiSum[ -nrval ];
#endif
#ifdef EVAL_VAR
	new_binaries++;
#endif
//	weighted_new_binaries++;
	return SAT;
}

/*******************************************************
	Restores the sizes of the big clauses while
	backtracking. Using during lookahaed, doublelook,
	and resolvent_look
********************************************************/

void restore_big_clauses( int *head_stackp, int *tail_stackp ) {

	while( --head_stackp >= tail_stackp ) {
	    int* clauseSet = clause_set[ -*(head_stackp) ];
            while( *clauseSet != LAST_CLAUSE )
        	clause_length[ *(clauseSet++) ]++;
//		clause_mask  [ *clauseSet ] = clause_mask[ *clauseSet ] ^ head_stackp + SIZE_MASK;
//		clauseSet++;
	}
	end_fixstackp = tail_stackp;
}

int look_fix_equivalences( const int nrval )
{
        int i, j, eq_clause, *eq_array;

	eq_array = Veq[ NR(nrval) ] + 1;
        for( i = eq_array[ -1 ] - 1; i > 0; i-- )
        {
            eq_clause = *(eq_array++);

	    int lit  = 0;
	    int sign = 1;

	    for( j = CeqSizes[ eq_clause ] - 1; j >= 0; j-- )
	    {
	    	if( IS_FIXED(Ceq[ eq_clause ][ j ]) )
			sign *= EQSGN( Ceq[ eq_clause ][ j ] );
	    	else if( !lit )
  	               	lit = Ceq[ eq_clause ][ j ];
		else
		{
			new_binaries += 2;
                       	weighted_new_binaries += lengthWeight[ j + 2 ];
			goto ceqend;
		}
	    }
	    sign = sign * CeqValues[ eq_clause ];

	    if( lit != 0 )
	    {
	        if (add_windfall_resolvent(lit * sign) == UNSAT ) return UNSAT;
	    }
	    else if( sign == -1 )
	 	return UNSAT;

	    ceqend :;
        }
	return SAT;
}

/*
inline void compensate_for_reduction( const int nrval )
{
	int i, lit1, lit2, *tImp = TernaryImp[ nrval ];

	for( i = TernaryImpSize[ nrval ]; i > 0; i-- )
	{
	    lit1 = *(tImp++);
	    lit2 = *(tImp++);

	    if( IS_FIXED(lit1) )
	    {
		if( !IS_FIXED(lit2) && FIXED_ON_COMPLEMENT(lit1) )
		{
		    new_binaries--;
		    weighted_new_binaries -= diff[ nrval ] * diff[ lit2 ];
		}
	    }
	    if( IS_FIXED(lit2) && FIXED_ON_COMPLEMENT(lit2) )
	    {
		new_binaries--;
		weighted_new_binaries -= diff[ nrval ] * diff[ lit1 ];
	    }
	}
}
*/

void add_resolvents (const int nrval) {
  int stackSize = (int) (look_resstackp - look_resstack);
  if (addIMP) {
    CHECK_NODE_STAMP(nrval);
    CHECK_BIMP_UPPERBOUND (nrval, stackSize); }

  while (look_resstackp > look_resstack) {
    int imp = *(--look_resstackp);

    CHECK_BIMP_BOUND(-imp);
    CHECK_NODE_STAMP(-imp);
    if (addIMP) {
      ADD_BINARY_IMPLICATION( (-nrval), imp ); }

    ADD_BINARY_IMPLICATION(imp, (-nrval) ); }
}

void lookahead_subsume (const int nrval) {
  int i, *tImp = TernaryImp[nrval];

  for (i = TernaryImpSize[nrval] - 1; i >= 0; i--) {
    int lit1 = tImp[2*i  ];
    int lit2 = tImp[2*i+1];

    if (IS_FIXED(lit1) || IS_FIXED(lit2)) {
      if (IS_FORCED(lit1) || IS_FORCED(lit2)) continue;

      PUSH(subsume, nrval);

      int last = --TernaryImpSize[nrval];

      if (last != i) {
        tImp[2*i  ] = tImp[2*last  ]; tImp[2*last  ] = lit1;
        tImp[2*i+1] = tImp[2*last+1]; tImp[2*last+1] = lit2; }

      swap_ternary_implications (lit1, lit2, nrval);
      swap_ternary_implications (lit2, nrval, lit1); } } }

int look_fix_forced_literal(int nrval) {
  unsigned long long _currentTimeStamp;

  forced_literal_array[ forced_literals++ ] = nrval;

  _currentTimeStamp = currentTimeStamp;
  currentTimeStamp  = LOOK_MAX;

  if (look_IFIUP (nrval) == UNSAT)
    return UNSAT;

  currentTimeStamp = _currentTimeStamp;

  return SAT;
}

int init_lookahead_procedure () {
  forced_literals  = 0;
  currentTimeStamp = 2;

#ifdef INTELLOOK
  if (treebased_lookahead () == UNSAT) return UNSAT;
#else
  tree_elements = 2 * lookaheadArrayLength;
#endif
#ifdef DL_DECREASE
	DL_decrease = pow(DL_DECREASE, 1.0 / ((double) tree_elements));
#endif
  return SAT; }

int long_fix_forced_literals () {
  int i;
  unsigned long long _currentTimeStamp;

  _currentTimeStamp = currentTimeStamp;
  currentTimeStamp  = LOOK_MAX;

  for (i = 0; i < forced_literals; i++)
    if (look_IFIUP (forced_literal_array[i]) == UNSAT)
      return UNSAT;

  currentTimeStamp = _currentTimeStamp;
  return SAT; }

int tree_lookahead () {
  int iterCount   = 0;
  int lastChanged = 0;

  init_lookahead_procedure();

  do {
    iterCount++;
    int _forced_literals  = forced_literals;
    struct treeNode* _treeArray = treeArray;
    int i; for (i = tree_elements-1; i >= 0; i--) {
      struct treeNode node = *(_treeArray++);
      if (node.literal == lastChanged)
        return SAT;

      currentTimeStamp += node.gap;
      if (currentTimeStamp >= LOOK_MAX) {
        currentTimeStamp -= node.gap;
        return SAT; }

      if (treelookvar (node.literal) == UNSAT)
        return UNSAT;
      currentTimeStamp -= node.gap;

      if (forced_literals > _forced_literals) {
        if (IS_FIXED(node.literal) && (Rank[NR(node.literal)] < Rank_trigger)) { // obsolete ?
	  Rank_trigger = Rank[NR(node.literal)];
          printf ("c forced var with Rank %i\n", Rank_trigger); }
	_forced_literals = forced_literals;
	lastChanged = node.literal; } }
    currentTimeStamp += 2 * tree_elements;
  } while (lastChanged != 0 && iterCount <= sl_iter);

  return SAT; }

void look_add_autarky_binary_implications (const int parent, const int nrval) {
  int i, *bImp = BIMP_START((-nrval));

  for (i = BIMP_ELEMENTS; --i;)
    if (*(bImp++) == parent)
      return;

  CHECK_BIMP_BOUND( -nrval );
  CHECK_BIMP_BOUND( parent );
  CHECK_NODE_STAMP( -nrval );
  CHECK_NODE_STAMP( parent );
  ADD_BINARY_IMPLICATIONS( (-parent), nrval ); }

int check_doublelook (const int nrval) {
  if (dl_iter == 0) return SAT;

	if( failed_DL_stamp[ nrval ] != nodeCount )
	{
	    dl_possibility_counter++;

	    if( WNBCounter[ nrval ] > DL_trigger )
//	    if(  NBCounter[ nrval ] > (int) DL_trigger )
	    {
		dl_actual_counter++;
              	if( (currentTimeStamp + (dl_iter+1)*tree_elements ) >= LOOK_MAX )
		    return SAT;
		else
		    currentTimeStamp += tree_elements;

		if( doublelook( nrval, dl_iter*tree_elements) == UNSAT )
                	return look_fix_forced_literal(-nrval);

#ifdef DL_DECREASE
		DL_trigger = WNBCounter[ nrval ];
//		DL_trigger =  NBCounter[ nrval ];
#endif
		failed_DL_stamp[nrval] = nodeCount;
	    }
#ifdef DL_DECREASE
	    else DL_trigger *= DL_decrease;
#endif
	}
	return SAT;
}

int treelookvar( const int nrval )
{
        int i, parent;
	const int *loc;

	assert( currentTimeStamp < VARMAX );

	parent = assignment_array[ nrval ].parent;

	assert(parent != nrval);

	if( (parent != 0) && IS_FIXED(parent) && IS_NOT_FORCED(parent) )
	{
	    NBCounter [ nrval ] = NBCounter [ parent ];
            WNBCounter[ nrval ] = WNBCounter[ parent ];
	}
	else
	{
	    NBCounter [ nrval ] = 0;
	    WNBCounter[ nrval ] = 0;
	}

        if( IS_FIXED(nrval) )
	{
	    if (IS_FORCED(nrval) )
		return SAT;
	    if( FIXED_ON_COMPLEMENT(nrval) )
	    {
	    	return look_fix_forced_literal(-nrval);
	    }

#ifdef AUTARKY
	    look_add_autarky_binary_implications( parent, nrval );
#endif
	    return SAT;
	}

        lookAheadCount++;

        if( look_IFIUP(nrval) == UNSAT )
                return look_fix_forced_literal(-nrval);

	NBCounter [ nrval ] += new_binaries;
        WNBCounter[ nrval ] += weighted_new_binaries;

	if (check_doublelook (nrval) == UNSAT) return UNSAT;

#ifdef AUTARKY
	if( new_binaries == 0 )
	{
	    if( (parent == 0) || IS_FORCED(parent) )
	    {
		look_fix_forced_literal( nrval );
		return SAT;
	    }
	    look_add_autarky_binary_implications( parent, nrval );
	}
#endif
	loc = BinaryImp[ -nrval ];
        for( i = 2; i < loc[ 0 ]; i++ )
        {
            const int lit = loc[ i ];
            if( IS_FIXED(lit) && IS_NOT_FORCED(lit) )
	    {
 	        if( !FIXED_ON_COMPLEMENT(lit) )
                {
                    necessary_assignments++;
                    if( look_fix_forced_literal(lit) == UNSAT ) return UNSAT;
		    loc = BinaryImp[ -nrval ];
                }
                else
                {
#ifdef BIEQ
	            int bieq = -parent;
		    if( VeqDepends[ NR(nrval) ] != INDEPENDENT ) return 1;

                    while( VeqDepends[ NR(bieq) ] != INDEPENDENT )
		    {
			if( VeqDepends[ NR(bieq) ] != EQUIVALENT )
	                       	bieq = VeqDepends[ NR(bieq) ] * SGN(bieq);
			else
				bieq = EQUIVALENT;

			if( bieq == nrval ) break;
		    }

                    if( (bieq != EQUIVALENT) && (bieq != nrval) )
                    {
                        VeqDepends[ NR(bieq) ] = nrval * SGN(bieq);
                        PUSH( bieq, NR(bieq) );
		    }
#endif
		}
            }
        }

        return SAT;
}

int get_signedBranchVariable () {
  int i, maxDiffVar, maxDiffSide;
  double maxDiffScore, diffScore, left, right;

/* set maxDiffScore to unreachable minimum */
  maxDiffScore = -1;
  maxDiffVar   =  0;
  maxDiffSide  =  0;

//	printf("c get_signedbranch %i (%i)\n", nodeCount, lookaheadArrayLength );

  int only_reduced_variables_flag = 0;
  if (gah) only_reduced_variables_flag = 1;

  do {
    for (i = 0; i < lookaheadArrayLength; i++) {
      int varnr = lookaheadArray[ i ];

      if (gah) { // global autarky heuristic
	if ((only_reduced_variables_flag == 1) &&
	    (VeqDepends[ varnr ] == EQUIVALENT)) continue;

	if ((only_reduced_variables_flag == 1) &&
	    (TernaryImpReduction[ varnr] == 0) &&
	    (TernaryImpReduction[-varnr] == 0))
          continue; }

       if (IS_NOT_FORCED(varnr)) {
#ifdef EVAL_VAR
         left  = NBCounter[ varnr];
         right = NBCounter[-varnr];
#else
         left  = 1024 * WNBCounter[ varnr] + 0.0;
         right = 1024 * WNBCounter[-varnr] + 0.0;
#endif
         diffScore = left * right + left + right;

         if (diffScore > maxDiffScore) {
           maxDiffScore = diffScore;
           maxDiffVar   = varnr;
           maxDiffSide  = (left > right)? -1 : 1; } } }
      only_reduced_variables_flag--;
    } while ((maxDiffVar == 0) && (only_reduced_variables_flag >= 0));

#ifdef FLIP_UNBALANCE
    {
	double bias;
	left  = WNBCounter[  maxDiffVar ] + 0.01;
	right = WNBCounter[ -maxDiffVar ] + 0.01;

	bias = left / right + right / left - 1.0;

	if( bias > 6 ) maxDiffSide *= -1;
    }
#endif
//	printf("secelted %i at %i with diff %i\n", maxDiffVar * maxDiffSide, nodeCount, (int) maxDiffScore );

  if (seed && (rand () % 2))
    maxDiffSide *= -1;

  return maxDiffVar * maxDiffSide;
}

void cleanFormula() { // currently only used in preprocessor
  int i;
  for (i = 1; i <= nrofvars; i++)
    if (timeAssignments[ i ] < VARMAX) { UNFIX(i); }

  currentTimeStamp = 0; }

int serial_lookahead () {
  int iterCount   = 0;
  int lastChanged = 0;

  init_lookahead_procedure();

  do {
    iterCount++;

    if ((currentTimeStamp + 4 * lookaheadArrayLength) >= LOOK_MAX) {
      printf("c CTS: %i; LOOK_MAX: %i\n", currentTimeStamp, LOOK_MAX ); }

    int i; for (i = 0; i < lookaheadArrayLength; i++) {
      int var = lookaheadArray[ i ];

      if (var == lastChanged) return SAT;
      if (IS_FORCED(var)) continue;

      lookAheadCount++;

      int s; for (s = 1; s >= -1; s -= 2) {
        int lit = var * s;
        currentTimeStamp += 2;

        if (look_IFIUP(lit) == UNSAT) {
          if (look_fix_forced_literal (-lit) == UNSAT) return UNSAT;
          lastChanged = var; continue; }
#ifdef AUTARKY
        if (new_binaries == 0) {
          look_fix_forced_literal (lit);
          lastChanged = var; continue; }
#endif
        NBCounter [lit] = new_binaries;
        WNBCounter[lit] = weighted_new_binaries;

        if (check_doublelook (lit) == UNSAT) return UNSAT;
        if (IS_FORCED(lit)) { lastChanged = var; continue; }

        int j; for (j = 2; j < BinaryImp[-lit][0]; j++) {
          int imp = BinaryImp[-lit][j];
	  if (timeAssignments[ imp ] == currentTimeStamp) {
            necessary_assignments++;
            if (look_fix_forced_literal(imp) == UNSAT) return UNSAT;
	    lastChanged = var; } } } }
  } while (lastChanged != 0 && iterCount <= sl_iter);

  return SAT; }

void get_forced_literals (int **_forced_literal_array, int *_forced_literals) {
  *_forced_literal_array = forced_literal_array;
  *_forced_literals      = forced_literals; }

int ternarylook_fix_ternary_implications (const int nrval) {
  int i, *tImp = TernaryImp[ -nrval ];
  for (i = TernaryImpSize[ -nrval ]; i > 0; i--) {
    int lit1 = *(tImp++);
    int lit2 = *(tImp++);

    if (IS_FIXED(lit1)) {
      if (FIXED_ON_COMPLEMENT(lit1)) {
        if (IS_FIXED(lit2)) {
          if (FIXED_ON_COMPLEMENT(lit2)) return UNSAT; }
        else {
          FIX(lit2, currentTimeStamp);
          *(look_fixstackp++) = lit2;
          *(look_resstackp++) = lit2; } } }
     else if (IS_FIXED(lit2))
       if (FIXED_ON_COMPLEMENT(lit2)) {
         FIX (lit1, currentTimeStamp);
         *(look_fixstackp++) = lit1;
         *(look_resstackp++) = lit1; } }

  return SAT; }

int ternarylook_fix_direct_implications (const int parent, const int reference) {
  int i, *tImp = TernaryImp[parent];
  for (i = TernaryImpSize[parent]; i > 0; i--) {
    int lit1 = *(tImp++);
    int lit2 = *(tImp++);

    if (lit1 == reference) {
      if (IS_FIXED(lit2)) {
        if (FIXED_ON_COMPLEMENT(lit2)) return UNSAT; }
      else { FIX(lit2, currentTimeStamp); *(look_fixstackp++) = lit2; } }
    else if (lit2 == reference) {
      if (IS_FIXED(lit1)) {
        if( FIXED_ON_COMPLEMENT(lit1) ) return UNSAT; }
      else { FIX(lit1, currentTimeStamp); *(look_fixstackp++) = lit1; } } }

  return SAT; }

void ternarylook_detect_constraint_resolvents( const int lit1, const int lit2 )
{
	if( !ternarylook_add_constraint_resolvents( lit1, lit2 ) )
	{
	    int i;
	    for( i = 2; i < BinaryImp[ lit1 ][ 0 ]; i++ )
		if( BinaryImp[ lit1 ][ i ] == -lit2 )	return;

	    CHECK_BIMP_BOUND( lit1 );
	    CHECK_BIMP_BOUND( lit2 );
	    BinaryImp[ lit1 ][ ( BinaryImp[ lit1 ][ 0 ] )++ ] = -lit2;
	    BinaryImp[ lit2 ][ ( BinaryImp[ lit2 ][ 0 ] )++ ] = -lit1;

	    Cv                = (int**) realloc( Cv,      sizeof( int*) * ( nrofclauses + 1 ) );
	    Cv[ nrofclauses ] = (int* ) malloc ( sizeof(int) * 3);
	    Clength           = (int* ) realloc( Clength, sizeof( int ) * ( nrofclauses + 1 ) );

	    Clength[ nrofclauses ] = 2;
	    Cv[ nrofclauses ][ 0 ] = -lit1;
	    Cv[ nrofclauses ][ 1 ] = -lit2;

	    nrofclauses++;
	}
}

int ternarylook_add_constraint_resolvents( const int lit1, const int lit2 )
{
	int *_look_fixstackp, *_look_resstackp, clause[ 3 ], i, j, varnr;

	look_fixstackp = look_fixstack;
	look_resstackp = look_resstack;
	_look_fixstackp = look_fixstackp;
	_look_resstackp = look_resstackp;
        currentTimeStamp += 2;

        FIX( lit1, currentTimeStamp );
	*(look_fixstackp++) = lit1;

        FIX( lit2, currentTimeStamp );
	*(look_fixstackp++) = lit2;

	if( ternarylook_fix_direct_implications( -lit1, -lit2 ) == UNSAT )
		return UNSAT;

	while( _look_fixstackp < look_fixstackp )
	    if( ternarylook_fix_ternary_implications( *(_look_fixstackp++) ) == UNSAT )
		return UNSAT;

        Cv      = (int**) realloc( Cv,      sizeof( int*) * ( nrofclauses + (look_resstackp - _look_resstackp ) ) );
        Clength = (int *) realloc( Clength, sizeof( int ) * ( nrofclauses + (look_resstackp - _look_resstackp ) ) );

	clause[ 0 ] = -lit1;
	clause[ 1 ] = -lit2;

	while( _look_resstackp < look_resstackp )
	{
	    clause[ 2 ] = *(_look_resstackp++);

	    Cv[ nrofclauses ] = (int*) malloc( sizeof(int) * 3);
	    Clength[ nrofclauses ] = 3;
	    for( i = 0; i < 3; i++ )
	    {
		Cv[ nrofclauses ][ i ] = clause[ i ];
		if( tmpTernaryImpSize[ clause[i] ] <= (2 * TernaryImpSize[ clause[i] ])  )
		{
	 	    tmpTernaryImpSize[ clause[i] ] *= 2;
		    TernaryImp[ clause[i] ] = (int*) realloc( TernaryImp[ clause[i] ],
 				sizeof(int) * (2 * tmpTernaryImpSize[ clause[i] ]+2) );
		}
	    }
 	    nrofclauses++;

            for( j = 0; j < 3; j++ )
            {
                varnr = clause[ j ];
                TernaryImp[ varnr ][ 2 * TernaryImpSize[ varnr ]     ] = clause[ (j + 1) % 3 ];
                TernaryImp[ varnr ][ 2 * TernaryImpSize[ varnr ] + 1 ] = clause[ (j + 2) % 3 ];
            }
            for( j = 0; j < 3; j++ )
                TernaryImpSize[ clause[j] ]++;
        }
	return SAT;
}

void ComputeDiffWeights( )
{
        int i, j, index, *Reductions, accuracy;
        int *tImp, *bImp, iteration_count = 1;
	float *tmpfloat;
	float pos, neg;
	float sum = 0.0, wnorm, factor, fsquare;

//	float diff_weight = DIFF_WEIGHT;
	float diff_weight = h_bin;

	diff     = _diff;
	diff_tmp = _diff_tmp;

	if (kSAT_flag)	Reductions = big_occ;
	else		Reductions = TernaryImpSize;

#ifdef EQ
        if (non_tautological_equivalences) {
          for( i = freevars - 1; i >= 0; i-- ) {
	        sum = 0.0;
            	index = freevarsArray[ i ];
		if( Veq[ index ][ 0 ] > 1 )
		    for( j = Veq[ index ][ 0 ] - 1; j > 0; j-- )
			sum += 2 * lengthWeight[ CeqSizes[ Veq[ index ][ j ] ] - 1 ];

		EqDiff[  index ] = sum + Reductions[  index ];
		EqDiff[ -index ] = sum + Reductions[ -index ];
	    }
	}
	else
#endif
	if( (non_tautological_equivalences == 0) && (kSAT_flag == 0) &&
		(depth > ROOTSIZE) && (depth <= RECORDSIZE) && 0) {
	    diff = diff_depth[ depth - 1 ];
	    sum  = 2.0 * freevars;
	}
	else
	{
	    sum = 0.0;
            assert (freevars > 0);
            for( i = freevars - 1; i >= 0; i-- )
            {
         	index = freevarsArray[ i ];
#ifdef EQ
		if( non_tautological_equivalences )
		{
		    pos = 1 + EqDiff[ index ]; bImp = BinaryImp[ index ] + 2;
		    for(j = bImp[ -2 ] - 1; --j; ) pos += EqDiff[ -*(bImp++) ];
		    neg = 1 + EqDiff[ -index ]; bImp = BinaryImp[ -index ] + 2;
		    for(j = bImp[ -2 ] - 1; --j; ) neg += EqDiff[ -*(bImp++) ];
		}
		else
#endif
		if( kSAT_flag )
		{
#ifdef HIDIFF
		    pos = 1 + hiSum[ index ]; bImp = BinaryImp[ index ] + 2;
		    for(j = bImp[ -2 ] - 1; --j; ) pos += hiSum[ -*(bImp++) ];
		    neg = 1 + hiSum[ -index ]; bImp = BinaryImp[ -index ] + 2;
		    for(j = bImp[ -2 ] - 1; --j; ) neg += hiSum[ -*(bImp++) ];
#else
		    pos = 1 + Reductions[ index ]; bImp = BinaryImp[ index ] + 2;
		    for(j = bImp[ -2 ] - 1; --j; ) pos += Reductions[ -*(bImp++) ];
		    neg = 1 + Reductions[ -index ]; bImp = BinaryImp[ -index ] + 2;
		    for( j = bImp[ -2 ] - 1; --j; ) neg += Reductions[ -*(bImp++) ];
#endif
		    Rank[ index ] = 1024 * pos * neg + pos + neg + 1;
//		    assert( Rank[ index ] > 0 );
		}
		else
		{
                    float dw = diff_weight;
	            pos = 0.1 + (Reductions[ -index ] +
			dw * (BinaryImp[  index ][ 0 ] - bImp_satisfied[  index ]));

	            neg = 0.1 + (Reductions[ index ] +
			dw * (BinaryImp[ -index ][ 0 ] - bImp_satisfied[ -index ]));

		    if( non_tautological_equivalences ) Rank[ index ] = 1024 * pos * neg + 1;
		    else
		    {   sum += pos + neg; diff[ index ] = pos; diff[ -index ] = neg; }
		}
	    }
	}

        if( non_tautological_equivalences | kSAT_flag ) return;

	dist_acc_flag = dist_acc_flag > 0;

	if( depth <= ROOTSIZE )	accuracy = ROOTACC;
	else			accuracy = ACCURACY;

//            float min, max;
    float max = h_max;
    float min = h_min;
//    max = MAXONE;
//    min = MINONE;

    if( depth <= RECORDSIZE )
    {
	while (iteration_count < (accuracy + dist_acc_flag) )
	{
/*
	    float avg = (freevars * 2) / sum;
            sum = 0.0;
            for (i = freevars - 1; i >= 0; i--)
            {
            	index = freevarsArray[ i ];
		diff[-index] *= avg;
		diff[ index] *= avg;
                sum += diff[-index] + diff[index];
	    }
*/
//break;
	    factor  = 2.0 * freevars / sum;
	    fsquare = factor * factor;
	    wnorm   = 1.0 * diff_weight / factor;

//            printf("fsq %.7f, factor %.3f, wnorm = %.3f, iter %i, average %.3f\n", fsquare, 1.0 / factor, wnorm, iteration_count, sum / freevars);

	    tmpfloat = diff_tmp;
	    diff_tmp = diff;
	    diff     = tmpfloat;

	    if (iteration_count == 2) diff = _diff;

	    sum = 0.0;

            for (i = freevars - 1; i >= 0; i--)
            {
            	index = freevarsArray[ i ];

	        pos = 0.0; bImp = BIMP_START( -index );
                for( j = BIMP_ELEMENTS; --j; )
	        {  if( IS_NOT_FIXED(*bImp) ) pos += diff_tmp[ *bImp ] ; bImp++; }
	    	pos *= wnorm;

		{ tImp = TernaryImp[ index ];
                for( j = TernaryImpSize[ index ]; j > 0; j-- )
                {  pos += diff_tmp[ tImp[0] ] * diff_tmp[ tImp[1] ]; tImp += 2;  } }

	        neg = 0.0; bImp = BIMP_START( index );
                for( j = BIMP_ELEMENTS; --j; )
	        {  if( IS_NOT_FIXED(*bImp) ) neg += diff_tmp[ *bImp ]; bImp++; }
	        neg *= wnorm;

		{ tImp = TernaryImp[ -index ];
                for( j = TernaryImpSize[ -index ]; j > 0; j-- )
                {  neg += diff_tmp[ tImp[0] ] * diff_tmp[ tImp[1] ]; tImp += 2;  } }

	        diff[  index ] = fsquare * neg;
	        diff[ -index ] = fsquare * pos;

//if (iteration_count >= ROOTACC - 1)
{
		if( diff[ -index ] > max ) diff[ -index ] = max;
		if( diff[  index ] > max ) diff[  index ] = max;
//		if( diff[ -index ] > max ) diff[ -index ] = max + sqrt(diff[-index] - max);//, iteration_count++;
//		if( diff[  index ] > max ) diff[  index ] = max + sqrt(diff[ index] - max);//, iteration_count++;
}
		if( diff[ -index ] < min ) diff[ -index ] = min;
		if( diff[  index ] < min ) diff[  index ] = min;

	        sum += diff[ index ] + diff[ -index ];
	    }
	    iteration_count++;
	}
    }


	diff_tmp = diff;
	if( depth < RECORDSIZE ) diff = diff_depth[ depth ];
	else	 	  	 diff = _diff;

	factor = 2.0 * freevars / sum;
	wnorm  = diff_weight / factor;

        for( i = freevars - 1; i >= 0; i-- )
        {
            index = freevarsArray[ i ];

	    diff[  index ] = diff_tmp[  index ] * factor;
	    diff[ -index ] = diff_tmp[ -index ] * factor;

	    Rank[  index ] = 1024 * diff[ index ] * diff[ -index ];
	}

	dist_acc_flag = 0;

	return;
}

void reset_lookahead_resstack_head () {
  *look_resstack = 0; }

int get_lookahead_resstack_head () {
  return *look_resstack != 0; }
