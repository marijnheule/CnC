/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

#ifndef __LOOKAHEAD_H__
#define __LOOKAHEAD_H__

void init_lookahead   ();
void dispose_lookahead();

int lookahead();

       int treelookvar			( const int nrval );
       int look_IFIUP			( const int nrval );
       int look_fix_forced_literal	( const int nrval );

       int look_fix_big_clauses         ( const int nrval );
       int look_fix_binary_implications	( const int nrval );
int look_fix_equivalences	( const int nrval );
int look_fix_ternary_implications( const int nrval );
int add_constraint_resolvent	( const int nrval );
       void add_resolvents		( const int nrval );

       void restore_big_clauses ( int *head_stackp, int *tail_stackp );
       void evaluate_big_clauses( int *head_stackp, int *tail_stackp );

       void look_backtrack();

void lookahead_subsume( const int nrval );

void get_forced_literals( int **_forced_literal_array, int *_forced_literals );
int  get_signedBranchVariable( );

int check_all_equal( int clsidx );

void ComputeDiffWeights( );

void cleanLookahead();
void cleanFormula();

void reset_lookahead_resstack_head( );
int    get_lookahead_resstack_head( );

int ternarylook_fix_direct_implications ( const int parent, const int reference );
int ternarylook_fix_ternary_implications( const int nrval );
void   ternarylook_detect_constraint_resolvents( const int lit1, const int lit2 );
int    ternarylook_add_constraint_resolvents   ( const int lit1, const int lit2 );

#endif
