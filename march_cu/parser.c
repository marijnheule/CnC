/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#include <stdio.h>
#include <stdlib.h>

#include "math.h"

#include "common.h"
#include "parser.h"
#include "memory.h"
#include "equivalence.h"

int *simplify_stack, *simplify_stackp;

#define PUSH_PARSER_NA( __a ) \
{ \
	if( timeAssignments[ __a ] >= VARMAX ) \
	{ \
            if( FIXED_ON_COMPLEMENT( __a )  )\
		return UNSAT; \
        } \
        else \
        { \
	    timeAssignments[  __a ] = VARMAX; \
            timeAssignments[ -__a ] = VARMAX + 1; \
            *( simplify_stackp++ ) = __a; \
        } \
}


/*
************************************************************************
*  CNF init and deinit, parsing and unary clause removal.              *
************************************************************************
*/

/*
	MALLOCS: 	-
	REALLOCS:	-
	FREES:	 	-
*/
int initFormula( FILE* in )
{
	int result;

	/*
		initialize global data structure.
	*/
	original_nrofvars    = 0;
	original_nrofclauses = 0;
	nrofvars             = 0;
	activevars           = 0;
	nrofclauses          = 0;
        nrofceq              = 0;
	initial_freevars     = 0;
	non_tautological_equivalences = 0;
        lookaheadArrayLength = 0;
	forced_literals = 0;

	Cv                   = NULL;
	Clength              = NULL;
	timeAssignments      = NULL;
	VeqDepends           = NULL;

	/*
		search for p-line in DIMACS format
	*/
	do
	{
		result = fscanf( in, " p cnf %i %i \n", &( original_nrofvars ), &( original_nrofclauses ) );
		if( result > 0 && result != EOF )
			break;

		result = fscanf( in, "%*s\n" );
	}
	while (result != 2 && result != EOF);

	if (result == EOF || result != 2) return 0;

        if (quiet_mode) printf ("p inccnf\n");

	nrofvars    = original_nrofvars;
	activevars  = original_nrofvars;
	nrofclauses = original_nrofclauses;
	freevars    = nrofvars;

	if ((nrofclauses / nrofvars) > 10) {
          if (quiet_mode == 0)
	    printf("c full lookahead due to high density!\n");
	  percent = 100; }
	else
	   percent = PERCENT;

        if (quiet_mode == 0)
          printf( "c the DIMACS p-line indicates a CNF of %i variables and %i clauses.\n", nrofvars, nrofclauses );

	return 1;
}


/*
	MALLOCS: 	-
	REALLOCS:	-
	FREES:	 	Cv[ * ], Cv, Clength, timeAssignments, VeqDepends
*/
void disposeFormula () {
/* Can also be used to delete a partial formula, because Cv[ i ]
   is initialized to NULL. IMPORTANT: according to 'man free',
   free (void *ptr) does nothing iff (ptr == NULL). This
   behaviour is vital to disposeFormula () and other parts of
   the solver where memory is freed. */

  if (Cv != NULL) {
    int i;
    for (i = 0; i < nrofclauses; i++) free (Cv[i]);
    free (Cv);
    Cv = NULL; }

/* IMPORTANT: timeAssignments should be corrected before
   attempting this. (In the lookahead, nrofvars is added to both
   pointers to speed up indexing.) Neglecting this correction
   means Segfault Suicide! */

  FREE_OFFSET( timeAssignments );
  FREE( VeqDepends );
  FREE( Clength );

/* Update cnf structure. */

  original_nrofvars    = 0;
  original_nrofclauses = 0;
  nrofvars 	       = 0;
  nrofclauses	       = 0;

  dispose_equivalence ();
}

/*
	MALLOCS: 	_clause, Cv, Cv[], Clength, timeAssignments
	REALLOCS:	-
	FREES:	 	_clause
*/
int parseCNF( FILE* in )
{
	int *_clause, clen, _lit;
	int i, j, error;

	int unary = 0;

	/*
		Allocate buffer to hold clause. A clause can never
		be longer than nrofvars, for obvious reasons.
	*/
	_clause = (int*) malloc( sizeof( int ) * nrofvars );

	/* INIT GLOBAL DATASTRUCTURES!! */

	Cv = (int**) malloc( sizeof( int* ) * nrofclauses );
	for( i = 0; i < nrofclauses; i++ )
		Cv[ i ] = NULL;

	/* Clength: length of clause i */
	Clength = (int*) malloc( sizeof( int ) * nrofclauses );

        /* BinaryImp: implication clause table */
        BinaryImp       = (int**) malloc( sizeof( int* ) * ( 2 * nrofvars + 1) );
        BinaryImpLength = (int* ) malloc( sizeof( int  ) * ( 2 * nrofvars + 1) );

        for( i = 0; i < (2 * nrofvars + 1); i++ )
        {
                BinaryImp      [ i ] = (int*) malloc( sizeof( int ) * INITIAL_ARRAY_SIZE );
                BinaryImpLength[ i ] = INITIAL_ARRAY_SIZE - 1;
                BinaryImp [ i ][ 0 ] = 2;
                BinaryImp [ i ][ 1 ] = 0;              //Moet nog weggewerkt worden...
        }

        BinaryImp       += nrofvars;
        BinaryImpLength += nrofvars;

	/* timeAssignments & VeqDepends */
	timeAssignments = (tstamp*) malloc( sizeof( tstamp ) * ( 2 * nrofvars + 1 ) );
	VeqDepends      = (int*   ) malloc( sizeof( int ) * ( nrofvars + 1 ) );

	timeAssignments += nrofvars;

	for( i = 0; i < ( nrofvars + 1 ); i++ )
	{
	    VeqDepends     [  i ] = 0;
	    timeAssignments[  i ] = 0;
	    timeAssignments[ -i ] = 0;
	}

	i = clen = error = 0;
	while( i < nrofclauses && !error )
	{
	    error = (fscanf (in, " %i ", &_lit) != 1);

	    if( !error )
	    {
		if( _lit == 0 )
		{
		    if( clen == 0 )
		    {
			/* a zero-length clause is not good! */
			printf( "c WARNING: zero length clause found in input!\n" );
			error = 1;
		    }
		    else
		    {
			if( clen == 1 )
			    unary++;

			Cv[ i ] = (int*) malloc( sizeof( int ) * clen );
			Clength[ i ] = clen;
                        if (quiet_mode) {
  			  for (j = 0; j < clen; j++) printf ("%i ", _clause[j]);
                          printf ("0\n"); }
			for( j = 0; j < clen; j++ ) Cv[ i ][ j ] = _clause[ j ];
			    clen = 0;
			i++;
		    }
		}
		else
		{
		    if( clen < nrofvars )
			_clause[ clen++ ] = _lit;
		    else
		    {
			printf( "c WARNING: clause length exceeds total number of variables in this CNF.\n" );
			error = 1;
		    }
		}
	    }
	}


	/* free clause buffer */
	free( _clause );

//	if( !error )
//	    printf( "c parseCNF():: the CNF contains %i unary clauses.\n", unary );
	if( error )
	    disposeFormula();

	return !error;
}

int simplify_formula () {
  int _iterCounter    = 0;
  int tautologies     = 0;
  int satisfied       = 0;
  int duplicates      = 0;
  int bi_equivalences = 0;

  do {
    _iterCounter  = bi_equivalences + nrofvars - freevars;


    tautologies += sort_literals();
    if (find_and_propagate_unary_clauses () == UNSAT) return UNSAT;
    satisfied  += compactCNF ();
    duplicates += sort_clauses ();
#ifdef SIMPLE_EQ
    if (sharp_mode == 0) {
      bi_equivalences += find_and_propagate_binary_equivalences ();
      if (check_vadility_equivalences () == UNSAT) return UNSAT; }
#endif


  } while ((bi_equivalences + nrofvars - freevars) > _iterCounter);

  return SAT; }

/*******************************************************************************
  sort_literals bubble sorts all _variables_ in all clauses of the CNF
  and returns the number of tautological clauses (clauses that contain
  both a literal xi and literals ~xi) found while sorting.
********************************************************************************/

int sort_literals () {
  int i, j, k, count = 0;

  for (i = 0; i < nrofclauses; i++)
    for (k = 0; k < Clength[i] - 1; k++)
      for (j = 0; j < Clength[i] - k - 1; j++) {
        if (NR(Cv[i][j]) > NR(Cv[i][j+1])) {
	  int tmp = Cv[i][j];
          Cv[i][j  ] = Cv[i][j+1];
          Cv[i][j+1] = tmp; }
        else if( NR(Cv[i][j]) == NR(Cv[i][j+1]) ) {
          /* Double literal? -> swap it out of the clause. */
          if (Cv[i][j] == Cv[i][j+1])
            Cv[i][j--] = Cv[i][--Clength[i]] ;
         else {
	   /* The same literal positive and negative. So a tautology. -> eliminate clause. */
	   Clength[i] = 0;
	   count++; } } }

  return count; }

int find_and_propagate_unary_clauses () {
  int i;

  simplify_stack = (int*) malloc (sizeof(int) * (nrofvars + 1));
  simplify_stackp = simplify_stack;

  for (i = 0; i < nrofclauses; i++)
    if (Clength[ i ] == 1) { PUSH_PARSER_NA( Cv[ i ][ 0 ] ); }

  for (i = 0; i < nrofceq; i++)
    if (CeqSizes[ i ] == 1) { PUSH_PARSER_NA( Ceq[ i ][ 0 ] * CeqValues[ i ] ); }

  int result = propagate_unary_clauses();

  free (simplify_stack);

  return result; }

/*
	MALLOCS: 	_Vc, _Vc[], _VcTemp
	REALLOCS:	-
	FREES:	 	_VcTemp, _Vc[ * ], _Vc
*/
int propagate_unary_clauses()
{
        int i, j, nrval, clsidx, *_simplify_stackp;
        int **_variableArray;


	_simplify_stackp = simplify_stack;

	allocateSmallVc( &_variableArray , 1 );
	_variableArray += nrofvars;

	/* fix monotone variables that do not occur in equivalence clauses */
#ifdef FIX_MONOTONE
	for( i = 1; i <= nrofvars; i++ )
	   if( Veq[ i ][ 0 ] == 1 )
	   {
		if( (_variableArray[ i ][ 0 ] == 0) && (_variableArray[ -i ][ 0 ] > 0) )
		{
		    PUSH_PARSER_NA( -i );
		}
		else if( (_variableArray[ i ][ 0 ] > 0) && (_variableArray[ -i ][ 0 ] == 0) )
		{
		    PUSH_PARSER_NA(  i );
		}
	   }
#endif

	while( _simplify_stackp < simplify_stackp )
	{
		nrval = *( _simplify_stackp++ );
		freevars--;

		/*
			All clauses containing nrval are satisfied.
			They are removed from the CNF by setting Clength = 0.
		*/
	        for( i = 1; i <= _variableArray[ nrval ][ 0 ] ; i++ )
	        	Clength[ _variableArray[ nrval ][ i ] ] = 0;

		/*
			All clauses containing ~nrval are shortened by removing ~nrval
			from the clause. If this operation results in a unary clause,
			then this clause is removed from the CNF by setting Clength = 0
			and the literal is pushed on the fix stack to be fixed later.
		*/
	        for( i = 1; i <= _variableArray[ -nrval ][ 0 ]; i++ )
	        {
			clsidx = _variableArray[ -nrval ][ i ];
	                for( j = 0; j < Clength[ clsidx ]; j++ )
	                {
	                        if( Cv[ clsidx ][ j ] == -nrval )
	                        {
	                                /*
						Swap literal to the front of the clause.
					*/
	                                Cv[ clsidx ][ j-- ] = Cv[ clsidx ][ --( Clength[ clsidx ] ) ];
	                                if( Clength[ clsidx ] == 1 )
	                                {
	                                        PUSH_PARSER_NA( Cv[ clsidx ][ 0 ] );
	                                        Clength[ clsidx ] = 0;
	                                }
	                        }
	                }
		}

		while( Veq[ NR(nrval) ][ 0 ] > 1 )
		{
			clsidx = Veq[ NR(nrval) ][ 1 ];

			fixEq( NR(nrval), 1, SGN(nrval));
			if( CeqSizes[ clsidx ] == 1 )
			{
				PUSH_PARSER_NA( Ceq[ clsidx ][ 0 ] * CeqValues[ clsidx ] );
			}
		}
	}

	/*
		Free temporary allocated space.
	*/
	_variableArray -= nrofvars;
	freeSmallVc( _variableArray );

	return 1;
}

int sort_clauses () {
	int i, j, clen, *tmpcls, flag, _nrofclauses, _result;

	for( i = 0; i < nrofclauses; i++ )
	{
		clen = Clength[ i ];
		tmpcls = (int*) malloc( sizeof( int ) * ( clen + 1 ) );
		tmpcls[ 0 ] = clen;

		for( j = 0; j < clen; j++ )
			tmpcls[ j + 1 ] = Cv[ i ][ j ];

		free (Cv[i]);
		Cv[i] = tmpcls;
	}
	free( Clength );
	Clength = NULL;

	/* Quick sort all clauses in the CNF. */
	qsort( Cv, nrofclauses, sizeof( int* ), clsCompare );

	/* Remove all identical clauses. */
	for( i = 0; i < nrofclauses - 1; i++ )
	{
	   flag = 1;
	   for( j = 0; j <= Cv[ i ][ 0 ]; j++ )
		if( Cv[ i ][ j ] != Cv[ i + 1 ][ j ] )
		{
			flag = 0;
			break;
		}

	   if( flag ) Cv[ i ][ 0 ] = 0;
	}

	/* Restore Clength and Cv. */
	Clength = (int*) malloc( sizeof( int ) * nrofclauses );

	_nrofclauses = 0;
	for( i = 0; i < nrofclauses; i++ )
	{
		clen = Cv[ i ][ 0 ];
		if( clen == 0 )
		{
			free( Cv[ i ] );
			Cv[ i ] = NULL;
		}
		else
		{
			tmpcls = (int*) malloc( sizeof( int ) * clen );
			Clength[ _nrofclauses ] = clen;

			for( j = 0; j < clen; j++ )
				tmpcls[ j ] = Cv[ i ][ j + 1 ];

			free( Cv[ i ] );
			Cv[ _nrofclauses ] = tmpcls;
			_nrofclauses++;
		}
	}

	Cv 	= (int**) realloc( Cv     , sizeof( int* ) * _nrofclauses );
	Clength = (int* ) realloc( Clength, sizeof( int  ) * _nrofclauses );

	_result = nrofclauses - _nrofclauses;

	nrofclauses = _nrofclauses;

	compactCNF();

	return _result;
}

int find_and_propagate_binary_equivalences() {
  int count = 0;
  int i; for (i = 0; i < (nrofclauses - 1); i++) {
    if ((Clength[ i ] == 2) && (Clength[ i + 1 ] == 2) &&
        (Cv[ i ][ 0 ] == -Cv[ i + 1 ][ 0 ]) &&
        (Cv[ i ][ 1 ] == -Cv[ i + 1 ][ 1 ]) &&
        (NR(Cv[ i ][ 0 ]) != NR(Cv[ i ][ 1 ]))) {
       /* We found a new bi-equivalency. */
       count++;
       add_binary_equivalence( Cv[ i ][ 0 ], Cv[ i ][ 1 ] );

       /* Remove clauses; */
       Clength[i  ] = 0;
       Clength[i+1] = 0; } }

  count += find_and_propagate_bieq();

  return count; }

/*****  MALLOCS: 	-                     *****
 *****	REALLOCS:	Cv[ .. ], Cv, Clength *****
 *****	FREES:	 	Cv[ .. ]              *****/

int compactCNF() {
  int _nrofclauses = 0;
  int i; for (i = 0; i < nrofclauses; i++) {
     if (Clength[i] == 0) {
       free (Cv[i]);
       Cv[i] = NULL; }
     else {
       if (i != _nrofclauses) {
         Cv     [_nrofclauses] = Cv     [i];
         Clength[_nrofclauses] = Clength[i]; }
       _nrofclauses++; } }

  if (_nrofclauses > 0) {
    Cv      = (int**) realloc (Cv,      sizeof(int*) * _nrofclauses);
    Clength = (int* ) realloc (Clength, sizeof(int ) * _nrofclauses); }

  int count = nrofclauses - _nrofclauses;
  nrofclauses = _nrofclauses;

  return count; }

int clsCompare( const void *ptrA, const void *ptrB ) {
  int i;

  /***** Compare the first variable of both clauses *****/
  if (NR( *( *(int **) ( ptrA ) + 1 ) ) != NR( *( *(int **) ( ptrB ) + 1)))
    return (NR( *( *(int **) ( ptrA ) + 1 ) ) - NR( *( *(int **) ( ptrB ) + 1 ) ) > 0 ? -1 : 1);

  /***** Compare the second variable of both clauses *****/
  if (NR( *( *(int **) ( ptrA ) + 2 ) ) != NR( *( *(int **) ( ptrB ) + 2)))
    return (NR( *( *(int **) ( ptrA ) + 2 ) ) - NR( *( *(int **) ( ptrB ) + 2 ) ) > 0 ? -1 : 1 );

  /***** Now compare the lengths of the clauses *****/
  if (**(int **) ptrA != **(int **) ptrB)
    return (**(int **) ptrA - **(int **) ptrB > 0 ? -1 : 1);

  /***** The lengths of A and B are the same and the first 2 _variables_ are also *****
   ***** the same. So now we take a look at the other _variables_ in the clauses. *****/
  for (i = 3; i <= **(int **) ptrA; i++)
    if (NR( *( *(int **) ( ptrA ) + i ) ) != NR( *( *(int **) ( ptrB ) + i )))
      return ( NR( *( *(int **) ( ptrA ) + i ) ) - NR( *( *(int **) ( ptrB ) + i ) ) > 0 ? -1 : 1);

  /***** If the two clauses contain the same _variables_, we then consider them as *****
   ***** literals and compare again. ( So, no NR() is used here ). This is done to *****
   ***** make removal of duplets easy.                                             *****/
  for (i = 1; i <= **(int **) ptrA; i++)
    if (*( *(int **) ( ptrA ) + i ) != *( *(int **) ( ptrB ) + i))
      return ( *( *(int **) ( ptrA ) + i ) - *( *(int **) ( ptrB ) + i ) > 0 ? -1 : 1);

  /***** Default value if all is equal. ( Thus a duplet... ) *****/
  return 1; }

void printFormula (int** _Cv) {
  int i;
  for (i = 0; i < nrofclauses; i++) {
    printf ("clause %i ( %i ): ( ", i, Clength[i]);
    int j;
    for (j = 0; j < Clength[i]; j++)
      printf ("%i ", _Cv[i][j]);
    printf (")\n"); }
}
