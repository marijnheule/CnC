/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

#include "equivalence.h"
#include "memory.h"
#include "solver.h"
#include "common.h"

int equivalence_reasoning () {
#ifdef FIND_EQ
  int i;
  for (i = 0; i < nrofclauses; i++)
    if (Clength[i] > 2)
      i += find_equivalence (i);

  printNrofEq();
#endif

  find_and_remove_tautologies();
  while (find_and_propagate_bieq ()) { };

  if (substitude_equivalences() == UNSAT)
    return UNSAT;

  find_and_remove_tautologies();
  shorten_equivalence();
  while (find_and_propagate_bieq ()) { };

#ifndef EQ
  if (quiet_mode == 0)
    printf("c equivalence reasoning is turned off.\n");
#endif
  return 1; }

void init_equivalence () {
  int i;

        Ceq        = (int**) malloc( sizeof( int* ) * 2 * nrofclauses );
        CeqSizes   = (int*)  malloc( sizeof( int  ) * 2 * nrofclauses );
        CeqStamps  = (int*)  malloc( sizeof( int  ) * 2 * nrofclauses );
        CeqValues  = (int*)  malloc( sizeof( int  ) * 2 * nrofclauses );
        CeqDepends = (int*)  malloc( sizeof( int  ) * 2 * nrofclauses );
	Veq        = (int**) malloc( sizeof( int* ) * ( nrofvars + 1 ) );
        VeqLUT     = (int**) malloc( sizeof( int* ) * ( nrofvars + 1 ) );
        VeqLength  = (int*)  malloc( sizeof( int  ) * ( nrofvars + 1 ) );

        for( i = 0; i <= nrofvars; i++ )
        {
            Veq        [ i ] = (int*) malloc( sizeof( int ) * 3 );
            VeqLUT     [ i ] = (int*) malloc( sizeof( int ) * 3 );
            VeqLength  [ i ] = 2;
            Veq   [ i ][ 0 ] = 1;
            VeqLUT[ i ][ 0 ] = 1;
        }

        for( i = 0; i < 2 * nrofclauses; i++ ) CeqDepends[ i ] = 0;

	eq_found = (int*) malloc( sizeof(int) * original_nrofvars );

	for( i = 0; i < original_nrofvars; i++ )
		eq_found[ i ] = 0;
}

void dispose_equivalence()
{
	int i;

	if( Ceq != NULL )
	{
	    for( i = 0; i < nrofceq; i++ ) free( Ceq[ i ] );
	    free( Ceq );
	}

        FREE( CeqSizes   );
        FREE( CeqStamps  );
        FREE( CeqValues  );
        FREE( CeqDepends );
        FREE( VeqLength  );
}

void dispose_preprocessor_eq()
{
	free( VeqLength );

	Ceq        = (int**) realloc( Ceq       , sizeof( int* ) * (nrofceq+1) );
	CeqSizes   = (int* ) realloc( CeqSizes  , sizeof( int  ) * (nrofceq+1) );
	CeqStamps  = (int* ) realloc( CeqStamps , sizeof( int  ) * (nrofceq+1) );
	CeqValues  = (int* ) realloc( CeqValues , sizeof( int  ) * (nrofceq+1) );
	CeqDepends = (int* ) realloc( CeqDepends, sizeof( int  ) * (nrofceq+1) );
}

/*****************************************************************************

	The procedure find_and_remove_tautologies finds and removes all
	tautological equivalences from the active datastructure CoE.
	Tautological equivalences are equivalence clauses that contain
	a least one variable that occurs only once in the CoE and does
	not appear in the CNF.

******************************************************************************/

int find_and_remove_tautologies()
{
	int i, j, _tautologies, tautologies;
	int **_Vc, **_VcLUT;

	allocateVc( &_Vc, &_VcLUT );
	_Vc += nrofvars;

	_tautologies = 0;

	do
	{
	    tautologies = _tautologies;

	    for( i = 1; i <= nrofvars; i++ )
		if(  ((_Vc[ i ][ 0 ] + _Vc[ -i ][ 0 ]) == 0) &&
		      (Veq[ i ][ 0 ] == 2) && (CeqSizes[ Veq[ i ][ 1 ] ] != 1) )
		{
		    CeqStamps[ Veq[ i ][ 1 ] ] = TAUTOLOGY;
		    VeqDepends[ i ] = INDEPENDENT;	// why?
		    VeqDepends[ CeqDepends[ Veq[ i ][ 1 ] ] ] = INDEPENDENT;
		    CeqDepends[ Veq[ i ][ 1 ] ] = i;
		    _tautologies++;
		}

	    for( i = 1; i <= nrofvars; i++ )
		for( j = 1; j < Veq[ i ][ 0 ]; j++ )
	 	    if( CeqStamps[ Veq[ i ][ j ] ] == TAUTOLOGY )
		    {
			if( CeqSizes[ Veq[ i ][ j ] ] == 1 )
			    continue;

			Veq   [ i ][ j ] = Veq   [ i ][ --Veq   [ i ][ 0 ] ];
			VeqLUT[ i ][ j ] = VeqLUT[ i ][ --VeqLUT[ i ][ 0 ] ];
			j--;
		    }
	}
	while( tautologies < _tautologies );

//	if( tautologies > 0 )
//	    printf("c find_and_remove_tautogolies():: found and removed %i tautologies\n", tautologies );

	_Vc -= nrofvars;
	freeVc( _Vc, _VcLUT );

	return tautologies;
}

int check_vadility_equivalences()
{
	int i;

        for( i = 0; i < nrofceq; i++ )
            if( CeqSizes[ i ] == 0 )
                if( CeqValues[ i ] == -1 )
		    return UNSAT;

	return SAT;
}

/****************************************************************************

	substitude_equivalences selects in all equivalence clauses one
	variable to eliminate from all other equivalence clauses. The
	selection is based on the occurences of variables in the CNF.

*****************************************************************************/

int substitude_equivalences( )
{
        int i, j, index, *VeqValues, maximum, minimum;

        VeqValues = (int*) malloc( sizeof( int ) * ( nrofvars + 1 ) );

        for( i = 0; i <= nrofvars; i++ )
                VeqValues[ i ] = 0;

        for( i = 0; i < nrofclauses; i++ )
        {
            if( (Clength[ i ] == 2) && !VeqDepends[ NR(Cv[ i ][ 0 ]) ] )
                for( j = 0; j < Clength[ i ]; j++ )
                   VeqValues[ NR( Cv[ i ][ j ] ) ] += 11;
            else if(  Clength[ i ] > 2 )
                for( j = 0; j < Clength[ i ]; j++ )
                   VeqValues[ NR( Cv[ i ][ j ] ) ] += 1;
        }

	maximum = 0;
	for( i = 1; i <= nrofvars; i++ )
		if( VeqValues[ i ] > maximum )
			maximum = VeqValues[ i ];


        for( i = 0; i < nrofceq; i++ )
        {
            if( CeqStamps[ i ] == TAUTOLOGY ) continue;
            //if( CeqDepends[ i ] != 0 ) continue;

            VeqDepends[ CeqDepends[ i ] ] = INDEPENDENT;

            if( CeqSizes[ i ] == 0 )
            {
               if( CeqValues[ i ] == -1 )
               {
                  printf("c eqProduct():: invalid equivalence found!\n");
		  return UNSAT;
               }
            }
            else if( CeqSizes[ i ] >= 1 )
            {
                for( j = 0; j < CeqSizes[ i ]; j++ )
                {
		    if( VeqValues[ Ceq[ i ][ j ] ] == 0 )
                    {
			substitude_equivalence( i, j );
			break;
		    }
		}
            }
        }

#ifndef MODEL_FILTER
        for( i = 0; i < nrofceq; i++ )
        {
            if( CeqStamps[ i ] == TAUTOLOGY ) continue;
            //if( CeqDepends[ i ] != 0 ) continue;

            VeqDepends[ CeqDepends[ i ] ] = INDEPENDENT;

            if( CeqSizes[ i ] == 0 )
            {
               if( CeqValues[ i ] == -1 )
               {
                  printf("c eqProduct():: invalid equivalence found!\n");
		  return UNSAT;
               }
            }
            else if( CeqSizes[ i ] >= 1 )
            {
                minimum = maximum + 1;
                index = CeqSizes[ i ];

                for( j = 0; j < CeqSizes[ i ]; j++ )
                {
		    if( VeqValues[ Ceq[ i ][ j ] ] < minimum )
                    {
                      	index = j;
                        minimum = VeqValues[ Ceq[ i ][ j ] ];
       	            }
                }

		substitude_equivalence( i, index );
		if( minimum == 0 )			// if variable does not occur in CNF
			CeqStamps[ i ] = TAUTOLOGY;	// Ceq[ i ] is tautological.
            }
        }
#endif
	free( VeqValues );

	return 1;
}

/*******************************************************

	sustitude a literal form a equivalence-clause
	in all other equivalence clauses where it occurs.

*******************************************************/

void substitude_equivalence( int clause, int index )
{
        int i, var;

        var = Ceq[ clause ][ index ];

#ifdef EQ
        VeqDepends[ var ] = EQUIVALENT;
#endif
        CeqDepends[ clause ] = var;

        for( i = Veq[ var ][ 0 ] - 1; i > 0; i-- )
	    if( Veq[ var ][ i ] != clause )
            {
                int ceqidx = Veq[ var ][ i ];

		if( CeqStamps[ ceqidx ] != TAUTOLOGY )
		    substitude_ceq( ceqidx, clause );
            }
}

void substitude_ceq( int ceqsource, int ceqtarget )
{
	int k, l, m;

        Ceq[ ceqsource ] = (int*) realloc( Ceq[ ceqsource ], sizeof( int ) *
				         ( CeqSizes[ ceqsource ] + CeqSizes[ ceqtarget ] ) );

        CeqValues[ ceqsource ] *= CeqValues[ ceqtarget ];

        for( k = CeqSizes[ ceqtarget ] - 1; k >= 0; k-- )
        {
        	int current = Ceq[ ceqtarget ][ k ];

                for( l = CeqSizes[ ceqsource ] - 1; l >= 0; l-- )
		   if( Ceq[ ceqsource ][ l ] == current)
                   {    // place the last element on the place of the current
                        int last = Ceq[ ceqsource ][ --CeqSizes[ ceqsource ] ];
                        Ceq[ ceqsource ][ l ] = last;

                        for( m = 1; Veq[ last ][ m ] != ceqsource; m++ ) {}
                           VeqLUT[ last ][ m ] = l;

                        for( m = 1; Veq[ current ][ m ] != ceqsource; m++ ) {}
                           Veq   [ current ][ m ] = Veq   [ current ][ --Veq   [ current ][ 0 ] ];
                           VeqLUT[ current ][ m ] = VeqLUT[ current ][ --VeqLUT[ current ][ 0 ] ];

			goto varsubst;
		    }

	        CHECK_VEQ_BOUND( current );

        	Ceq[ ceqsource ][ CeqSizes[ ceqsource ] ] = current;
	        Veq   [ current ][ Veq   [ current ][ 0 ]++ ] = ceqsource;
		VeqLUT[ current ][ VeqLUT[ current ][ 0 ]++ ] = CeqSizes[ ceqsource ]++;

		varsubst:;
       	}
}


/**********************************************************************

	find_equivalence returns 0 if no equivalence clause
	is found, otherwise it will return the domain

***********************************************************************/

int find_equivalence( int clause )
{
	int i, j;

	int size = Clength[ clause ];
	int domain = pow( 2, size - 1);
	int *lit;
        lit = (int*) malloc (sizeof(int) * size);

	int sign, tmp;

	if( domain < 0 ) return 0;
	if( (clause + domain) > nrofclauses ) return 0;

	for( i = 1; i < domain; i++ )	if( Clength[ clause + i ] != size ) return 0;
	for( i = 0; i < size;   i++ )	if( NR(Cv[ clause ][ i ]) != NR(Cv[ clause + domain - 1 ][ i ]) ) return 0;

	sign = 1;
	for( i = 0; i < size; i++ )	sign *= SGN( Cv[ clause ][ i ] );

	for( i = 1; i < domain; i++ )
	{
	    tmp = 1;
	    for( j = 0; j < size; j++ )	tmp *= SGN( Cv[ clause + i ][ j ]);
	    if( tmp != sign )	return 0;
	}

        Ceq      [ nrofceq ] = (int*) malloc( sizeof( int ) * size );
        CeqSizes [ nrofceq ] = size;
        CeqValues[ nrofceq ] = pow( -1, size + 1 );

        for( i = 0; i < size; i++ )
        {
            lit[ i ] = abs( Cv[ clause ][ i ] );
            Ceq[ nrofceq ][ i ] = lit[ i ];
            CeqValues[ nrofceq ] *= SGN( Cv[ clause ][ i ] );

            CHECK_VEQ_BOUND( lit[ i ] );
            Veq[ lit[ i ] ][ Veq[ lit[ i ] ][ 0 ]++ ] = nrofceq;
            VeqLUT[ lit[ i ] ][ VeqLUT[ lit[ i ] ][ 0 ]++ ] = i;
        }

#ifdef EQ
	for( i = 0; i < domain; i ++ )	Clength[ clause + i ] = 0;
#endif

	eq_found[ size ]++;
	nrofceq++;

	return domain - 1;
}

void shorten_equivalence( )
{
	int i, j, k, l,  nf1, nf2, doublenf, iterCounter;
	int current, cmp1, cmp2, dep, ceqidx, counter;

#ifdef LOCALSUBST
	int var;
	int _ceq_stamp[ nrofceq ];
#endif

	int sum, members;

	sum = 0; members = 0;

        for( i = 0; i < nrofceq; i++ )
	    if( (CeqStamps[ i ] != TAUTOLOGY) && (CeqSizes[i] > 2) )
	    {
		sum += CeqSizes[ i ];
		members++;
	    }

	if( members > 0 )
	    printf("c shorten_equivalence(): average equivalence length reduced from %f ", sum / (double) members);

    	do
	{
	   iterCounter = 0;

           for( i = 0; i < nrofceq; i++ )
	   //for( i = nrofceq - 1; i >= 0; i-- )
           {
              if( (CeqStamps[ i ] == TAUTOLOGY ) ||
                    (CeqDepends[ i ] == 0) )
		 	continue;
              if( CeqSizes[ i ] == 3 )
	      {

                for( j = 0; j < 3; j++ )
                    if( VeqDepends[ Ceq[ i ][ j ] ] == EQUIVALENT )
                        break;

		if( j == 3 ) continue;

                nf1 = Ceq[ i ][ (j + 1) %3 ];
                nf2 = Ceq[ i ][ (j + 2) %3 ];

                doublenf = 0;

                for( k = 1; k < Veq[ nf1 ][ 0 ]; k++ )
                    for( l = 1; l < Veq[ nf2 ][ 0 ]; l++ )
                    	if( Veq[ nf1 ][ k ] == Veq[ nf2 ][ l ] )
                            doublenf++;

                if( Veq[ nf1 ][ 0 ] <= Veq[ nf2 ][ 0 ] )
                {
                    if( Veq[ nf1 ][ 0 ] < (2*doublenf) )
                    {
                    	VeqDepends[ Ceq[ i ][ j ] ] = INDEPENDENT;
                        VeqDepends[ nf1           ] = EQUIVALENT;
			CeqDepends[ i 		  ] = nf1;
                        substitude_equivalence( i, (j + 1) %3 );
			iterCounter++;
                    }
                }
                else if( Veq[ nf2 ][ 0 ] < (2*doublenf) )
		{
                    VeqDepends[ Ceq[ i ][ j ] ] = INDEPENDENT;
                    VeqDepends[ nf2           ] = EQUIVALENT;
		    CeqDepends[ i 	      ] = nf2;
                    substitude_equivalence( i, (j + 2) %3 );
		    iterCounter++;
                }
	     }
	     else if(CeqSizes[ i ] == 4)
	     {
	  	for( dep = 0; Ceq[ i ][ dep ] != CeqDepends[ i ]; dep++ ) {}

	     	for( j = 0; j < 4; j++ )
	     	{
			if( j == dep )	continue;

			cmp1 = (j+1) % 4;	if(cmp1 == dep)	cmp1 = (j+3) % 4;
			cmp2 = (j+2) % 4;	if(cmp2 == dep) cmp2 = (j+3) % 4;

			current = Ceq[ i ][ j ];
			cmp1    = Ceq[ i ][ cmp1 ];
			cmp2    = Ceq[ i ][ cmp2 ];
			counter = 2 - Veq[ current ][ 0 ];

			for( k = 1; k < Veq[ current ][ 0 ]; k++ )
			{
				ceqidx = Veq[ current ][ k ];
				if( ceqidx == i ) continue;
				for( l = 0; l < CeqSizes[ ceqidx ]; l++ )
					if( (Ceq[ ceqidx ][ l ] == cmp1) || (Ceq[ ceqidx ][ l ] == cmp2) )
						counter++;
			}

			if( counter > 0 )
			{
				VeqDepends[ CeqDepends[ i ] ] = INDEPENDENT;
	                        VeqDepends[ current         ] = EQUIVALENT;
	                        CeqDepends[ i               ] = current;

	                        substitude_equivalence( i, j );
				iterCounter++;
				//printf("variable %i must substitude clause %i\n", current, i);
				break;
			}
		     }
 	    	}
           }
	}
	while( iterCounter );

#ifdef LOCALSUBST
	for( i = 0; i < nrofceq; i++ )
		_ceq_stamp[ i ] = 0;
do
{
	iterCounter = 0;

	for( i = 0; i < nrofceq; i++ )
        {
              	if( (CeqStamps[ i ] == TAUTOLOGY ) || (CeqSizes[ i ] == 2 ) )
		 	continue;

		for( k = 0; k < CeqSizes[ i ]; k++ )
		{
			var = Ceq[ i ][ k ];
			for( l = 1; l < Veq[ var ][ 0 ]; l++ )
				_ceq_stamp[ Veq[ var ][ l ] ]++;
		}

		//counter = CeqSizes[ i ] - 1;
		counter = CeqSizes[ i ] / 2 + 1;

		for( j = 0; j < nrofceq; j++ )
		{
			if( (_ceq_stamp[ j ] >= counter) &&  (j != i) )
			{
				substitude_ceq( j, i);
				if( CeqDepends[ i ] > 0 )
				{
					VeqDepends[ CeqDepends[ i ] ] = INDEPENDENT;
					CeqDepends[ i ] = 0;
				}
				iterCounter++;
			}
			_ceq_stamp[ j ] = 0;
		}
	}
}
while( iterCounter > 0 );
#endif
	sum = 0; members = 0;

        for( i = 0; i < nrofceq; i++ )
		if( (CeqStamps[ i ] != TAUTOLOGY) && (CeqSizes[i] > 2) )
		{
			sum += CeqSizes[ i ];
			members++;
		}

	if( members > 0 )
	    printf("to %f\n", sum / (double) members);

}

int propagate_bieq()
{
	int i;
	int **_Vc, **_VcLUT;

	allocateVc( &_Vc, &_VcLUT );

	for( i = 0; i < nrofceq; i++ )
	    if( (CeqSizes[ i ] == 2) && (CeqStamps[ i ] != TAUTOLOGY) )
	    {
		if( CeqDepends[ i ] == Ceq[ i ][ 0 ] )
		{
		    //printf("c replacing %i by %i\n", Ceq[ i ][ 0 ], Ceq[ i ][ 1 ] * CeqValues[ i ] );
		    substitude_equivalence(i, 0);
		    replace_bieq( Ceq[ i ][ 0 ], -Ceq[ i ][ 1 ] * CeqValues[ i ], &_Vc, &_VcLUT );
		}
		else
		{
		    //printf("c replacing %i by %i\n", Ceq[ i ][ 1 ], Ceq[ i ][ 0 ] * CeqValues[ i ] );
		    substitude_equivalence(i, 1);
		    replace_bieq( Ceq[ i ][ 1 ], -Ceq[ i ][ 0 ] * CeqValues[ i ], &_Vc, &_VcLUT );
		}

		freevars--;

	 	CeqStamps[ i ] = TAUTOLOGY;
	    }

	freeVc( _Vc, _VcLUT );

	return find_and_remove_tautologies();
}


//replace lit1 by lit2

void replace_bieq( int lit1, int lit2, int ***__Vc, int ***__VcLUT )
{
	int i, j, sign, VARfrom, VARto, clsidx;
	int **_Vc, **_VcLUT;

	_Vc    = *__Vc    + nrofvars;
	_VcLUT = *__VcLUT + nrofvars;

	//printf("found bieq %i %i\n", lit1, lit2);

	VeqDepends[ NR(lit1) ] = INDEPENDENT;

        sign = SGN( lit1 ) * SGN( lit2 );

	for( i = -1; i <= 1; i +=2 )
	{
        	VARfrom = i * NR( lit1 );
	        VARto = -i * sign * NR( lit2 );

  	      	_Vc[ VARto ] = (int*) realloc( _Vc[ VARto ],
        		( _Vc[ VARfrom ][ 0 ] + _Vc[ VARto ][ 0 ] + 2 ) * sizeof( int ) );

	        _VcLUT[ VARto ] = (int*) realloc( _VcLUT[ VARto ],
        		( _VcLUT[ VARfrom ][ 0 ] + _VcLUT[ VARto ][ 0 ] + 2 ) * sizeof( int ) );

	        /* alle literals veranderen */
	        for( j = 1; j <= _Vc[ VARfrom ][ 0 ]; j++ )
	        {
        		clsidx = _Vc[ VARfrom ][ j ];
	                if ( Clength[ clsidx ] != 0 )
	                {
        	        	Cv[ clsidx ][ _VcLUT[ VARfrom ][ j ] ] = VARto;
               	        	_Vc[ VARto ][ ++_Vc[ VARto ][ 0 ] ] = clsidx;
	                        _VcLUT[ VARto ][ ++_VcLUT[ VARto ][ 0 ] ] = _VcLUT[ VARfrom ][ j ];
        	                _Vc[ VARfrom ][ j ] = _Vc[ VARfrom ][ _Vc[ VARfrom ][ 0 ]-- ];
                	        _VcLUT[ VARfrom ][ j ] = _VcLUT[ VARfrom ][ _VcLUT[ VARfrom ][ 0 ]-- ];
                        	j--;
                	}
   		}
	}
}

int find_and_propagate_bieq()
{
	int i, var, var1, var2, ceqidx, posidx;
	int *bi_stamp, *bi_target;

	/*
		Voor de snelheid een Veq aanmaken met alle 3 equivalenties erin?
	*/

	bi_stamp  = (int*) malloc( sizeof(int) * (nrofvars + 1) );
	bi_target = (int*) malloc( sizeof(int) * (nrofvars + 1) );

	for( i = 1; i <= nrofvars; i++ )
		bi_stamp[ i ] = 0;

	for( var = 1; var <= nrofvars; var++ )
	{
	   for( i = 1; i < Veq[ var ][ 0 ]; i++ )		//omdraaien??
	   {
		ceqidx = Veq[ var ][ i ];

		if( CeqStamps[ ceqidx ] == TAUTOLOGY ) continue;
		if( CeqSizes [ ceqidx ] != 3         ) continue;

		posidx = VeqLUT[ var ][ i ];
		var1 = Ceq[ ceqidx ][ (posidx + 1) % 3 ];
		var2 = Ceq[ ceqidx ][ (posidx + 2) % 3 ];

		if( bi_stamp[ var1 ] != var )
		{
			bi_stamp [ var1 ] = var;
			bi_target[ var1 ] = ceqidx;
		}
		else
		{
			substitude_ceq( ceqidx, bi_target[ var1 ] );
			continue;
		}
		if( bi_stamp[ var2 ] != var )
		{
			bi_stamp [ var2 ] = var;
			bi_target[ var2 ] = ceqidx;
		}
		else
		{
			substitude_ceq( ceqidx, bi_target[ var2 ] );
			continue;
		}
	   }
	}

	free( bi_stamp  );
	free( bi_target );

	return propagate_bieq();

}

/******************************************************************

	March found a satisfying assignment.
	Fix all variables that haven's been set yet.

*******************************************************************/

void fixDependedEquivalences()
{
	int i, j, varnr, sign, iterCounter;

	do
	{
	   iterCounter = 0;
	   for( i = 0; i < nrofceq; i++ )
	   {
		varnr = 0;
		for( j = 0; j < CeqSizes[ i ]; j++ )
		{
			if( timeAssignments[ Ceq[ i ][ j ] ] < VARMAX )
			{
				if( varnr == 0 )
					varnr =  Ceq[ i ][ j ]; 
				else
					goto fixend;
			}
		}

		if( varnr == 0 ) continue;

//		printf("c FixD: fixing %i in ceq %i\n", varnr, i);

		iterCounter++;

		sign = CeqValues[ i ];
		for( j = 0; j < CeqSizes[ i ]; j++ )
			if( Ceq[ i ][ j ] != varnr )
				sign *= EQSGN( Ceq[ i ][ j ] );

		if( sign == 1 ) timeAssignments[ varnr ] = VARMAX;
		else            timeAssignments[ varnr ] = VARMAX + 1;

//		IFIUP( varnr * sign, FIX_BRANCH_VARIABLE );

		fixend:;
	   }
	}
	while( iterCounter );
}


void restoreVeq()
{
	int i, j;

        for( i = 1; i <= nrofvars; i++ )
        {
                Veq   [ i ][ 0 ] = 1;
                VeqLUT[ i ][ 0 ] = 1;
        }

        for( i = 0; i < nrofceq; i++ )
                if( CeqStamps[ i ] != TAUTOLOGY )
                        for( j = 0; j < CeqSizes[ i ]; j++ )
                        {
                                Veq   [ Ceq[ i ][ j ] ][ Veq   [ Ceq[ i ][ j ] ][ 0 ]++ ] = i;
                                VeqLUT[ Ceq[ i ][ j ] ][ VeqLUT[ Ceq[ i ][ j ] ][ 0 ]++ ] = j;
                        }
}


int dependantsExists() {
	int i, j, k, varnr;

//	printCeq ();

//	for( i = nrofceq - 1; i >=0 ; i-- )
	for( i = 0; i < nrofceq; i++ )
      	   for( j = 0; j < CeqSizes[ i ]; j++ )
           	if( timeAssignments[ Ceq[i][j] ] < VARMAX )
                {
			varnr = Ceq[ i ][ j ];

//			printf("c Ceq[%i][%i] = %i (%i)\n", i, j, varnr, VeqDepends[ varnr ] );

			for( k = 0; k < nrofceq; k++ )
			   if( varnr == CeqDepends[ k ] )
				goto next_exit;

//			if( VeqDepends[ varnr ] == EQUIVALENT ) continue;
			//if( VeqDepends[ varnr ] == CeqDepends[i] ) continue;

			printf("c dep exists!!! fixing %i in ceq %i\n", varnr, i);

			timeAssignments[ varnr ] = VARMAX;

//			IFIUP( varnr, FIX_BRANCH_VARIABLE );

			return 1;

			next_exit:;
                }
	return 0;
}

void fixEq( int varnr, int pos, int value )
{
	int i, last = --Veq[ varnr ][ 0 ];
	int ceqidx = Veq   [ varnr ][ pos ];
        int ceqloc = VeqLUT[ varnr ][ pos ];
        int lit = Ceq[ ceqidx ][ --CeqSizes[ ceqidx ] ];

	assert( lit <= nrofvars );
	assert( lit > 0 );

        for( i = 1; Veq[ lit ][ i ] != ceqidx; i++ );
        VeqLUT[ lit ][ i ] = ceqloc;

        Ceq[ ceqidx ][ ceqloc ] = lit;
        Ceq[ ceqidx ][ CeqSizes[ ceqidx ] ] = varnr;

        CeqValues[ ceqidx ] *= value;

	Veq[ varnr ][ pos  ] = Veq[ varnr ][ last ];
	Veq[ varnr ][ last ] = ceqidx;

	VeqLUT[ varnr ][ pos  ] = VeqLUT[ varnr ][ last ];
	VeqLUT[ varnr ][ last ] = CeqSizes[ ceqidx ];
}

int check_non_tautological_equivalences( )
{
	int i;
#ifndef MODEL_FILTER
	for( i= 0; i < nrofceq; i++ )
	    if( (CeqStamps[ i ] != TAUTOLOGY) && (CeqSizes[ i ] > 0) )
		return 1;
#endif
	return 0;
}

void add_binary_equivalence( int lit1, int lit2 )
{
	int i, ceqidx;

	for( i = 1; i < Veq[ NR(lit1) ][ 0 ]; i++ )
	{
	    ceqidx = Veq[ NR(lit1) ][ i ];
	    if( (CeqSizes[ ceqidx ] == 2) &&
	        (Ceq[ ceqidx ][ VeqLUT[ NR(lit1) ][ i ] ^ 1 ] == NR(lit2)) &&
		(CeqValues[ ceqidx ] == -1 * SGN(lit1) * SGN(lit2) ) )
	    {
		printf("c skipping %i %i\n", lit1, lit2 );
		return;	//wellicht nog op sign checken...
	    }
	}

	Ceq      [ nrofceq ]      = (int*) malloc( sizeof(int) * 2 );
        Ceq      [ nrofceq ][ 0 ] = NR(lit1);
        Ceq      [ nrofceq ][ 1 ] = NR(lit2);
        CeqSizes [ nrofceq ]      = 2;
        CeqValues[ nrofceq ]      = -1 * SGN(lit1) * SGN(lit2);

        CHECK_VEQ_BOUND( NR(lit1) );
        Veq[ NR(lit1) ][ Veq[ NR(lit1) ][ 0 ]++ ] = nrofceq;
        VeqLUT[ NR(lit1) ][ VeqLUT[ NR(lit1) ][ 0 ]++ ] = 0;

        CHECK_VEQ_BOUND( NR(lit2) );
        Veq[ NR(lit2) ][ Veq[ NR(lit2) ][ 0 ]++ ] = nrofceq;
        VeqLUT[ NR(lit2) ][ VeqLUT[ NR(lit2) ][ 0 ]++ ] = 1;

	nrofceq++;
}

void printCeq()
{
	int i, j;

        printf("CEQ\n---\n\n");
        for( i = 0; i < nrofceq; i++ )
        {
	    //if( CeqStamps[ i ] == TAUTOLOGY ) continue;
	    if( CeqStamps[ i ] == TAUTOLOGY ) printf("SAT ");

	    if( CeqSizes[ i ] != 0 )
	    	printf("%i ( %i ): %i [%i]", i, CeqDepends[ i ], Ceq[ i ][ 0 ], timeAssignments[ Ceq[i][0] ] );
	    else
		printf("%i (%i ): TRUE ", i, CeqDepends[ i ] );

            for( j = 1; j < CeqSizes[ i ]; j++ )
            	printf("* %i [%i]", Ceq[ i ][ j ], timeAssignments[ Ceq[i][j] ] );
            printf("= %i\n", CeqValues[ i ] );
        }
}

void printNrofEq()
{
	int i;

	for( i = 0; i < original_nrofvars; i++ )
	    if( eq_found[ i ] > 0 )
		printf("c find_equivalence():: found %i %i-equivalences\n", eq_found[ i ], i );

	//printCeq();

	free( eq_found );
}

void check_integrety()
{
	int i;

	for( i =0; i< nrofceq; i++ )
	   printf("Veq[ %i ][ 0 ] = %i\n",  CeqDepends[i] , Veq[ CeqDepends[i] ][ 0 ]);
}
