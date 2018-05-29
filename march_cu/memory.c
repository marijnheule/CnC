/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "memory.h"
#include "common.h"

void allocate_big_clauses_datastructures()
{
	int i, j, nrofliterals = 0, lit, tmp;

        nrofbigclauses = 0;

        float* wlit = (float *) malloc (sizeof(float) * (2*nrofvars + 1));
        wlit += nrofvars;

        for( i = 1; i <= nrofvars; i++ )
        { wlit[  i ] = 0; wlit[ -i ] = 0; }

        for (i = 0; i < nrofclauses; i++) {
//          float w = pow (1000.0 * Clength[i], 0.5);
          float w = 1.0;
          for (j = 0; j < Clength[ i ]; j++)
            wlit [Cv[i][j]] += w; }

        clause_weight   = (float*) malloc( sizeof(float) * nrofclauses );

        for (i = 0; i < nrofclauses; i++) {
          float sum = 0.0;
          for (j = 0; j < Clength[ i ]; j++ )
            sum += wlit[ Cv[i][j] ];
          if (sum == 0) sum = 1;
          clause_weight[i] = Clength[i] / sum; }

        wlit -= nrofvars;
        free (wlit);

//        for (i = 0; i < nrofclauses; i++)
//          printf("%.5f ", clause_weight[i]);

        big_occ = (int*) malloc( sizeof(int) * (2*nrofvars + 1) );
        big_occ += nrofvars;
        for( i = 1; i <= nrofvars; i++ )
        {   big_occ[  i ] = 0; big_occ[ -i ] = 0; }


        for( i = 1; i <= nrofvars; i++ )
        {   big_occ[  i ] = 0; big_occ[ -i ] = 0; }

        for (i = 0; i < nrofclauses; i++)
            if( Clength[ i ] >= 3 ) {
                nrofliterals += Clength[ i ];
                nrofbigclauses++;
            }

        literal_list    = (int*  ) malloc( sizeof(int  ) * (nrofliterals + nrofbigclauses) );
        clause_list     = (int** ) malloc( sizeof(int* ) * nrofbigclauses );
        clause_length   = (int*  ) malloc( sizeof(int  ) * nrofbigclauses );
        clause_database = (int*  ) malloc( sizeof(int  ) * (nrofliterals + 2 * nrofvars) );

        for( i = 0; i < (nrofliterals + 2 * nrofvars); i++ )
            clause_database[ i ] = LAST_CLAUSE;

        nrofliterals   = 0;
        nrofbigclauses = 0;
        for( i = 0; i < nrofclauses; i++ )
            if( Clength[ i ] >= 3 )
            {
                clause_weight[ nrofbigclauses   ] = clause_weight[ i ];
                clause_length[ nrofbigclauses   ] = Clength[ i ];
                clause_list  [ nrofbigclauses++ ] = &literal_list[ nrofliterals ];

                for( j = 0; j < Clength[ i ]; j++ )
                {
                    literal_list[ nrofliterals++ ] = Cv[i][j];
                    big_occ[ Cv[i][j] ]++;
                }
                literal_list[ nrofliterals++ ] = LAST_LITERAL;
            }

        clause_set  = (int**) malloc( sizeof(int*) * (2*nrofvars + 1) );
        clause_set += nrofvars;

        tmp = 0;
        for( i = 1; i <= nrofvars; i++ )
        {
            clause_set[  i ] = &clause_database[ tmp ];
            tmp += big_occ[  i ] + 1;
            big_occ[  i ] = 0;

            clause_set[ -i ] = &clause_database[ tmp ];
            tmp += big_occ[ -i ] + 1;
            big_occ[ -i ] = 0;
        }

        nrofbigclauses = 0;
        for( i = 0; i < nrofliterals; i++ )
        {
            lit = literal_list[ i ];
            if( lit == 0 ) nrofbigclauses++;
            else clause_set[ lit ][ big_occ[ lit ]++ ] = nrofbigclauses;
        }
}

void free_big_clauses_datastructures () {
  FREE_OFFSET( big_occ    );
  FREE_OFFSET( clause_set );

  FREE( literal_list    );
  FREE( clause_list     );
  FREE( clause_length   );
  FREE( clause_database ); }

void allocateTernaryImp( int **_tImpTable, int ***_tImp, int **_tImpSize )
{
	int i, j, _nrofternaryclauses, varnr;
	int *_TernaryImpTable, **_TernaryImp, *_TernaryImpSize;

        _TernaryImpSize  = (int* ) malloc( sizeof(int ) * ( 2 * nrofvars + 1 ) );
	_TernaryImpSize += nrofvars;

        for( i = -nrofvars; i <= nrofvars; i++ )
                _TernaryImpSize[ i ] = 0;

	_nrofternaryclauses = 0;
        for( i = 0; i < nrofclauses; i++ )
            if( Clength[ i ] == 3 )
	    {
		_nrofternaryclauses++;
		for( j = 0; j < 3; j++ )
		    _TernaryImpSize[ Cv[ i ][ j ] ]++;
	    }

	_TernaryImpTable = (int* ) malloc( sizeof(int ) * ( 6 * _nrofternaryclauses ) );
        _TernaryImp      = (int**) malloc( sizeof(int*) * ( 2 * nrofvars + 1 ) );
        _TernaryImp     += nrofvars;

        _nrofternaryclauses = 0;
        for( i = -nrofvars; i <= nrofvars; i++ )
        {
            _TernaryImp    [ i ]    = _TernaryImpTable + 2 * _nrofternaryclauses;
            _nrofternaryclauses    += _TernaryImpSize[ i ];
            _TernaryImpSize[ i ]    = 0;
        }

        for( i = 0; i < nrofclauses; i++ )
        {
            if( Clength[ i ] != 3 ) continue;

            for( j = 0; j < 3; j++ )
            {
		varnr = Cv[ i ][ j ];
		_TernaryImp[ varnr ][ 2 * _TernaryImpSize[ varnr ]     ] = Cv[ i ][ (j + 1) % 3 ];
		_TernaryImp[ varnr ][ 2 * _TernaryImpSize[ varnr ] + 1 ] = Cv[ i ][ (j + 2) % 3 ];
	    }
            for( j = 0; j < 3; j++ )
		_TernaryImpSize[ Cv[i][j] ]++;
        }

	*_tImpTable = _TernaryImpTable;
	*_tImp	    = _TernaryImp;
	*_tImpSize  = _TernaryImpSize;
}

void freeTernaryImp (int *_tImpTable, int **_tImp, int *_tImpSize) {
  FREE_OFFSET( _tImp      );
  FREE_OFFSET( _tImpSize  );

  FREE( _tImpTable ); }

void allocateVc( int ***_Vc, int ***_VcLUT )
{
        int i, j, varnr, *__VcTemp;
        int **__Vc, **__VcLUT;

        /*
                Create temporary Vc and VcLUT.
        */
        __Vc     = (int**) malloc( sizeof( int*) * ( 2 * nrofvars + 1 ) );
        __VcLUT  = (int**) malloc( sizeof( int*) * ( 2 * nrofvars + 1 ) );
        __VcTemp = (int* ) malloc( sizeof( int ) * ( 2 * nrofvars + 1 ) );

        for( i = 0; i < ( 2 * nrofvars + 1 ); i++ )     __VcTemp[ i ] = 1;

        for( i = 0; i < nrofclauses; i++ )
                for( j = 0; j < Clength[ i ]; j++ )
                        __VcTemp[ Cv[ i ][ j ] + nrofvars ]++;

        /*
                Allocate space.
        */
        for( i = 0; i < 2 * nrofvars + 1; i++ )
        {
                __Vc   [ i ] = (int*) malloc( sizeof( int ) * __VcTemp[ i ]  );
                __VcLUT[ i ] = (int*) malloc( sizeof( int ) * __VcTemp[ i ] );

                __Vc   [ i ][ 0 ] = __VcTemp[ i ] - 1;
                __VcLUT[ i ][ 0 ] = __VcTemp[ i ] - 1;

                __VcTemp[ i ] = 1;
        }

        for( i = 0; i < nrofclauses; i++ )
                for( j = 0; j < Clength[ i ]; j++ )
                {
                        varnr = Cv[ i ][ j ] + nrofvars;
                        __Vc[ varnr ][ __VcTemp[ varnr ] ] = i;
                        __VcLUT[ varnr ][ __VcTemp[ varnr ] ] = j;
                        __VcTemp[ varnr ]++;
                }

        free( __VcTemp );

        *_Vc    = __Vc;
        *_VcLUT = __VcLUT;
}


void allocateSmallVc (int ***_Vc, int length)
{
        int i, j, varnr, *__VcTemp;
        int **__Vc;

        /*
                Create temporary Vc and VcLUT.
        */
        __Vc     = (int**) malloc (sizeof( int*) * (2 * nrofvars + 1) );
        __VcTemp = (int* ) malloc (sizeof( int ) * (2 * nrofvars + 1) );

        for (i = 0; i < (2 * nrofvars + 1); i++)     __VcTemp[ i ] = 1;

 for (i = 0; i < nrofclauses; i++)
   if (Clength[ i ] >=  length)
     for (j = 0; j < Clength[ i ]; j++)
       __VcTemp[ Cv[ i ][ j ] + nrofvars ]++;

        /*
                Allocate space.
        */
  for( i = 0; i < 2 * nrofvars + 1; i++ ) {
    __Vc    [ i ]      = (int*) malloc( sizeof( int ) * __VcTemp[ i ]  );
    __Vc    [ i ][ 0 ] = __VcTemp[ i ] - 1;
    __VcTemp[ i ]      = 1; }

  for (i = 0; i < nrofclauses; i++)
    if (Clength[ i ] >= length)
      for (j = 0; j < Clength[ i ]; j++) {
        varnr = Cv[ i ][ j ] + nrofvars;
        __Vc[ varnr ][ __VcTemp[ varnr ] ] = i;
        __VcTemp[ varnr ]++; }

  free( __VcTemp );
  *_Vc = __Vc; }

void freeVc( int **_Vc, int **_VcLUT )
{
        int i;

        for( i = 0; i < ( 2 * nrofvars + 1 ); i++ )
	{
	    free( _Vc   [ i ] );
	    free( _VcLUT[ i ] );
	}

	free( _Vc    );
	free( _VcLUT );
}

void freeSmallVc (int **_Vc) {
  int i; for (i = 0; i < ( 2 * nrofvars + 1 ); i++) free (_Vc[ i ]);
  free (_Vc); }

void rebuild_BinaryImp () {
  int i; for( i = 1; i <= nrofvars; i++ ) {
    BinaryImp[  i ][  0 ] = 2;
    BinaryImp[ -i ][  0 ] = 2; }

  for (i = 0; i < nrofclauses; i++)
    if (Clength[ i ] == 2 ) {
      CHECK_AND_ADD_BINARY_IMPLICATIONS(Cv[ i ][ 0 ], Cv[ i ][ 1 ]); } }

void resize_BinaryImp()
{
        int i;

        BinaryImp       -= original_nrofvars;
        BinaryImpLength -= original_nrofvars;

        /* BinaryImp: implication clause table */
        BinaryImp       = (int**) realloc( BinaryImp,       sizeof(int*) * ( 2 * nrofvars + 1) );
        BinaryImpLength = (int* ) realloc( BinaryImpLength, sizeof(int ) * ( 2 * nrofvars + 1) );

        for( i = 0; i < (2 * nrofvars + 1); i++ )
        {
                BinaryImp      [ i ] = (int*) malloc( sizeof( int ) * INITIAL_ARRAY_SIZE );
                BinaryImpLength[ i ] = INITIAL_ARRAY_SIZE - 1;
                BinaryImp [ i ][ 0 ] = 2;
                BinaryImp [ i ][ 1 ] = 0;		//Moet nog weggewerkt worden...
        }

	BinaryImp       += nrofvars;
	BinaryImpLength += nrofvars;

	rebuild_BinaryImp( );
}

void free_BinaryImp()
{
	int i;

	if( BinaryImp == NULL ) return;

	BinaryImp       -= nrofvars;
	BinaryImpLength -= nrofvars;

	for( i = 0; i < (2 * nrofvars + 1); i++ )
	    free( BinaryImp[ i ] );

	free( BinaryImp       );
	free( BinaryImpLength );
}
