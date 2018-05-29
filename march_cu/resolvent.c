#include <stdio.h>
#include <stdlib.h>

#include "common.h"
#include "lookahead.h"
#include "memory.h"
#include "resolvent.h"
#include "parser.h"

int *new_resolvent_begin, *new_resolvent_end;
int **resolvent_list, *resolvent_size, resolvent_list_size;
int nrofresolvents;

int propagate_big_clauses( const int nrval )
{
        int lit, *literals;
        int clause_index;

        int *clauseSet = clause_set[ -nrval ];
        while( *clauseSet != LAST_CLAUSE )
        {
            clause_index = *(clauseSet++);
            clause_length[ clause_index ]--;

            if( clause_length[ clause_index ] <= 1 )
            {
                literals = clause_list[ clause_index ];
                while( *literals != LAST_LITERAL )
                {
                    lit = *(literals)++;
                    if( IS_NOT_FIXED( lit ) )
                    {
			FIX( lit, currentTimeStamp );
			*(end_fixstackp++) = lit;
                        goto BL_next_clause;
                    }
                    else if( !FIXED_ON_COMPLEMENT(lit) ) goto BL_next_clause;

                }
                while( *clauseSet != LAST_CLAUSE )
                    clause_length[ *(clauseSet++) ]--;

                return UNSAT;
            }
            BL_next_clause:;
        }
        return SAT;
}

void add_resolvent () {
  if (nrofresolvents == resolvent_list_size) {
    resolvent_list_size *= 2;
    resolvent_list = (int**) realloc (resolvent_list, sizeof(int*) * resolvent_list_size);
    resolvent_size = (int* ) realloc (resolvent_size, sizeof(int ) * resolvent_list_size); }

  int size = new_resolvent_end - new_resolvent_begin;
  resolvent_size[ nrofresolvents ] = size;
  resolvent_list[ nrofresolvents ] = (int*) malloc (sizeof(int) * size);

  int i; for (i = 0; i < size; i++)
    resolvent_list[ nrofresolvents ][ i ] = new_resolvent_begin[ i ];

  nrofresolvents++; }

int strengthen_big_clause( int *_literals, const int nrval )
{
	int *big_resolventp, *literals;
	int *local_fixstackp = rstackp;
	end_fixstackp = local_fixstackp;

	currentTimeStamp += 2;

	literals = _literals;
        while( *literals != LAST_LITERAL )
        {
	    int lit = *(literals)++;
	    if( lit != nrval )
	    {
		FIX( -lit, currentTimeStamp );
		*(end_fixstackp++) = -lit;
	    }
	}

	big_resolventp = end_fixstackp;

	while( local_fixstackp < end_fixstackp )
	{
	    if( propagate_big_clauses( *(local_fixstackp++) ) == UNSAT )
	    {
		restore_big_clauses( local_fixstackp, rstackp );
		return UNSAT;
	    }
	}

	while( big_resolventp < end_fixstackp )
	{
	    if( *big_resolventp != nrval )
	    {
		new_resolvent_end = new_resolvent_begin;

		literals = _literals;
	        while( *literals != LAST_LITERAL )
	        {
		    int lit = *(literals)++;
		    if( lit != nrval )
			*(new_resolvent_end++) = lit;
		}
		*(new_resolvent_end++) = *(big_resolventp);
		add_resolvent();
	    }
	    big_resolventp++;
	}

	restore_big_clauses( end_fixstackp, rstackp );
	return SAT;
}

int check_reduction( int *_literals )
{
	int *literals = _literals;

	if( _literals[ 2 ] == LAST_LITERAL )	return 0; // break on binary clause;

	while( *literals != LAST_LITERAL )
        {
	    int lit = *(literals++);
	    if( strengthen_big_clause( _literals, lit ) == UNSAT )
	    {
		while( *literals != LAST_LITERAL )
		{
		    literals[ -1 ] = *literals;
		    literals++;
		}
		literals[ -1 ]  = *literals;

		return 1;
	    }
        }
	return 0;
}

void make_resolvents()
{
	int i, j, *stamps, *literals, clash, clash_lit, join;

	nrofresolvents = 0;

	resolvent_list_size = INITIAL_ARRAY_SIZE;
	resolvent_list = (int**) malloc( sizeof(int*) * resolvent_list_size );
	resolvent_size = (int* ) malloc( sizeof(int ) * resolvent_list_size );

	stamps  = (int*) malloc( sizeof(int) * nrofvars );

	new_resolvent_begin = (int*) malloc( sizeof(int) * nrofvars );
	new_resolvent_end   = new_resolvent_begin;

	for( i = 0; i < nrofvars; i++ ) stamps[ i ] = nrofbigclauses;

	currentTimeStamp = 2;

	for( i = 0; i < nrofbigclauses; i++ )
	{
	    literals = clause_list[ i ];

            while( *literals != LAST_LITERAL )
            {
	    	int lit = *(literals)++;

		if( lit > 0 ) stamps[  lit ] =  i;
		else	      stamps[ -lit ] = -i;
	    }

	    for( j = i + 1; j < nrofbigclauses; j++ )
	    {
	    	literals = clause_list[ j ];

	        clash = 0; join = 0, clash_lit = 0;
            	while( *literals != LAST_LITERAL )
            	{
	    	    int lit = *(literals)++;

		    if( lit > 0 )
		    {
			if     ( stamps[  lit ] ==  i ) join++;
			else if( stamps[  lit ] == -i ) { clash++; clash_lit = -lit; }
		    }
		    else
		    {
			if     ( stamps[ -lit ] == -i ) join++;
			else if( stamps[ -lit ] ==  i ) { clash++; clash_lit = -lit; }
		    }
	        }

		if( (clash == 1) && (join > 2) )
		{
		     new_resolvent_end   = new_resolvent_begin;

		     literals = clause_list[ i ];
                     while( *literals != LAST_LITERAL )
		     {
	    	        int lit = *(literals)++;
			if( lit != clash_lit ) *(new_resolvent_end++) = lit;
		     }

		     literals = clause_list[ j ];
                     while( *literals != LAST_LITERAL )
		     {
	    	        int lit = *(literals)++;
			if( (lit != -clash_lit) && (lit > 0) && (stamps[  lit ] !=  i)  ) *(new_resolvent_end++) = lit;
			if( (lit != -clash_lit) && (lit < 0) && (stamps[ -lit ] != -i)  ) *(new_resolvent_end++) = lit;
		     }
		     add_resolvent();
		}
	    }
	}

	Cv      = (int**) realloc( Cv     , sizeof(int*) * (nrofclauses + nrofresolvents) );
	Clength = (int* ) realloc( Clength, sizeof(int ) * (nrofclauses + nrofresolvents) );

	for( i = 0; i < nrofresolvents; i++ )
	{
	    Cv     [ nrofclauses ] = resolvent_list[ i ];
	    Clength[ nrofclauses ] = resolvent_size[ i ];
	    nrofclauses++;
	}

	free( new_resolvent_begin );
	free( resolvent_list );
	free( resolvent_size );
}

void detect_resolvents()
{
	int i, reduction_flag;

	nrofresolvents = 0;

	resolvent_list_size = INITIAL_ARRAY_SIZE;
	resolvent_list = (int**) malloc( sizeof(int*) * resolvent_list_size );
	resolvent_size = (int* ) malloc( sizeof(int ) * resolvent_list_size );

	rstack  = (int*) malloc( sizeof(int) * nrofvars );
	rstackp = rstack;

	new_resolvent_begin = (int*) malloc( sizeof(int) * nrofvars );
	new_resolvent_end   = new_resolvent_begin;

	for( i = 0; i < nrofvars; i++ )
	    if( IS_NOT_FIXED( i ) )
		UNFIX( i );

	currentTimeStamp = 2;

	for( i = 0; i < nrofbigclauses; i++ )
	{
	    reduction_flag = 0;

	    if( check_reduction( clause_list[ i ] ) )
	    {
		reduction_flag = 1;
	        while( check_reduction( clause_list[ i ] ) );
	    }

	    if( reduction_flag )
	    {
		int *literals;
		new_resolvent_end   = new_resolvent_begin;

		literals = clause_list[ i ];
            	while( *literals != LAST_LITERAL )
		{    *(new_resolvent_end++) = *(literals++); }

		add_resolvent();
	    }
	}

	Cv      = (int**) realloc( Cv     , sizeof(int*) * (nrofclauses + nrofresolvents) );
	Clength = (int* ) realloc( Clength, sizeof(int ) * (nrofclauses + nrofresolvents) );

	for( i = 0; i < nrofresolvents; i++ )
	{
	    Cv     [ nrofclauses ] = resolvent_list[ i ];
	    Clength[ nrofclauses ] = resolvent_size[ i ];
	    nrofclauses++;
	}

	free( rstack );
	free( new_resolvent_begin );
	free( resolvent_list );
	free( resolvent_size );
}

int resolvent_look (int* nrofresolvents) {
  int old_nrofclauses = nrofclauses;

  if (simplify_formula() == UNSAT) return UNSAT;

  allocate_big_clauses_datastructures();

//  make_resolvents();

  detect_resolvents();

  free_big_clauses_datastructures();

  if (simplify_formula () == UNSAT) return UNSAT;

  if (nrofclauses > old_nrofclauses)
    printf ("c resolvent_look() :: found %i resolvents\n", nrofclauses - old_nrofclauses);

  return SAT; }
