/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

#include "common.h"
#include "distribution.h"
#include "solver.h"

#define INITIAL_FORCED_ARRAY_SIZE	20
#define INITIAL_RECORD_ARRAY_SIZE	20

#define JUMP_DEPTH			999

#ifdef DISTRIBUTION
int *recorded_literal_array, recorded_literals;
unsigned int record_array_size, recorded_nodes = 0;
int *forced_array, forced_array_size, forced_elements;
int bin_mask = 0, current_bin = 0;

void fill_distribution_bins();

void init_direction()
{
	recorded_literals = 0;
	bin_mask          = 0;
	current_bin       = 0;
	current_record    = 0;
	recorded_nodes    = 0;
	forced_elements   = 0;
	jump_depth        = JUMP_DEPTH;
#ifdef SUBTREE_SIZE
	jump_depth 	  = 0;
#endif
#ifdef CUT_OFF
	jump_depth 	= CUT_OFF;
#endif
	forced_array_size = INITIAL_ARRAY_SIZE;
	forced_array = (int*) malloc( sizeof(int) * forced_array_size );

	record_array_size = INITIAL_RECORD_ARRAY_SIZE;
	records = (struct record*) malloc( sizeof(struct record) * record_array_size );

	records[0].branch_literal = 0;
	records[0].forced_offset  = 0;
	records[0].nrofforced     = 0;
	records[0].child[0]       = 0;
	records[0].child[1]       = 0;
	records[0].UNSAT_flag     = 0;
#ifdef CUT_OFF
	fill_distribution_bins();
#endif
}

int init_new_record()
{
	if( (depth > jump_depth) && (jump_depth > 0) ) return 0;

	recorded_nodes++;
	current_record = recorded_nodes;

	if( record_array_size <= recorded_nodes )
	{
	    record_array_size += (unsigned int)(0.5 * record_array_size);
	    records = (struct record*) realloc( records, sizeof(struct record) * record_array_size );
	}

	records[ recorded_nodes ].branch_literal = 0;
	records[ recorded_nodes ].forced_offset  = 0;
	records[ recorded_nodes ].nrofforced     = 0;
	records[ recorded_nodes ].child[0]       = 0;
	records[ recorded_nodes ].child[1]       = 0;
	records[ recorded_nodes ].UNSAT_flag     = 1;

	return recorded_nodes;
}

int fix_recorded_literals( int record_index )
{
	if( record_index == 0 ) 		 return SAT;
	if( records[ record_index ].UNSAT_flag ) return UNSAT;

	records[ record_index ].UNSAT_flag = 1;

        set_recorded_literals( record_index );
        if( IFIUP( 0, FIX_RECORDED_LITERALS ) == UNSAT )
            return UNSAT;

	return SAT;
}

void record_node( const int record_index, int record_literal, const int skip_left, const int skip_right )
{
        if( (depth < jump_depth) )	// || jump_depth == 0??
        {
            if( (skip_left == 0) && (records[ record_index ].child[ record_literal > 0 ] == 0) )
	    {
		int tmp =  init_new_record();
                records[ record_index ].child[ record_literal > 0 ] = tmp;
	    }

            if( (skip_right == 0) && (records[ record_index ].child[ record_literal < 0 ] == 0) )
	    {
		int tmp =  init_new_record();
                records[ record_index ].child[ record_literal < 0 ] = tmp;
	    }

            struct record *node = &records[ record_index ];
	    node->UNSAT_flag = records[ node->child[0] ].UNSAT_flag &
			       records[ node->child[1] ].UNSAT_flag;
        }
	else records[ record_index ].UNSAT_flag = (depth == jump_depth);

        if( (record_index > 0) &&
            ((depth < jump_depth)) &&  // || jump_depth == 0?
            (records[ record_index ].branch_literal == 0) &&
            (records[ record_index ].UNSAT_flag     == 0) )
	{
	    int *_rstackp = rstackp;
	    struct record *node  = &records[ record_index ];

	    if( TOP_OF_TREE ) record_literal *= -1;

	    node->branch_literal = record_literal;
	    node->forced_offset  = forced_elements;

	    check_forced_array_capacity();

	    while( *(--_rstackp) != STACK_BLOCK )
	    {	forced_array[ forced_elements++ ] = *(_rstackp);    }

	    node->nrofforced = forced_elements - node->forced_offset;
	}
}

void check_forced_array_capacity()
{
	if( forced_elements + freevars > forced_array_size )
	{
	    forced_array_size *= 2;
	    forced_array_size += freevars;
	    forced_array = (int*) realloc( forced_array, sizeof(int) * forced_array_size );
	}
}

void set_recorded_literals( int record_index )
{
	recorded_literal_array = &forced_array[records[record_index].forced_offset];
	recorded_literals = records[record_index].nrofforced;
}

void get_recorded_literals( int **_forced_literal_array, int *_forced_literals )
{
        *_forced_literal_array = recorded_literal_array;
        *_forced_literals      = recorded_literals;
}

void print_records()
{
	int i;

	for( i = 1; i <= recorded_nodes; i++ )
	{
	    printf("record[%i] b_l: %i, UNSAT %i l_c: %i r_c: %i\n",
		i, records[i].branch_literal, records[i].UNSAT_flag, records[i].child[0], records[i].child[1] );
	}

}

#ifdef CUT_OFF
/*************************
	 the procedure fill distribution_bin create a mapping
	 for a fixed JUMP DEPTH given a explicit jumping strategy
*************************/
int current_rights = 0;

void fill_distribution_bins_rec()
{
	if( depth == CUT_OFF )
	{
	    if( current_rights == target_rights )
		bins[ bin_mask ] = current_bin++;
	    return;
	}

	depth++;
#ifdef OPPOSITE_DIRECTION
	bin_mask ^= 1 << (CUT_OFF - depth);
	current_rights++;
#endif
	fill_distribution_bins_rec();
#ifdef OPPOSITE_DIRECTION
	bin_mask ^= 1 << (CUT_OFF - depth);
	current_rights--;
#endif
#ifndef OPPOSITE_DIRECTION
	bin_mask ^= 1 << (CUT_OFF - depth);
	current_rights++;
#endif
	fill_distribution_bins_rec();
#ifndef OPPOSITE_DIRECTION
	bin_mask ^= 1 << (CUT_OFF - depth);
	current_rights--;
#endif
	depth--;
}

void fill_distribution_bins()
{
        target_rights  = 0;
        current_rights = 0;

	bins = (int*) malloc( sizeof(int) * (1<<CUT_OFF) );

        do
        {
	    fill_distribution_bins_rec();
            target_rights++;
        }
        while( target_rights <= CUT_OFF );
}
#endif

#endif
