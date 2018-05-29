/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

#include "common.h"

struct record {
    int branch_literal;
    int nrofforced;
    int forced_offset;
    int child[2];
    int UNSAT_flag;
};

unsigned int current_record;
struct record *records;

void init_direction();

int init_new_record();

int fix_recorded_literals( int record_index );
void record_node( const int record_index, int branch_literal, const int skip_left, const int skip_right );
void check_forced_array_capacity();

void set_recorded_literals( int record_index );
void get_recorded_literals( int **_forced_literal_array, int *_forced_literals );

void print_records();
