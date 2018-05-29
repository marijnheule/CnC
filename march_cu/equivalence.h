/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

int equivalence_reasoning();

void init_equivalence();
void dispose_equivalence();
void dispose_preprocessor_eq();

int find_and_remove_tautologies();
void fixDependedEquivalences();
int find_and_propagate_bieq();


int check_vadility_equivalences();

int substitude_equivalences( );
void substitude_equivalence( int clause, int index );
void substitude_ceq( int ceqsource, int ceqtarget );

void shorten_equivalence( );

void restoreVeq();

int find_equivalence( int clause );

int propagate_bieq();

void replace_bieq( int lit1, int lit2, int ***__Vc, int ***__VcLUT );

int root_reduce_equivalnces( int nrval, int literal );

int check_non_tautological_equivalences();

int dependantsExists();

void fixEq( int nr, int pos, int value );

void add_binary_equivalence (int, int);

void printCeq();
void printNrofEq();
void check_integrety();
