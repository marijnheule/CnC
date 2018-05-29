/* 
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

void allocate_big_clauses_datastructures();
void free_big_clauses_datastructures();

void allocateTernaryImp( int **_tImpTable, int ***_tImp, int **_tImpSize );
void freeTernaryImp( int *_tImpTable, int **_tImp, int *_tImpSize );

void allocateVc( int ***__Vc, int ***__VcLUT );
void allocateSmallVc( int ***__Vc, int length );

void freeVc( int **__Vc, int **__VcLUT );
void freeSmallVc( int **__Vc );

void rebuild_BinaryImp( );
void resize_BinaryImp( );
void free_BinaryImp( );

