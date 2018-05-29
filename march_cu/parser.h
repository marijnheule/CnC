/* MARCH Satisfiability Solver

   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2011 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*/

#ifndef __PARSER_H__
#define __PARSER_H__

#include <stdio.h>
#include "common.h"

/*
	Parsing...
*/
int initFormula( FILE* in );
int parseCNF( FILE* in );
int propagate_unary_clauses( );
void disposeFormula();

int simplify_formula();
int sort_literals();
int find_and_propagate_unary_clauses();
int compactCNF();
int sort_clauses();
int find_and_propagate_binary_equivalences();
int clsCompare( const void *ptrA, const void *ptrB );

/*
	Preprocessing...
*/
int sortCv( int useStack, int *_fstack, int **_fstackp );
int replaceEq();
int eqProduct();
int addResolvents();

/*
	Debugging...
*/
	void printFormula( int** Cv );

#ifdef DEBUGGING
	void printCNF( const CNF *cnf );
	void printDIMACSFormula( const CNF *cnf );
#endif

#endif

