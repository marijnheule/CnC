/* MARCH Satisfiability Solver

   Copyright (C) 2001-2004 M. Dufour, M. Heule, J. van Zwieten
   [m.dufour@student.tudelft.nl, marijn@heule.nl, zwieten@ch.tudelft.nl]

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

#ifndef __SOLVER_H__
#define __SOLVER_H__

#include "common.h"

int initSolver();
void disposeSolver();
void scaleTimeAssignments();

void centerPtrs();

void clearTernaryImpReduction();
int verifySolution();
int checkSolution();

int super_linear_branching();
int distribution_branching();

int march_solve_rec();
void backtrack();
int get_direction( int nrval );
void printSolution( int orignrofvars );

int DPLL_add_binary_implications( int lit1, int lit2 );
int DPLL_propagate_binary_equivalence( const int bieq );

void MainDead( int *__rstackp );

int IFIUP( const int nrval, const int forced_or_branch_flag );
int DPLL_update_datastructures( const int nrval );

int DPLL_fix_ternary_implications   ( const int nrval );
int DPLL_fix_binary_implications_rec( const int nrval );

void swap_ternary_implications( const int nrval, const int lit1, const int lit2 );

void remove_satisfied_implications( const int nrval );
void restore_implication_arrays   ( const int nrval );

void fillBinaryImpOne();
void printCv();
void printConflict();

#endif
