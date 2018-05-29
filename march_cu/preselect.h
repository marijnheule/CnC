/* MARCH II! Satisfiability Solver

   Copyright (C) 2001 M. Dufour, M. Heule, J. van Zwieten
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

#ifndef __MAR_H__
#define __MAR_H__
#include "common.h"

void init_preselection( );
void re_init_preselection( );
void dispose_preselection( );

void init_freevars();
void dispose_freevars();

void reduce_freevars( int nrval );

int ConstructCandidatesSet( );
void ConstructPreselectedSet( );
void DeltaRankPreselectedSet( );
int PreselectAll( );

int RankCompare( const void *prtA, const void *ptrB );

int check_ternary_clause_density();

void clearEqAndTernaryImpSize( const int nrval );

void update_fraction_parameter( const int nrval );

void set_block_stamps( const int nrval );

void StaticRank( unsigned int accuracy );

void updateValues( unsigned int clause_index, float value );
void HiRemoveLiteral( unsigned int clause_index, int nrval );
void HiAddLiteral( unsigned int clause_index, int nrval );
void HiRemoveClause( unsigned int clause_index );
void HiAddClause( unsigned int clause_index );

#endif
