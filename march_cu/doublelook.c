/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule.
   [marijn@heule.nl, jevanzwieten@gmail.com, mark.dufour@gmail.com]
*/

#include <stdlib.h>
#include <stdio.h>

#include "common.h"
#include "doublelook.h"
#include "lookahead.h"

int *doublelook_fixstackp;
int *doublelook_resstackp;

int DL_MAX_Stamp;
int DL_lastChanged;

int (*DL_IUP        ) (int *local_fixstackp);
int DL_IUP_w_eq_3SAT  (int *local_fixstackp);
int DL_IUP_w_eq_kSAT  (int *local_fixstackp);
int DL_IUP_wo_eq_3SAT (int *local_fixstackp);
int DL_IUP_wo_eq_kSAT (int *local_fixstackp);

void init_doublelook () {
  doublelook_count  = 0;
  doublelook_failed = 0;
  DL_trigger_sum    = 0;
  DL_MAX_Stamp      = 0;
  DL_lastChanged    = 0;

  dl_possibility_counter = 0;
  dl_actual_counter      = 0;

#ifdef EQ
  if (non_tautological_equivalences) {
    if (kSAT_flag) DL_IUP = &DL_IUP_w_eq_kSAT;
    else           DL_IUP = &DL_IUP_w_eq_3SAT; }
  else
#endif
  if (kSAT_flag)   DL_IUP = &DL_IUP_wo_eq_kSAT;
  else             DL_IUP = &DL_IUP_wo_eq_3SAT; }

int perform_doublelook (const int nrval, const int offset) {
  int i;

  DL_trigger_sum += DL_trigger;

  do {
    DL_lastChanged = 0;
#ifdef INTELLOOK
    struct treeNode* _treeArray = treeArray;
    for (i = tree_elements-1; i >= 0; i--) {
      struct treeNode _treeNode = *(_treeArray++);

      if (DL_lastChanged == _treeNode.literal) goto doublelook_end;

      currentTimeStamp += _treeNode.gap;

      if (currentTimeStamp + tree_elements >= DL_MAX_Stamp) goto doublelook_end;

      if (DL_treelook (_treeNode.literal) == UNSAT)
        return UNSAT;

      currentTimeStamp -= _treeNode.gap; }
    currentTimeStamp += 2 * tree_elements;
#else
    for (i = 0; i < lookaheadArrayLength; i++) {
      if ((currentTimeStamp+4) >= DL_MAX_Stamp) goto doublelook_end;
      int nrvar = lookaheadArray[i];
      if (nrvar == abs (DL_lastChanged)) goto doublelook_end;

      if (timeAssignments[nrvar] >= DL_MAX_Stamp) continue;

      currentTimeStamp += 2;
      if (DL_IFIUP (nrvar) == UNSAT) {
        if (DL_fix_forced_literal (-nrvar) == UNSAT)
          return UNSAT; }
      else {
        currentTimeStamp += 2;
        if (DL_IFIUP (-nrvar) == UNSAT) {
          if (DL_fix_forced_literal (nrvar) == UNSAT)
            return UNSAT; } } }
#endif
  } while (DL_lastChanged != 0);

  doublelook_end:;

  doublelook_failed++;

  currentTimeStamp = DL_MAX_Stamp;

  look_resstackp = doublelook_resstackp;

  if (look_resstackp > look_resstack) add_resolvents (nrval);

  return SAT; }

int doublelook (int nrval, int offset) {
  int _result = SAT;

  doublelook_count++;

  DL_MAX_Stamp      = currentTimeStamp + offset;
  currentTimeStamp  = DL_MAX_Stamp;

  if (kSAT_flag) look_backtrack();

  int *local_stackp = end_fixstackp;

  look_fix_binary_implications (nrval);

  if (kSAT_flag) DL_IUP (local_stackp);

  currentTimeStamp -= offset;

  doublelook_fixstackp = end_fixstackp;
  doublelook_resstackp = look_resstack;

  _result = perform_doublelook (nrval, offset);

  if (kSAT_flag) restore_big_clauses (end_fixstackp, local_stackp);

  return _result; }

int DL_treelook (const int nrval) {
  if (IS_FIXED(nrval)) {
    if ((timeAssignments[ nrval ] < DL_MAX_Stamp) && (timeAssignments[ nrval ] & DEATHMASK))
      return DL_fix_forced_literal (-nrval); }
  else if (DL_IFIUP(nrval) == UNSAT)
    return DL_fix_forced_literal (-nrval);

  return SAT; }

int DL_IUP_w_eq_3SAT (int *local_fixstackp) {
  while (local_fixstackp < end_fixstackp) {
    int lit = *(local_fixstackp++);
    if (DL_fix_3SAT_clauses (lit) == UNSAT) return UNSAT;
    if (DL_fix_equivalences (lit) == UNSAT) return UNSAT; }

  return SAT; }

int DL_IUP_w_eq_kSAT (int *local_fixstackp) {
  while (local_fixstackp < end_fixstackp) {
    int lit = *(local_fixstackp++);
    if (DL_fix_kSAT_clauses (lit) == UNSAT) {
      end_fixstackp = local_fixstackp;
      return UNSAT; }
    if (DL_fix_equivalences (lit) == UNSAT) {
      end_fixstackp = local_fixstackp;
      return UNSAT; } }
  return SAT; }

int DL_IUP_wo_eq_3SAT (int *local_fixstackp) {
  while (local_fixstackp < end_fixstackp)
    if (DL_fix_3SAT_clauses (*(local_fixstackp++)) == UNSAT)
      return UNSAT;
  return SAT; }

int DL_IUP_wo_eq_kSAT (int *local_fixstackp) {
  while (local_fixstackp < end_fixstackp)
    if (DL_fix_kSAT_clauses (*(local_fixstackp++)) == UNSAT) {
      end_fixstackp = local_fixstackp;
      return UNSAT; }
  return SAT; }

int DL_IFIUP (const int nrval) {
  int *local_fixstackp;

  if (kSAT_flag) look_backtrack ();
  else end_fixstackp = doublelook_fixstackp;

  local_fixstackp = end_fixstackp;
  look_resstackp  = doublelook_resstackp;

  if (look_fix_binary_implications (nrval) == UNSAT) {
    end_fixstackp = local_fixstackp;
    return UNSAT; }

  return DL_IUP (local_fixstackp); }

inline int DL_fix_3SAT_clauses (const int nrval) {
  int i, *tImp = TernaryImp[ -nrval ];

  for (i = TernaryImpSize[ -nrval ]; i--;) {
    int lit1 = *(tImp++);
    int lit2 = *(tImp++);

    if (IS_FIXED(lit1)) {
      if (FIXED_ON_COMPLEMENT(lit1)) {
        if (IS_FIXED(lit2)) {
          if (FIXED_ON_COMPLEMENT(lit2))                       return UNSAT; }
        else if (look_fix_binary_implications (lit2) == UNSAT) return UNSAT; } }
    else if ((IS_FIXED(lit2)) && (FIXED_ON_COMPLEMENT(lit2)))
      if (look_fix_binary_implications (lit1) == UNSAT)        return UNSAT; }

  return SAT; }

inline int DL_fix_kSAT_clauses (const int nrval) {
  int *clauseSet = clause_set[ -nrval ];
  while (*clauseSet != LAST_CLAUSE) {
    int clause_index = *(clauseSet++);
    clause_length[ clause_index ]--;

    if (clause_length[ clause_index ] <= 1) {
      int *clause = clause_list[ clause_index ];
      while (*clause != LAST_LITERAL) {
        int lit = *clause++;
        if (IS_NOT_FIXED(lit)) {
          if (look_fix_binary_implications (lit) == SAT)
            goto DL_next_clause;
	  break; }
        else if (!FIXED_ON_COMPLEMENT(lit))
          goto DL_next_clause; }
      while (*clauseSet != LAST_CLAUSE)
        clause_length[ *(clauseSet++) ]--;
      return UNSAT; }

    DL_next_clause:; }
  return SAT; }

inline int DL_fix_equivalences (const int nrval) {
  int i, j;
  int nr = NR(nrval);

  for (i = Veq[ nr ][ 0 ] - 1; i > 0; i--) {
    int ceqidx = Veq[ nr ][ i ];
    int var    = 0;
    int value  = 1;

    for (j = CeqSizes[ ceqidx ] - 1; j >= 0; j--) {
      if (IS_FIXED(Ceq[ ceqidx ][ j ]))
        value *= EQSGN( Ceq[ ceqidx ][ j ] );
      else if (var == 0)
  	var = Ceq[ ceqidx ][ j ];
      else goto dl_ceqend; }

      if (var) {
        if (look_fix_binary_implications (var * value * CeqValues[ ceqidx ]) == UNSAT)
          return UNSAT; }
	else if (value == -CeqValues[ ceqidx ])
          return UNSAT;

     dl_ceqend :; }
  return SAT; }

int DL_fix_forced_literal (int nrval) {
  tstamp _cts               = currentTimeStamp;
  currentTimeStamp    	    = DL_MAX_Stamp;

  if (DL_IFIUP (nrval) == UNSAT) return UNSAT;

  DL_lastChanged   	    = -nrval;
  currentTimeStamp    	    = _cts;
  *(doublelook_resstackp++) = nrval;

  return SAT; }
