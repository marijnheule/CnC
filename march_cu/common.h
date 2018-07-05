/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#ifndef __COMMON_H__
#define __COMMON_H__

/*
        --------------------------------------------------------------------------------------------------------------
        -------------------------------------------------[ defines ]--------------------------------------------------
        --------------------------------------------------------------------------------------------------------------
*/

//#define SCHUR

#define CUBE

#ifdef CUBE
	#define FLIP_BIAS
//	#define FLIP_ASSUMPTIONS
//	#define EVAL_VAR
//	#define DISCREPANCY_SEARCH
#endif

//#define SHARPSAT		// probably absolete due to sharp_mode

//#define EVAL_VAR

//#define SUPER_LINEAR
#ifdef SUPER_LINEAR
  #define STORATE_DEPTH		12
  #define SL_MAX		1000
#endif

//#define TIMEOUT		3600

//#define COUNT_SAT
#ifdef COUNT_SAT
  #define CUT_OFF   		12
#endif

//#define DISTRIBUTION
#ifdef DISTRIBUTION
  #define SUBTREE_SIZE     	100
  #define OPPOSITE_DIRECTION
#endif

/* array's */

#define WBINARIES

//#define EQ
//#define DYNAMIC_PRESELECT_SETSIZE
//#define FLIP_UNBALANCE

#ifdef EQ
	#define QXCONST		11
	#define QXBASE		25
#endif

//#define EMPTYVARS	      // Probably absolete due to sharp_mode
#define SIMPLE_EQ             // Probably no longer required to turn off due to sharp_mode

//#define BIEQ			//Gaat nog mis bij het toevoegen van binary clauses

#define INTELLOOK

//#define LOOK_SUBSUME

// Preprocessing techniques
//#define RESOLVENTLOOK
//#define FIND_EQ
//#define FIX_MONOTONE

#define GAH			  1  // on
#define WFR			  1  // on
#define IMP			  1  // on

#define H_MIN			8.0
#define H_MAX		      550.0
#define H_BIN		       25.0
//#define H_MIN			0.1
//#define H_MAX		       25.0
//#define H_BIN			3.3
#define H_DEC			0.5

#define SL_ITER			  9
#define DL_ITER			  2

#define CUBE_MODE		  1
#define PLAIN_MODE		  2

/* parameters */
#define DL_DECREASE		0.85
//#define DL_VARMULT		15
//#define DL_STATIC		52

#define PERCENT			10
#define MAX_FULL_LOOK_DEPTH	30

#define DL_INITIAL		0.0

#define INITIAL_ARRAY_SIZE	4

/* readibilaty define */
#define STACK_BLOCK		0
#define ABS_MIN_DIFF_SCORE	-1

#define SAT			1
#define UNSAT			0
#define UNKNOWN			-1

#define FIX_FORCED_LITERALS	1
#define FIX_RECORDED_LITERALS	2
#define FIX_BRANCH_VARIABLE     3

#define	INDEPENDENT		0
#define EQUIVALENT		1
#define DUMMY			2

#define TRUE			1
#define FALSE			0

#define LAST_LITERAL		0
#define LAST_CLAUSE		-1

#define EXIT_CODE_UNKNOWN	0
#define EXIT_CODE_SAT		10
#define EXIT_CODE_UNSAT		20
#define EXIT_CODE_ERROR		1

/* Macro's to increase readibilaty */

#define FIX( __a, __timeStamp ) 		   \
{ 				 		   \
        timeAssignments[  __a ] = __timeStamp;     \
        timeAssignments[ -__a ] = __timeStamp + 1; \
}

#define UNFIX( __a )					\
{							\
        timeAssignments[  __a ] = 0;			\
        timeAssignments[ -__a ] = 0;			\
}

#define TAUTOLOGY       	0x40000004
#define MAX			0x40000004
#define ALL_VARS		0x40000004
#define VARMAX			0x40000004
#define NARY_MAX		0x40000004
#define BARY_MAX		0x40000002
#define LOOK_MAX		0x40000000

#define SGN( __a )		( __a < 0 ? -1 : 1 )
#define VAR( __a )		( __a + nrofvars )
#define NR( __a )		( abs( __a ) )

#define DEATHMASK			1
#define EQSGN( __a )           		( ((timeAssignments[ __a ] & DEATHMASK) > 0) ? -1: 1 )

#define IS_FIXED(__a)			(timeAssignments[ __a ] >= currentTimeStamp)
#define IS_NOT_FIXED(__a)		(timeAssignments[ __a ] <  currentTimeStamp)
#define IS_FORCED(__a)			(timeAssignments[ __a ] >= LOOK_MAX)
#define IS_NOT_FORCED(__a)		(timeAssignments[ __a ] <  LOOK_MAX)
#define FIXED_ON_COMPLEMENT(__a)	(timeAssignments[ __a ] &  DEATHMASK)

#define BIMP_START(__a)			(BinaryImp[  __a ] + 2)
#define BIMP_ELEMENTS			(bImp[ -2 ] - 1)

#ifdef OPPOSITE_DIRECTION
  #define TOP_OF_TREE           ( target_rights > current_rights )
#else
  #define TOP_OF_TREE            0
#endif

/* miscellaneous */
//#define DEBUGGING
#ifndef CUT_OFF
  #define PROGRESS_BAR
#endif

/*
        --------------------------------------------------------------------------------------------------------------
        -------------------------------------------------[ typedef's ]------------------------------------------------
        --------------------------------------------------------------------------------------------------------------
*/

struct timeAssignment {
  int stamp;
  int value; };

typedef unsigned int tstamp;

struct resolvent {
  int stamp;
  int literal; };

struct treeNode {
  int literal;
  int gap; };

/*
        --------------------------------------------------------------------------------------------------------------
        -------------------------------------------------[ MACRO'S ]--------------------------------------------------
        --------------------------------------------------------------------------------------------------------------
*/

#define INIT_ARRAY( _a, _size ) \
{ \
        _a##stackSize = _size; \
        _a##stack     = (int*) malloc (sizeof(int) * _a##stackSize); \
        _a##stackp    = _a##stack; \
}

#define MALLOC_OFFSET( _a, _type, _size, _value ) \
{ \
	int i; \
\
        _a = (_type *) malloc( sizeof(_type) * ( 2*_size+1 ) ); \
        for (i = 0; i < (2 * _size + 1); i++) \
            _a[ i ] = _value; \
\
	_a += _size; \
}

#define FREE(__a) \
{\
        if( __a != NULL ) \
        { free( __a ); __a = NULL; } \
}

#define FREE_OFFSET(__a) \
{\
        if( __a != NULL ) \
        { __a -= nrofvars; free( __a ); __a = NULL; } \
}

#define CHECK_NODE_STAMP( _nrval ) \
{ \
    if( node_stamps[ _nrval ] != current_node_stamp ) \
    { \
        PUSH( imp, _nrval ); \
        PUSH( imp, BinaryImp[ _nrval ][ 0 ] ); \
        node_stamps[ _nrval ] = current_node_stamp; \
    } \
}


#define CHECK_AND_ADD_BINARY_IMPLICATIONS( __a, __b ) \
{ \
	CHECK_BIMP_BOUND( -__a ); \
	CHECK_BIMP_BOUND( -__b ); \
  \
	BinaryImp[ -__a ][ (BinaryImp[ -__a ][ 0 ])++ ] = __b; \
	BinaryImp[ -__b ][ (BinaryImp[ -__b ][ 0 ])++ ] = __a; \
}


#define ADD_BINARY_IMPLICATION( __a, __b ) \
{ \
	BinaryImp[ -__a ][ (BinaryImp[ -__a ][ 0 ])++ ] = __b; \
}


#define ADD_BINARY_IMPLICATIONS( __a, __b ) \
{ \
	BinaryImp[ -__a ][ (BinaryImp[ -__a ][ 0 ])++ ] = __b; \
	BinaryImp[ -__b ][ (BinaryImp[ -__b ][ 0 ])++ ] = __a; \
}

#define DL_ADD_BINARY_IMPLICATIONS( __a, __b ) \
{ \
	CHECK_BIMP_DOUBLEBOUND( -__a, doubleBinaryImp[ -__a] ); \
	CHECK_BIMP_DOUBLEBOUND( -__b, doubleBinaryImp[ -__b] ); \
  \
	BinaryImp[ -__a ][ doubleBinaryImp[-__a]++ ] = __b; \
	BinaryImp[ -__b ][ doubleBinaryImp[-__b]++ ] = __a; \
}

#define PUSH( stk, value ) \
	{ \
	if( stk##stackp >= ( stk##stack + stk##stackSize ) ) \
	{ \
		int __tmp; \
		stk##stackSize *= 2; \
		__tmp = stk##stackp - stk##stack; \
		stk##stack = (int *) realloc( stk##stack, stk##stackSize*sizeof(int)); \
		stk##stackp = stk##stack + __tmp; \
	} \
        *stk##stackp = value; \
        stk##stackp++; \
	}

#define POP( stack, value ) \
	{ \
        stack##stackp--;        \
        value = ( *stack##stackp ); \
	}

#define POP_RECURSION_STACK_TO_DEV_NULL \
	{ \
        rstackp--;      \
	}

#define POP_IMPLICATION_STACK_TO_DEV_NULL \
	{ \
        istackp--;      \
	}

#define POP_BACKTRACK_RECURSION_STACK \
	{ \
        rstackp--;      \
        restore_implication_arrays( *rstackp ); \
	}
int *clause_red_depth;

#define POP_BACKTRACK_LOOKAHEAD_STACK \
	{ \
        lstackp--;      \
        unfixonevarLookahead( *lstackp ); \
	}

#define CHECK_BIMP_BOUND( ic ) \
{ \
        if( BinaryImpLength[ ic ] <= BinaryImp[ ic ][ 0 ] ) \
        { \
             BinaryImp[ ic ] = (int*) realloc( BinaryImp[ ic ], sizeof( int ) * 2 * ( BinaryImpLength[ ic ] + 1 ) ); \
             BinaryImpLength[ ic ] += BinaryImpLength[ ic ] + 1; \
        }\
}

#define CHECK_BIMP_UPPERBOUND( ic, size ) \
{ \
        if( BinaryImpLength[ ic ] <= (BinaryImp[ ic ][ 0 ] + size) ) \
        { \
             BinaryImp[ ic ] = (int*) realloc( BinaryImp[ ic ], sizeof( int ) * (2 * BinaryImpLength[ ic ] + size + 1) ); \
             BinaryImpLength[ ic ] += BinaryImpLength[ ic ] + 1 + size; \
        }\
}

#define CHECK_BIMP_DOUBLEBOUND( ic, size ) \
{ \
        if( BinaryImpLength[ ic ] <= size ) \
        { \
             BinaryImp[ ic ] = (int*) realloc( BinaryImp[ ic ], sizeof( int ) * (2 * BinaryImpLength[ ic ] + size + 1) ); \
             BinaryImpLength[ ic ] += BinaryImpLength[ ic ] + 1 + size; \
        }\
}

#define CHECK_VEQ_BOUND( vq ) \
{ \
        if( VeqLength[ vq ] <= Veq[ vq ][ 0 ] ) \
        { \
             VeqLength[ vq ] += VeqLength[ vq ] + 1; \
             Veq[ vq ] = (int*) realloc( Veq[ vq ], sizeof( int ) * VeqLength[ vq ]  ); \
             VeqLUT[ vq ] = (int*) realloc( VeqLUT[ vq ], sizeof( int ) * VeqLength[ vq ]  ); \
        }\
}

/*
        --------------------------------------------------------------------------------------------------------------
        ------------------------------------------------[ variables ]-------------------------------------------------
        --------------------------------------------------------------------------------------------------------------
*/

char cubesFile[1024];
char initFile[1024];

unsigned int seed, hardLimit;
int *trail, trailSize;

int addIMP, addWFR, gah;

int *clause_reduction;
int *clause_SAT_flag;
int **big_to_binary, *btb_size, *big_global_table;

#ifdef CUBE
int conflicts;
int assigned_th;
double sum_th, factor_th;
double free_th;
int part_free;
int nr_cubes;
unsigned int cut_depth, cut_var, dynamic;
#endif

int mode, sharp_mode, quiet_mode;

char *cubeFile, *learnFile;

int cweight;
double downexp, fraction;
unsigned int cubeLimit;

#ifdef SUPER_LINEAR
int subtree_size;
#endif

unsigned int sl_iter, dl_iter;
float h_min, h_max, h_bin, h_dec;

float *hiRank, *clause_weight, *hiSum;
int kSAT_flag;
int dist_acc_flag;

// used for big clauses and resolvent_look
int *literal_list, **clause_list, *clause_length, **clause_set, *clause_database, *big_occ;
int nrofbigclauses;

int target_rights, current_rights;
#ifdef CUT_OFF
int *bins;
#endif

int *decisions;
int jump_depth;

int percent;
float *Rank;
int Rank_trigger;
float *diff, *_diff, *size_diff, *diff_tmp, *_diff_tmp, **diff_depth, *diff_table;
int initial_freevars;

double percentage_forced;

#ifdef COUNT_SAT
  int count_sat;
#endif

int *dpll_fixstackp, *end_fixstackp;

long long dl_possibility_counter, dl_actual_counter;

int *TernaryImpReduction;

int tree_elements;

/* doublelook statistics */
float DL_trigger, DL_trigger_sum;
long long doublelook_count, doublelook_failed;

int bin_sat, bin_unsat;
int non_tautological_equivalences;

/* solver AND lookahead AND pre-selection */
int **TernaryImp, *TernaryImpSize, *tmpTernaryImpSize;
int *lookaheadArray, lookaheadArrayLength;
int *bImp_satisfied;
int *bImp_start;

double *lengthWeight;

int *freevarsArray;

/* statistics */
int nrofvars, nrofclauses, nrofceq, nroforigvars;
int original_nrofvars, original_nrofclauses;
int freevars, activevars, depth;

int **Ceq, **Veq, **VeqLUT, *CeqValues, *CeqSizes;
int *CeqStamps;
int *CeqDepends, *VeqDepends;
int *VeqLength;
int *eq_found;

/* data structure */
tstamp current_node_stamp;
tstamp *timeAssignments, *node_stamps;
int **Cv, *Clength, **BinaryImp, *BinaryImpLength;

/* various stacks */
int *rstack, *rstackp, rstackSize;
int *look_fixstack, *look_fixstackp, look_fixstackSize;
int *look_resstack, *look_resstackp, look_resstackSize;
int *subsumestack,  *subsumestackp,  subsumestackSize;
int *bieqstack,  *bieqstackp,  bieqstackSize;
int *impstack,   *impstackp,   impstackSize;

/* lookahead */
int *forced_literal_array, forced_literals;
tstamp currentTimeStamp;
int iterCounter;

struct treeNode *treeArray;

/* accounting */
int nodeCount;
long long lookAheadCount;
int unitResolveCount;
int necessary_assignments;
int lookDead, mainDead;

#endif
