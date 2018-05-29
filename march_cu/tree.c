/* tree-based lookahead */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

//#define OLDTREES
//#define OLDALGORITHM
#define NEW

#ifndef OLDTREES
  #ifndef OLDALGORITHM
     #ifndef NEW
        #define NEW
     #endif
  #endif
#endif

#include "common.h"
#include "tree.h"
#include "preselect.h"
#include "equivalence.h"
#include "lookahead.h"

#define LOOSELEAF		1
#define ORDEREDLEAF		2
#define STRONGLEAF		3
#define USEDNODE		4
#define	TREEROOT		5
#define	PREREDUCE		7

int N = 0;
int K = 0;
int *comp_ ;
int *child ;
int *fai_;
int *vstack;
int vindex = 0;

int toprank;
int nrofroots;

int *NodeType;

/****************************************************************

	init_tree() initialise the datastructures required
	by the tree build algorithm.

****************************************************************/


void init_tree()
{
	int i, j;

	tree_elements = 0;

	N = K = vindex = nrofroots = toprank = 0;

	NodeType = (int *) malloc (sizeof(int)*(2*nrofvars+1));
	for(i = 0; i < 2* nrofvars + 1; i++ ) NodeType[ i ] = USEDNODE;
	NodeType += nrofvars;

        assignment_array = (struct assignment *)malloc(sizeof(struct assignment)*(nrofvars+1)*2);
        assignment_array += nrofvars;

        for( i = 1; i < nrofvars+1; i++ )
            for( j = 0; j < 2; j++ )
        {
            int varnr;
            struct assignment *assignment;

            varnr = i * ( (2 * j) - 1 );
            assignment = &assignment_array[ varnr ];
            assignment->varnr = varnr;
            assignment->incoming_size = 16;
            assignment->incoming = (int *)malloc( 16 * sizeof(int));
        }

/* ================== group SG4 ======================= */
	fai_  = (int *) malloc (sizeof(int)*(2*nrofvars+1));
	for(i = 0; i < 2* nrofvars + 1; i++ ) fai_ [ i ] = 0 ;

	comp_  = (int *) malloc (sizeof(int)*(2*nrofvars+1));
	for(i = 0; i < 2* nrofvars + 1; i++ ) comp_ [ i ] = 0 ;

	vstack  = (int *) malloc (sizeof(int)*(2*nrofvars+1));
	for(i = 0; i < 2* nrofvars + 1; i++ ) vstack [ i ] = 0 ;
}

void dispose_tree()
{
        int i, j, index;
	struct assignment *assignment;

	FREE_OFFSET( NodeType );

	if( assignment_array != NULL )
	{
          for( i = 1; i < nrofvars+1; i++ )
            for( j = 0; j < 2; j++ )
	    {
		index = i * ( (2 * j) - 1 );
		assignment = &assignment_array[ index ];
		free( assignment->incoming );
	    }
	    FREE_OFFSET( assignment_array );
	}

	FREE( fai_   );
	FREE( comp_  );
	FREE( vstack );
}


void order_nodes_rec( const int nrval )
{
	int i, *bImp, lit;
	struct assignment *parent;

	NodeType[ nrval ] = ORDEREDLEAF;

	parent = &assignment_array[ -nrval ];
	parent->nr_incoming = 0;

	bImp = BIMP_START(nrval);
	for( i = BIMP_ELEMENTS; --i; )
	{
	    lit = *(bImp++);
	    if( NodeType[ lit ] != USEDNODE )
	    {
		if( NodeType[ lit ] == LOOSELEAF )
		    order_nodes_rec( lit );
		ADD_INCOMING( parent, -lit );
	    }
	}
	fai_[ ++N ] = nrval;
}

void crtree( const int nrval )
{
    	int i, *incoming;
	struct assignment *parent, *child;

	parent = &assignment_array[ nrval ];

	incoming = parent->incoming;
	for ( i = parent->nr_incoming; i--; )
	{
		child = &assignment_array[ incoming[i] ];
		if( parent->tree_size >= child->tree_size )
		{
			child->tree_size = parent->tree_size + 1;
			child->parent = nrval;
		}
	}
        parent->nr_incoming = 0;
	NodeType[ nrval ] = USEDNODE;

	if( parent->tree_size == 0 )
	{	fai_[ nrofroots++ ] = nrval; }
	else
	{	parent = &assignment_array[parent->parent];
        	parent->incoming[ parent->nr_incoming++ ] = nrval; }
}

void contract( )
{
	int i, *incoming, nrval;
	struct assignment *parent, *equivalent;

	parent = &assignment_array[ toprank ];		// start with toprank
	parent->parent = 0;				// no parent ; toprank node
	parent->tree_size = 0;				// no tree size yet

	while ( !emptys() )
	{
	    nrval = vpop();

	    if( nrval == toprank ) continue;

	    if( nrval > 0 )
	    {
		if( nodeCount == 0 )
		{    add_binary_equivalence( toprank, -nrval ); }
		else if( VeqDepends[ nrval ] == INDEPENDENT )
		{
		     PUSH( bieq, nrval )
		     VeqDepends[ nrval ] = EQUIVALENT;
		}
	    }

	    equivalent = &assignment_array[ nrval ];
	    equivalent->parent = toprank;
 	    NodeType[ nrval ] = USEDNODE;

	    incoming = equivalent->incoming;
	    for(i = equivalent->nr_incoming; i--; )
	    {	ADD_INCOMING( parent, *(incoming++) ); }

	}
}

void reduce_strong_component(const int nrval)
{
	int i, *incoming;
	struct assignment *parent;

	parent = &assignment_array[ nrval ];

	vpush( nrval );

	if( (Rank[abs(nrval)] + 1.0/abs(nrval)) > (Rank[abs(toprank)] + 1.0 /abs(toprank)) )
		toprank = nrval;

	NodeType[nrval] = PREREDUCE;

	incoming = parent->incoming;
	for( i = parent->nr_incoming; i--; )
	    if( NodeType[ incoming[i] ] == ORDEREDLEAF )
	    {   reduce_strong_component( incoming[i] );
		incoming[ i ] = incoming[ --parent->nr_incoming ]; }
	    else if( NodeType[ incoming[i] ] == USEDNODE )
		incoming[ i ] = assignment_array[ incoming[i] ].parent;
	    else if( NodeType[ incoming[i] ] == PREREDUCE )
		incoming[ i ] = incoming[ --parent->nr_incoming ];
}

int detect_strong_component( const int nrval )
{
	toprank = nrval;

	reduce_strong_component( toprank );

	if( NodeType[ -toprank ] == PREREDUCE )
		return 0;

	contract( );

	NodeType[ toprank ] = STRONGLEAF;

	comp_[++K] = toprank;

	return 1;
}

/* ================== group SG4 ======================= */

/***********************************************************

	treebased_lookahead() is the main procedure of
	the tree based lookahead. it is called in each
	node of the search-tree just before performing
	the actual lookahead.

***********************************************************/


int treebased_lookahead()
{
    int i, varnr;

    nrgiven = 0;
    nrofroots = 0;
    tree_elements = 0;

//    printf ("c performing treebased lookahead on %i elements\n", lookaheadArrayLength);

    for( i = lookaheadArrayLength; i--; )
    {
            varnr = lookaheadArray[ i ];
	    NodeType[ -varnr ] = LOOSELEAF;
            NodeType[  varnr ] = LOOSELEAF;
    }

#ifdef OLDALGORITHM
    for( i = 0; i < lookaheadArrayLength; i++ )
    {
        varnr = lookaheadArray[i];
        if( NodeType[-varnr] == LOOSELEAF )
        {   create_tree_rec( -varnr );
	    looklist_rec( -varnr ); }
        if( NodeType[ varnr] == LOOSELEAF )
        {   create_tree_rec( varnr );
	    looklist_rec( varnr ); }
    }
    return 1;
#endif

    /* phase 1*/
    N = 0;
    for(i = 0; i < lookaheadArrayLength; i++ )
    {
	varnr = lookaheadArray[i];
        if( NodeType[  varnr ] == LOOSELEAF )
	{	order_nodes_rec( varnr); }
        if( NodeType[ -varnr ] == LOOSELEAF )
        {	order_nodes_rec(-varnr); }
    }

    initvs();
    K = 0;
    /* execute detect_strong_component on all nodes */
    for(i = N; i >= 1 ; i--)
    	if( NodeType[fai_[i]] == ORDEREDLEAF )
	{
	    if( detect_strong_component(fai_[i]) == 0 )
	    {
    		for( i = lookaheadArrayLength; i--; )
    		{
       		    varnr = lookaheadArray[i];
		    NodeType[ -varnr ] = USEDNODE;
        	    NodeType[  varnr ] = USEDNODE;
    		}
		return 0;
	    }
	}

   /* phase 2 */
   for( i = K; i >= 1; i--)
   {
   	varnr = comp_[i];

#ifdef OLDTREES
	if( NodeType[ varnr ] == STRONGLEAF )
	{   create_tree_rec( varnr );
	    looklist_rec( varnr );    }
    }
#else
	crtree( varnr );
    }

    /* phase 3 */
    for( i = 0; i < nrofroots; i++ )
    {
	varnr = fai_[i];
	calc_tree_size_rec( varnr );
	looklist_rec( varnr );
    }
#endif

    assert( (tree_elements % 2) == 0 );

    return 1;
}

#ifndef NEW
/***********************************************************

	create_tree_rec(int nrval) creates trees in a
	recursive manner.

***********************************************************/

void create_tree_rec( int nrval )
{
    int i, *bImp, tree_size, incoming;
    struct assignment *parent;

    tree_size = 1;				// initinal tree_size = 1 (counted form this level downwards)
    NodeType[ nrval ] = USEDNODE;		// now the node (root) is used NOW (is in current tree)
    parent = &assignment_array[ nrval ];	// it is own parent
    parent->nr_incoming = 0;			// no childeren yet
    parent->parent = 0;				// no parent yet

    bImp = BIMP_START(-nrval);			// bImp is pointer to all implications to 'nrval'
    for( i = BIMP_ELEMENTS; --i; )		// loop though these implications
    {
	incoming = -(*(bImp++));			// current implication is 'incoming'
        if( NodeType[ incoming ] != USEDNODE )
	{
		ADD_INCOMING( parent, incoming );	// 'incoming' becomes a child of 'nrval' (parent)
#ifdef OLDTREES
		if( NodeType[ incoming ] == STRONGLEAF ) // if 'incoming' is not been visited yet then
#else
		if( NodeType[ incoming ] == LOOSELEAF ) // if 'incoming' is not been visited yet then
#endif
			create_tree_rec( incoming );	// recursively call create_tree_rec
		else					// else 'incoming' is a root of previously generated tree, so cut and past
		    	NodeType[ incoming ] = USEDNODE;
		tree_size += (&assignment_array[ incoming ])->tree_size; //tree_size is increased by tree_size of 'incoming'
		(&assignment_array[ incoming ])->parent = nrval; 	 // parent of 'incoming' becomes 'nrval'
	}
    }
    parent->tree_size = tree_size; 		// tree_size = treesize of this level downwards
}

/*********************************************************

	looklist_rec( int nrval ) fills the treeArray
	structure.

**********************************************************/
#endif

int calc_tree_size_rec( const int nrval )
{
    int i;
    struct assignment *assignment = &assignment_array[ nrval ];

    assignment->tree_size = 1;

    for( i = assignment->nr_incoming; i--; )
         assignment->tree_size += calc_tree_size_rec( assignment->incoming[i] );

    return(assignment->tree_size);
}

void looklist_rec (int nrval) {
    int i, current;
    struct assignment *assignment = &assignment_array[ nrval ];

    current = assignment->tree_size - 1 + nrgiven;

    treeArray[ tree_elements   ].literal = nrval;
    treeArray[ tree_elements++ ].gap = 2 * current;

    for( i = assignment->nr_incoming; i--; )
        looklist_rec( assignment->incoming[i] );

    if( current == nrgiven )
        nrgiven++; }
