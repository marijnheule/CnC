#include "common.h"

struct assignment {
    int *incoming;
    int incoming_size;
    int nr_incoming;
    int tree_size;
    int parent;
    int varnr;
};

struct assignment *assignment_array;
int node_stamp, tree_stamp, changed;

void init_tree();
void dispose_tree();
int treebased_lookahead();
void create_tree_rec( int nrval );
int calc_tree_size_rec( const int nrval );
void looklist_rec( int nrval );

int nrgiven;
int minpos;
int lastCTS;

int complement_value;
int impgiven;

#define ADD_INCOMING( __parent, __incoming ) \
{ \
	if( __parent->nr_incoming == __parent->incoming_size ) \
	{\
	    __parent->incoming_size *= 2; \
	    __parent->incoming = (int*)realloc(__parent->incoming, __parent->incoming_size*sizeof(int));\
\
	}\
	__parent->incoming[__parent->nr_incoming++] = __incoming; \
}


#define initvs() vindex = 0 
#define vpush(x)  vstack[ ++vindex ] = x  
#define vpop()  ( vstack[ vindex -- ] ) 
#define emptys() ( ( vindex >= 1 )?0:1 ) 


