/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]
*/

#define INTERNAL_DNODE	3
#define	REFUTED_DNODE	4
#define CUBE_DNODE	5
#define FILTER_DNODE	6

struct Dnode {
  int index;
  int left;
  int right;
  int decision;
  int type;
  int weight;
};

void init_assumptions ();

void Dnode_setDecision (int index, int decision);
void Dnode_setType     (int index, int type    );
void Dnode_setWeight   (int index, int weight  );

int  Dnode_new   (         );
int  Dnode_left  (int index);
int  Dnode_right (int index);
void Dnode_init  (int index);
void Dnode_close (int index);

int  getNodes ();
void printDecisionNode (struct Dnode Dnode, int depth, int dis, int max);
void printUNSAT ();
void printDecisionTree ();
