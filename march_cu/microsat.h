struct solver { // The variables in the struct are described in the allocate procedure
  int  *DB, nVars, nClauses, mem_used, mem_fixed, mem_max, maxLemmas, nLemmas, *buffer,
       *assumptions, *assumeHead, nConflicts, *model, *reason, *falseStack,
       *false, *first, *forced, *processed, *assigned, *next, *prev, head, res, set, not; };

int* addClause        (struct solver* S, int* array, int size, int ir);
void initCDCL         (struct solver* S, int nVars, int nClauses);
int  solve            (struct solver* S, int limit);
void resetAssumptions (struct solver* S);
void assume           (struct solver* S, int lit);
int  getModel         (struct solver* S, int var);
