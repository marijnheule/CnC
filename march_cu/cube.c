/*
   MARCH Satisfiability Solver
   Copyright (C) 2001-2005 M.J.H. Heule, J.E. van Zwieten, and M. Dufour.
   Copyright (C) 2005-2017 M.J.H. Heule. [marijn@heule.nl]

   This file contains the code for cube-and-conquer
*/

#include <stdio.h>
#include <stdlib.h>

#include "cube.h"
#include "common.h"

FILE *cubes;

int *cubeTrail;
int nrofDnodes;
int Dnodes_size;
struct Dnode *Dnodes;
int _nr_cubes;

int num_refuted, num_cubes;
long long sum_refuted, sum_cubes;

int getNodes () {
  return num_cubes + num_refuted; }

int Dnode_left (int index) {
  return Dnodes[ index ].left; }

int Dnode_right (int index) {
  return Dnodes[ index ].right; }

void Dnode_setType (int index, int type) {
  Dnodes[ index ].type = type; }

void Dnode_setWeight (int index, int weight) {
  Dnodes[ index ].weight = weight; }

void Dnode_setDecision (int index, int decision) {
  Dnodes[ index ].decision = decision; }

void Dnode_close (int index) {
  if ((Dnodes[Dnodes[index].left ].type == REFUTED_DNODE) &&
      (Dnodes[Dnodes[index].right].type == REFUTED_DNODE))
    Dnodes[index].type = REFUTED_DNODE;
  else Dnodes[index].type = INTERNAL_DNODE; }

int Dnode_new () {
  nrofDnodes++;
  Dnodes[ nrofDnodes ].type  = REFUTED_DNODE;
  return nrofDnodes; }

void Dnode_init (int index) {
  Dnodes[index].index = index;
  Dnodes[index].left  = Dnode_new();
  Dnodes[index].right = Dnode_new();
  Dnodes[index].type  = INTERNAL_DNODE;

  if (nrofDnodes + 3 > Dnodes_size) {
    Dnodes = (struct Dnode*) realloc (Dnodes, sizeof(struct Dnode) * Dnodes_size * 2);
    int i; for (i = Dnodes_size; i < 2 * Dnodes_size; i++) {
      Dnodes[i].weight   = 0;
      Dnodes[i].index    = 0;
      Dnodes[i].left     = 0;
      Dnodes[i].right    = 0;
      Dnodes[i].decision = 0;
      Dnodes[i].type     = 0; }
    Dnodes_size *= 2; } }

void init_assumptions () {
  nrofDnodes  =   1;
  Dnodes_size = 100;
  Dnodes = (struct Dnode*) malloc (sizeof(struct Dnode) * Dnodes_size);
  int i; for (i = 0; i < Dnodes_size; i++) {
    Dnodes[i].weight   = 0;
    Dnodes[i].index    = 0;
    Dnodes[i].left     = 0;
    Dnodes[i].right    = 0;
    Dnodes[i].decision = 0;
    Dnodes[i].type     = 0; } }

void printWeights (struct Dnode Dnode) {
  if (Dnode.type == REFUTED_DNODE) {
    num_refuted++;
    sum_refuted += (long long) Dnode.weight; }
  else if (Dnode.type == CUBE_DNODE) {
    num_cubes++;
    sum_cubes += (long long) Dnode.weight; }
  else {
    printWeights (Dnodes[Dnode.left ]);
    printWeights (Dnodes[Dnode.right]); } }

void printDecisionNode (struct Dnode Dnode, int depth, int discrepancies, int target) {
  if (Dnode.type != INTERNAL_DNODE) {
    if ((target == -1) || (discrepancies == target)) {
      _nr_cubes++;
      fprintf (cubes, "a ");
      int i; for (i = 0; i < depth; i++)
	fprintf (cubes, "%d ", cubeTrail[ i ] );
      fprintf (cubes, "0\n" ); }
    return; }

#ifndef FLIP_ASSUMPTIONS
  cubeTrail[depth] = Dnodes[Dnode.left].decision;
  printDecisionNode (Dnodes[Dnode.left ], depth+1, discrepancies+1, target);
#endif
  cubeTrail[depth] = Dnodes[Dnode.right].decision;
  printDecisionNode (Dnodes[Dnode.right], depth+1, discrepancies, target);
#ifdef FLIP_ASSUMPTIONS
  cubeTrail[depth] = Dnodes[Dnode.left].decision;
  printDecisionNode (Dnodes[Dnode.left ], depth+1, discrepancies+1, target);
#endif
}

void printUNSAT () {
  if (quiet_mode) cubes = stdout;
  else            cubes = fopen (cubesFile, "w");
  if (quiet_mode == 0)
    printf  ("c number of cubes 1, including 1 refuted leaf\n");
  fprintf (cubes, "a 0\n");
  if (quiet_mode == 0)
    fclose (cubes); }

void filterTree (int limit) {
  int i;
  int *filter = (int*) malloc (sizeof(int) * limit);
  filter[0] = 1;
  int t; for (t = 1; t < limit; t++) {
    int max = 0, flag = 0;
    for (i = 0; i < t; i++) {
      if (Dnodes[filter[i]].type != INTERNAL_DNODE) continue;
      if (Dnodes[filter[i]].weight >= Dnodes[filter[max]].weight) {
        flag = 1; max = i; } }
    if (flag == 0) break;
    filter[ t ] = Dnodes[filter[max]].right;
    filter[max] = Dnodes[filter[max]].left; }

  for (i = 0; i < t; i++)
    Dnodes[filter[i]].type = FILTER_DNODE; }

void printDecisionTree () {
  if (mode == PLAIN_MODE) return;
  int i;
  int discrepancy_search = 0;

#ifdef DISCREPANCY_SEARCH
  discrepancy_search = 1;
#endif
  if (Dnodes[1].type == REFUTED_DNODE) return printUNSAT ();

  cubeTrail = (int*) malloc(sizeof(int) * nrofvars);
  for (i = 0; i < nrofvars; i++) cubeTrail[i] = 0;

  if (quiet_mode) cubes = stdout;
  else            cubes = fopen (cubesFile, "w");

  if (quiet_mode == 0)
    printf("c print learnt clauses and cubes\n");

  _nr_cubes   = 0;
  num_refuted = 0;
  num_cubes   = 0;
  sum_refuted = 0;
  sum_cubes   = 0;
  printWeights (Dnodes[1]);

  if (quiet_mode == 0) {
    printf("c number of cubes %i, including %i refuted leaves\n", num_cubes + num_refuted, num_refuted);
    printf("c average weight cubes %.3f, average weights leaves %.3f\n", sum_cubes / (float) num_cubes, sum_refuted / (float) num_refuted); }

  if (cubeLimit)
    filterTree (cubeLimit);

  if (discrepancy_search) {
    int target = 0;
    do {
      printDecisionNode (Dnodes[1], 0, 0, target++); }
    while (_nr_cubes != nr_cubes); }
    else printDecisionNode (Dnodes[1], 0, 0, -1);
  if (quiet_mode == 0)
    fclose (cubes);
  free (cubeTrail);
}
