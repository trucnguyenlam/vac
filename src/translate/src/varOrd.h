#ifndef VARORD_H
#define VAR ORD_H

#include<stdlib.h>
#include<stdio.h>

// DEFINED TYPES
typedef struct graph_el vertex;

struct list_el {
       vertex *vert;
       struct list_el *next;
};

typedef struct list_el item;

struct sList{
	item *head;
	item *tail;
};

typedef struct sList linkedList;

struct graph_el{
       int val;
       int weight;
       int visited;
       int nop;  //number of predecessors
//       int id;  //debug
       linkedList* successors;
};

struct sGraph{
//	vertex *start;
	linkedList* vertices;
};

typedef struct sGraph graph;

// END DEFINED TYPES

graph* createDependencyGraph(void);  //test case
linkedList* variableOrdering(graph*,int);    //it computes a variable ordering 
graph* newGraph(); // it creates a new and empty dependancy graph
vertex* addNode(graph *g, int i); // it adds a new node to the dependency graph
void addEdge(graph *g,int i,int j); // it adds a new edge to the dependency graph

// prototypes of utility routines


void salvatore(graph*,linkedList*);

void resetVisited(graph*);
void connectedPreorderVisit(vertex*);
vertex* searchV(graph*, int);
void printList(linkedList*);

#endif
