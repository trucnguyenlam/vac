#include "varOrd.h"

//int nodes=0;  //debug

// Operations on the data types items and vertex

linkedList* newLinkedList() {
   linkedList *newL;
   newL=(linkedList *)malloc(sizeof(linkedList));
   newL->head = NULL;
   newL->tail = NULL;
   return newL;
}

int isEmptyList(linkedList *list) {
   if (list->head == NULL)
      return 1;
   return 0;
}

item* newItem(vertex* newV) {
   item *newI;
   newI=(item *)malloc(sizeof(item));
   newI->vert = newV;
   newI->next = NULL;
   return newI;
}


vertex* newVertex(int val){
      vertex *curr;
      curr = (vertex *)malloc(sizeof(vertex));
      curr->val = val;
      curr->successors  = newLinkedList();
      curr->visited=0;
      curr->weight = 0;
      curr->nop = 0;
     // curr->id = nodes++;  // debug
      //printf("New node for v%d\n",val);  // debug
      return curr;
}

graph* newGraph(){
	graph* g;
	g = (graph *)malloc(sizeof(graph));
	g->vertices = newLinkedList();

	return g;
}


// adds newI after i

void addNodeList(item *newI, item *i){

      if (i == NULL)
         newI->next = NULL;
      else {
          newI->next = i->next;
          i->next = newI;
      }
}


void addHeadNodeList(item *i, linkedList* l){

      i->next  = l->head;
      l->head = i;
      if (l->tail == NULL)
         l->tail = i;
   }

void addTailNodeList(item* newI, linkedList* l){
         addNodeList(newI,l->tail);
         l->tail = newI;
         if (l->head == NULL)
            l->head = l->tail;
}



//  vertex* addNode(vertex* g, int i)
//  aggiunge un vertice di indice i come primo elemento del grafo g e
//  restituisce il suo indirizzo

vertex* addNode(graph *g, int i){

    vertex *newV;
    item *newI;

    newV=searchV(g,i);
    if (newV!= NULL) return newV;
    newV=newVertex(i);
    newI=newItem(newV);
    //if(isEmptyList(g->vertices)) printf("Empty graph!!\n");  // debug
    addHeadNodeList(newI, g->vertices);
    //if(isEmptyList(g->vertices)) printf("Empty graph after!!\n");  // debug

    return newV;

   }




//  void addEdge(graph* g, int i, int j)
// aggiunge un arco dal vertice di indice i al vertice
//   di indice j nel grafo g (se un vertice non e'
//     presente nel grafo lo inserisce, inserisce l'arco solo se non
//     non e' gia' presente nel grafo)

vertex* searchV(graph *g, int i){
        item *curr;

        if (isEmptyList(g->vertices)) {
//		printf("List is empty\n");   //debug
  		return NULL;
	}
	//printf("List is not empty\n");  //debug

        curr = (g->vertices)->head;

        while (curr != NULL) {
            if ((curr->vert)->val == i) return curr->vert;
            curr = curr->next;
        }
	//printf("Vertex not found!\n");
        return NULL;
}

item* searchI(linkedList* l, vertex* v){
        item *curr;

        if (isEmptyList(l)) return NULL;

        curr = l->head;
        while (curr != NULL) {
            if (curr->vert == v) return curr;
            curr = curr->next;
        }

        return NULL;
}

void addEdge(graph *g,int i,int j){
     vertex *I, *J;
     item* itemJ;

     //printf("Search for v%d\n",i);  //debug
     I=searchV(g,i);

     if (I == NULL) I=addNode(g,i);

     //printf("Search for v%d\n",j);  //debug
     J=searchV(g,j);

     if (J == NULL) J=addNode(g,j);

     if (searchI(I->successors,J)== NULL){
        itemJ = newItem(J);
        addHeadNodeList(itemJ,I->successors);
	(itemJ->vert)->nop++;
	//printf("Added new Edge\n"); // debug
      }
}

// utility

void connectedPreorderVisit (vertex *g){
     item *succ;

     printf("v%d\n", g->val);
     g->visited=1;
     succ = (g->successors)->head;
     while ( succ!= NULL) {
           if ((succ->vert)->visited==0)
               connectedPreorderVisit(succ->vert);
           succ = succ->next;
     }
}


void printList(linkedList *l){
    item* curr;

    curr= l->head;

    while (curr != NULL){
          printf("v%d  weight=%d  nop=%d\n", (curr->vert)->val,
		(curr->vert)->weight, (curr->vert)->nop);
          curr = curr->next;
    }

    printf("\n");
}

// constructing a graph instance
graph* createDependencyGraph(){
     graph *g;
     int i;

     g=newGraph();
     for (i=1;i<=5;i++) addNode(g,i);

//     addEdge(g,1,2);
//     addEdge(g,1,3);
//     addEdge(g,2,4);
//     addEdge(g,4,3);
//     addEdge(g,4,1);
//     addEdge(g,3,5);

     addEdge(g,1,2);
     addEdge(g,1,3);
     addEdge(g,2,4);
     addEdge(g,3,4);
     addEdge(g,2,5);

     return g;

}

void orderByWeights(linkedList*);
void visit(vertex*, linkedList*);
void breakCycles(graph*);
void genericSuccessorsOrdering(graph*, int);
void computeWeights(graph *);
void resetWeights(graph*);

linkedList* variableOrdering(graph *g,int choice){

     item *currItem;
     linkedList *orderedList;
     vertex *v;
     int i;

     breakCycles(g);

     resetWeights(g);
     computeWeights(g);
     genericSuccessorsOrdering(g, choice);
     orderByWeights(g->vertices);
     resetVisited(g);
     orderedList= newLinkedList();

     currItem = (g-> vertices)->head;
     while (currItem!= NULL) {
           if ((currItem->vert)->visited == 0) visit(currItem->vert,orderedList);
           currItem = currItem->next;
     }

     return orderedList;

}

void removeNode(linkedList *l, item* preSucc, item* cSucc){
	if (preSucc == NULL)
		l->head = cSucc->next;
	else
		preSucc->next = cSucc->next;

}

void bCycles(vertex* curr){

     item *cSucc, *preSucc;

     curr->visited=1;
    // printf("Visited v%d\n", curr->val); //debug
     preSucc = NULL;
     cSucc = (curr->successors)->head;

     while ( cSucc!= NULL) {
           if ((cSucc->vert)->visited==0){
               bCycles(cSucc->vert);
		preSucc = cSucc;
	   }
	   else if ((cSucc->vert)->visited==1){   //found a loop
//		printf("Loop through v%d\n",(cSucc->vert)->val);
		removeNode(curr->successors, preSucc,cSucc);
//		printList(curr->successors);
	   }
           cSucc = cSucc->next;
     }
    curr->visited=2;

}

void breakCycles(graph* g){
	item* curr;

	resetVisited(g);
	curr = (g->vertices)->head;


	while(curr!=NULL) {
		if( (curr->vert)->visited == 0) bCycles(curr->vert);
		curr=curr->next;
	}

}

void visit(vertex *curr, linkedList *l){
     item *succ;

     curr->visited=1;
     succ = (curr->successors)->head;
     while (succ != NULL) {
           if ((succ->vert)->visited == 0)
                visit(succ->vert,l);
	   succ = succ->next;
     }

     succ = newItem(curr);
     addTailNodeList(succ,l);
}


int weight(vertex *ver){
     item *succ;
     int w=0;

     succ = (ver->successors)->head;

     ver->visited=1;

     while (succ!=NULL) {
       	if ((succ->vert)->visited == 0) {
           	w++;
	   	w+=weight(succ->vert);
	}
	succ = succ->next;
     }
     return w;

}


void computeWeights(graph* g){

     item *curr;
     curr = (g->vertices)->head;

     while (curr != NULL) {
          resetVisited(g);
          (curr->vert)->weight=weight(curr->vert);
          curr = curr->next;
     }

}

void insert(linkedList *l, item *newI){

    item* prev;
    item* curr;

    curr = l->head;
    if ((newI->vert)->weight >= (curr->vert)->weight) {
       addHeadNodeList(newI,l);
       return;
    }

    prev=curr;
    curr=prev->next;

    while (curr != NULL && (curr->vert)->weight > (newI->vert)->weight){
          prev =curr; curr=prev->next;
    }

    if (curr != NULL)
       addNodeList(newI,prev);
    else
       addTailNodeList(newI,l);
}

void orderByWeights(linkedList* list){
     item *curr, *next;

     if (isEmptyList(list)) return;

     curr = (list->head)->next;
     list->tail = list->head;
     (list->tail)->next = NULL;

     while( curr != NULL) {
            next=curr->next;
            insert(list,curr);
            curr=next;
     }
}

void resetVisited(graph* g){
     item *curr;

     curr= (g->vertices)->head;
     while (curr != NULL){
           (curr->vert)->visited = 0;
           curr = curr->next;
     }
}

void resetWeights(graph* g){
     item *curr;

     curr= (g->vertices)->head;
     while (curr != NULL){
           (curr->vert)->weight = 0;
           curr = curr->next;
     }
}


// more heuristics for variable ordering

void orderSuccessorsByWeights(graph *g){

     item *curr, *next;

     if (isEmptyList(g->vertices)) return;

     curr = (g->vertices)->head;

     while( curr != NULL) {
            next=curr->next;
            orderByWeights((curr->vert)->successors);
            curr=next;
     }


}



// It compares vertices according to different criteria:
//   choice=1 means compare by weights
//   choice=2 means compare by weights and then by inverse nop
//   choice=3 means compare by difference of weights plus nop

int compare(vertex* v1,vertex* v2, int choice){

	int answer;

	switch(choice){
		case 1:
			if (v1->weight > v2->weight)
				return 1;
			else if (v1->weight < v2->weight)
					return -1;
			else return 0;
			break;
		case 2:
			if (v1->weight > v2->weight)
                                return 1;
                        else if (v1->weight < v2->weight)
                                        return -1;
                        else if (v1->nop < v2->nop)
				return 1;
			else if (v1->nop > v2->nop)
				return -1;
			else return 0;
			break;
		case 3:
			if (v1->weight-v1->nop > v2->weight-v2->nop)
				return 1;
			else if (v1->weight-v1->nop < v2->weight-v2->nop)
					return -1;
			else return 0;
			break;
		default:

	return 0;
	}


}

void genericInsert(linkedList *l, item *newI,int sortCriteria){

    item* prev;
    item* curr;

    curr = l->head;
    if (compare(newI->vert,curr->vert,sortCriteria) >= 0) {
       addHeadNodeList(newI,l);
       return;
    }

    prev=curr;
    curr=prev->next;

    while (curr != NULL && compare(curr->vert, newI->vert,sortCriteria)>0){
          prev =curr; curr=prev->next;
    }

    if (curr != NULL)
       addNodeList(newI,prev);
    else
       addTailNodeList(newI,l);
}

void genericListSorting(linkedList* list, int sortingCriteria){
     item *curr, *next;

     if (isEmptyList(list)) return;

     curr = (list->head)->next;
     list->tail = list->head;
     (list->tail)->next = NULL;

     while( curr != NULL) {
            next=curr->next;
            genericInsert(list,curr,sortingCriteria);
            curr=next;
     }
}

void genericSuccessorsOrdering(graph *g, int criteria){

     item *curr, *next;

     if (isEmptyList(g->vertices) || criteria == 0) return;

     curr = (g->vertices)->head;

     while( curr != NULL) {
            next=curr->next;
            genericListSorting((curr->vert)->successors,criteria);
            curr=next;
     }


}

// debugging

void recSuccList(vertex *ver){
     item *succ;

     succ = (ver->successors)->head;

     ver->visited=1;

     while (succ!=NULL) {
       	if ((succ->vert)->visited == 0) {
		printf("v%d ",(succ->vert)->val);
	   	recSuccList(succ->vert);
	}
	succ = succ->next;
     }

}

void salvatore(graph *g,linkedList *l){
/*  	vertex *v;
	int i;
	//printList(g->vertices);
	printList(l);

/*	printf("\nStart\n");
	for (i=1;i<=42; i++){
		v=searchV(g,i);
		printf("\nSuccessors of v%d (weight=%d): \n",i,v->weight);
        	printList(v->successors);
	}
	printf("\nEnd\n");
*/
}
