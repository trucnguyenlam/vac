#ifndef _ARBACUtil_H
#define _ARBACUtil_H

typedef struct _set
{
	int * array;
	int array_size;
} set;

int
belong_to(int *, int, int);
int
index_of(int, int *, int);
int
subset_of(set, set);
int
equal_set(set, set);
set
add_element(set, int);
set
add_last_element(set, int);
set
remove_element(set, int);
set
union_set(set, set);
set
intersect_set(set, set);
set
different_set(set, set);
set
duplicate_set(set);
set
build_set(int *, int);
#endif
