#ifndef _ARBACSimplify_H
#define _ARBACSimplify_H

#include "ARBACUtil.h"
#include "ARBACData.h"
#include "ARBACLexer.h"
#include "ARBACParser.h"

typedef struct _Trace
{
	/**
	 * Simplify rule identification
	 * 0 : slicing forward
	 * 1 : slicing backward
	 * 2 : pruning rule non-positive
	 * 3 : pruning rule non-negative
	 * 4 : pruning rule mixed
	 * 5 : pruning rule combinable
	 * 6 : pruning rule implied
	 * 7 : pruning rule non-fireable
	 */
	int simplify_rule;

	/**
	 * -1 : if not affected
	 */
	int affected_role_index;
	/**
	 * -1 : if not affected
	 */
	int affected_rule_index;
	int affected_rule_type;
	/**
	 * -1 : if has no related rule
	 */
	int related_rule_index;
	int related_rule_type;
} Trace;

Trace * trace_array;
int trace_array_size;

// One of the user will become super user
set promoted_users;

// Log file of the program
FILE *tmplog;
FILE *simplifyLog;

// Define the slicing function of ReduceAdmin algorithm
int
slicing();
// Define the aggressive_pruning function of ReduceAdmin algorithm
int
aggressive_pruning();
// Define the immaterial function of ReduceAdmin algorithm
int
immaterial();

// Check for trivial policy
int
precheck(int, char *);

void
drop_role_precondition(int, int);

// Logging purpose
void
print_ca_rule(int);

char *
get_role(int);
char *
get_user(int);
void
read_ARBAC(char *);
void
write_ARBAC(char *);

void
generateADMIN(void);
void
write_ARBACMOHAWK(char *);

void
reduction_finiteARBAC(void);

// Free data structure
void
free_data();

#endif
