#ifndef _ARBACData_H
#define _ARBACData_H

#include "containers.h"

// A user role assignment element
typedef struct __UA
{
	int user_index;
	int role_index;
} _UA;
// A can_revoke element
typedef struct __CR
{
	int admin_role_index;
	int target_role_index;
} _CR;
// A can_assign element
typedef struct __CA
{
	/* Determination for the rule with TRUE or NEW in precondition */
	int type;
	int admin_role_index;
	int *positive_role_array;
	int positive_role_array_size;
	int *negative_role_array;
	int negative_role_array_size;
	int target_role_index;
} _CA;
//Define the role array
char **role_array;
int role_array_size;
//Define the user array
char **user_array;
int user_array_size;
//Define array of user role assignment
_UA *ua_array;
int ua_array_size;
//Define array of can_revoke rules
_CR *cr_array;
int cr_array_size;
//Define array of can_assignment rules
_CA *ca_array;
int ca_array_size;
//Define the admin user array
int *admin_array_index;
int admin_array_index_size;
//Define the admin role array
int *admin_role_array_index;
int admin_role_array_index_size;
//Define the specification
int goal_user_index;
int goal_role_index;
char* goal_temp;
// Variable to determine the positive or negative property of role
int iNeg;

// Variable to indicate mode to translate
int hasNewUserMode;
int * initialize_role_array;
int initialize_role_array_size;
int * new_rule_array;
int new_rule_array_size;



int hasGoalUserMode;

Dictionary *role_dict;
Dictionary *user_dict;

// Functions support
void
create_role_dict();
void
create_user_dict();
int
find_role_from_dict(char*);
int
find_user_from_dict(char*);

#endif
