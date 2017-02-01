#ifndef _ARBACData_H
#define _ARBACData_H

// CCL library
#include "containers.h"

// Define Data Structure of the ARBAC system

typedef struct __NEWUSER
{
	char * name;
	int * role_array;
	int role_array_size;
} _NEWUSER;

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
	int admin_role_index;
	/* Determination for the rule with TRUE or NEW in precondition */
	int type;
	int *positive_role_array;
	int positive_role_array_size;
	int *negative_role_array;
	int negative_role_array_size;
	int target_role_index;
} _CA;

//Define the role array
extern char **role_array;
extern int role_array_size;

//Define the user array
extern char **user_array;
extern int user_array_size;

// Define new user array
extern int hasNewUserMode;
extern _NEWUSER * newuser_array;
extern int newuser_array_size;

//Define array of user role assignment
extern _UA *ua_array;
extern int ua_array_size;

//Define array of can_revoke rules
extern _CR *cr_array;
extern int cr_array_size;

//Define array of can_assignment rules
extern _CA *ca_array;
extern int ca_array_size;

//Define the admin user array
extern int *admin_array_index;
extern int admin_array_index_size;

//Define the admin role array
extern int *admin_role_array_index;
extern int admin_role_array_index_size;

//Define the specification
extern int hasGoalUserMode;
extern int goal_user_index;
extern int goal_role_index;
extern int goalUserIsNew;

// Temporary variable
extern char * goal_temp;
// Variable to determine the positive or negative property of role
extern int iNeg;
// Indicate the super user in the ARBAC system
extern int super_exist;

extern int *promoted_user_array;
extern int promoted_user_array_size;

extern Dictionary *role_dict;
extern Dictionary *user_dict;
extern Dictionary *newuser_dict;

// Functions support
void
create_role_dict();
void
create_user_dict();
void
create_newuser_dict();
int
find_role_from_dict(char*);
int
find_user_from_dict(char*);
int
find_newuser_from_dict(char*);

#endif
