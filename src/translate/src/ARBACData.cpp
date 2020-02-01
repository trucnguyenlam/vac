#include "ARBACData.h"

//Define the role array
char **role_array;
int role_array_size;

//Define the user array
char **user_array;
int user_array_size;

// Define new user array
int hasNewUserMode;
_NEWUSER * newuser_array;
int newuser_array_size;

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
int hasGoalUserMode;
int goal_user_index;
int goal_role_index;
int goalUserIsNew;

// Temporary variable
char * goal_temp;
// Variable to determine the positive or negative property of role
int iNeg;
// Indicate the super user in the ARBAC system
int super_exist;

int *promoted_user_array;
int promoted_user_array_size;

Dictionary *role_dict;
Dictionary *user_dict;
Dictionary *newuser_dict;