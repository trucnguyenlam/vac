#ifndef _CounterExampleData_H
#define _CounterExampleData_H

// A element for store an assignment in CBMC XML Log Data
typedef struct _CBMCAssignment
{
	int line;
	int track_user;
	int value;
	char* role;
	int type;
} CBMCAssignment;
CBMCAssignment * assignment_array;
int assignment_array_size;

// CBMC Translated Data
int declaration_lim;
int initialize_lim;
int configuration_lim;

typedef struct _RuleTranslated
{
	int line;
	int rule_number;
	int rule_type; // 0 mean CA, 1 mean CR
} RuleTranslated;
RuleTranslated * rule_translated_array;
int rule_translated_array_size;

typedef struct _Configuration_user
{
	int line;
	char *user_name;
	int rule_index;
} Configuration_user;

Configuration_user *user_configuration_array;
int user_configuration_array_size;

// Simplification Map data
typedef struct _map
{
	int origin;
	int after;
} map;

// Associate each user with track user
typedef struct _Translated_user
{
	char *user_name;
	int track_user;
	int *config_array;
	int config_array_size;
} Translated_user;

Translated_user *user_translated_array;
int user_translated_array_size;

// Trace data for counter example
typedef struct _Trace
{
	char *administrative_user;
	char *target_user;
	int rule_number;
	int rule_type;
	int *config_array;
	int config_array_size;
	int *config_array_before;
	int config_array_before_size;

} Trace;

Trace *trace_array;
int trace_array_size;

Trace *original_trace_array;
int original_trace_array_size;

// Map index of this array to the original role index
int * role_map_array;
int role_map_array_size;

// Map index of this array to the original role index
int * user_map_array;
int user_map_array_size;

// Map index of this rule to the original rule index
int * ca_map_array;
int ca_map_array_size;

// Map index of this rule to the original rule index
int * cr_map_array;
int cr_map_array_size;

// Store a step of simplification
typedef struct _Step
{
	/**
	 * Simplify rule identification
	 * 0 : slicing forward
	 * 1 : slicing backward
	 * 2 : pruning rule non-positive
	 * 3 : pruning rule non-negative
	 * 4 : pruning rule mixed
	 * 5 : pruning rule combinable
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
} Step;

Step * simplify_steps;
int simplify_steps_size;

// // For produce counter example
// typedef struct _Rule_Collected
// {
// 	int rule_index;
// 	int rule_type;
// 	int level;
// } Rule_Collected;

// typedef struct _RuleCollectedSet
// {
// 	Rule_Collected * array;
// 	int array_size;
// } RuleCollectedSet;

typedef struct Array
{
	int * array;
	int array_size;
} Array;

typedef struct Pair
{
	int v1;
	int v2;
} Pair;

typedef struct Node
{
	int * siblings;
	int siblings_size;
	int level;
} Node;

typedef struct RelatedRules
{
	int * related;
	int related_size;
	int rule_index;
} RelatedRules;


// typedef struct NodeArray
// {
// 	Node * array;
// 	int array_size;
// } NodeArray;

#endif
