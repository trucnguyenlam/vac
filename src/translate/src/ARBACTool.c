#include "ARBACLexer.h"
#include "ARBACParser.h"
#include "ARBACTransform.h"
#include "ARBACUtil.h"

/**
 * Combinatoric
 */

int gen_comb_norep_lex_init(int *vector, const int n, const int k)
{
	int j; //index

//test for special cases
	if (k > n)
		return (3);

	if (k == 0)
		return (2);

//initialize: vector[0, ..., k - 1] are 0, ..., k - 1
	for (j = 0; j < k; j++)
		vector[j] = j;

	return (0);
}

int gen_comb_norep_lex_next(int *vector, const int n, const int k)
{
	int j; //index

//easy case, increase rightmost element
	if (vector[k - 1] < n - 1)
	{
		vector[k - 1]++;
		return (0);
	}

//find rightmost element to increase
	for (j = k - 2; j >= 0; j--)
		if (vector[j] < n - k + j)
			break;

//terminate if vector[0] == n - k
	if (j < 0)
		return (1);

//increase
	vector[j]++;

//set right-hand elements
	while (j < k - 1)
	{
		vector[j + 1] = vector[j] + 1;
		j++;
	}

	return (0);
}


// Create a dictionary of role
void
create_role_dict()
{
	int i;
	int *r_array = 0;

	r_array = malloc(role_array_size * sizeof(int));

	for (i = 0; i < role_array_size; i++)
	{
		r_array[i] = i;
	}

	role_dict = iDictionary.Create(sizeof(int *), role_array_size);

	for (i = 0; i < role_array_size; i++)
	{
		iDictionary.Add(role_dict, role_array[i], &r_array[i]);
	}
}

// create a dictionary of user
void
create_user_dict()
{
	int i;
	int *u_array = 0;
	u_array = malloc(user_array_size * sizeof(int));

	for (i = 0; i < user_array_size; i++)
	{
		u_array[i] = i;
	}

	user_dict = iDictionary.Create(sizeof(int *), user_array_size);

	for (i = 0; i < user_array_size; i++)
	{
		iDictionary.Add(user_dict, user_array[i], &u_array[i]);
	}
}

// create a dictionary of user
void
create_newuser_dict()
{
	int i;
	int *nu_array = 0;
	nu_array = malloc(newuser_array_size * sizeof(int));

	for (i = 0; i < newuser_array_size; i++)
	{
		nu_array[i] = i;
	}

	newuser_dict = iDictionary.Create(sizeof(int *), newuser_array_size);

	for (i = 0; i < newuser_array_size; i++)
	{
		iDictionary.Add(newuser_dict, newuser_array[i].name, &nu_array[i]);
	}
}


// Find a role index from dictionary by its name
int
find_role_from_dict(char *name)
{
	int *i;

	if (role_dict != NULL)
	{
		i = (int *) iDictionary.GetElement(role_dict, name);
	}
	else
	{
		return -1;
	}
	if (i == NULL)
	{
		fprintf(stderr, "error: cannot find role %s, please check the policy again\n", name);
		abort();
		return -1;
	}
	else
	{
		return *i;
	}
}

// Find a user index from dictionary by his name
int
find_user_from_dict(char *name)
{
	int *i;

	if (user_dict != NULL)
	{
		i = (int *) iDictionary.GetElement(user_dict, name);
	}
	else
	{
		return -1;
	}
	if (i == NULL)
	{
		return -1;
	}
	else
	{
		return *i;
	}
}

// Find a user index from dictionary by his name
int
find_newuser_from_dict(char *name)
{
	int *i;
	if (newuser_dict != NULL)
	{
		i = (int *) iDictionary.GetElement(newuser_dict, name);
	}
	else
	{
		return -1;
	}
	if (i == NULL)
	{
		return -1;
	}
	else
	{
		return *i;
	}
}

// Helper function to read the ARBAC file input
void
read_ARBAC(char * inputFile)
{
	pANTLR3_INPUT_STREAM input;
	pARBACLexer lex;
	pANTLR3_COMMON_TOKEN_STREAM tokens;
	pARBACParser parser;

	input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) inputFile);
	lex = ARBACLexerNew(input);
	tokens = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(lex));
	parser = ARBACParserNew(tokens);

	parser->parse(parser);

	// Manually free the resource
	parser->free(parser);
	tokens->free(tokens);
	lex->free(lex);
	input->close(input);
}

/**
 * Reduction of ARBAC system with infinite users into a finite one
 */
void
reduction_finiteARBAC(void)
{
	// For each user in NEW user, create k+1
	if (hasNewUserMode && newuser_array_size > 0)
	{
		int i;
		// Need k + 1 users in the system for each
		int NUM_USER = admin_role_array_index_size + 1;
		int old_user_array_size = user_array_size;
		user_array_size += NUM_USER * newuser_array_size;
		user_array = realloc(user_array, user_array_size * sizeof(char*));
		int old_ua_array_size;

		for (i = 0; i < newuser_array_size; i++)
		{
			char temp[2000];    // No way a username longer than 2000 characters
			old_ua_array_size = ua_array_size;
			ua_array_size += NUM_USER * newuser_array[i].role_array_size;
			ua_array = realloc(ua_array, ua_array_size * sizeof(_UA));

			// For each new user add k+1 new user to the system
			int j;
			for (j = 0; j < NUM_USER; j++)
			{
				int size = sprintf(temp, "NEWUSER%d_%s", j, newuser_array[i].name);
				user_array[old_user_array_size + i * NUM_USER + j] = malloc(size + 1);
				strcpy(user_array[old_user_array_size + i * NUM_USER + j], temp);
				// Add to ua_array
				int k;
				for (k = 0; k < newuser_array[i].role_array_size; k++)
				{
					ua_array[old_ua_array_size + j * newuser_array[i].role_array_size + k].user_index = old_user_array_size + i * NUM_USER + j;
					ua_array[old_ua_array_size + j * newuser_array[i].role_array_size + k].role_index = newuser_array[i].role_array[k];
				}
			}
		}
		// Change to SPEC if possible
		if (hasGoalUserMode && goalUserIsNew)
		{
			// Translation of index
			goal_user_index = old_user_array_size + goal_user_index * NUM_USER;
			goalUserIsNew = 0;
		}

		// Reseting things
		hasNewUserMode = 0;

		// Add these user to the dictionary
		if (user_dict != NULL);
		{
			iDictionary.Finalize(user_dict);
		}
		// create new dictionary for user
		create_user_dict();

		// Free data
		for (i = 0; i < newuser_array_size; i++)
		{
			free(newuser_array[i].name);
			newuser_array[i].name = 0;
			free(newuser_array[i].role_array);
			newuser_array[i].role_array = 0;
			newuser_array[i].role_array_size = 0;
		}
		free(newuser_array);
		newuser_array_size = 0;
		newuser_array = 0;
	}
}

/**
 * TODO: Remove unused user in the system
 */

set *configs;
int configs_size;

set *partition_users;
int partition_users_size;

set *equal_config_array;
int equal_config_array_size;

set immaterial_admins;

// Temporary variables
int max_user_config_size;
set temp_remain;

// Free the array of set
static void
free_array_set(set *sets, int sets_size)
{
	int i;

	// Free variable
	for (i = 0; i < sets_size; i++)
	{
		if (sets[i].array_size != 0)
		{
			free(sets[i].array);
			sets[i].array = 0;
		}
	}
	free(sets);
	sets = 0;
	sets_size = 0;
}

// Make the configuration set for each user
static void
make_configs()
{
	int i, j;
	int max = 0;

	// The array of each configuration for each user
	configs = calloc(user_array_size, sizeof(set));

	// Size equal to the user size
	configs_size = user_array_size;

	// Create user configuration arrays, removed user have empty configurations set
	for (i = 0; i < user_array_size; i++)
	{
		// If this is not a removed user
		if (strcmp(user_array[i], "removed_user") != 0)
		{
			configs[i].array = 0;
			configs[i].array_size = 0;
			for (j = 0; j < ua_array_size; j++)
			{
				// Not a removed user role combination
				if (ua_array[j].user_index != -13 && i == ua_array[j].user_index)
				{
					configs[i] = add_last_element(configs[i], ua_array[j].role_index);
				}
			}
		} // If this is a removed user
		else
		{
			configs[i].array = 0;
			configs[i].array_size = -1;
		}

		// Also find the maximum size of configuration
		if (max < configs[i].array_size)
		{
			max = configs[i].array_size;
		}
	}
	// Max size of a user configuration (the maximum number of roles associated to user)
	max_user_config_size = max;
}

// Partition the configuration sets of each user by their size
static void
partition_configs()
{
	int i;

	partition_users_size = max_user_config_size + 1;
	partition_users = calloc(partition_users_size, sizeof(set));

	for (i = 0; i < partition_users_size; i++)
	{
		partition_users[i].array = 0;
		partition_users[i].array_size = 0;
	}

	for (i = 0; i < configs_size; i++)
	{
		// If there are roles associate to that user, i  is a user index
		if (configs[i].array_size != -1)
		{
			// Add the user i to the partition config of size of the configuration of user i
			// All user with the same |ROLES| is add to the partition
			partition_users[configs[i].array_size] = add_last_element(partition_users[configs[i].array_size], i);
		}
	}
}

// Recursive function to partition the configuration set of each user
static void
process_configs_recur(set group, int size_config)
{
	int i;
	set tmp, equal;

	// Equal set
	equal.array = 0;
	equal.array_size = 0;

	if (group.array_size > 0)
	{
		if (size_config == 0)
		{
			equal_config_array_size++;
			equal_config_array = realloc(equal_config_array, equal_config_array_size * sizeof(set));
			equal_config_array[equal_config_array_size - 1] = build_set(group.array, group.array_size);
			return;
		}

		tmp = build_set(configs[group.array[0]].array, configs[group.array[0]].array_size);
		equal = add_last_element(equal, group.array[0]);

		for (i = 1; i < group.array_size; i++)
		{
			if (equal_set(configs[group.array[i]], tmp))
			{
				equal = add_last_element(equal, group.array[i]);
			}
		}

		equal_config_array_size++;
		equal_config_array = realloc(equal_config_array, equal_config_array_size * sizeof(set));
		equal_config_array[equal_config_array_size - 1] = build_set(equal.array, equal.array_size);

		free(tmp.array);
		tmp.array = 0;
		tmp = duplicate_set(group);
		free(temp_remain.array);
		temp_remain = different_set(tmp, equal);

		// Call recursive procedure in the remaining group
		process_configs_recur(temp_remain, size_config);
	}
	else
	{
		free(temp_remain.array);
		temp_remain.array = 0;
		return;
	}
}

// Process the configuration set of each user to find users with same role combination
static void
process_configs()
{
	int i;

	// Initialize all array of sets variable
	configs = 0;
	configs_size = 0;

	partition_users = 0;
	partition_users_size = 0;

	equal_config_array = 0;
	equal_config_array_size = 0;

	temp_remain.array = 0;
	temp_remain.array_size = 0;

	// Make array of user configuration
	make_configs();

	// Partition by number of roles in the configuration of each user
	partition_configs();

	for (i = 0; i < partition_users_size; i++)
	{
		process_configs_recur(partition_users[i], i);
	}
}

// Remove a user from ARBAC system
static int
remove_user(int user_index)
{
	int i;

	// Do not remove goal user
	if (hasGoalUserMode && goal_user_index != -13 && user_index == goal_user_index)
	{
		return 0;
	}

	// Remove from user array
	free(user_array[user_index]);
	user_array[user_index] = 0;
	user_array[user_index] = calloc(strlen("removed_user") + 1, sizeof(char));
	strcpy(user_array[user_index], "removed_user");

	// Remove from admin user array
	for (i = 0; i < admin_array_index_size; i++)
	{
		if (admin_array_index[i] != -13 && admin_array_index[i] == user_index)
		{
			admin_array_index[i] = -13;
		}
	}

	// Remove users from UA
	for (i = 0; i < ua_array_size; i++)
	{
		if (ua_array[i].user_index != -13 && ua_array[i].user_index == user_index)
		{
			ua_array[i].user_index = -13;
		}
	}

	return 1;
}

static void
reduction_user(void)
{
	// remove all user share the same configurations
	int i, j, flag = 0;

	int no_admins = admin_role_array_index_size;

	// For the set of users with the same role combination, remove the rest apart from K+1 users
	for (i = 0; i < equal_config_array_size; i++)
	{
		// Remove spare users
		for (j = no_admins + 1; j < equal_config_array[i].array_size; j++)
		{
			flag += remove_user(equal_config_array[i].array[j]);
		}
	}

	free_array_set(configs, configs_size);
	free_array_set(partition_users, partition_users_size);
	free_array_set(equal_config_array, equal_config_array_size);

	// Rebuild user array
	// Temporary array
	_UA *tmp_ua_array = 0;
	int tmp_ua_array_size = 0;
	char **tmp_user_array = 0;
	int tmp_user_array_size = 0;
	int *tmp_admin_array_index = 0;
	int tmp_admin_array_index_size = 0;

	int *map_user_index;
	int map_user_index_size;

	map_user_index_size = user_array_size;
	map_user_index = calloc(map_user_index_size, sizeof(int));

	// User array
	for (i = 0; i < user_array_size; i++)
	{
		if (strcmp(user_array[i], "remove_user") == 0)
		{
			map_user_index[i] = -1;
		}
		else
		{
			tmp_user_array_size++;
			tmp_user_array = realloc(tmp_user_array, tmp_user_array_size * sizeof(char *));
			tmp_user_array[tmp_user_array_size - 1] = calloc(strlen(user_array[i]) + 1, sizeof(char));
			strcpy(tmp_user_array[tmp_user_array_size - 1], user_array[i]);
			map_user_index[i] = tmp_user_array_size - 1;
		}
	}
	user_array_size = tmp_user_array_size;
	user_array      = tmp_user_array;

	// ua array
	for (i = 0; i < ua_array_size; ++i)
	{
		if (ua_array[i].user_index != -13)
		{
			// Change index
			ua_array[i].user_index = map_user_index[ua_array[i].user_index];
			tmp_ua_array_size++;
			tmp_ua_array = realloc(tmp_ua_array, tmp_ua_array_size * sizeof(_UA));
			tmp_ua_array[tmp_ua_array_size - 1].user_index = ua_array[i].user_index;
			tmp_ua_array[tmp_ua_array_size - 1].role_index = ua_array[i].role_index;
		}
	}
	ua_array_size   = tmp_ua_array_size;
	ua_array        = tmp_ua_array;
	// admin user array
	for (i = 0; i < admin_array_index_size; i++)
	{
		if (admin_array_index[i] != -13)
		{
			admin_array_index[i] = map_user_index[admin_array_index[i]];
			tmp_admin_array_index_size++;
			tmp_admin_array_index = realloc(tmp_admin_array_index, tmp_admin_array_index_size * sizeof(int));
			tmp_admin_array_index[tmp_admin_array_index_size - 1] = admin_array_index[i];
		}
	}
	admin_array_index_size   = tmp_admin_array_index_size;
	admin_array_index        = tmp_admin_array_index;

	// goal user index
	if(hasGoalUserMode && goal_user_index != -13)
	{
		goal_user_index = map_user_index[goal_user_index];
	}
}

void
preprocess(int require_reduction_user)
{
	// First reduce the system
	reduction_finiteARBAC();

	// Remove non-engage user
	if (require_reduction_user)
	{
		reduction_user();
	}

	if (hasGoalUserMode)
	{
		// Add a specific role name ToCheckRole to that specific user
		role_array_size++;
		role_array = realloc(role_array, role_array_size * sizeof(char*));
		role_array[role_array_size - 1] = malloc(13);
		strcpy(role_array[role_array_size - 1], "ToCheckRole");
		ua_array_size++;
		ua_array = realloc(ua_array, ua_array_size * sizeof(_UA));
		ua_array[ua_array_size - 1].user_index = goal_user_index;
		ua_array[ua_array_size - 1].role_index = role_array_size - 1;
		// Add that role to admin role array
		admin_role_array_index_size++;
		admin_role_array_index = realloc(admin_role_array_index, admin_role_array_index_size * sizeof(int));
		admin_role_array_index[admin_role_array_index_size - 1] = role_array_size - 1;

		// Add a new target role
		role_array_size++;
		role_array = realloc(role_array, role_array_size * sizeof(char*));
		role_array[role_array_size - 1] = malloc(13);
		strcpy(role_array[role_array_size - 1], "TargetPrime");

		// Add a fresh CA rule
		ca_array_size++;
		ca_array = realloc(ca_array, ca_array_size * sizeof(_CA));
		ca_array[ca_array_size - 1].type = 0;
		ca_array[ca_array_size - 1].admin_role_index = role_array_size - 2; // ToCheckRole
		ca_array[ca_array_size - 1].target_role_index = role_array_size - 1; // TargetPrime
		ca_array[ca_array_size - 1].negative_role_array = 0;
		ca_array[ca_array_size - 1].negative_role_array_size = 0;
		ca_array[ca_array_size - 1].positive_role_array_size = 2;
		ca_array[ca_array_size - 1].positive_role_array = malloc(2 * sizeof(int));
		ca_array[ca_array_size - 1].positive_role_array[0] = role_array_size - 2; // ToCheckRole
		ca_array[ca_array_size - 1].positive_role_array[1] = goal_role_index;
		goal_role_index = role_array_size - 1;
	}
}

/**********************************************************************
 * Function free_ARBAC_data
 * Free the entire data allocated
 **********************************************************************/
void
free_data()
{
	int i;

	// Free roles
	for (i = 0; i < role_array_size; i++)
	{
		free(role_array[i]);
	}
	free(role_array);

	// Free users
	for (i = 0; i < user_array_size; i++)
	{
		free(user_array[i]);
	}
	free(user_array);

	// Free admin roles
	free(admin_role_array_index);

	// Free admin
	free(admin_array_index);

	// Free UA
	free(ua_array);

	// Free CR
	free(cr_array);

	// Free CA
	for (i = 0; i < ca_array_size; i++)
	{
		free(ca_array[i].positive_role_array);
		free(ca_array[i].negative_role_array);
	}
	free(ca_array);

	if (role_dict != NULL)
	{
		iDictionary.Finalize(role_dict);
	}
	if (user_dict != NULL);
	{
		iDictionary.Finalize(user_dict);
	}
	if (newuser_dict != NULL)
	{
		iDictionary.Finalize(newuser_dict);
	}
}

// Print the comment of a CA rule
void
print_ca_comment(FILE * out, int ca_rule)
{
	int i;
	int has_head = 0;

	fprintf(out, "\t\t//------------------ CAN_ASSIGN RULE NUMBER %d -----------------\n\t\t// ", ca_rule);

	if (ca_array[ca_rule].type == 0)
	{
		fprintf(out, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(out, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(out, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(out, "&-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
			}
			else
			{
				fprintf(out, "-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
				has_head = 1;
			}
		}

		fprintf(out, ",%s>", role_array[ca_array[ca_rule].target_role_index]);
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1)
	{
		fprintf(out, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if (ca_array[ca_rule].type == 2)
	{
		fprintf(out, "<%s,NEW,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}

	fprintf(out, "\n\t\t//------------------------------------------------------------------\n");
}

void
print_ca_comment_z3(FILE * outputFile, int ca_rule)
{
	int i;
	int has_head = 0;

	fprintf(outputFile, "#------------------ CAN_ASSIGN RULE NUMBER %d -----------------\n# ", ca_rule);

	if (ca_array[ca_rule].type == 0)
	{
		fprintf(outputFile, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
				has_head = 1;
			}
		}

		fprintf(outputFile, ",%s>", role_array[ca_array[ca_rule].target_role_index]);
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1)
	{
		fprintf(outputFile, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if (ca_array[ca_rule].type == 2)
	{
		fprintf(outputFile, "<%s,NEW,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}

	fprintf(outputFile, "\n#------------------------------------------------------------------\n");
}

void print_ca_comment_hsf(FILE * outputFile, int ca_rule)
{
	int i;
	int has_head = 0;

	fprintf(outputFile, "%%--------------------------Can assign rule------------------------\n");
	fprintf(outputFile, "%%---------  ");

	if (ca_array[ca_rule].type == 0)
	{
		fprintf(outputFile, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
				has_head = 1;
			}
		}

		fprintf(outputFile, ",%s>", role_array[ca_array[ca_rule].target_role_index]);
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1)
	{
		fprintf(outputFile, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if (ca_array[ca_rule].type == 2)
	{
		fprintf(outputFile, "<%s,NEW,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}

	fprintf(outputFile, "\n%%---------------------------------------------------------------\n");
}

void print_ca_comment_smt2(FILE * outputFile, int ca_rule)
{
	int i;
	int has_head = 0;

	fprintf(outputFile, ";--------------------------Can assign rule------------------------\n");
	fprintf(outputFile, ";---------  ");

	if (ca_array[ca_rule].type == 0)
	{
		fprintf(outputFile, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if (has_head)
			{
				fprintf(outputFile, "&-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "-%s", role_array[ca_array[ca_rule].negative_role_array[i]]);
				has_head = 1;
			}
		}

		fprintf(outputFile, ",%s>", role_array[ca_array[ca_rule].target_role_index]);
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1)
	{
		fprintf(outputFile, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if (ca_array[ca_rule].type == 2)
	{
		fprintf(outputFile, "<%s,NEW,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}

	fprintf(outputFile, "\n;---------------------------------------------------------------\n");
}

// Print the comment of a CR rule
void
print_cr_comment(FILE * out, int cr_rule)
{
	fprintf(out, "\t\t//------------------- CAN_REVOKE RULE NUMBER %d ---------------------\n\t\t// ", cr_rule);
	fprintf(out, "<%s,%s>", role_array[cr_array[cr_rule].admin_role_index], role_array[cr_array[cr_rule].target_role_index]);
	fprintf(out, "\n\t\t//------------------------------------------------------------------\n");
}

void
print_cr_comment_z3(FILE * outputFile, int cr_rule)
{
	fprintf(outputFile, "#------------------- CAN_REVOKE RULE NUMBER %d ---------------------\n# ", cr_rule);
	fprintf(outputFile, "<%s,%s>", role_array[cr_array[cr_rule].admin_role_index], role_array[cr_array[cr_rule].target_role_index]);
	fprintf(outputFile, "\n#------------------------------------------------------------------\n");
}

void print_cr_comment_hsf(FILE * outputFile, int cr_rule)
{
	fprintf(outputFile, "%%-----------------------Can revoke rule------------------------\n");
	fprintf(outputFile, "%%-----------   ");

	fprintf(outputFile, "<%s,%s>", role_array[cr_array[cr_rule].admin_role_index], role_array[cr_array[cr_rule].target_role_index]);
	fprintf(outputFile, "\n%%------------------------------------------------------------\n");
}

void print_cr_comment_smt2(FILE * outputFile, int cr_rule)
{
	fprintf(outputFile, ";-----------------------Can revoke rule------------------------\n");
	fprintf(outputFile, ";-----------   ");

	fprintf(outputFile, "<%s,%s>", role_array[cr_array[cr_rule].admin_role_index], role_array[cr_array[cr_rule].target_role_index]);
	fprintf(outputFile, "\n;------------------------------------------------------------\n");
}
