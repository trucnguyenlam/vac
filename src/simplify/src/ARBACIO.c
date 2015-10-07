#include "ARBACSimplify.h"

// Drop a role from the precondition of a can assign rule
void
drop_role_precondition(int role_index, int rule_index)
{
	if (ca_array[rule_index].type == 0)
	{
		int index = belong_to(ca_array[rule_index].positive_role_array, ca_array[rule_index].positive_role_array_size, role_index);
		if (index == -1)
		{
			if (ca_array[rule_index].negative_role_array_size > 0)
			{
				index = belong_to(ca_array[rule_index].negative_role_array, ca_array[rule_index].negative_role_array_size, role_index);
				if (index != -1)
				{
					ca_array[rule_index].negative_role_array[index] = ca_array[rule_index].negative_role_array[ca_array[rule_index].negative_role_array_size - 1];
					ca_array[rule_index].negative_role_array_size--;
					if (ca_array[rule_index].negative_role_array_size == 0)
					{
						free(ca_array[rule_index].negative_role_array);
						ca_array[rule_index].negative_role_array = 0;
					}
					else
					{
						ca_array[rule_index].negative_role_array = realloc(ca_array[rule_index].negative_role_array, ca_array[rule_index].negative_role_array_size * sizeof(int));
					}
				}
			}
		}
		else
		{
			if (ca_array[rule_index].positive_role_array_size > 0)
			{
				ca_array[rule_index].positive_role_array[index] = ca_array[rule_index].positive_role_array[ca_array[rule_index].positive_role_array_size - 1];
				ca_array[rule_index].positive_role_array_size--;
				if (ca_array[rule_index].positive_role_array_size == 0)
				{
					free(ca_array[rule_index].positive_role_array);
					ca_array[rule_index].positive_role_array = 0;
				}
				else
				{
					ca_array[rule_index].positive_role_array = realloc(ca_array[rule_index].positive_role_array, ca_array[rule_index].positive_role_array_size * sizeof(int));
				}
			}
		}
	}
	// Check if that rule become another type
	if (ca_array[rule_index].type == 0 && ca_array[rule_index].negative_role_array_size == 0 && ca_array[rule_index].positive_role_array_size == 0)
	{
		ca_array[rule_index].type = 1; // TURN it into TRUE
	}
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

// Check two equivalent can revoke rule
static int
equivalent_cr(int cr1, int cr2)
{
	if (cr_array[cr1].admin_role_index == cr_array[cr2].admin_role_index && cr_array[cr1].target_role_index == cr_array[cr2].target_role_index)
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

// Check two equivalent can assign rule
static int
equivalent_ca(int ca1, int ca2)
{
	int result = 0;
	set P1, N1, P2, N2;

	if (ca_array[ca1].type != ca_array[ca2].type)
	{
		return 0;
	}

	if (ca_array[ca1].admin_role_index != ca_array[ca2].admin_role_index)
	{
		return 0;
	}

	if (ca_array[ca1].target_role_index != ca_array[ca2].target_role_index)
	{
		return 0;
	}

	if (ca_array[ca1].type != 0 && ca_array[ca1].type == ca_array[ca2].type)
	{
		return 1;
	}

	P1 = build_set(ca_array[ca1].positive_role_array, ca_array[ca1].positive_role_array_size);
	P2 = build_set(ca_array[ca2].positive_role_array, ca_array[ca2].positive_role_array_size);

	N1 = build_set(ca_array[ca1].negative_role_array, ca_array[ca1].negative_role_array_size);
	N2 = build_set(ca_array[ca2].negative_role_array, ca_array[ca2].negative_role_array_size);

	if (equal_set(P1, P2) && equal_set(N1, N2))
	{
		result = 1;
	}

	// Free temporary data
	free(P1.array);
	free(P2.array);
	free(N1.array);
	free(N2.array);

	return result;
}

// Rebuild can revoke array
static void
rebuild_cr_array()
{
	int i, j;

	for (i = 0; i < cr_array_size; i++)
	{
		if (cr_array[i].admin_role_index != -13) // -13 means removed
		{
			for (j = i + 1; j < cr_array_size; j++)
			{
				if (cr_array[j].admin_role_index != -13 && equivalent_cr(i, j))
				{
					cr_array[j].admin_role_index = -13;
				}
			}
		}
	}
}

// Check if there is still rule with NEW precondition existing in the system
int no_NEW_rule = 1;

// Rebuild can assign array
static void
rebuild_ca_array()
{
	int i, j;

	for (i = 0; i < ca_array_size; i++)
	{
		if (ca_array[i].admin_role_index != -13)
		{
			for (j = i + 1; j < ca_array_size; j++)
			{
				if (ca_array[j].admin_role_index != -13 && equivalent_ca(i, j))
				{
					ca_array[j].admin_role_index = -13;
				}
			}
			if (ca_array[i].type == 2)
			{
				no_NEW_rule = 0;
			}
		}
	}
}

static void
rebuild_admin_array(void)
{
	int i, j, count = 0, flag = 0;

	for (i = 0; i < admin_array_index_size; i++)
	{
		if (admin_array_index[i] != -13)
		{
			if (admin_array_index[i] == -10
			        || strcmp(get_user(admin_array_index[i]), "SUPER_USER") == 0
			   )
			{
				flag = 1;
				continue;
			}
			count = 0;
			for (j = 0; j < ua_array_size; j++)
			{
				if (ua_array[j].user_index == admin_array_index[i]
				        && ua_array[j].role_index != -13
				        && (belong_to(admin_role_array_index, admin_role_array_index_size, ua_array[j].role_index) != -1 )
				   )
				{
					count++;
				}
			}
			if (count == 0)
			{
				admin_array_index[i] = -13;  // Mark as removal
			}
		}
	}

	if (!flag && super_exist)
	{
		// Create super user here
		admin_array_index_size++;
		admin_array_index = realloc(admin_array_index, admin_array_index_size * sizeof(int));
		admin_array_index[admin_array_index_size - 1] = -10;   // SUPER_USER
	}
}

/**
 * Return index of the user that will become the SUPER_USER
 */
static int
candidate_SUPER_USER(void)
{
	int i = -1;
	for (i = promoted_users.array_size - 1; i >= 0; i--)
	{
		// make sure that user is not removed
		if (0 <= promoted_users.array[i]
		        && promoted_users.array[i] < user_array_size
		        // && strcmp(user_array[promoted_users.array[i]], "removed_user") != 0
		   )
		{
			return i;
		}
	}
	return i;
}

int super_user_index = 0;

// Rebuild ARBAC system
static void
rebuild_ARBAC_system()
{
	int i, flag = 0;

	// Rebuild role array if SUPER ROLE exist
	if (super_exist)
	{
		role_array_size++;
		role_array = realloc(role_array, role_array_size * sizeof(char *));
		role_array[role_array_size - 1] = malloc(strlen("SUPER_ROLE") + 1);
		strcpy(role_array[role_array_size - 1], "SUPER_ROLE");

		admin_role_array_index_size++;
		admin_role_array_index = realloc(admin_role_array_index, admin_role_array_index_size * sizeof(int));
		admin_role_array_index[admin_role_array_index_size - 1] = -10;
	}

	// Rebuild user array
	for (i = user_array_size - 1; i >= 0; i--)
	{
		if (strcmp(user_array[i], "SUPER_USER") == 0)
		{
			flag = 1;
			break;
		}
	}

	if (!flag && super_exist)
	{
		// Elect a user to become SUPER_USER
		int elected_user_index = candidate_SUPER_USER();
		if (elected_user_index == -1)
		{
			printf("error: there is something wrong with IMMATERIAL module\n");
			abort();
		}
		else
		{
			// Change that user to SUPER_USER, no matter what that user is
			free(user_array[elected_user_index]);
			user_array[elected_user_index] = malloc(strlen("SUPER_USER") + 1);
			strcpy(user_array[elected_user_index], "SUPER_USER");
		}
	}

	// Rebuild user membership UA
	// Test if there is UA <SUPER_USER, SUPER_ROLE>
	flag = 0;
	for (i = 0; i < ua_array_size; i++)
	{
		if (ua_array[i].role_index == -10)
		{
			flag = 1;
			break;
		}
	}
	if (!flag && super_exist)
	{
		ua_array_size++;
		ua_array = realloc(ua_array, ua_array_size * sizeof(_UA));
		ua_array[ua_array_size - 1].user_index = -10;
		ua_array[ua_array_size - 1].role_index = -10;
	}

	// Rebuild admin array
	rebuild_admin_array();

	// Rebuild can revoke rules
	rebuild_cr_array();

	// Rebuild can assign rules
	rebuild_ca_array();

}

// Get user name from the index
char *
get_user(int user_index)
{
	if (user_index == -10)
	{
		return "SUPER_USER";
	}
	if (user_index == -13)
	{
		return "removed_user";
	}
	return user_array[user_index];
}

// Get role name from the index
char *
get_role(int role_index)
{
	if (role_index == -1)
	{
		return "FALSE";
	}
	if (role_index == -10)
	{
		return "SUPER_ROLE";
	}
	if (role_index == -13)
	{
		return "removed_role";
	}
	return role_array[role_index];
}

// Print a can assign rule (for logging purpose)
void
print_ca_rule(int ca_index)
{
	int j, has_head = 0;
	if (ca_array[ca_index].admin_role_index != -13)
	{
		// Check for the precondition of each role
		if (ca_array[ca_index].type == 0)
		{
			fprintf(tmplog, "<%s,", get_role(ca_array[ca_index].admin_role_index));
			for (j = 0; j < ca_array[ca_index].positive_role_array_size; j++)
			{
				if (ca_array[ca_index].positive_role_array[j] != -13)
				{
					if (has_head)
					{
						fprintf(tmplog, "&%s", get_role(ca_array[ca_index].positive_role_array[j]));
					}
					else
					{
						fprintf(tmplog, "%s", get_role(ca_array[ca_index].positive_role_array[j]));
						has_head = 1;
					}
				}
			}

			for (j = 0; j < ca_array[ca_index].negative_role_array_size; j++)
			{
				if (ca_array[ca_index].negative_role_array[j] != -13)
				{
					if (has_head)
					{
						fprintf(tmplog, "&-%s", get_role(ca_array[ca_index].negative_role_array[j]));
					}
					else
					{
						fprintf(tmplog, "-%s", get_role(ca_array[ca_index].negative_role_array[j]));
						has_head = 1;
					}
				}
			}
			fprintf(tmplog, ",%s> ", get_role(ca_array[ca_index].target_role_index));
			has_head = 0;
		}
		else if (ca_array[ca_index].type == 1)
		{
			fprintf(tmplog, "<%s,TRUE,%s> ", get_role(ca_array[ca_index].admin_role_index), get_role(ca_array[ca_index].target_role_index));
		}
		else if (ca_array[ca_index].type == 2)
		{
			fprintf(tmplog, "<%s,NEW,%s> ", get_role(ca_array[ca_index].admin_role_index), get_role(ca_array[ca_index].target_role_index));
		}
	}
}

// Read ARBAC policies file in its appropriate format
void
read_ARBAC(char *inputFile)
{
	pANTLR3_INPUT_STREAM input;
	pARBACLexer lex;
	pANTLR3_COMMON_TOKEN_STREAM tokens;
	pARBACParser parser;

	input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) inputFile);
	if (input == NULL)
	{
		printf("ARBAC file does not exist!!!\n");
		abort();
	}
	lex = ARBACLexerNew(input);
	tokens = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT, TOKENSOURCE(lex));
	parser = ARBACParserNew(tokens);

	// Parse the file to data structure
	parser->parse(parser);

	// Manually free parsing data
	parser->free(parser);
	tokens->free(tokens);
	lex->free(lex);
	input->close(input);
}

// Write simplification trace in order to find counter example
static void
write_trace(FILE *output)
{
	int i;
	fprintf(output, "Trace\n");
	for (i = 0; i < trace_array_size; i++)
	{
		fprintf(output, "%d -> %d -> %d + %d -> %d + %d\n",
		        trace_array[i].simplify_rule,
		        trace_array[i].affected_role_index,
		        trace_array[i].affected_rule_index,
		        trace_array[i].affected_rule_type,
		        trace_array[i].related_rule_index,
		        trace_array[i].related_rule_type);
	}
	fprintf(output, "EndTrace\n");
}


void
generateADMIN(void)
{
	if (admin_array_index_size == 0)
	{
		set admin_set;
		admin_set.array = 0;
		admin_set.array_size = 0;
		int i;
		for (i = 0; i < ua_array_size; i++)
		{
			if (belong_to(admin_role_array_index, admin_role_array_index_size, ua_array[i].role_index) != -1)
			{
				admin_set = add_element(admin_set, ua_array[i].user_index);
			}
		}
		admin_array_index_size = admin_set.array_size;
		admin_array_index = malloc(admin_array_index_size * sizeof(int));
		for (i = 0; i < admin_array_index_size; i++)
		{
			admin_array_index[i] = admin_set.array[i];
		}
	}
}


void
write_ARBACMOHAWK(char *fileName)
{
	FILE *output;
	char *newfile = 0;
	int i, j;
	int count = 0;

	newfile = malloc(strlen(fileName) + strlen("_mohawk.arbac") + 2);
	sprintf(newfile, "%s_mohawk.arbac", fileName);
	output = fopen(newfile, "w");

	fprintf(output, "Roles ");
	for (i = 0; i < role_array_size; i++)
	{
		fprintf(output, "%s ", role_array[i]);
	}
	fprintf(output, ";\n\n");

	fprintf(output, "Users ");
	for (i = 0; i < user_array_size; i++)
	{
		fprintf(output, "%s ", user_array[i]);
	}
	fprintf(output, ";\n\n");

	//Write the UA
	fprintf(output, "UA ");
	for (i = 0; i < ua_array_size; i++)
	{
		fprintf(output, "<%s,%s> ", get_user(ua_array[i].user_index), get_role(ua_array[i].role_index));
	}
	fprintf(output, ";\n\n");

	fprintf(output, "CR ");
	for (i = 0; i < cr_array_size; i++)
	{
		fprintf(output, "<%s,%s> ", get_role(cr_array[i].admin_role_index), get_role(cr_array[i].target_role_index));
	}
	fprintf(output, ";\n\n");

	int has_head = 0;
	fprintf(output, "CA ");
	for (i = 0; i < ca_array_size; i++)
	{
		// Check for the precondition of each role
		if (ca_array[i].type == 0)
		{
			fprintf(output, "<%s,", get_role(ca_array[i].admin_role_index));

			for (j = 0; j < ca_array[i].positive_role_array_size; j++)
			{
				if (has_head)
				{
					fprintf(output, "&%s", get_role(ca_array[i].positive_role_array[j]));
				}
				else
				{
					fprintf(output, "%s", get_role(ca_array[i].positive_role_array[j]));
					has_head = 1;
				}
			}

			for (j = 0; j < ca_array[i].negative_role_array_size; j++)
			{
				if (has_head)
				{
					fprintf(output, "&-%s", get_role(ca_array[i].negative_role_array[j]));
				}
				else
				{
					fprintf(output, "-%s", get_role(ca_array[i].negative_role_array[j]));
					has_head = 1;
				}
			}
			fprintf(output, ",%s> ", get_role(ca_array[i].target_role_index));
			has_head = 0;
		}
		else if (ca_array[i].type == 1)
		{
			fprintf(output, "<%s,TRUE,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
		}
		else if (ca_array[i].type == 2)
		{
			fprintf(output, "<%s,NEW,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
		}
	}
	fprintf(output, ";\n\n");


	//Write the ADMIN
	fprintf(output, "ADMIN ");
	for (i = 0; i < admin_array_index_size; i++)
	{
		fprintf(output, "%s ", get_user(admin_array_index[i]));
	}
	fprintf(output, ";\n\n");

	//Write the SPEC
	fprintf(output, "SPEC");
	if (goal_user_index != -13)
	{
		fprintf(output, " %s", get_user(goal_user_index));
	}
	fprintf(output, " %s ;", get_role(goal_role_index));

	fclose(output);
	free(newfile);
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

		// Free data
		for(i = 0; i < newuser_array_size; i++)
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

// Write ARBAC policies to a file output
void
write_ARBAC(char *fileName)
{
	FILE *output;
	char *newfile = 0;
	int i, j;
	int count = 0;

	newfile = malloc(strlen(fileName) + strlen("_reduceAdmin.arbac") + 2);
	sprintf(newfile, "%s_reduceAdmin.arbac", fileName);
	output = fopen(newfile, "w");

	fprintf(tmplog, "ARBAC system after reducing\n");
	// Rebuild the system before printing
	rebuild_ARBAC_system();

	fprintf(simplifyLog, "---------------------------------------------\nSIMPLIFICATION LOG\n---------------------------------------------\n");

	//Write the roles
	fprintf(simplifyLog, "Roles\n");
	fprintf(output, "Roles ");
	for (i = 0; i < role_array_size; i++)
	{
		if (strcmp(role_array[i], "removed_role") != 0)
		{
			fprintf(output, "%s ", role_array[i]);
			fprintf(simplifyLog, "%d -> %d\n", i, count);
			count++;
		}
		else
		{
			fprintf(simplifyLog, "%d -> -1\n", i);
		}
	}
	fprintf(output, ";\n\n");
	fprintf(simplifyLog, "EndR\n");
	fprintf(tmplog, "Roles: %d\n", count);

	count = 0;
	//Write the users
	fprintf(simplifyLog, "Users\n");
	fprintf(output, "Users ");
	for (i = 0; i < user_array_size; i++)
	{
		if (strcmp(user_array[i], "removed_user") != 0)
		{
			fprintf(output, "%s ", user_array[i]);
			if (super_exist && strcmp(user_array[i], "SUPER_USER") == 0)
			{
				fprintf(simplifyLog, "%d -> -10\n", i); // -10 is for super
			}
			else
			{
				fprintf(simplifyLog, "%d -> %d\n", i, count);
			}
			count++;
		}
		else
		{
			fprintf(simplifyLog, "%d -> -1\n", i);
		}
	}
	fprintf(output, ";\n\n");
	fprintf(simplifyLog, "EndU\n");
	fprintf(tmplog, "Users: %d\n", count);

	//Write the UA
	fprintf(output, "UA ");
	for (i = 0; i < ua_array_size; i++)
	{
		if (ua_array[i].user_index != -13)
		{
			fprintf(output, "<%s,%s> ", get_user(ua_array[i].user_index), get_role(ua_array[i].role_index));
		}
	}
	fprintf(output, ";\n\n");

	count = 0;
	//Write the CR
	fprintf(simplifyLog, "CRs\n");
	fprintf(output, "CR ");
	for (i = 0; i < cr_array_size; i++)
	{
		if (cr_array[i].admin_role_index != -13 && cr_array[i].admin_role_index != -1)
		{
			fprintf(output, "<%s,%s> ", get_role(cr_array[i].admin_role_index), get_role(cr_array[i].target_role_index));
			fprintf(simplifyLog, "%d <- %d\n", count, i);
			count++;
		}
	}
	fprintf(output, ";\n\n");
	fprintf(simplifyLog, "EndCR\n");
	fprintf(tmplog, "CR Rules: %d\n", count);

	count = 0;
	//Write the CA
	int has_head = 0;
	fprintf(simplifyLog, "CAs\n");
	fprintf(output, "CA ");
	for (i = 0; i < ca_array_size; i++)
	{
		// Not a deleted rule
		if (ca_array[i].admin_role_index != -13)
		{
			// Check for the precondition of each role
			if (ca_array[i].type == 0)
			{
				fprintf(output, "<%s,", get_role(ca_array[i].admin_role_index));

				for (j = 0; j < ca_array[i].positive_role_array_size; j++)
				{
					if (ca_array[i].positive_role_array[j] != -13)
					{
						if (has_head)
						{
							fprintf(output, "&%s", get_role(ca_array[i].positive_role_array[j]));
						}
						else
						{
							fprintf(output, "%s", get_role(ca_array[i].positive_role_array[j]));
							has_head = 1;
						}
					}
				}

				for (j = 0; j < ca_array[i].negative_role_array_size; j++)
				{
					if (ca_array[i].negative_role_array[j] != -13)
					{
						if (has_head)
						{
							fprintf(output, "&-%s", get_role(ca_array[i].negative_role_array[j]));
						}
						else
						{
							fprintf(output, "-%s", get_role(ca_array[i].negative_role_array[j]));
							has_head = 1;
						}
					}
				}
				fprintf(output, ",%s> ", get_role(ca_array[i].target_role_index));
				has_head = 0;
			}
			else if (ca_array[i].type == 1)
			{
				fprintf(output, "<%s,TRUE,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
			}
			else if (ca_array[i].type == 2)
			{
				fprintf(output, "<%s,NEW,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
			}
			fprintf(simplifyLog, "%d <- %d\n", count, i);
			count++;
		}
	}
	fprintf(output, ";\n\n");
	fprintf(simplifyLog, "EndCA\n");
	fprintf(tmplog, "CA Rules: %d\n", count);

	//Write the SPEC
	fprintf(output, "SPEC");
	if (goal_user_index != -13)
	{
		fprintf(output, " %s", get_user(goal_user_index));
	}
	fprintf(output, " %s ;", get_role(goal_role_index));

	write_trace(simplifyLog);
	fprintf(simplifyLog, "---------------------------------------------\nEND SIMPLIFICATION LOG\n---------------------------------------------\n");

	fclose(output);
	free(newfile);
}

// Free data
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
