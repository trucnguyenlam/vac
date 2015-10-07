#include "ARBACLexer.h"
#include "ARBACParser.h"
#include "ARBACTransform.h"

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

void
preprocess()
{
	// First reduce the system
	reduction_finiteARBAC();

	if(hasGoalUserMode)
	{
		// Add a specific role name ToCheckRole to that specific user
		role_array_size++;
		role_array = realloc(role_array, role_array_size*sizeof(char*));
		role_array[role_array_size-1] = malloc(13);
		strcpy(role_array[role_array_size-1], "ToCheckRole");
		ua_array_size++;
		ua_array = realloc(ua_array, ua_array_size*sizeof(_UA));
		ua_array[ua_array_size-1].user_index = goal_user_index;
		ua_array[ua_array_size-1].role_index = role_array_size-1;

		// Add a new target role
		role_array_size++;
		role_array = realloc(role_array, role_array_size*sizeof(char*));
		role_array[role_array_size-1] = malloc(13);
		strcpy(role_array[role_array_size-1], "TargetPrime");

		// Add a fresh CA rule
		ca_array_size++;
		ca_array = realloc(ca_array, ca_array_size*sizeof(_CA));
		ca_array[ca_array_size-1].type = 0;
		ca_array[ca_array_size-1].admin_role_index = role_array_size-2; // ToCheckRole
		ca_array[ca_array_size-1].target_role_index = role_array_size-1; // TargetPrime
		ca_array[ca_array_size-1].negative_role_array = 0;
		ca_array[ca_array_size-1].negative_role_array_size = 0;
		ca_array[ca_array_size-1].positive_role_array_size = 2;
		ca_array[ca_array_size-1].positive_role_array = malloc(2*sizeof(int));
		ca_array[ca_array_size-1].positive_role_array[0] = role_array_size-2;
		ca_array[ca_array_size-1].positive_role_array[1] = goal_role_index;
		goal_role_index = role_array_size-1;
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

	if(ca_array[ca_rule].type == 0)
	{
		fprintf(outputFile, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for(i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if(has_head)
			{
				fprintf(outputFile, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for(i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if(has_head)
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
	else if(ca_array[ca_rule].type == 1)
	{
		fprintf(outputFile, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if(ca_array[ca_rule].type == 2)
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

	if(ca_array[ca_rule].type == 0)
	{
		fprintf(outputFile, "<%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for(i = 0; i < ca_array[ca_rule].positive_role_array_size; i++)
		{
			if(has_head)
			{
				fprintf(outputFile, "&%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else
			{
				fprintf(outputFile, "%s", role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}

		for(i = 0; i < ca_array[ca_rule].negative_role_array_size; i++)
		{
			if(has_head)
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
	else if(ca_array[ca_rule].type == 1)
	{
		fprintf(outputFile, "<%s,TRUE,%s>", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if(ca_array[ca_rule].type == 2)
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
