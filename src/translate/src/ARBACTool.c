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

// Find a role index from dictionary by its name
int
find_role_from_dict(char *name)
{
	int *i;

	i = (int *) iDictionary.GetElement(role_dict, name);
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
find_user_from_dict(char *name)
{
	int *i;

	i = (int *) iDictionary.GetElement(user_dict, name);
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

void
preprocess()
{
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

	iDictionary.Finalize(role_dict);
	iDictionary.Finalize(user_dict);

	// New User mode only
	if(hasNewUserMode)
	{
		free(initialize_role_array);
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
