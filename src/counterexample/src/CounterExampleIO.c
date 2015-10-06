#include <roxml.h>
#include "ARBACLexer.h"
#include "ARBACParser.h"
#include "ARBACData.h"
#include "CounterExample.h"

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

// Read ARBAC policies input file
void
readARBAC(char *inputFile)
{
    pANTLR3_INPUT_STREAM input;
    pARBACLexer lex;
    pANTLR3_COMMON_TOKEN_STREAM tokens;
    pARBACParser parser;

    input = antlr3AsciiFileStreamNew((pANTLR3_UINT8) inputFile);

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

static void
printCBMCAssignment(CBMCAssignment a)
{
    if (a.type == 0)
    {
        fprintf(debugFile, "Assignment in line %d with track_user %d with value %d with role %s\n", a.line, a.track_user, a.value, a.role);
    }
    else
    {
        fprintf(debugFile, "Assignment in line %d with track_user %d with value %d\n", a.line, a.track_user, a.value);
    }
}

// Read CBMC XML Log file
void
readCBMCXMLLog(char *inputfile)
{
    // 1306 is the maximum string length
    char tmp1[1306] = " ";
    char tmp2[6] = " ";
    char tmp_role[1306] = " ";
    int track_user;
    int a, i = 0;
    assignment_array = 0;
    assignment_array_size = 0;
    node_t *root = roxml_load_doc(inputfile);
    if(!root)
    {
        fprintf(stderr, "error: please input the correct log file from CBMC\n");
        abort();
    }

    node_t *cprover = roxml_get_chld(root, NULL, 0);

    roxml_get_content(roxml_get_chld(cprover, "cprover-status", 0), tmp1, 1306, &a);

    hasCounterExample = 1;

    if (strcmp(tmp1, "FAILURE") != 0)
    {
        hasCounterExample = 0;
        return;
    }

    fprintf(debugFile, "READ CBMC XML LOG\n");

    // Counter Example trace
    node_t *goto_trace = roxml_get_chld(cprover, "goto_trace", 0);
    for (i = 0; i < roxml_get_chld_nb(goto_trace); i++)
    {
        node_t *assignment_node = roxml_get_chld(goto_trace, NULL, i);
        if (strcmp(roxml_get_name(assignment_node, NULL, 0), "assignment") == 0)
        {
            node_t *display_name = roxml_get_chld(assignment_node, "display_name", 0);
            node_t *value = roxml_get_chld(assignment_node, "value", 0);
            node_t *location = roxml_get_chld(assignment_node, "location", 0);
            node_t *line_attr = roxml_get_attr(location, "line", 0);

            roxml_get_content(display_name, tmp1, 1306, &a);

            // Only consider assignment to track variable
            if (strstr(tmp1, "track_") != NULL)
            {
                sscanf(tmp1, "track_%d_%s", &track_user, tmp_role);
                assignment_array_size++;
                assignment_array = realloc(assignment_array, assignment_array_size * sizeof(CBMCAssignment));
                assignment_array[assignment_array_size - 1].track_user = track_user;
                assignment_array[assignment_array_size - 1].role = 0;
                assignment_array[assignment_array_size - 1].role = malloc(strlen(tmp_role) + 1);
                strcpy(assignment_array[assignment_array_size - 1].role, tmp_role);
                roxml_get_content(value, tmp2, 6, &a);
                assignment_array[assignment_array_size - 1].value = atoi(tmp2);
                roxml_get_content(line_attr, tmp2, 6, &a);
                assignment_array[assignment_array_size - 1].line = atoi(tmp2);
                assignment_array[assignment_array_size - 1].type = 0;
                printCBMCAssignment(assignment_array[assignment_array_size - 1]);
            }
            else if (strstr(tmp1, "b_") != NULL)
            {
                sscanf(tmp1, "b_%d", &track_user);
                assignment_array_size++;
                assignment_array = realloc(assignment_array, assignment_array_size * sizeof(CBMCAssignment));
                assignment_array[assignment_array_size - 1].track_user = track_user;
                assignment_array[assignment_array_size - 1].role = 0;
                roxml_get_content(value, tmp2, 6, &a);
                assignment_array[assignment_array_size - 1].value = atoi(tmp2);
                roxml_get_content(line_attr, tmp2, 6, &a);
                assignment_array[assignment_array_size - 1].line = atoi(tmp2);
                assignment_array[assignment_array_size - 1].type = 1;
                printCBMCAssignment(assignment_array[assignment_array_size - 1]);
            }
        }
    }
    roxml_close(root);
}

static char *
readline(FILE *stream)
{
    char buffer[99999] = " ";
    int curr, counter = 0;
    do
    {
        curr = fgetc(stream);
        buffer[counter] = curr;
        counter++;
        if (curr == EOF)
            return NULL;
    }
    while (curr != '\n');
    buffer[counter] = '\0';
    return strdup(buffer);
}

// Read Translated CBMC file from the ARBAC policies
void
readCBMCTranslated(char *inputFile)
{
    FILE *input;
    int line_count = 1;
    char *c;
    char tmp1[1306], tmp2[1306];
    int rule_number;

    // Initialize limit variable
    declaration_lim = 0;
    initialize_lim = 0;
    configuration_lim = 0;
    rule_translated_array = 0;
    rule_translated_array_size = 0;

    user_configuration_array = 0;
    user_configuration_array_size = 0;

    input = fopen(inputFile, "r");
    do
    {
        c = readline(input);
        if (c != NULL)
        {
            if (strstr(c, "MAIN PROGRAM") != NULL)
            {
                declaration_lim = line_count;
            }
            else if (strstr(c, "CONFIGURATION_USERS") != NULL)
            {
                initialize_lim = line_count;
            }
            else if (strstr(c, "Configuration of") != NULL)
            {
                sscanf(c, "%s of %s", tmp2, tmp1);
                user_configuration_array_size++;
                user_configuration_array = realloc(user_configuration_array, user_configuration_array_size * sizeof(Configuration_user));
                user_configuration_array[user_configuration_array_size - 1].user_name = malloc(strlen(tmp1) + 1);
                strcpy(user_configuration_array[user_configuration_array_size - 1].user_name, tmp1);
                user_configuration_array[user_configuration_array_size - 1].line = line_count;
                user_configuration_array[user_configuration_array_size - 1].rule_index = -1;
            }
            else if (strstr(c, "Configuration OF") != NULL)
            {
                int rule_index;
                sscanf(c, "%s OF %s WITH %d", tmp2, tmp1, &rule_index);
                user_configuration_array_size++;
                user_configuration_array = realloc(user_configuration_array, user_configuration_array_size * sizeof(Configuration_user));
                user_configuration_array[user_configuration_array_size - 1].user_name = malloc(strlen(tmp1) + 1);
                strcpy(user_configuration_array[user_configuration_array_size - 1].user_name, tmp1);
                user_configuration_array[user_configuration_array_size - 1].line = line_count;
                user_configuration_array[user_configuration_array_size - 1].rule_index = rule_index;
            }
            else if (strstr(c, "SIMULATION") != NULL)
            {
                configuration_lim = line_count;
            }
            // Record a can assign rule
            else if (strstr(c, "CAN_ASSIGN") != NULL)
            {
                sscanf(c, "%s CAN_ASSIGN RULE NUMBER %d %s\n", tmp1, &rule_number, tmp2);
                rule_translated_array_size++;
                rule_translated_array = realloc(rule_translated_array, rule_translated_array_size * sizeof(RuleTranslated));
                rule_translated_array[rule_translated_array_size - 1].rule_number = rule_number;
                rule_translated_array[rule_translated_array_size - 1].rule_type = 0;
                rule_translated_array[rule_translated_array_size - 1].line = line_count;
            }
            // Record a can revoke rule
            else if (strstr(c, "CAN_REVOKE") != NULL)
            {
                sscanf(c, "%s CAN_REVOKE RULE NUMBER %d %s\n", tmp1, &rule_number, tmp2);
                rule_translated_array_size++;
                rule_translated_array = realloc(rule_translated_array, rule_translated_array_size * sizeof(RuleTranslated));
                rule_translated_array[rule_translated_array_size - 1].rule_number = rule_number;
                rule_translated_array[rule_translated_array_size - 1].rule_type = 1;
                rule_translated_array[rule_translated_array_size - 1].line = line_count;
            }
        }
        line_count++;
    }
    while (c != NULL);
    fclose(input);
}

// Read Simplify log file
void
readSimplifyLog(char *inputFile)
{
    FILE *input;
    char *c;
    int i, original_index, simplify_index;
    int i1, i2, i3, i4, i5, i6;

    input = fopen(inputFile, "r");
    role_map_array = 0;
    role_map_array_size = 0;
    user_map_array = 0;
    user_map_array_size = 0;
    ca_map_array = 0;
    ca_map_array_size = 0;
    cr_map_array = 0;
    cr_map_array_size = 0;
    simplify_steps = 0;
    simplify_steps_size = 0;

    for (i = 0; i < 4; i++)
    {
        c = readline(input);
    }
    while (strcmp(c, "EndR\n") != 0)
    {
        c = readline(input);
        if (strcmp(c, "EndR\n") != 0)
        {
            sscanf(c, "%d -> %d", &original_index, &simplify_index);
            role_map_array_size++;
            role_map_array = realloc(role_map_array, role_map_array_size * sizeof(int));
            role_map_array[role_map_array_size - 1] = simplify_index;
        }
    }
    c = readline(input);
    while (strcmp(c, "EndU\n") != 0)
    {
        c = readline(input);
        if (strcmp(c, "EndU\n") != 0)
        {
            sscanf(c, "%d -> %d", &original_index, &simplify_index);
            user_map_array_size++;
            user_map_array = realloc(user_map_array, user_map_array_size * sizeof(int));
            user_map_array[user_map_array_size - 1] = simplify_index;
        }
    }
    c = readline(input);
    while (strcmp(c, "EndCR\n") != 0)
    {
        c = readline(input);
        if (strcmp(c, "EndCR\n") != 0)
        {
            sscanf(c, "%d <- %d", &simplify_index, &original_index);
            cr_map_array_size++;
            cr_map_array = realloc(cr_map_array, cr_map_array_size * sizeof(int));
            cr_map_array[cr_map_array_size - 1] = original_index;
        }
    }
    c = readline(input);
    while (strcmp(c, "EndCA\n") != 0)
    {
        c = readline(input);
        if (strcmp(c, "EndCA\n") != 0)
        {
            sscanf(c, "%d <- %d", &simplify_index, &original_index);
            ca_map_array_size++;
            ca_map_array = realloc(ca_map_array, ca_map_array_size * sizeof(int));
            ca_map_array[ca_map_array_size - 1] = original_index;
        }
    }
    c = readline(input);
    while (strcmp(c, "EndTrace\n") != 0)
    {
        c = readline(input);
        if (strcmp(c, "EndTrace\n") != 0)
        {
            sscanf(c, "%d -> %d -> %d + %d -> %d + %d", &i1, &i2, &i3, &i4, &i5, &i6);
            // Will consider can revoke rule in the next development if it is worth doing that.
            if(i1 != 2)
            {
                simplify_steps_size++;
                simplify_steps = realloc(simplify_steps, simplify_steps_size * sizeof(Step));
                simplify_steps[simplify_steps_size - 1].simplify_rule = i1;
                simplify_steps[simplify_steps_size - 1].affected_role_index = i2;
                simplify_steps[simplify_steps_size - 1].affected_rule_index = i3;
                simplify_steps[simplify_steps_size - 1].affected_rule_type = i4;
                simplify_steps[simplify_steps_size - 1].related_rule_index = i5;
                simplify_steps[simplify_steps_size - 1].related_rule_type = i6;
            }
        }
    }
    fclose(input);
}
