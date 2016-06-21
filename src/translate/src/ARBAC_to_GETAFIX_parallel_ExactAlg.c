#include "ARBACExact.h"


static void
declare_variables(FILE *outputFile)
{
    // Declaration of admin roles
    int i;

    fprintf(outputFile, "//---------- GLOBAL VARIABLES DECLARATION ---------\n");

    fprintf(outputFile, "decl atomic,\n");

    for (i = 0; i < admin_role_array_index_size; ++i)
    {
        fprintf(outputFile, "\tg_%s", role_array[admin_role_array_index[i]]);
        if (i == admin_role_array_index_size - 1)
        {
            fprintf(outputFile, ";\n");
        }
        else
        {
            fprintf(outputFile, ",\n");
        }
    }

    fprintf(outputFile, "\n");
}

static void
initialize_variables(FILE *outputFile)
{
    int i, j, flag;

    fprintf(outputFile, "//---------- INITIALIZE GLOBAL VARIABLES ---------\n");

    fprintf(outputFile, "void init()\n");
    fprintf(outputFile, "begin\n");

    for (i = 0; i < admin_role_array_index_size; i++)
    {
        flag = 0;
        // Check if an admin role is already in some user
        for (j = 0; j < user_config_array_size; j++)
        {
            if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i]))
            {
                flag = 1;
                break;
            }
        }
        if (flag)
        {
            fprintf(outputFile, "\tg_%s := T;\n", role_array[admin_role_array_index[i]]);
        }
        else
        {
            fprintf(outputFile, "\tg_%s := F;\n", role_array[admin_role_array_index[i]]);
        }
    }

    fprintf(outputFile, "\tendinit: skip;\n");
    fprintf(outputFile, "end\n");
    fprintf(outputFile, "\n");
}


static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "\t\tif (");
    // Admin role must be available
    fprintf(outputFile, "g_%s", role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & l_%s", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & !l_%s", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & !l_%s", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") then\n");

    // Applying this rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
    {
        fprintf(outputFile, "\t\t\tif (*) then l_%s, g_%s := T, T; fi\n", role_array[ca_array[ca_rule].target_role_index], role_array[ca_array[ca_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "\t\t\tif (*) then l_%s := T; fi\n", role_array[ca_array[ca_rule].target_role_index]);
    }
    fprintf(outputFile, "\t\tfi\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, "\t\t//Rule with NEW in the precondition are already involved in initialization\n");
        }
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "\t\tif (");
    // Admin role must be available
    fprintf(outputFile, " g_%s", role_array[cr_array[cr_rule].admin_role_index]);
    // The user must be in that target role
    fprintf(outputFile, " & l_%s", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") then\n");
    // Applying can_revoke rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    {
        fprintf(outputFile, "\t\t\tif (*) then l_%s, g_%s := F, F; fi\n", role_array[cr_array[cr_rule].target_role_index], role_array[cr_array[cr_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "\t\t\tif (*) then l_%s := F; fi\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    fprintf(outputFile, "\t\tfi\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
}


static void
simulate_rules(FILE * outputFile)
{
    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);
}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i;
    // Check for the consistency of each admin role
    fprintf(outputFile, "\t\t//--- ADMIN ROLE CONSISTENCY ----\n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        fprintf(outputFile, "\t\tg_%s := (l_%s|g_%s);\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
    }
}

static void
simulate_error(FILE * outputFile, int user_index)
{
    if (hasGoalUserMode)
    {
        if(user_index == goal_user_index)
        {
            fprintf(outputFile, "\t\t//--- REACHABILITY CHECK ----\n");
            fprintf(outputFile, "\t\tif (");
            // One of the user reach target role
            fprintf(outputFile, " l_%s ", role_array[goal_role_index]);
            fprintf(outputFile, ") then\n");
            fprintf(outputFile, "\t\t\tSLIC_ERROR: skip;\n");
            fprintf(outputFile, "\t\tfi\n");
        }
    }
    else
    {
        fprintf(outputFile, "\t\t//--- REACHABILITY CHECK ----\n");
        fprintf(outputFile, "\t\tif (");
        // One of the user reach target role
        fprintf(outputFile, " l_%s ", role_array[goal_role_index]);
        fprintf(outputFile, ") then\n");
        fprintf(outputFile, "\t\t\tSLIC_ERROR: skip;\n");
        fprintf(outputFile, "\t\tfi\n");
    }
}

static void
simulate_user(FILE *outputFile, int user_index)
{
    int i;

    fprintf(outputFile, "void %s ()\n", user_array[user_index]);
    fprintf(outputFile, "begin\n");
    // Declaration of local variables
    fprintf(outputFile, "\tdecl");
    for (i = 0; i < role_array_size; i++)
    {
        fprintf(outputFile, " l_%s", role_array[i]);
        if (i == role_array_size - 1)
        {
            fprintf(outputFile, ";");
        }
        else
        {
            fprintf(outputFile, ",");
        }
    }
    fprintf(outputFile, "\n");

    // Init of local variable
    fprintf(outputFile, "\t");
    for (i = 0; i < role_array_size; i++)
    {
        if (i > 0)
        {
            fprintf(outputFile, ", ");
        }
        fprintf(outputFile, "l_%s", role_array[i]);
    }

    fprintf(outputFile, " := ");
    for (i = 0; i < role_array_size; i++)
    {
        if (i > 0)
        {
            fprintf(outputFile, ", ");
        }
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, i))
        {
            fprintf(outputFile, "T");
        }
        else
        {
            fprintf(outputFile, "F");
        }
    }
    fprintf(outputFile, ";\n");

    fprintf(outputFile, "\t//---------- SIMULATION OF RULES ---------\n");
    fprintf(outputFile, "\twhile (T) do\n");
    // Simulate every rule in the system (this is the same for all user)
    simulate_rules(outputFile);

    // Simulate share admin role
    simulate_admin_roles(outputFile);

    // Simulate error check
    simulate_error(outputFile, user_index);

    fprintf(outputFile, "\tod\n");
    fprintf(outputFile, "end\n\n");
}

static void
simulate(FILE *outputFile)
{
    int i;

    for (i = 0; i < user_array_size; i++)
    {
        simulate_user(outputFile, i);
    }

}

void
transform_2_GETAFIX_parallel_ExactAlg(char *inputFile)
{
    FILE *outputFile;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_parallel_GETAFIX.bp") + 2);
    sprintf(newfile, "%s_ExactAlg_parallel_GETAFIX.bp", inputFile);
    outputFile = fopen(newfile, "w");

    read_ARBAC(inputFile);

    // Preprocess the ARBAC Policies
    preprocess(0);
    build_config_array();

    //Declare global variables
    declare_variables(outputFile);

    // Init global variables
    initialize_variables(outputFile);

    // Declare threads (for each user, also the simulation)
    simulate(outputFile);

    fclose(outputFile);
    free(newfile);
    free_data();
    free_precise_temp_data();
}
