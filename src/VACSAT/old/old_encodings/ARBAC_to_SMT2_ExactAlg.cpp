#include "ARBACExact.h"

static void
declare_variables(FILE *outputFile)
{
    int i, j;

    // Declare Fixedpoint
    fprintf(outputFile, "; Declare options and fixedpoint\n");
    fprintf(outputFile, "(set-logic HORN)\n");

    fprintf(outputFile, ";---------- FUNCTION DECLARATION ---------\n");

    // Declare Relations
    fprintf(outputFile, "; Declare the relations, each relation manage one intended user\n");
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "(declare-fun u%d (Bool", i);
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " Bool");
        }
        // Return value of the function in Boolean
        fprintf(outputFile, ") Bool)\n");
    }
}

// Print the relation with associated variables to it
static void
relation_shorthand(FILE *outputFile, int user_index)
{
    int i;
    fprintf(outputFile, "(u%d %s", user_index, tracked_user_var(user_index));
    for (i = 0; i < role_array_size; i++)
    {
        fprintf(outputFile, " %s", tracked_user_and_role(user_index, i));
    }
    fprintf(outputFile, ")");
}

static void
admin_condition_shorthand(FILE *outputFile, int user_index, int admin_role_index)
{
    fprintf(outputFile, " (and ");
    relation_shorthand(outputFile, user_index);
    fprintf(outputFile, " (= %s true)", tracked_user_var(user_index));
    fprintf(outputFile, " (= %s true)", tracked_user_and_role(user_index, admin_role_index));
    fprintf(outputFile, ")");
}

static void
configuration_user(FILE *outputFile, int user_index)
{
    int i, j;

    fprintf(outputFile, "; Configuration of %s\n", user_array[user_index]);

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "(assert (forall (");
        fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
        fprintf(outputFile, " (%s_1 Bool)", tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
            if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
            {
                fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
            }
        }
        fprintf(outputFile, ") (=> (and ");
        relation_shorthand(outputFile, i);
        fprintf(outputFile, " (= %s false)", tracked_user_var(i));
        fprintf(outputFile, " (= %s_1 true)", tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " (= %s false)", tracked_user_and_role(i, j));
            if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
            {
                fprintf(outputFile, " (= %s_1 true)", tracked_user_and_role(i, j));
            }
        }
        fprintf(outputFile, ") ");
        fprintf(outputFile, "(u%d %s_1", i, tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
            {
                fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
            }
            else
            {
                fprintf(outputFile, " %s", tracked_user_and_role(i, j));
            }
        }
        fprintf(outputFile, "))))\n");
    }
}

static void
configuration_user_with_counter(FILE *outputFile, int user_index, int i)
{
    int j;

    fprintf(outputFile, "; Configuration of %s\n", user_array[user_index]);

    fprintf(outputFile, "(assert (forall (");
    fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
    fprintf(outputFile, " (%s_1 Bool)", tracked_user_var(i));
    for (j = 0; j < role_array_size; j++)
    {
        fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
        {
            fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
        }
    }
    fprintf(outputFile, ") (=> (and ");
    relation_shorthand(outputFile, i);
    fprintf(outputFile, " (= %s false)", tracked_user_var(i));
    fprintf(outputFile, " (= %s_1 true)", tracked_user_var(i));
    for (j = 0; j < role_array_size; j++)
    {
        fprintf(outputFile, " (= %s false)", tracked_user_and_role(i, j));
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
        {
            fprintf(outputFile, " (= %s_1 true)", tracked_user_and_role(i, j));
        }
    }
    fprintf(outputFile, ") ");
    fprintf(outputFile, "(u%d %s_1", i, tracked_user_var(i));
    for (j = 0; j < role_array_size; j++)
    {
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
        {
            fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
        }
        else
        {
            fprintf(outputFile, " %s", tracked_user_and_role(i, j));
        }
    }
    fprintf(outputFile, "))))\n");
}

static void
initialize_variables(FILE *outputFile)
{
    int i, j;

    fprintf(outputFile, "\n;---------- INITIALIZE VARIABLES ---------\n");

    // Initialize variables
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "(assert (forall (");
        fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
        }
        fprintf(outputFile, ") (=> (and");
        fprintf(outputFile, " (= %s false)", tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " (= %s false)", tracked_user_and_role(i, j));
        }
        fprintf(outputFile, ") ");
        relation_shorthand(outputFile, i);
        fprintf(outputFile, ")))\n");
    }

    // Initialize variables by user configurations
    fprintf(outputFile, "\n;---------- CONFIGURATION_USERS ---------\n");

    int NUM_USER_IN_SYSTEM = user_array_size;
    // if (hasNewUserMode)
    // {
    //     NUM_USER_IN_SYSTEM += initialize_role_array_size;
    // }

    // There will be two cases for this
    if (NUM_USER_IN_SYSTEM > NUM_USER_TO_TRACK)
    {
        for (i = 0; i < user_array_size; i++)
        {
            configuration_user(outputFile, i);
        }
    }
    else
    {
        int counter = 0;
        for (i = 0; i < user_array_size; i++)
        {
            configuration_user_with_counter(outputFile, i, counter);
            counter++;
        }
    }

    fprintf(outputFile, "\n");
}

static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j, k;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (k = 0; k < NUM_USER_TO_TRACK; k++)
        {
            if (k == i)
            {
                fprintf(outputFile, "(assert (forall (");
                fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
                    if (j == ca_array[ca_rule].target_role_index)
                    {
                        fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, ") ");
                fprintf(outputFile, "(=> ");
                // Condition
                fprintf(outputFile, "(and ");
                admin_condition_shorthand(outputFile, i, ca_array[ca_rule].admin_role_index);
                fprintf(outputFile, " (= %s true)", tracked_user_var(i));
                if (ca_array[ca_rule].type == 0)
                {
                    for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
                    {
                        fprintf(outputFile, " (= %s true)", tracked_user_and_role(i, ca_array[ca_rule].positive_role_array[j]));
                    }
                    for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
                    {
                        fprintf(outputFile, " (= %s false)", tracked_user_and_role(i, ca_array[ca_rule].negative_role_array[j]));
                    }
                }
                fprintf(outputFile, " (= %s false) ", tracked_user_and_role(i, ca_array[ca_rule].target_role_index));
                fprintf(outputFile, " (= %s_1 true))", tracked_user_and_role(i, ca_array[ca_rule].target_role_index));
                // Execution
                fprintf(outputFile, "(u%d %s", i, tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    if (j != ca_array[ca_rule].target_role_index)
                    {
                        fprintf(outputFile, " %s", tracked_user_and_role(i, j));
                    }
                    else
                    {
                        fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, "))))\n");
            }
            else
            {
                fprintf(outputFile, "(assert (forall (");
                fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
                    if (j == ca_array[ca_rule].target_role_index)
                    {
                        fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, " (%s Bool)", tracked_user_var(k));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(k, j));
                }
                fprintf(outputFile, ") ");
                fprintf(outputFile, "(=> ");
                // Condition
                fprintf(outputFile, "(and ");
                admin_condition_shorthand(outputFile, k, ca_array[ca_rule].admin_role_index);
                fprintf(outputFile, " (= %s true)", tracked_user_var(i));
                if (ca_array[ca_rule].type == 0)
                {
                    for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
                    {
                        fprintf(outputFile, " (= %s true)", tracked_user_and_role(i, ca_array[ca_rule].positive_role_array[j]));
                    }
                    for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
                    {
                        fprintf(outputFile, " (= %s false)", tracked_user_and_role(i, ca_array[ca_rule].negative_role_array[j]));
                    }
                }
                fprintf(outputFile, " (= %s false) ", tracked_user_and_role(i, ca_array[ca_rule].target_role_index));
                relation_shorthand(outputFile, i);
                fprintf(outputFile, " (= %s_1 true))", tracked_user_and_role(i, ca_array[ca_rule].target_role_index));
                // Execution
                fprintf(outputFile, "(u%d %s", i, tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    if (j != ca_array[ca_rule].target_role_index)
                    {
                        fprintf(outputFile, " %s", tracked_user_and_role(i, j));
                    }
                    else
                    {
                        fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, "))))\n");
            }
        }
    }
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        print_ca_comment_smt2(outputFile, i);
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
        else
        {
            fprintf(outputFile, ";Rule with NEW in the precondition are already involved in initialization\n");
        }
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i, j, k;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (k = 0; k < NUM_USER_TO_TRACK; k++)
        {
            if (k == i)
            {
                fprintf(outputFile, "(assert (forall (");
                fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
                    if (j == cr_array[cr_rule].target_role_index)
                    {
                        fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, ") ");
                fprintf(outputFile, "(=> ");
                // Condition
                fprintf(outputFile, "(and ");
                admin_condition_shorthand(outputFile, i, cr_array[cr_rule].admin_role_index);
                fprintf(outputFile, " (= %s true)", tracked_user_var(i));
                fprintf(outputFile, " (= %s true) ", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
                fprintf(outputFile, " (= %s_1 false))", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
                // Execution
                fprintf(outputFile, "(u%d %s", i, tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    if (j != cr_array[cr_rule].target_role_index)
                    {
                        fprintf(outputFile, " %s", tracked_user_and_role(i, j));
                    }
                    else
                    {
                        fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, "))))\n");
            }
            else
            {
                fprintf(outputFile, "(assert (forall (");
                fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
                    if (j == cr_array[cr_rule].target_role_index)
                    {
                        fprintf(outputFile, " (%s_1 Bool)", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, " (%s Bool)", tracked_user_var(k));
                for (j = 0; j < role_array_size; j++)
                {
                    fprintf(outputFile, " (%s Bool)", tracked_user_and_role(k, j));
                }
                fprintf(outputFile, ") ");
                fprintf(outputFile, "(=> ");
                // Condition
                fprintf(outputFile, "(and ");
                admin_condition_shorthand(outputFile, k, cr_array[cr_rule].admin_role_index);
                fprintf(outputFile, " (= %s true)", tracked_user_var(i));
                fprintf(outputFile, " (= %s true) ", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
                relation_shorthand(outputFile, i);
                fprintf(outputFile, " (= %s_1 false))", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
                // Execution
                fprintf(outputFile, "(u%d %s", i, tracked_user_var(i));
                for (j = 0; j < role_array_size; j++)
                {
                    if (j != cr_array[cr_rule].target_role_index)
                    {
                        fprintf(outputFile, " %s", tracked_user_and_role(i, j));
                    }
                    else
                    {
                        fprintf(outputFile, " %s_1", tracked_user_and_role(i, j));
                    }
                }
                fprintf(outputFile, "))))\n");
            }
        }
    }
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i;
    for (i = 0; i < cr_array_size; i++)
    {
        print_cr_comment_smt2(outputFile, i);
        simulate_can_revoke_rule(outputFile, i);
    }
}

static void
query(FILE *outputFile)
{
    int i, j;
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "(assert (not (exists (");
        fprintf(outputFile, " (%s Bool)", tracked_user_var(i));
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, " (%s Bool)", tracked_user_and_role(i, j));
        }
        fprintf(outputFile, ") (and (= %s true) ", tracked_user_and_role(i, goal_role_index));
        relation_shorthand(outputFile, i);
        fprintf(outputFile, "))))\n");
    }
}

static void
simulate(FILE *outputFile)
{
    fprintf(outputFile, ";---------- SIMULATION OF RULES ---------\n");

    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);

    // Query the error state
    fprintf(outputFile, ";------------- The query ------------\n");
    query(outputFile);
    fprintf(outputFile, "(check-sat)\n");
}

void
transform_2_SMT2_ExactAlg(char *inputFile, FILE *outputFile)
{
    /*
    FILE *outputFile;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_SMT.smt2") + 2);
    sprintf(newfile, "%s_ExactAlg_SMT.smt2", inputFile);
    outputFile = fopen(newfile, "w");
    */

    read_ARBAC(inputFile);

    // Preprocess the ARBAC Policies
    preprocess(1);

    // Build user configuration array
    build_config_array();

    //Specify the number of user to track, exactly equal to the number of users
    NUM_USER_TO_TRACK = user_array_size;

    //Declare variable
    declare_variables(outputFile);

    //Initialize variables
    initialize_variables(outputFile);

    //Simulation in while loop
    simulate(outputFile);

    //fclose(outputFile);
    //free(newfile);
    free_data();
    free_precise_temp_data();
}
