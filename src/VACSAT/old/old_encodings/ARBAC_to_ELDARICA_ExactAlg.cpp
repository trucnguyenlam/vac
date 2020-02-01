#include "ARBACExact.h"

static void declare_variables(FILE *outputFile)
{
    int i, j;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "u%d(b_%d", i, i);
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
        }
        fprintf(outputFile, ") :- b_%d=0", i);
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, ", %s=0", tracked_user_and_role(i, j));
        }
        fprintf(outputFile, ".\n");
    }
}

// Print the relation with associated variables to it
static void relation_shorthand(FILE *outputFile, int user_index)
{
    int i;
    fprintf(outputFile, "u%d(b_%d", user_index, user_index);
    for (i = 0; i < role_array_size; i++)
    {
        fprintf(outputFile, ", %s", tracked_user_and_role(user_index, i));
    }
    fprintf(outputFile, ")");
}

// Print the relation with associated variables to it
static void relation_with_admin_shorthand(FILE *outputFile, int user_index, int admin_role_index)
{
    relation_shorthand(outputFile, user_index);
    fprintf(outputFile, ", b_%d=1", user_index);
    fprintf(outputFile, ", %s=1", tracked_user_and_role(user_index, admin_role_index));
}

static void
configuration_user(FILE *outputFile, int user_index)
{
    int i, j;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "u%d(b_%d_1", i, i);

        for (j = 0; j < role_array_size; j++)
        {
            if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
            {
                fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
            }
            else
            {
                fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
            }
        }
        fprintf(outputFile, ") :- ");

        relation_shorthand(outputFile, i);

        fprintf(outputFile, ", b_%d=0, b_%d_1=1", i, i);
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, ", %s=0", tracked_user_and_role(i, j));
            if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
            {
                fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
            }
        }
        fprintf(outputFile, ".\n");
    }
}

static void
configuration_user_with_counter(FILE *outputFile, int user_index, int i)
{
    int j;

    fprintf(outputFile, "u%d(b_%d_1", i, i);

    for (j = 0; j < role_array_size; j++)
    {
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
        {
            fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
        }
        else
        {
            fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
        }
    }
    fprintf(outputFile, ") :- ");

    relation_shorthand(outputFile, i);

    fprintf(outputFile, ", b_%d=0, b_%d_1=1", i, i);
    for (j = 0; j < role_array_size; j++)
    {
        fprintf(outputFile, ", %s=0", tracked_user_and_role(i, j));
        if (belong_to(user_config_array[user_index].array, user_config_array[user_index].array_size, j))
        {
            fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
        }
    }
    fprintf(outputFile, ".\n");
}

// static void
// configuration_new_user(FILE *outputFile, int role_index)
// {
//     int i, j;

//     for (i = 0; i < NUM_USER_TO_TRACK; i++)
//     {
//         fprintf(outputFile, "u%d(b_%d_1", i, i);

//         for (j = 0; j < role_array_size; j++)
//         {
//             if (j == role_index)
//             {
//                 fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
//             }
//             else if (j == role_array_size - 2 && hasGoalUserMode && goal_user_index == -1)
//             {
//                 fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
//             }
//             else
//             {
//                 fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
//             }
//         }
//         fprintf(outputFile, ") :- ");

//         relation_shorthand(outputFile, i);

//         fprintf(outputFile, ", b_%d=0, b_%d_1=1", i, i);
//         for (j = 0; j < role_array_size; j++)
//         {
//             fprintf(outputFile, ", %s=0", tracked_user_and_role(i, j));
//             if (j == role_index)
//             {
//                 fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
//             }
//             if (j == role_array_size - 2 && hasGoalUserMode && goal_user_index == -1)
//             {
//                 fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
//             }
//         }
//         fprintf(outputFile, ".\n");
//     }
// }

// static void
// configuration_new_user_with_counter(FILE *outputFile, int role_index, int i)
// {
//     int j;

//     fprintf(outputFile, "u%d(b_%d_1", i, i);

//     for (j = 0; j < role_array_size; j++)
//     {
//         if (j == role_index)
//         {
//             fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
//         }
//         else if (j == role_array_size - 2 && hasGoalUserMode && goal_user_index == -1)
//         {
//             fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
//         }
//         else
//         {
//             fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
//         }
//     }
//     fprintf(outputFile, ") :- ");

//     relation_shorthand(outputFile, i);

//     fprintf(outputFile, ", b_%d=0, b_%d_1=1", i, i);
//     for (j = 0; j < role_array_size; j++)
//     {
//         fprintf(outputFile, ", %s=0", tracked_user_and_role(i, j));
//         if (j == role_index)
//         {
//             fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
//         }
//         if (j == role_array_size - 2 && hasGoalUserMode && goal_user_index == -1)
//         {
//             fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, j));
//         }
//     }
//     fprintf(outputFile, ".\n");
// }

// Initialize configuration of user
static void initialize_variables(FILE *outputFile)
{
    int i;

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

        // // For new user mode only
        // if (hasNewUserMode)
        // {
        //     for (i = 0; i < initialize_role_array_size; i++)
        //     {
        //         configuration_new_user(outputFile, initialize_role_array[i]);
        //     }
        // }
    }
    else
    {
        int counter = 0;
        for (i = 0; i < user_array_size; i++)
        {
            configuration_user_with_counter(outputFile, i, counter);
            counter++;
        }

        // // For new user mode only
        // if (hasNewUserMode)
        // {
        //     for (i = 0; i < initialize_role_array_size; i++)
        //     {
        //         configuration_new_user_with_counter(outputFile, initialize_role_array[i], counter);
        //         counter++;
        //     }
        // }
    }
}

static void simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j, k, h;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (h = 0; h < NUM_USER_TO_TRACK; h++)
        {
            fprintf(outputFile, "u%d(b_%d", i, i);
            for (j = 0; j < role_array_size; j++)
            {
                if (j != ca_array[ca_rule].target_role_index)
                {
                    fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
                }
                else
                {
                    fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
                }
            }
            fprintf(outputFile, ") :- ");

            // Condition of the administrator
            relation_with_admin_shorthand(outputFile, h, ca_array[ca_rule].admin_role_index);

            // User coherent condition
            fprintf(outputFile, ", ");
            relation_shorthand(outputFile, i);
            fprintf(outputFile, ", b%d=1", i);
            for (k = 0; k < role_array_size; k++)
            {
                if (belong_to(ca_array[ca_rule].positive_role_array, ca_array[ca_rule].positive_role_array_size, k))
                {
                    fprintf(outputFile, ", %s=1", tracked_user_and_role(i, k));
                }
                else if (belong_to(ca_array[ca_rule].negative_role_array, ca_array[ca_rule].negative_role_array_size, k))
                {
                    fprintf(outputFile, ", %s=0", tracked_user_and_role(i, k));
                }
                else if (k == ca_array[ca_rule].target_role_index)
                {
                    fprintf(outputFile, ", %s_1=1", tracked_user_and_role(i, k));
                }
            }
            fprintf(outputFile, ".\n");
        }
    }
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].type != 2)
        {
            simulate_can_assign_rule(outputFile, i);
        }
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i, j, h;

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (h = 0; h < NUM_USER_TO_TRACK; h++)
        {
            fprintf(outputFile, "u%d(b_%d", i, i);
            for (j = 0; j < role_array_size; j++)
            {
                if (j != cr_array[cr_rule].target_role_index)
                {
                    fprintf(outputFile, ", %s", tracked_user_and_role(i, j));
                }
                else
                {
                    fprintf(outputFile, ", %s_1", tracked_user_and_role(i, j));
                }
            }
            fprintf(outputFile, ") :- ");
            relation_with_admin_shorthand(outputFile, h, cr_array[cr_rule].admin_role_index);
            fprintf(outputFile, ", ");
            relation_shorthand(outputFile, i);
            fprintf(outputFile, ", b%d=1", i);
            fprintf(outputFile, ", %s=1", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
            fprintf(outputFile, ", %s_1=0", tracked_user_and_role(i, cr_array[cr_rule].target_role_index));
            fprintf(outputFile, ".\n");
        }
    }
}

static void simulate_can_revokes(FILE *outputFile)
{
    int i;
    for (i = 0; i < cr_array_size; i++)
    {
        simulate_can_revoke_rule(outputFile, i);
    }
}

static void query(FILE *outputFile)
{
    int i;
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "false :- ");
        relation_with_admin_shorthand(outputFile, i, goal_role_index);
        fprintf(outputFile, ".\n");
    }
}

static void simulate(FILE *outputFile)
{
    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);
    // Query the error state
    query(outputFile);
}


void transform_2_ELDARICA_ExactAlg(char *inputFile, FILE *outputFile)
{
    /*
    FILE *outputFile;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_ELDARICA.horn") + 2);
    sprintf(newfile, "%s_ExactAlg_ELDARICA.horn", inputFile);
    outputFile = fopen(newfile, "w");
    */

    read_ARBAC(inputFile);

    // Preprocess the ARBAC Policies
    preprocess(1);

    // Build user configuration array
    build_config_array();

    //Specify the number of user to track
    NUM_USER_TO_TRACK = admin_role_array_index_size + 1;

    //Declare variable
    declare_variables(outputFile);

    //Begin program

    //Initialize variables
    initialize_variables(outputFile);

    //Simulation in while loop
    simulate(outputFile);

    //fclose(outputFile);
    //free(newfile);

    free_data();
    free_precise_temp_data();
}
