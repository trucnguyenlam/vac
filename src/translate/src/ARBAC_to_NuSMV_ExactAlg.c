#include "ARBACExact.h"

// set *new_user_config_array;
// int new_user_config_array_size;
// static void
// build_config_new_user(void)
// {
//     int i;

//     new_user_config_array_size = initialize_role_array_size;
//     new_user_config_array = malloc(new_user_config_array_size * sizeof(set));

//     for (i = 0; i < new_user_config_array_size; i++)
//     {
//         new_user_config_array[i].array_size = 0;
//         new_user_config_array[i].array = 0;
//     }

//     for (i = 0; i < initialize_role_array_size; i++)
//     {
//         new_user_config_array[i] = add_element(new_user_config_array[i], initialize_role_array[i]);
//     }

//     if (hasGoalUserMode && goal_user_index == -1)
//     {
//         // Add toCheckRole to user configuration array
//         for (i = 0; i < new_user_config_array_size; i++)
//         {
//             new_user_config_array[i] = add_element(new_user_config_array[i], role_array_size - 2);
//         }
//     }
// }

static int
calculate_pc()
{
    int ret;

    ret = user_array_size + 1 + ca_array_size + cr_array_size;

    // if (hasNewUserMode)
    // {
    //     ret += initialize_role_array_size;
    // }

    return ret;
}

static void
declare_variables(FILE *outputFile)
{
    int i, j;

    fprintf(outputFile, "---------- VARIABLES DECLARATION ---------\n");

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, "%s : boolean;\n", track_variable_name(i, j));
        }
    }

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "%s : boolean;\n", associate_user_to_track_name(i));
    }

    // Program Counter
    fprintf(outputFile, "pc : 0..%d;\n", calculate_pc());
    fprintf(outputFile, "nondet : boolean;\n");

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "nondet%d : boolean;\n", i);
    }

    fprintf(outputFile, "\n");
}

static void
initialize_variables(FILE *outputFile)
{
    int i, j;

    fprintf(outputFile, "\t---------- INITIALIZE VARIABLES ---------\n");

    // Initialize associate variable
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "\tinit(%s) := FALSE;\n", associate_user_to_track_name(i));
    }

    // Initialize other variables
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, "\tinit(%s) := FALSE;\n", track_variable_name(i, j));
        }
    }

    fprintf(outputFile, "\tinit(pc) := 0;\n");

    fprintf(outputFile, "\n");

}

static void
simulate_associated_user(FILE *outputFile)
{
    int i, j, k;
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "\tnext(%s) := case\n", associate_user_to_track_name(i));
        for (j = 0; j < user_array_size; j++)
        {
            fprintf(outputFile, "\t\tnondet & pc=%d", j + 1);

            for (k = i - 1; k >= 0; k--)
            {
                fprintf(outputFile, " & %s", associate_user_to_track_name(k));
            }

            fprintf(outputFile, " & !%s : TRUE;\n", associate_user_to_track_name(i));
        }
        // if (hasNewUserMode)
        // {
        //     for (j = 0 ; j < initialize_role_array_size; j++)
        //     {
        //         fprintf(outputFile, "\t\tnondet & pc=%d", user_array_size + j + 1);

        //         for (k = i - 1; k >= 0; k--)
        //         {
        //             fprintf(outputFile, " & %s", associate_user_to_track_name(k));
        //         }

        //         fprintf(outputFile, " & !%s : TRUE;\n", associate_user_to_track_name(i));
        //     }
        // }
        fprintf(outputFile, "\t\tTRUE : %s;\n", associate_user_to_track_name(i));
        fprintf(outputFile, "\tesac;\n\n");
    }
}

static void
simulate_track_user(FILE *outputFile)
{
    int i, j, k, l;
    int padding = 0;
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, "\tnext(%s) := case\n", track_variable_name(i, j));

            // Simulate user configuration
            for (k = 0; k < user_config_array_size; k++)
            {
                if (belong_to(user_config_array[k].array, user_config_array[k].array_size, j))
                {
                    fprintf(outputFile, "\t\tnondet & pc=%d", k + 1);

                    for (l = i - 1; l >= 0; l--)
                    {
                        fprintf(outputFile, " & %s", associate_user_to_track_name(l));
                    }

                    fprintf(outputFile, " & !%s : TRUE;\n", associate_user_to_track_name(i));
                }
            }

            // // New user
            // if (hasNewUserMode)
            // {
            //     padding = initialize_role_array_size;
            //     for (k = 0; k < new_user_config_array_size; k++)
            //     {
            //         if (belong_to(new_user_config_array[k].array, new_user_config_array[k].array_size, j))
            //         {
            //             fprintf(outputFile, "\t\tnondet & pc=%d", user_array_size + k + 1);

            //             for (l = i - 1; l >= 0; l--)
            //             {
            //                 fprintf(outputFile, " & %s", associate_user_to_track_name(l));
            //             }

            //             fprintf(outputFile, " & !%s : TRUE;\n", associate_user_to_track_name(i));
            //         }
            //     }
            // }

            // Simulate on can assign rule
            for (k = 0; k < ca_array_size; k++)
            {
                if (j == ca_array[k].target_role_index)
                {
                    if (ca_array[k].type == 2) // New rule
                    {
                        fprintf(outputFile, "\t\tnondet%d & pc=%d : %s;\n", i, user_array_size + 1 + padding + k, track_variable_name(i, j));
                    }
                    else
                    {
                        fprintf(outputFile, "\t\tnondet%d & pc=%d & (", i, user_array_size + 1 + padding + k);
                        for (l = 0; l < NUM_USER_TO_TRACK; l++)
                        {
                            if (l == 0)
                            {
                                fprintf(outputFile, " %s", track_variable_name(l, ca_array[k].admin_role_index));
                            }
                            else
                            {
                                fprintf(outputFile, " | %s", track_variable_name(l, ca_array[k].admin_role_index));
                            }
                        }
                        fprintf(outputFile, ") & %s", associate_user_to_track_name(i));

                        if (ca_array[k].type == 0)
                        {
                            for (l = 0; l < ca_array[k].positive_role_array_size; l++)
                            {
                                fprintf(outputFile, " & %s", track_variable_name(i, ca_array[k].positive_role_array[l]));
                            }
                            for (l = 0; l < ca_array[k].negative_role_array_size; l++)
                            {
                                fprintf(outputFile, " & !%s", track_variable_name(i, ca_array[k].negative_role_array[l]));
                            }
                        }
                        fprintf(outputFile, " : TRUE;\n");
                    }
                }
            }

            // Simulate on CR rules

            for (k = 0; k < cr_array_size; k++)
            {
                if (j == cr_array[k].target_role_index)
                {
                    fprintf(outputFile, "\t\tnondet%d & pc=%d & (", i, user_array_size + 1 + ca_array_size + padding + k);
                    for (l = 0; l < NUM_USER_TO_TRACK; l++)
                    {
                        if (l == 0)
                        {
                            fprintf(outputFile, " %s", track_variable_name(l, cr_array[k].admin_role_index));
                        }
                        else
                        {
                            fprintf(outputFile, " | %s", track_variable_name(l, cr_array[k].admin_role_index));
                        }
                    }
                    fprintf(outputFile, ") & %s : FALSE;\n", associate_user_to_track_name(i));
                }
            }

            fprintf(outputFile, "\t\tTRUE : %s;\n", track_variable_name(i, j));
            fprintf(outputFile, "\tesac;\n\n");
        }
    }
}

static void
simulate_pc(FILE *outputFile)
{
    fprintf(outputFile, "\tnext(pc) := case\n");
    // if (hasNewUserMode)
    // {
    //     fprintf(outputFile, "\t\tpc<%d : pc+1;\n", user_array_size + 1 + ca_array_size + cr_array_size + initialize_role_array_size);
    //     fprintf(outputFile, "\t\tpc=%d : %d;\n", user_array_size + 1 + ca_array_size + cr_array_size + initialize_role_array_size, user_array_size + 1 + initialize_role_array_size);
    // }
    // else
    // {
    fprintf(outputFile, "\t\tpc<%d : pc+1;\n", user_array_size + 1 + ca_array_size + cr_array_size);
    fprintf(outputFile, "\t\tpc=%d : %d;\n", user_array_size + 1 + ca_array_size + cr_array_size, user_array_size + 1);
    // }
    fprintf(outputFile, "\t\tTRUE : pc;\n");
    fprintf(outputFile, "\tesac;\n\n");
}

static void
simulate(FILE *outputFile)
{
    int i;

    fprintf(outputFile, "\t---------- SIMULATION ---------\n");

    simulate_associated_user(outputFile);

    simulate_track_user(outputFile);

    simulate_pc(outputFile);

    // Error state
    fprintf(outputFile, "------------ REACHABILITY CHECK ------------\n");
    fprintf(outputFile, "LTLSPEC G (");
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        if (i == 0)
        {
            fprintf(outputFile, "!%s", track_variable_name(i, goal_role_index));
        }
        else
        {
            fprintf(outputFile, " & !%s", track_variable_name(i, goal_role_index));
        }
    }
    fprintf(outputFile, ")\n");
}

void
transform_2_NuSMV_ExactAlg(char *inputFile)
{
    FILE *outputFile;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_NuSMV.smv") + 2);
    sprintf(newfile, "%s_ExactAlg_NuSMV.smv", inputFile);
    outputFile = fopen(newfile, "w");

    read_ARBAC(inputFile);

    // Preprocess the ARBAC Policies
    preprocess();

    // if (hasNewUserMode)
    // {
    //     build_config_new_user();
    // }

    //Specify the number of user to track
    NUM_USER_TO_TRACK = admin_role_array_index_size + 1;

    build_config_array();

    fprintf(outputFile, "MODULE main\n");
    fprintf(outputFile, "VAR\n");

    //Declare variable
    declare_variables(outputFile);

    //Begin program
    fprintf(outputFile, "ASSIGN\n");

    //Initialize variables
    initialize_variables(outputFile);

    //Simulation in while loop
    simulate(outputFile);

    fclose(outputFile);
    free(newfile);

    free_data();
    free_precise_temp_data();
}