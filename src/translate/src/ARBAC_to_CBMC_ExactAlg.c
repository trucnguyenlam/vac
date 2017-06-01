#include "ARBACExact.h"

static void
declare_variables(FILE *outputFile)
{
    int i, j;

    fprintf(outputFile, "//---------- VARIABLES DECLARATION ---------\n");

    fprintf(outputFile, "int");
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, "\t%s,\n", track_variable_name(i, j));
        }
    }

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        if (i == (NUM_USER_TO_TRACK - 1))
        {
            fprintf(outputFile, "\t%s;\n\n", associate_user_to_track_name(i));
        }
        else
        {
            fprintf(outputFile, "\t%s,\n", associate_user_to_track_name(i));
        }
    }
}

static void
configuration_user(FILE *outputFile, int user_index)
{
    int i, j;

    fprintf(outputFile, "\t//Configuration of %s\n", user_array[user_index]);

    fprintf(outputFile, "\tif (nondet_bool()){\n");

    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        if (i == 0)
        {
            fprintf(outputFile, "\t\tif (!%s) {\n", associate_user_to_track_name(i));
        }
        else
        {
            fprintf(outputFile, "\t\telse if (!%s) {\n", associate_user_to_track_name(i));
        }

        fprintf(outputFile, "\t\t\t%s = 1;\n", associate_user_to_track_name(i));

        for (j = 0; j < user_config_array[user_index].array_size; j++)
        {
            fprintf(outputFile, "\t\t\t%s = 1;\n", track_variable_name(i, user_config_array[user_index].array[j]));
        }
        fprintf(outputFile, "\t\t}\n");
    }
    fprintf(outputFile, "\t}\n\n");
}

// static void
// configuration_new_user(FILE *outputFile, int rule_index, int new_user_index)
// {
//     int i;

//     fprintf(outputFile, "\t//Configuration OF NEW_USER%d WITH %d\n", new_user_index, rule_index);

//     fprintf(outputFile, "\tif (nondet_bool()){\n");

//     for (i = 0; i < NUM_USER_TO_TRACK; i++)
//     {
//         if (i == 0)
//         {
//             fprintf(outputFile, "\t\tif (!%s) {\n", associate_user_to_track_name(i));
//         }
//         else
//         {
//             fprintf(outputFile, "\t\telse if (!%s) {\n", associate_user_to_track_name(i));
//         }
//         fprintf(outputFile, "\t\t\t%s = 1;\n", associate_user_to_track_name(i));
//         fprintf(outputFile, "\t\t\t%s = 1;\n", track_variable_name(i, ca_array[rule_index].target_role_index));
//         if (hasGoalUserMode && goal_user_index == -1)
//         {
//             fprintf(outputFile, "\t\t\t%s = 1;\n", track_variable_name(i, role_array_size - 2));
//         }
//         fprintf(outputFile, "\t\t}\n");
//     }
//     fprintf(outputFile, "\t}\n\n");
// }

static void
initialize_variables(FILE *outputFile)
{
    int i, j;

    fprintf(outputFile, "\t//---------- INITIALIZE VARIABLES ---------\n");

    // Initialize associate variable
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "\t%s = 0;\n", associate_user_to_track_name(i));
    }

    fprintf(outputFile, "\n");

    // Initialize other variables
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        for (j = 0; j < role_array_size; j++)
        {
            fprintf(outputFile, "\t%s = 0;\n", track_variable_name(i, j));
        }
    }

    fprintf(outputFile, "\n");

    fprintf(outputFile, "\t//---------- CONFIGURATION_USERS ---------\n");
    // Initialize variables by user configurations
    for (i = 0; i < user_array_size; i++)
    {
        configuration_user(outputFile, i);
    }

}

static void
print_if_conditions(FILE *outputFile, int role_index)
{
    int i;
    fprintf(outputFile, "\t\tif(");
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        if (i == 0)
        {
            fprintf(outputFile, "%s", track_variable_name(i, role_index));
        }
        else
        {
            fprintf(outputFile, " || %s", track_variable_name(i, role_index));
        }
    }
    fprintf(outputFile, "){\n");
}

static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule)
{
    int i, j;

    print_if_conditions(outputFile, ca_array[ca_rule].admin_role_index);
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "\t\t\tif(nondet_bool()){\n");
        fprintf(outputFile, "\t\t\t\tif(%s", associate_user_to_track_name(i));
        if (ca_array[ca_rule].type == 0)
        {
            for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
            {
                fprintf(outputFile, " && %s", track_variable_name(i, ca_array[ca_rule].positive_role_array[j]));
            }
            for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
            {
                fprintf(outputFile, " && !%s", track_variable_name(i, ca_array[ca_rule].negative_role_array[j]));
            }
        }
        fprintf(outputFile, "){\n");
        fprintf(outputFile, "\t\t\t\t\t%s = 1;\n", track_variable_name(i, ca_array[ca_rule].target_role_index));
        fprintf(outputFile, "\t\t\t\t}\n");
        fprintf(outputFile, "\t\t\t}\n");
    }
    fprintf(outputFile, "\t\t}\n");
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
            fprintf(outputFile, "\t\t\t//Rule with NEW in the precondition are already involved in initialization\n");
        }
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule)
{
    int i;
    print_if_conditions(outputFile, cr_array[cr_rule].admin_role_index);
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        fprintf(outputFile, "\t\t\tif(nondet_bool()){\n");
        fprintf(outputFile, "\t\t\t\tif(%s && %s){\n", associate_user_to_track_name(i), track_variable_name(i, cr_array[cr_rule].target_role_index));
        fprintf(outputFile, "\t\t\t\t\t%s = 0;\n", track_variable_name(i, cr_array[cr_rule].target_role_index));
        fprintf(outputFile, "\t\t\t\t}\n");
        fprintf(outputFile, "\t\t\t}\n");
    }

    fprintf(outputFile, "\t\t}\n");
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
simulate(FILE *outputFile)
{
    int i;

    fprintf(outputFile, "\t//---------- SIMULATION OF RULES ---------\n");

    fprintf(outputFile, "\twhile(1){\n");

    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);

    // Error state
    fprintf(outputFile, "\t\t//---------------Error------------\n");
    fprintf(outputFile, "\t\tif(");
    for (i = 0; i < NUM_USER_TO_TRACK; i++)
    {
        if (i == 0)
        {
            fprintf(outputFile, "%s==1", track_variable_name(i, goal_role_index));
        }
        else
        {
            fprintf(outputFile, " || %s==1", track_variable_name(i, goal_role_index));
        }
    }
    fprintf(outputFile, "){\n\t\t\tassert(0);\n\t\t}\n");
    fprintf(outputFile, "\t}\n");
}

void
transform_2_CBMC_ExactAlg(char *inputFile)
{
    FILE *outputFile;
    char *newfile = 0;
    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_CBMC.c") + 2);
    sprintf(newfile, "%s_ExactAlg_CBMC.c", inputFile);
    outputFile = fopen(newfile, "w");

    read_ARBAC(inputFile);

    // Preprocess the ARBAC Policies
    preprocess();
    build_config_array();

    //Specify the number of user to track
    NUM_USER_TO_TRACK = admin_role_array_index_size + 1;

    //Include
    fprintf(outputFile, "#include <stdio.h>\n");
    fprintf(outputFile, "_Bool nondet_bool();\n\n");

    //Declare variable
    declare_variables(outputFile);

    //Begin program

    fprintf(outputFile, "//---------- BEGIN MAIN PROGRAM ---------\n");

    fprintf(outputFile, "int main()\n{\n\n");
    //Initialize variables
    initialize_variables(outputFile);

    //Simulation in while loop
    simulate(outputFile);
    fprintf(outputFile, "\n}\n");

    // Cleaning up
    fclose(outputFile);
    free(newfile);

    free_data();
    free_precise_temp_data();
}