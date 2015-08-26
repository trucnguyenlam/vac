#include "ARBACExact.h"

// Build the configuration for each user of the system
void
build_config_array()
{
    int i;

    user_config_array_size = user_array_size;
    user_config_array = malloc(user_config_array_size * sizeof(set));

    // Initialize this array
    for (i = 0; i < user_config_array_size; i++)
    {
        user_config_array[i].array = 0;
        user_config_array[i].array_size = 0;
    }

    // Add role to each user configuration
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -1) // In case of GOAL USER
        {
            user_config_array[ua_array[i].user_index] = add_last_element(user_config_array[ua_array[i].user_index], ua_array[i].role_index);
        }
    }
}

static char *
int2str(int i)
{
    char buffer[10];
    sprintf(buffer, "%d", i);
    return strdup(buffer);
}

// Return the track variable name
char *
track_variable_name(int index_user_to_track, int role_index)
{
    char track_name[100] = "track_";
    char temp[90] = "";

    strcpy(temp, int2str(index_user_to_track));

    strcat(track_name, temp);
    strcat(track_name, "_");

    memset(temp, 0, sizeof(temp));

    strcpy(temp, role_array[role_index]);

    strcat(track_name, temp);

    return strdup(track_name);
}

// Return the associate variable to user name
char *
associate_user_to_track_name(int index_user_to_track)
{
    char variable_name[20] = "b_";
    char temp[10] = "";

    strcpy(temp, int2str(index_user_to_track));

    strcat(variable_name, temp);

    return strdup(variable_name);
}

void
free_precise_temp_data()
{
    int i;

    for (i = 0; i < user_config_array_size; i++)
    {
        free(user_config_array[i].array);
    }
    free(user_config_array);
}
