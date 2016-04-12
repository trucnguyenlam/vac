#include "ARBACExact.h"

// Build the configuration for each user of the system
void
build_config_array()
{
    int i;

    user_config_array_size = user_array_size;
    user_config_array = calloc(user_config_array_size, sizeof(set));

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

// Return the track variable name
char *
tracked_user_and_role(int index_user_to_track, int role_index)
{
    char buffer[1000];

    snprintf(buffer, 1000, "track_%d_%s",
        index_user_to_track, role_array[role_index]);

    return strdup(buffer);
}

// Return the associate variable to user name
char *
tracked_user_var(int index_user_to_track)
{
    char buffer[100];

    snprintf(buffer, 100, "b_%d", index_user_to_track);

    return strdup(buffer);
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
