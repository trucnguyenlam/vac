#include "ARBACSimplify.h"

set *configs;
int configs_size;

set *partition_users;
int partition_users_size;

set *equal_config_array;
int equal_config_array_size;

set immaterial_admins;

// Temporary variables
int max_user_config_size;
set temp_remain;

// Free the array of set
static void
free_array_set(set *sets, int sets_size)
{
    int i;

    // Free variable
    for (i = 0; i < sets_size; i++)
    {
        if (sets[i].array_size != 0)
        {
            free(sets[i].array);
            sets[i].array = 0;
        }
    }
    free(sets);
    sets = 0;
    sets_size = 0;
}

// Make the configuration set for each user
static void
make_configs()
{
    int i, j;
    int max = 0;

    // The array of each configuration for each user
    configs = malloc(user_array_size * sizeof(set));

    // Size equal to the user size
    configs_size = user_array_size;

    // Create user configuration arrays, removed user have empty configurations set
    for (i = 0; i < user_array_size; i++)
    {
        // If this is not a removed user
        if (strcmp(user_array[i], "removed_user") != 0)
        {
            configs[i].array = 0;
            configs[i].array_size = 0;
            for (j = 0; j < ua_array_size; j++)
            {
                // Not a removed user role combination
                if (ua_array[j].user_index != -13 && i == ua_array[j].user_index)
                {
                    configs[i] = add_last_element(configs[i], ua_array[j].role_index);
                }
            }
        } // If this is a removed user
        else
        {
            configs[i].array = 0;
            configs[i].array_size = -1;
        }

        // Also find the maximum size of configuration
        if (max < configs[i].array_size)
        {
            max = configs[i].array_size;
        }
    }
    // Max size of a user configuration (the maximum number of roles associated to user)
    max_user_config_size = max;
}

// Partition the configuration sets of each user by their size
static void
partition_configs()
{
    int i;

    partition_users_size = max_user_config_size + 1;
    partition_users = malloc(partition_users_size * sizeof(set));

    for (i = 0; i < partition_users_size; i++)
    {
        partition_users[i].array = 0;
        partition_users[i].array_size = 0;
    }

    for (i = 0; i < configs_size; i++)
    {
        // If there are roles associate to that user, i  is a user index
        if (configs[i].array_size != -1)
        {
            // Add the user i to the partition config of size of the configuration of user i
            // All user with the same |ROLES| is add to the partition
            partition_users[configs[i].array_size] = add_last_element(partition_users[configs[i].array_size], i);
        }
    }
}

// Recursive function to partition the configuration set of each user
static void
process_configs_recur(set group, int size_config)
{
    int i;
    set tmp, equal;

    // Equal set
    equal.array = 0;
    equal.array_size = 0;

    if (group.array_size > 0)
    {
        if (size_config == 0)
        {
            equal_config_array_size++;
            equal_config_array = realloc(equal_config_array, equal_config_array_size * sizeof(set));
            equal_config_array[equal_config_array_size - 1] = build_set(group.array, group.array_size);
            return;
        }

        tmp = build_set(configs[group.array[0]].array, configs[group.array[0]].array_size);
        equal = add_last_element(equal, group.array[0]);

        for (i = 1; i < group.array_size; i++)
        {
            if (equal_set(configs[group.array[i]], tmp))
            {
                equal = add_last_element(equal, group.array[i]);
            }
        }

        equal_config_array_size++;
        equal_config_array = realloc(equal_config_array, equal_config_array_size * sizeof(set));
        equal_config_array[equal_config_array_size - 1] = build_set(equal.array, equal.array_size);

        free(tmp.array);
        tmp.array = 0;
        tmp = duplicate_set(group);
        free(temp_remain.array);
        temp_remain = different_set(tmp, equal);

        // Call recursive procedure in the remaining group
        process_configs_recur(temp_remain, size_config);
    }
    else
    {
        free(temp_remain.array);
        return;
    }
}

// Process the configuration set of each user to find users with same role combination
static void
process_configs()
{
    int i;

    // Initialize all array of sets variable
    configs = 0;
    configs_size = 0;

    partition_users = 0;
    partition_users_size = 0;

    equal_config_array = 0;
    equal_config_array_size = 0;

    temp_remain.array = 0;
    temp_remain.array_size = 0;

    // Make array of user configuration
    make_configs();

    // Partition by number of roles in the configuration of each user
    partition_configs();

    for (i = 0; i < partition_users_size; i++)
    {
        process_configs_recur(partition_users[i], i);
    }
}

// Calculate the administrative role size
static int
admin_roles_size()
{
    int i;
    int result = 0;

    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != -13)
        {
            result++;
        }
    }

    // Plus one rule for the SUPER ROLE
    if (super_exist)
    {
        result++;
    }
    return result;
}

// Helper function of replace super user
static void
replace_super_help(int admin_role, int condition)
{
    int i;

    // Replace by super in can_assign rules
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13 && ca_array[i].admin_role_index == admin_role)
        {
            ca_array[i].admin_role_index = -10; /* Super role*/
        }
    }

    // Replace by super in can_revoke rules
    for (i = 0; i < cr_array_size; i++)
    {
        if (cr_array[i].admin_role_index != -13 && cr_array[i].admin_role_index == admin_role)
        {
            cr_array[i].admin_role_index = -10; /* Super role*/
        }
    }

    // Remove this role from admin role and make this a regular role
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != -13 && admin_role_array_index[i] == admin_role)
        {
            admin_role_array_index[i] = -13;
            break;
        }
    }
}

// Replace super in ARBAC system
static void
replace_super(int condition)
{
    int i;

    // Replace super in the can_assign and can_revoke
    for (i = 0; i < immaterial_admins.array_size; i++)
    {
        fprintf(tmp_log, "Immaterial administrative role %s is made regular\n", get_role(immaterial_admins.array[i]));
        replace_super_help(immaterial_admins.array[i], condition);
    }

    // Free variables
    free(immaterial_admins.array);
    immaterial_admins.array = 0;
    immaterial_admins.array_size = 0;
}

// Remove a user from ARBAC system
static int
remove_user(int user_index)
{
    int i;

    if (goal_user_index != -13 && user_index == goal_user_index)
    {
        return 0;
    }

    // Remove from user array
    free(user_array[user_index]);
    user_array[user_index] = 0;
    user_array[user_index] = malloc(strlen("removed_user") + 1);
    strcpy(user_array[user_index], "removed_user");

    // Remove from admin user array
    for (i = 0; i < admin_array_index_size; i++)
    {
        if (admin_array_index[i] != -13 && admin_array_index[i] == user_index)
        {
            admin_array_index[i] = -13;
        }
    }

    // Remove users from UA
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -13 && ua_array[i].user_index == user_index)
        {
            ua_array[i].user_index = -13;
        }
    }

    return 1;
}

// Helper function for the first condition of immaterial admin role
static int
immaterial_condition_1_help(int admin_role)
{
    int i;

    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13)
        {
            // Check if this admin role appear in negative form in any precondition
            if (belong_to(ca_array[i].negative_role_array, ca_array[i].negative_role_array_size, admin_role) != -1)
            {
                return 0;
            }
        }
    }

    // Initially this admin role contains a user at least
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -13 && ua_array[i].role_index == admin_role)
        {
            // Add this user to the list of promoted user
            promoted_users = add_element(promoted_users, ua_array[i].user_index);
            return 1;
        }
    }

    return 0;
}

// The first condition of immaterial admin role
static int
immaterial_condition_1()
{
    int i;
    int flag = 0;

    immaterial_admins.array = 0;
    immaterial_admins.array_size = 0;

    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != -13 && immaterial_condition_1_help(admin_role_array_index[i]))
        {
            flag = 1;

            fprintf(tmp_log, "Satisfy immaterial condition 1 ------------------------\n");
            fprintf(tmp_log, "Immaterial administrative role is %s\n", get_role(admin_role_array_index[i]));
            fprintf(tmp_log, "--------------------------------------\n");

            immaterial_admins = add_last_element(immaterial_admins, admin_role_array_index[i]);
        }
    }

    if (flag)
    {
        super_exist = 1;
        replace_super(1);
    }
    return flag;
}

// Remove spare users from the ARBAC system
static int
spare()
{
    fprintf(tmp_log, "----------------------------\n");
    fprintf(tmp_log, "----- SPARE USER CHECK -----\n");
    fprintf(tmp_log, "----------------------------\n");

    int i, j, flag = 0;

    int no_admins = admin_roles_size();

    // For the set of users with the same role combination, remove the rest apart from K+1 users
    for (i = 0; i < equal_config_array_size; i++)
    {
        // Remove spare users
        for (j = no_admins + 1; j < equal_config_array[i].array_size; j++)
        {
            fprintf(tmp_log, "Remove spare user %s from the system\n", get_user(equal_config_array[i].array[j]));
            flag += remove_user(equal_config_array[i].array[j]);
        }
    }

    free_array_set(configs, configs_size);
    free_array_set(partition_users, partition_users_size);
    free_array_set(equal_config_array, equal_config_array_size);

    return flag;
}

// The second condition of immaterial admin role
static int
immaterial_condition_2()
{
    int i, j;
    int no_admins;
    int flag = 0;

    immaterial_admins.array = 0;
    immaterial_admins.array_size = 0;

    no_admins = admin_roles_size();

    // If number of user smaller than admin role + 2 -> not satisfied
    if (user_array_size < no_admins + 2)
    {
        return 0;
    }

    // Create an array of equal configuration users
    process_configs();

    for (j = 0; j < equal_config_array_size; j++)
    {
        if (equal_config_array[j].array_size > no_admins + 1)
        {
            // Test if these users are in the administrative role
            for (i = 0; i < admin_role_array_index_size; i++)
            {
                if (admin_role_array_index[i] != -13
                    // These user have the same role membership
                    && belong_to(configs[equal_config_array[j].array[0]].array, configs[equal_config_array[j].array[0]].array_size, admin_role_array_index[i]) != -1)
                {
                    // Show that this successfully find super role
                    flag = 1;

                    fprintf(tmp_log, "Satisfy immaterial condition 2 ------------------\n");
                    fprintf(tmp_log, "Immaterial administrative role is %s\n", get_role(admin_role_array_index[i]));
                    fprintf(tmp_log, "--------------------------------------\n");

                    // Add the last member of equal_config_array[j], which is likely to be removed
                    promoted_users = add_element(promoted_users, equal_config_array[j].array[equal_config_array[j].array_size - 1]);

                    // Add this admin role to the immaterial admin roles set
                    immaterial_admins = add_last_element(immaterial_admins, admin_role_array_index[i]);
                }
            }
        }
    }

    // Indicate the role super to replace other immaterial admin roles
    if (flag)
    {
        super_exist = 1;
        replace_super(2);
    }

    // Remove spare users
    flag += spare();
    return flag;
}

// Immaterial admin role finding function
int
immaterial()
{
    fprintf(tmp_log, "----------------------------\n");
    fprintf(tmp_log, "-- IMMATERIAL ADMIN CHECK --\n");
    fprintf(tmp_log, "----------------------------\n");

    // The system does not make sense if there are no user
    if (user_array_size == 0 || role_array_size == 0)
    {
        return 0;
    }

    return (immaterial_condition_1() + immaterial_condition_2());
}
