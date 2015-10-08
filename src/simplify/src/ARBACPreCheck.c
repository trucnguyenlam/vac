#include "ARBACSimplify.h"

static int
partition(int a[], int l, int r)
{
    int pivot, i, j, t;
    pivot = a[l];
    i = l; j = r + 1;

    while (1)
    {
        do ++i; while ( ca_array[a[i]].positive_role_array_size <= ca_array[pivot].positive_role_array_size && i <= r );
        do --j; while ( ca_array[a[j]].positive_role_array_size > ca_array[pivot].positive_role_array_size );
        if ( i >= j ) break;
        t = a[i]; a[i] = a[j]; a[j] = t;
    }
    t = a[l]; a[l] = a[j]; a[j] = t;
    return j;
}

/**
 * Borrowed quick sort algorithm
 */
static void
quickSort(int a[], int l, int r)
{
    int j;

    if ( l < r )
    {
        j = partition( a, l, r);
        quickSort( a, l, j - 1);
        quickSort( a, j + 1, r);
    }
}

// Write simplification trace in order to find counter example
static void
write_trace(FILE *output)
{
    int i;
    fprintf(output, "Trace\n");
    for (i = 0; i < trace_array_size; i++)
    {
        fprintf(output, "%d -> %d -> %d + %d -> %d + %d\n", trace_array[i].simplify_rule, trace_array[i].affected_role_index, trace_array[i].affected_rule_index, trace_array[i].affected_rule_type,
                trace_array[i].related_rule_index, trace_array[i].related_rule_type);
    }
    fprintf(output, "EndTrace\n");
}

/**
 * Return index of the user that will become the SUPER_USER
 */
static int
candidate_SUPER_USER(void)
{
    int i = -1;
    for (i = promoted_users.array_size - 1; i >= 0; i--)
    {
        // make sure that user is not removed
        if (0 <= promoted_users.array[i]
                && promoted_users.array[i] < user_array_size
                // && strcmp(user_array[promoted_users.array[i]], "removed_user") != 0
           )
        {
            return i;
        }
    }
    return i;
}

static void
write_small_policy(int hasPruning, int rules[], int rules_size, char *inputFile)
{
    int i, j, flag, flag2 = 0, count = 0;
    int keep_roles[role_array_size];
    int keep_users[user_array_size];
    int hasSuper = 0;
    FILE *output;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_reduceAdmin.arbac") + 2);
    sprintf(newfile, "%s_reduceAdmin.arbac", inputFile);
    output = fopen(newfile, "w");

    fprintf(tmplog, "Pre-checking ARBAC Policy successful. There is no need to perform pruning algorithm.\n");

    fprintf(simplifyLog, "---------------------------------------------\nSIMPLIFICATION LOG\n---------------------------------------------\n");

    // Create a quick dictionary
    for (i = 0; i < role_array_size; i++)
    {
        keep_roles[i] = 0;
    }
    for (i = 0; i < user_array_size; i++)
    {
        keep_users[i] = 0;
    }

    // Roles: keep all role Admin, target, roles in the precondition at that time
    for (i = 0; i < rules_size; i++)
    {
        if (ca_array[rules[i]].admin_role_index != -10)
        {
            keep_roles[ca_array[rules[i]].admin_role_index] = 1;
        }
        else
        {
            // There exist super role and super user
            hasSuper = 1;
        }

        for (j = 0; j < ca_array[rules[i]].positive_role_array_size; j++)
        {
            keep_roles[ca_array[rules[i]].positive_role_array[j]] = 1;
        }

        for (j = 0; j < ca_array[rules[i]].negative_role_array_size; j++)
        {
            keep_roles[ca_array[rules[i]].negative_role_array[j]] = 1;
        }

        keep_roles[ca_array[rules[i]].target_role_index] = 1;
    }

    int super_user_index = -1;

    // Users: keep Admin user, goal user (if present), otherwise a user with nothing in the configuration
    if (!hasPruning) // Not yet performing pruning
    {
        for (i = 0; i < ua_array_size; i++)
        {
            if(ua_array[i].user_index != -13
                && ua_array[i].user_index != -10
                && belong_to(admin_role_array_index, admin_role_array_index_size, ua_array[i].role_index) != -1)
            {
                keep_users[ua_array[i].user_index] = 1; // Keep admins
            }
        }
        if (goal_user_index != -1 && goal_user_index != -13) // If there is a goal user, keep this goal user
        {
            keep_users[goal_user_index] = 1;
        }
        else // If there is no goal user
        {
            // Pick any non-administrative user
            for (i = 0; i < user_array_size; i++)
            {
                if (belong_to(admin_array_index, admin_array_index_size, i) == -1)
                {
                    keep_users[i] = 1;
                    break;
                }
            }
        }
    }
    else // If performing pruning already
    {
        // Just keep current users
        for (i = 0; i < user_array_size; i++)
        {
            if (strcmp(user_array[i], "removed_user") != 0)
            {
                keep_users[i] = 1;
            }
        }

        if (hasSuper)
        {
            super_user_index = candidate_SUPER_USER();
        }
    }

    fprintf(tmplog, "ARBAC system after reducing:\n");

    //Write the roles
    fprintf(simplifyLog, "Roles\n");
    fprintf(output, "Roles ");
    for (i = 0; i < role_array_size; i++)
    {
        if (keep_roles[i])
        {
            fprintf(output, "%s ", role_array[i]);
            fprintf(simplifyLog, "%d -> %d\n", i, count);
            count++;
        }
        else
        {
            fprintf(simplifyLog, "%d -> -1\n", i);
        }
    }

    if (hasPruning && hasSuper)
    {
        fprintf(output, "SUPER_ROLE ");
        fprintf(simplifyLog, "%d -> %d\n", role_array_size, count);
        count++;
    }
    fprintf(output, ";\n\n");
    fprintf(simplifyLog, "EndR\n");
    fprintf(tmplog, "Roles: %d\n", count);

    //Write the users
    count = 0;
    fprintf(simplifyLog, "Users\n");
    fprintf(output, "Users ");
    for (i = 0; i < user_array_size; i++)
    {
        if (keep_users[i] && i != super_user_index)
        {
            fprintf(output, "%s ", user_array[i]);
            fprintf(simplifyLog, "%d -> %d\n", i, count);
            count++;
        }
        else if (i == super_user_index)
        {
            fprintf(output, "SUPER_USER ");
            fprintf(simplifyLog, "%d -> -10\n", super_user_index);
            count++;
        }
        else
        {
            fprintf(simplifyLog, "%d -> -1\n", i);
        }
    }

    fprintf(output, ";\n\n");
    fprintf(simplifyLog, "EndU\n");
    fprintf(tmplog, "Users: %d\n", count);

    //Write the UA
    // UA: only for keep users and keep roles
    fprintf(output, "UA ");
    for (i = 0; i < ua_array_size; i++)
    {
        if (keep_users[ua_array[i].user_index] && keep_roles[ua_array[i].role_index])
        {
            fprintf(output, "<%s,%s> ", get_user(ua_array[i].user_index), get_role(ua_array[i].role_index));
        }
    }
    if (hasPruning && hasSuper)
    {
        fprintf(output, "<SUPER_USER,SUPER_ROLE> ");
    }
    fprintf(output, ";\n\n");

    //Write the CR
    fprintf(simplifyLog, "CRs\n");
    fprintf(output, "CR ;\n\n");
    fprintf(simplifyLog, "EndCR\n");
    fprintf(tmplog, "CR rules: 0\n");

    //Write CAs
    count = 0;
    int has_head = 0;
    fprintf(simplifyLog, "CAs\n");
    fprintf(output, "CA ");
    for (i = 0; i < ca_array_size; i++)
    {
        if (belong_to(rules, rules_size, i) != -1)
        {
            // Check for the precondition of each role
            if (ca_array[i].type == 0)
            {
                fprintf(output, "<%s,", get_role(ca_array[i].admin_role_index));

                for (j = 0; j < ca_array[i].positive_role_array_size; j++)
                {
                    if (has_head)
                    {
                        fprintf(output, "&%s", get_role(ca_array[i].positive_role_array[j]));
                    }
                    else
                    {
                        fprintf(output, "%s", get_role(ca_array[i].positive_role_array[j]));
                        has_head = 1;
                    }
                }

                for (j = 0; j < ca_array[i].negative_role_array_size; j++)
                {
                    if (has_head)
                    {
                        fprintf(output, "&-%s", get_role(ca_array[i].negative_role_array[j]));
                    }
                    else
                    {
                        fprintf(output, "-%s", get_role(ca_array[i].negative_role_array[j]));
                        has_head = 1;
                    }
                }
                fprintf(output, ",%s> ", get_role(ca_array[i].target_role_index));
                has_head = 0;
            }
            else if (ca_array[i].type == 1)
            {
                fprintf(output, "<%s,TRUE,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
            }
            else if (ca_array[i].type == 2)
            {
                fprintf(output, "<%s,NEW,%s> ", get_role(ca_array[i].admin_role_index), get_role(ca_array[i].target_role_index));
            }
            fprintf(simplifyLog, "%d <- %d\n", count, i);
            count++;
        }
    }
    fprintf(output, ";\n\n");
    fprintf(simplifyLog, "EndCA\n");
    fprintf(tmplog, "CA rules: %d\n", count);
    fprintf(tmplog, "Total rules: %d\n", count);

    //Write the SPEC
    fprintf(output, "SPEC");
    if (goal_user_index != -13 && goal_user_index != -1)
    {
        if (goal_user_index == super_user_index)
        {
            fprintf(output, " SUPER_USER");
        }
        else
        {
            fprintf(output, " %s", get_user(goal_user_index));
        }
    }
    fprintf(output, " %s ;", get_role(goal_role_index));

    // Write the trace
    write_trace(simplifyLog);
    fprintf(simplifyLog, "---------------------------------------------\nEND SIMPLIFICATION LOG\n---------------------------------------------\n");
}

static int
exist_admin_user(int rule_index)
{
    int i;

    if (ca_array[rule_index].admin_role_index == -10)
    {
        // If there is super role, there is always an administrative user
        return 1;
    }
    else
    {
        // Search on the initial configuration
        for (i = 0; i < ua_array_size; i++)
        {
            if (ua_array[i].user_index != -13)
            {
                if (ua_array[i].role_index == ca_array[rule_index].admin_role_index)
                {
                    return 1;
                }
            }
        }
        return 0;
    }
}

int
precheck(int hasPruning, char *inputFile)
{
    int i, j, index, temp = 0, success = 0;
    int *init_roles = 0;
    int init_roles_size = 0;
    int collected_rules[10000];
    int collected_rules_size = 0;
    int final_collected_rules[10000];
    int final_collected_rules_size;
    set *level2_rules = 0;   // level  2
    int level2_rules_size = 0; // level 2 rules

    // Precheck only useful when using with seperation of administration
    if (admin_role_array_index_size > 1)
    {
        return 0;
    }

    // if (hasNewUserMode)
    // {
    //     return 0;
    // }

    // First collect all rules with goal role as target
    for (i = 0; i < ca_array_size; i++)
    {
        // Consider in each iteration
        if (ca_array[i].admin_role_index != -13)
        {
            if (ca_array[i].target_role_index == goal_role_index)
            {
                collected_rules[collected_rules_size] = i;
                collected_rules_size++;
            }
        }
    }

    // Check on those collected rules and choose only the one with TRUE in precondition
    temp = 0;
    for (i = 0; i < collected_rules_size; i++)
    {
        if (ca_array[collected_rules[i]].type == 1)
        {
            temp = 1;
            index = collected_rules[i];
            break;
        }
    }

    if (temp) // If there exists one rule with TRUE in the precondition
    {
        if (exist_admin_user(index))  // If there exist one admin user
        {
            collected_rules[0] = index;
            write_small_policy(hasPruning, collected_rules, 1, inputFile);
            return 1;
        }
        else
        {
            // Will not consider it no more
            return 0;
        }
    }
    else
    {
        // Do a sort on this array
        quickSort(collected_rules, 0, collected_rules_size - 1);

        for (j = 0; j < collected_rules_size; j++)
        {
            index = collected_rules[j];

            level2_rules_size = ca_array[index].positive_role_array_size;
            level2_rules = malloc(level2_rules_size * sizeof(set));

            for (i = 0; i < level2_rules_size; i++)
            {
                level2_rules[i].array = 0;
                level2_rules[i].array_size = 0;
            }

            // Find all dependent rules from this rule
            for (i = 0; i < ca_array_size; i++)
            {
                if (ca_array[i].admin_role_index != -13)
                {
                    temp = belong_to(ca_array[index].positive_role_array, ca_array[index].positive_role_array_size, ca_array[i].target_role_index);
                    if (temp != -1)
                    {
                        level2_rules[temp].array_size++;
                        level2_rules[temp].array = realloc(level2_rules[temp].array, level2_rules[temp].array_size * sizeof(int));
                        level2_rules[temp].array[level2_rules[temp].array_size - 1] = i;
                    }
                }
            }

            final_collected_rules_size = 0;
            for (i = 0; i < level2_rules_size; i++)
            {
                for (temp = 0; temp < level2_rules[i].array_size; temp++)
                {
                    // Collected if this is the rule with TRUE in the precondition
                    if (ca_array[level2_rules[i].array[temp]].type == 1 && exist_admin_user(level2_rules[i].array[temp]))
                    {
                        final_collected_rules[final_collected_rules_size] = level2_rules[i].array[temp];
                        final_collected_rules_size++;
                        break;
                    }
                }
            }

            // Free variable
            for (i = 0; i < level2_rules_size; i++)
            {
                if (level2_rules[i].array_size != 0)
                {
                    free(level2_rules[i].array);
                    level2_rules[i].array = 0;
                }
            }
            free(level2_rules);
            level2_rules = 0;

            if (level2_rules_size > 0
                    && final_collected_rules_size == level2_rules_size)
            {
                final_collected_rules[final_collected_rules_size] = index;
                final_collected_rules_size++;
                success = 1;
                write_small_policy(hasPruning, final_collected_rules, final_collected_rules_size, inputFile);
                return 1;
            }
        }

        if (!success)
        {
            return 0;
        }
    }
}
