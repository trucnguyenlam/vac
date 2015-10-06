#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "ARBACData.h"
#include "CounterExample.h"

int debug = 0;

// Get role name from the index
static char *
get_role(int role_index)
{
    if (role_index == -1)
    {
        return "FALSE";
    }
    if (role_index == -10)
    {
        return "SUPER_ROLE";
    }
    if (role_index == -13)
    {
        return "removed_role";
    }
    if (role_index >= role_array_size)
    {
        return "OUTBOUNDED_ROLE";
    }
    return role_array[role_index];
}

static char *
get_user(int user_index)
{
    if (user_index == -1)
    {
        return "NEW_USER";
    }
    if (user_index >= user_array_size)
    {
        return "OUTBOUNDED_USER";
    }
    return user_array[user_index];
}

// Check if an element belong to an array
static int
belong_to(int *array, int array_size, int index)
{
    int i;
    for (i = 0; i < array_size; i++)
    {
        if (array[i] != -13 && index == array[i])
        {
            return i;
        }
    }
    return -1;
}

static int
belong(int *array, int array_size, int index)
{
    int i;
    for (i = array_size - 1; i >= 0; i--)
    {
        if (array[i] != -13 && index == array[i])
        {
            return i;
        }
    }
    return -1;
}

// Get index of a role from role array
static int
get_role_index(char **roles, int roles_size, char *role_name)
{
    int i;
    for (i = 0; i < roles_size; i++)
    {
        if (strcmp(roles[i], role_name) == 0)
        {
            return i;
        }
    }
    return -1;
}

static void
print_rule(int rule_number, int rule_type, FILE *outputFILE)
{
    int i, has_head = 0;
    if (rule_type == 0) // Can assign rule
    {
        if (ca_array[rule_number].type == 0)
        {
            fprintf(outputFILE, "<%s,", role_array[ca_array[rule_number].admin_role_index]);
            for (i = 0; i < ca_array[rule_number].positive_role_array_size; i++)
            {
                if (has_head)
                {
                    fprintf(outputFILE, "&%s", role_array[ca_array[rule_number].positive_role_array[i]]);
                }
                else
                {
                    fprintf(outputFILE, "%s", role_array[ca_array[rule_number].positive_role_array[i]]);
                    has_head = 1;
                }
            }
            for (i = 0; i < ca_array[rule_number].negative_role_array_size; i++)
            {
                if (has_head)
                {
                    fprintf(outputFILE, "&-%s", role_array[ca_array[rule_number].negative_role_array[i]]);
                }
                else
                {
                    fprintf(outputFILE, "-%s", role_array[ca_array[rule_number].negative_role_array[i]]);
                    has_head = 1;
                }
            }

            fprintf(outputFILE, ",%s>", role_array[ca_array[rule_number].target_role_index]);
            has_head = 0;
        }
        else if (ca_array[rule_number].type == 1)
        {
            fprintf(outputFILE, "<%s,TRUE,%s>", role_array[ca_array[rule_number].admin_role_index], role_array[ca_array[rule_number].target_role_index]);
        }
        else if (ca_array[rule_number].type == 2)
        {
            fprintf(outputFILE, "<%s,NEW,%s>", role_array[ca_array[rule_number].admin_role_index], role_array[ca_array[rule_number].target_role_index]);
        }
    }
    if (rule_type == 1) // Can revoke rule
    {
        fprintf(outputFILE, "<%s,%s>", role_array[cr_array[rule_number].admin_role_index], role_array[cr_array[rule_number].target_role_index]);
    }
}

static void
redirect_stdout(char *outputFILENAME)
{
    FILE *outputFILE;
    char c;
    // Rewrite to stdout
    outputFILE = fopen(outputFILENAME, "r");
    while (1)
    {
        c = fgetc(outputFILE);
        if (!feof(outputFILE))
        {
            fputc(c, stdout);
        }
        else
        {
            break;
        }
    }
    fclose(outputFILE);
}

void
print_no_counter_example(FILE *outputFILE)
{
    if (hasGoalUserMode)
    {
        if (goal_user_index == -1)
        {
            fprintf(outputFILE, "NEW_USER cannot reach %s.\n", role_array[goal_role_index]);
        }
        else
        {
            fprintf(outputFILE, "%s cannot reach %s.\n", user_array[goal_user_index], role_array[goal_role_index]);
        }
    }
    fprintf(outputFILE, "There is no Counter Example.\n");
}

void
print_cant_find_counter_example(FILE *outputFILE)
{
    fprintf(outputFILE, "Cannot find Counter Example.\n");
}

// Print counter example result
static void
print_trace(Trace *trace, int trace_size, FILE *outputFILE)
{
    int i, j, flag = 0;
    fprintf(outputFILE, "Counter Example Trace:\n");

    if (trace_array_size == 0)
    {
        fprintf(outputFILE, "error: Empty counter example trace.\n");
    }

    if (hasGoalUserMode)
    {
        fprintf(outputFILE, "Specification of query: Can %s REACH %s ?\n\n", trace[trace_size - 1].target_user, get_role(goal_role_index));
    }
    else
    {
        fprintf(outputFILE, "Role to check REACHABILITY: %s\n\n", get_role(goal_role_index));
    }

    for (i = 0; i < trace_size; i++)
    {
        fprintf(outputFILE, "==> Step %d:\n", i + 1);
        fprintf(outputFILE, "Target User: %s\n", trace[i].target_user);
        if (trace[i].rule_type == 0)
        {
            fprintf(outputFILE, "CAN ASSIGN ");
        }
        else
        {
            fprintf(outputFILE, "CAN REVOKE ");
        }
        fprintf(outputFILE, "rule applied to %s: ", trace[i].target_user);
        print_rule(trace[i].rule_number, trace[i].rule_type, outputFILE);
        fprintf(outputFILE, "\nAdministrative user to invoke the rule: %s", trace[i].administrative_user);

        fprintf(outputFILE, "\nRole configuration of %s before applying rule:", trace[i].target_user);
        for (j = 0; j < trace[i].config_array_before_size; j++)
        {
            if (trace[i].config_array_before[j] != -13)
            {
                fprintf(outputFILE, " %s", get_role(trace[i].config_array_before[j]));
                flag = 1;
            }
        }
        if (!flag)
        {
            fprintf(outputFILE, " No role");
        }
        flag = 0;

        fprintf(outputFILE, "\nRole configuration of %s after applying rule:", trace[i].target_user);

        for (j = 0; j < trace[i].config_array_size; j++)
        {
            if (trace[i].config_array[j] != -13)
            {
                fprintf(outputFILE, " %s", get_role(trace[i].config_array[j]));
                flag = 1;
            }
        }
        if (!flag)
        {
            fprintf(outputFILE, " No role");
        }
        flag = 0;
        fprintf(outputFILE, "\n\n");
    }
    fprintf(outputFILE, "%s can REACH %s\n", trace[trace_size - 1].target_user, role_array[goal_role_index]);
    fprintf(outputFILE, "%s is REACHABLE\n", role_array[goal_role_index]);
}

// Print counter example result
static void
print_trace_special(FILE *outputFILE)
{
    int i, j;
    fprintf(outputFILE, "Counter Example Trace:\n");

    if (hasGoalUserMode)
    {
        fprintf(outputFILE, "Specification of query: Can %s REACH %s ?\n\n", get_user(goal_user_index), get_role(goal_role_index));
        for (i = 0; i < ua_array_size; i++)
        {
            if (ua_array[i].user_index == goal_user_index && ua_array[i].role_index == goal_role_index)
            {
                fprintf(outputFILE, "==> %s already REACH in initial configuration\n", get_role(goal_role_index));
                return;
            }
        }
    }
    else
    {
        fprintf(outputFILE, "Role to check REACHABILITY: %s\n\n", get_role(goal_role_index));
        for (i = 0; i < ua_array_size; i++)
        {
            if (ua_array[i].role_index == goal_role_index)
            {
                fprintf(outputFILE, "==> %s already REACH in initial configuration\n", get_role(goal_role_index));
                return;
            }
        }
    }
}

/*===============================================================
 PHASE 1 : Produce Counter Example from Simplified ARBAC Policies
 ================================================================*/
/**
 * Search on CBMCAssignment Array to find the line number
 */
static int
find_assignment_index_via_line(CBMCAssignment *array, int array_size, int value)
{
    int start = 0, end = array_size - 1, mid;
    if (value > array[end].line)
    {
        return end;
    }
    while (end >= start)
    {
        mid = (start + end) / 2;
        if (array[mid + 1].line < value)
        {
            start = mid + 1;
        }
        else if (array[mid].line > value)
        {
            end = mid - 1;
        }
        else if (array[mid].line < value && array[mid + 1].line > value)
        {
            return mid;
        }
    }
    return -1;
}

static int
get_realuser_index_via_line(Configuration_user *array, int array_size, int value)
{
    int start = 0, end = array_size - 1, mid;
    if (value > array[end].line)
    {
        return end;
    }
    while (end >= start)
    {
        mid = (start + end) / 2;
        if (array[mid + 1].line < value)
        {
            start = mid + 1;
        }
        else if (array[mid].line > value)
        {
            end = mid - 1;
        }
        else if (array[mid].line < value && array[mid + 1].line > value)
        {
            return mid;
        }
    }
    return -1;
}

static int
find_real_rule_index_via_line(RuleTranslated *array, int array_size, int value)
{
    int start = 0, end = array_size - 1, mid;
    if (value > array[end].line)
    {
        return end;
    }
    while (end >= start)
    {
        mid = (start + end) / 2;
        if (array[mid + 1].line < value)
        {
            start = mid + 1;
        }
        else if (array[mid].line > value)
        {
            end = mid - 1;
        }
        else if (array[mid].line < value && array[mid + 1].line > value)
        {
            return mid;
        }
    }
    return -1;
}

static int
get_real_user_index_from_track_index(int track_user)
{
    int i;
    for (i = 0; i < user_translated_array_size; i++)
    {
        if (user_translated_array[i].track_user == track_user)
        {
            return i;
        }
    }
    return -1;
}

static char *
find_administrative_user(int rule_number, int rule_type)
{
    int admin_role_index, i;
    // Find real admin
    if (rule_type == 0) // Find on the CA rule
    {
        admin_role_index = ca_array[rule_number].admin_role_index;
    }
    else
    {
        admin_role_index = cr_array[rule_number].admin_role_index;
    }

    for (i = 0; i < user_translated_array_size; i++)
    {
        if (belong_to(user_translated_array[i].config_array, user_translated_array[i].config_array_size, admin_role_index) != -1)
        {
            return strdup(user_translated_array[i].user_name);
        }
    }
    return strdup("SUPER_USER");
}

static char *
find_target_user(int track_user_index)
{
    int i;
    for (i = 0; i < user_translated_array_size; i++)
    {
        if (track_user_index ==  user_translated_array[i].track_user)
        {
            return strdup(user_translated_array[i].user_name);
        }
    }
    return strdup("INVALID_USER");
}

static void
free_ARBAC_data()
{
    int i;
    for (i = 0; i < role_array_size; i++)
    {
        free(role_array[i]);
    }
    free(role_array);
    for (i = 0; i < user_array_size; i++)
    {
        free(user_array[i]);
    }
    free(user_array);
    free(admin_role_array_index);
    free(admin_array_index);
    free(ua_array);
    free(cr_array);
    for (i = 0; i < ca_array_size; i++)
    {
        free(ca_array[i].positive_role_array);
        free(ca_array[i].negative_role_array);
    }
    free(ca_array);
    iDictionary.Finalize(role_dict);
    iDictionary.Finalize(user_dict);
    free(new_rule_array);
    new_rule_array = 0;
    new_rule_array_size = 0;
}

static void
free_first_phase_data()
{
    int i;
    for (i = 0; i < assignment_array_size; i++)
    {
        free(assignment_array[i].role);
    }
    free(assignment_array);

    for (i = 0; i < user_translated_array_size; i++)
    {
        free(user_translated_array[i].user_name);
        free(user_translated_array[i].config_array);
    }
    free(user_translated_array);

    free(rule_translated_array);
    for (i = 0; i < user_configuration_array_size; i++)
    {
        free(user_configuration_array[i].user_name);
    }
    free(user_configuration_array);

    free_ARBAC_data();
}

int original_goal_role_index = 0;

static int
preprocess_ARBAC()
{
    int return_val = role_array_size;
    original_goal_role_index = goal_role_index;
    if (hasGoalUserMode)
    {
        // Add a specific role name ToCheckRole to that specific user
        role_array_size++;
        role_array = realloc(role_array, role_array_size * sizeof(char *));
        role_array[role_array_size - 1] = malloc(13);
        strcpy(role_array[role_array_size - 1], "ToCheckRole");
        return_val = role_array_size - 1;
        ua_array_size++;
        ua_array = realloc(ua_array, ua_array_size * sizeof(_UA));
        ua_array[ua_array_size - 1].user_index = goal_user_index;
        ua_array[ua_array_size - 1].role_index = role_array_size - 1;

        // Add a new target role
        role_array_size++;
        role_array = realloc(role_array, role_array_size * sizeof(char *));
        role_array[role_array_size - 1] = malloc(13);
        strcpy(role_array[role_array_size - 1], "TargetPrime");

        // Add a fresh CA rule
        ca_array_size++;
        ca_array = realloc(ca_array, ca_array_size * sizeof(_CA));
        ca_array[ca_array_size - 1].type = 0;
        ca_array[ca_array_size - 1].admin_role_index = role_array_size - 2; // ToCheckRole
        ca_array[ca_array_size - 1].target_role_index = role_array_size - 1; // TargetPrime
        ca_array[ca_array_size - 1].negative_role_array = 0;
        ca_array[ca_array_size - 1].negative_role_array_size = 0;
        ca_array[ca_array_size - 1].positive_role_array_size = 2;
        ca_array[ca_array_size - 1].positive_role_array = malloc(2 * sizeof(int));
        ca_array[ca_array_size - 1].positive_role_array[0] = role_array_size - 2;
        ca_array[ca_array_size - 1].positive_role_array[1] = goal_role_index;
        goal_role_index = role_array_size - 1;
    }
    return original_goal_role_index;
}

static int
find_real_user_from_SUPER_USER(void)
{
    int i;
    for (i = 0; i < user_map_array_size; i++)
    {
        if (user_map_array[i] == -10)
        {
            return i;
        }
    }
    return -1;
}

static int
find_trace_index_same_user(Trace * trace, int trace_size, char* user_name)
{
    int i;
    for (i = trace_size - 1; i >= 0; i--)
    {
        if (strcmp(user_name, trace[i].target_user) == 0)
        {
            return i;
        }
    }
    return i;
}

static void
postprocess_counter_example_trace(int ToCheckRole_index)
{
    if (hasGoalUserMode)
    {
        int trace_index = find_trace_index_same_user(trace_array, trace_array_size - 1 , trace_array[trace_array_size - 1].target_user);

        if (trace_index == -1)
        {
            // There is only one chance when this happen, a NEW_USER with role as the target
            int i;
            for (i = 0; i < trace_array_size; i++)
            {
                int index = belong_to(trace_array[i].config_array, trace_array[i].config_array_size, ToCheckRole_index);
                if (index != -1)
                {
                    trace_array[i].config_array[index] = -13; // Mark as removal
                }
                index = belong_to(trace_array[i].config_array_before, trace_array[i].config_array_before_size, ToCheckRole_index);
                if (index != -1)
                {
                    trace_array[i].config_array_before[index] = -13; // Mark as removal
                }
            }
            return;
        }

        int i;
        for (i = trace_array_size - 1; i > trace_index; i--)
        {
            // Remove last Trace
            free(trace_array[i].administrative_user);
            free(trace_array[i].target_user);
            free(trace_array[i].config_array);
            free(trace_array[i].config_array_before);
        }

        trace_array_size = trace_index + 1;
        trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));

        // Remove from the trace array all the configuration that has ToCheckRole
        for (i = 0; i < trace_array_size; i++)
        {
            int index = belong_to(trace_array[i].config_array, trace_array[i].config_array_size, ToCheckRole_index);
            if (index != -1)
            {
                trace_array[i].config_array[index] = -13; // Mark as removal
            }
            index = belong_to(trace_array[i].config_array_before, trace_array[i].config_array_before_size, ToCheckRole_index);
            if (index != -1)
            {
                trace_array[i].config_array_before[index] = -13; // Mark as removal
            }
        }
    }
}


int reached_initially = 0;
int countNEWAlready = 0;

/**
 * Produce Counter Example from XML CBMC, TRANSLATED FILE, SIMPLIFIED FILE
 */
static void
produce_counter_example(FILE *outputFILE, int silence)
{
    int i, j, flag = 0, invalid_rule = 0;
    int ToCheckRole_index;
    int init_lim_index, config_lim_index;

    // Do preprocess to identify what is the role to check for reachability
    ToCheckRole_index = preprocess_ARBAC();

    fprintf(debugFile, "ToCheckRole_index is %d\n", ToCheckRole_index);

    user_translated_array = 0;
    user_translated_array_size = 0;

    // Store the trace of execution (CA or CR)
    trace_array = 0;
    trace_array_size = 0;

    // Find limit line number of INITIALIZATIION, initialize_lim is the last line of INIT
    init_lim_index = find_assignment_index_via_line(assignment_array, assignment_array_size, initialize_lim);
    fprintf(debugFile, "Limit INDEX of INITIALIZATIION is %d\n", init_lim_index);

    // Find limit line number of CONFIGURATION USER, configuration_lim is the last line of CONFIG
    config_lim_index = find_assignment_index_via_line(assignment_array, assignment_array_size, configuration_lim);
    fprintf(debugFile, "Limit INDEX of CONFIGURATION USER is line %d\n", config_lim_index);

    // Get all user configuration (now include new user here, which will be in the trace
    for (i = init_lim_index + 1; i <= config_lim_index; i++)
    {
        if (assignment_array[i].value == 1)    // if there is any assignment to track user
        {
            j = get_realuser_index_via_line(user_configuration_array, user_configuration_array_size, assignment_array[i].line);

            fprintf(debugFile, "line %d and realuser is %d\n", assignment_array[i].line, j);

            if (j != -1)
            {
                int index = get_real_user_index_from_track_index(assignment_array[i].track_user);
                fprintf(debugFile, "Get real index %d from track user %d\n", index, assignment_array[i].track_user);

                if (index == -1)
                {
                    // Create a new user which associated everything (from track_user to username)
                    user_translated_array_size++;
                    user_translated_array = realloc(user_translated_array, user_translated_array_size * sizeof(Translated_user));
                    user_translated_array[user_translated_array_size - 1].track_user = assignment_array[i].track_user;

                    user_translated_array[user_translated_array_size - 1].user_name = malloc(strlen(user_configuration_array[j].user_name) + 1);
                    strcpy(user_translated_array[user_translated_array_size - 1].user_name, user_configuration_array[j].user_name);

                    user_translated_array[user_translated_array_size - 1].config_array_size = 0;
                    user_translated_array[user_translated_array_size - 1].config_array = 0;
                    if (assignment_array[i].type == 0)
                    {
                        user_translated_array[user_translated_array_size - 1].config_array_size = 1;
                        user_translated_array[user_translated_array_size - 1].config_array = malloc(sizeof(int));
                        user_translated_array[user_translated_array_size - 1].config_array[0] = get_role_index(role_array, role_array_size, assignment_array[i].role);
                    }
                }
                else    // Already in the list
                {
                    // Add role to the init configuration of this user
                    if (assignment_array[i].type == 0)
                    {
                        user_translated_array[index].config_array_size++;
                        user_translated_array[index].config_array = realloc(user_translated_array[index].config_array, user_translated_array[index].config_array_size * sizeof(int));
                        user_translated_array[index].config_array[user_translated_array[index].config_array_size - 1] = get_role_index(role_array, role_array_size, assignment_array[i].role);
                    }
                }

                if (
                    assignment_array[i].type == 0
                    && strstr(user_configuration_array[j].user_name, "NEW_USER") != NULL
                    && strcmp(user_configuration_array[j].user_name, "NEW_USER") != 0
                )
                {
                    countNEWAlready = 1;

                    char * administrative_user = find_administrative_user(user_configuration_array[j].rule_index, 0);
                    // Create trace for each new user
                    trace_array_size++;
                    trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));

                    trace_array[trace_array_size - 1].rule_number = user_configuration_array[j].rule_index;
                    trace_array[trace_array_size - 1].rule_type = 0;

                    trace_array[trace_array_size - 1].administrative_user = administrative_user;

                    trace_array[trace_array_size - 1].target_user = malloc(strlen(user_configuration_array[j].user_name) + 1);
                    strcpy(trace_array[trace_array_size - 1].target_user, user_configuration_array[j].user_name);

                    // User configuration before applying the rule
                    trace_array[trace_array_size - 1].config_array_before_size = 0;
                    trace_array[trace_array_size - 1].config_array_before = 0;

                    trace_array[trace_array_size - 1].config_array_size = 1;
                    trace_array[trace_array_size - 1].config_array = malloc(sizeof(int));
                    trace_array[trace_array_size - 1].config_array[0] = get_role_index(role_array, role_array_size, assignment_array[i].role);
                }
                else if (
                    assignment_array[i].type == 0
                    && get_role_index(role_array, role_array_size, assignment_array[i].role) == original_goal_role_index
                )
                {
                    reached_initially = 1;
                    goto END;
                }
            }
        }
    }

    // Show the evolution of the track user in the simulation
    for (i = config_lim_index + 1; i < assignment_array_size; i++)
    {
        // Simulate the assignment for track variable
        if (assignment_array[i].type == 0)   // Rule assignment (not b_* = something)
        {
            int index = get_real_user_index_from_track_index(assignment_array[i].track_user);
            fprintf(debugFile, "Track user is %d and index is %d\n", assignment_array[i].track_user, index);
            if (index != -1)
            {
                // Create a trace for this invocation
                // Find the rule number
                int rule_translated_index = find_real_rule_index_via_line(rule_translated_array, rule_translated_array_size, assignment_array[i].line);
                if (rule_translated_index != -1)
                {
                    trace_array_size++;
                    trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));

                    trace_array[trace_array_size - 1].rule_number = rule_translated_array[rule_translated_index].rule_number;
                    trace_array[trace_array_size - 1].rule_type = rule_translated_array[rule_translated_index].rule_type;

                    trace_array[trace_array_size - 1].administrative_user = find_administrative_user(trace_array[trace_array_size - 1].rule_number, trace_array[trace_array_size - 1].rule_type);
                    trace_array[trace_array_size - 1].target_user = find_target_user(assignment_array[i].track_user);

                    // User configuration before applying the rule
                    trace_array[trace_array_size - 1].config_array_before_size = user_translated_array[index].config_array_size;
                    trace_array[trace_array_size - 1].config_array_before = malloc(trace_array[trace_array_size - 1].config_array_before_size * sizeof(int));
                    memcpy(trace_array[trace_array_size - 1].config_array_before, user_translated_array[index].config_array, trace_array[trace_array_size - 1].config_array_before_size * sizeof(int));

                    // Assignment rule
                    if (assignment_array[i].value == 1)
                    {
                        // Add role to configuration of that user
                        user_translated_array[index].config_array_size++;
                        user_translated_array[index].config_array = realloc(user_translated_array[index].config_array, user_translated_array[index].config_array_size * sizeof(int));
                        user_translated_array[index].config_array[user_translated_array[index].config_array_size - 1] = get_role_index(role_array, role_array_size, assignment_array[i].role);

                    }
                    else if (assignment_array[i].value == 0) // Revocation rule
                    {
                        int role_index_target = belong_to(user_translated_array[index].config_array, user_translated_array[index].config_array_size, get_role_index(role_array, role_array_size, assignment_array[i].role));
                        if (role_index_target != -1)   // If this is a valid role
                        {
                            user_translated_array[index].config_array[role_index_target] = -13; // Deleted
                        }
                        else // Wrong rovocation
                        {
                            invalid_rule = 1;
                        }
                    }
                    if (!invalid_rule)
                    {
                        // Copy user configuration to the trace
                        trace_array[trace_array_size - 1].config_array_size = user_translated_array[index].config_array_size;
                        trace_array[trace_array_size - 1].config_array = malloc(trace_array[trace_array_size - 1].config_array_size * sizeof(int));
                        memcpy(trace_array[trace_array_size - 1].config_array, user_translated_array[index].config_array, trace_array[trace_array_size - 1].config_array_size * sizeof(int));
                    }
                    else
                    {
                        fprintf(stderr, "error: there is some thing wrong with the counter example from CBMC\n");
                        abort();
                    }
                }
                else
                {
                    fprintf(stderr, "error: there is some problem with the counter example\n");
                    abort();
                }

                if (trace_array[trace_array_size - 1].rule_type == 0)
                {
                    // Stop if it stop at goal role
                    if (ca_array[trace_array[trace_array_size - 1].rule_number].target_role_index == goal_role_index)
                    {
                        break;
                    }
                }

            }
            else
            {
                fprintf(stderr, "error: there is some problem with the counter example\n");
                abort();
            }
        }
        invalid_rule = 0;
    }

    if (debug)
    {
        print_trace(trace_array, trace_array_size, stdout);
    }

    postprocess_counter_example_trace(ToCheckRole_index);
    if (!silence)
    {
        print_trace(trace_array, trace_array_size, outputFILE);
    }

END:
    free_first_phase_data();
}

/*==============================================================
 PHASE 2 : Produce Counter Example from Original ARBAC Policies
 ===============================================================*/
static int
array_subset_of(int *array1, int array1_size, int *array2, int array2_size)
{
    int i;
    if (array1_size == 0)
    {
        return 1;
    }
    for (i = 0; i < array1_size; i++)
    {
        if (array1[i] != -13 && belong_to(array2, array2_size, array1[i]) == -1)
        {
            return 0;
        }
    }
    return 1;
}

static int
check_precondition_NEW_CA(int config_array_size, char * target_user)
{
    int i;
    if (strstr(target_user, "NEW_USER") == NULL)
    {
        return 0;
    }
    else
    {
        if (config_array_size > 0)
        {
            return 0;
        }
        return 1;
    }
}

// Check if a user configuration satisfy the precondition
static int
check_precondition_CA(int ca_index, int *config_array, int config_array_size, char* target_user)
{
    int i;

    // TRUE in precondition
    if (ca_array[ca_index].type == 1)
    {
        return 1;
    }

    // NEW in precondition
    if (ca_array[ca_index].type == 2)
    {
        return check_precondition_NEW_CA(config_array_size, target_user);
    }

    if (!array_subset_of(ca_array[ca_index].positive_role_array, ca_array[ca_index].positive_role_array_size, config_array, config_array_size))
    {
        return 0;
    }
    for (i = 0; i < ca_array[ca_index].negative_role_array_size; i++)
    {
        if (belong_to(config_array, config_array_size, ca_array[ca_index].negative_role_array[i]) != -1)
        {
            return 0;
        }
    }
    return 1;
}

static int
get_admin_user_index(int admin_role_index)
{
    int i;
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].role_index == admin_role_index)
        {
            return ua_array[i].user_index;
        }
    }
    return -1;
}

static char *
find_admin_user_from_trace(Trace * trace, int trace_size, int admin_role_index)
{
    int i;
    for (i = trace_size - 1; i >= 0; i--)
    {
        if (belong_to(trace[i].config_array, trace[i].config_array_size, admin_role_index) != -1)
        {
            return strdup(trace[i].target_user);
        }
    }
    return strdup("SUPER_USER");
}


static int
get_original_rule_index(int simplify_rule_index, int simplify_rule_type)
{
    if (simplify_rule_type == 0) // Can Assign rule
    {
        return ca_map_array[simplify_rule_index];
    }
    if (simplify_rule_type == 1) // Can Revoke rule
    {
        return cr_map_array[simplify_rule_index];
    }
    return -1;
}

static void
generate_trace_CA(Trace t)
{
    int * temp_config_array = 0;
    int temp_config_array_size = 0;

    int trace_index = find_trace_index_same_user(original_trace_array, original_trace_array_size, t.target_user);
    if (trace_index == -1)   // First time this user show up on the trace
    {
        temp_config_array = 0;
        temp_config_array_size = 0;

        int user_index = find_user_from_dict(t.target_user);
        if (user_index > -1)    // Super user
        {
            int y;
            for (y = 0; y < ua_array_size; y++)
            {
                if (ua_array[y].user_index == user_index)
                {
                    temp_config_array_size++;
                    temp_config_array = realloc(temp_config_array, temp_config_array_size * sizeof(int));
                    temp_config_array[temp_config_array_size - 1] = ua_array[y].role_index;
                }
            }
        }
    }
    else
    {
        temp_config_array_size = original_trace_array[trace_index].config_array_size;
        temp_config_array = original_trace_array[trace_index].config_array;
    }

    int administrative_user_index = get_admin_user_index(ca_array[t.rule_number].admin_role_index);
    char * admin_user = 0;
    if (administrative_user_index == -1) // Cannot find administrative user
    {
        admin_user = find_admin_user_from_trace(original_trace_array, original_trace_array_size, ca_array[t.rule_number].admin_role_index);
    }
    else
    {
        admin_user = user_array[administrative_user_index];
    }

    original_trace_array_size++;
    original_trace_array = realloc(original_trace_array, original_trace_array_size * sizeof(Trace));

    original_trace_array[original_trace_array_size - 1].rule_number = t.rule_number;
    original_trace_array[original_trace_array_size - 1].rule_type = 0;  // CAN ASSIGN RULE

    original_trace_array[original_trace_array_size - 1].target_user = malloc(strlen(t.target_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].target_user, t.target_user);

    original_trace_array[original_trace_array_size - 1].administrative_user = malloc(strlen(admin_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].administrative_user, admin_user);

    // Previous configuration
    original_trace_array[original_trace_array_size - 1].config_array_before_size = temp_config_array_size;
    original_trace_array[original_trace_array_size - 1].config_array_before = malloc(original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));
    memcpy(original_trace_array[original_trace_array_size - 1].config_array_before, temp_config_array, original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));

    original_trace_array[original_trace_array_size - 1].config_array_size = original_trace_array[original_trace_array_size - 1].config_array_before_size + 1;
    original_trace_array[original_trace_array_size - 1].config_array = malloc(original_trace_array[original_trace_array_size - 1].config_array_size * sizeof(int));
    int i;
    for (i = 0; i < original_trace_array[original_trace_array_size - 1].config_array_before_size; i++)
    {
        original_trace_array[original_trace_array_size - 1].config_array[i] = original_trace_array[original_trace_array_size - 1].config_array_before[i];
    }
    original_trace_array[original_trace_array_size - 1].config_array[i] = ca_array[t.rule_number].target_role_index;
}

static void
generate_trace_CA_version2(int rule_number, char* target_user)
{
    int * temp_config_array = 0;
    int temp_config_array_size = 0;

    int trace_index = find_trace_index_same_user(original_trace_array, original_trace_array_size, target_user);
    if (trace_index == -1)   // First time this user show up on the trace
    {
        temp_config_array = 0;
        temp_config_array_size = 0;

        int user_index = find_user_from_dict(target_user);
        if (user_index > -1)    // Super user
        {
            int y;
            for (y = 0; y < ua_array_size; y++)
            {
                if (ua_array[y].user_index == user_index)
                {
                    temp_config_array_size++;
                    temp_config_array = realloc(temp_config_array, temp_config_array_size * sizeof(int));
                    temp_config_array[temp_config_array_size - 1] = ua_array[y].role_index;
                }
            }
        }
    }
    else
    {
        temp_config_array = original_trace_array[trace_index].config_array;
        temp_config_array_size = original_trace_array[trace_index].config_array_size;
    }

    int administrative_user_index = get_admin_user_index(ca_array[rule_number].admin_role_index);
    char * admin_user;
    if (administrative_user_index == -1) // Cannot find administrative user
    {
        admin_user = find_admin_user_from_trace(original_trace_array, original_trace_array_size, ca_array[rule_number].admin_role_index);
    }
    else
    {
        admin_user = user_array[administrative_user_index];
    }

    original_trace_array_size++;
    original_trace_array = realloc(original_trace_array, original_trace_array_size * sizeof(Trace));
    original_trace_array[original_trace_array_size - 1].rule_number = rule_number;
    original_trace_array[original_trace_array_size - 1].rule_type = 0;  // CAN ASSIGN RULE
    original_trace_array[original_trace_array_size - 1].target_user = malloc(strlen(target_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].target_user, target_user);

    original_trace_array[original_trace_array_size - 1].administrative_user = malloc(strlen(admin_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].administrative_user, admin_user);

    // Copy configuration
    original_trace_array[original_trace_array_size - 1].config_array_before_size = temp_config_array_size;
    original_trace_array[original_trace_array_size - 1].config_array_before = malloc(original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));
    memcpy(original_trace_array[original_trace_array_size - 1].config_array_before, temp_config_array, original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));

    original_trace_array[original_trace_array_size - 1].config_array_size = original_trace_array[original_trace_array_size - 1].config_array_before_size + 1;
    original_trace_array[original_trace_array_size - 1].config_array = malloc(original_trace_array[original_trace_array_size - 1].config_array_size * sizeof(int));
    memcpy(original_trace_array[original_trace_array_size - 1].config_array, original_trace_array[original_trace_array_size - 1].config_array_before, original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));
    original_trace_array[original_trace_array_size - 1].config_array[original_trace_array[original_trace_array_size - 1].config_array_size - 1] = ca_array[rule_number].target_role_index;
}


static void
generate_trace_CA_NEW_USER(int rule_index, char* target_user)
{
    int administrative_user_index = get_admin_user_index(ca_array[rule_index].admin_role_index);

    char * admin_user = 0;
    if (administrative_user_index == -1) // Cannot find administrative user
    {
        admin_user = find_admin_user_from_trace(original_trace_array, original_trace_array_size, ca_array[rule_index].admin_role_index);
    }
    else
    {
        admin_user = user_array[administrative_user_index];
    }
    original_trace_array_size++;
    original_trace_array = realloc(original_trace_array, original_trace_array_size * sizeof(Trace));
    original_trace_array[original_trace_array_size - 1].rule_number = rule_index;
    original_trace_array[original_trace_array_size - 1].rule_type = 0;  // CAN ASSIGN RULE
    original_trace_array[original_trace_array_size - 1].target_user = malloc(strlen(target_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].target_user, target_user);

    original_trace_array[original_trace_array_size - 1].administrative_user = malloc(strlen(admin_user) + 1);
    strcpy(original_trace_array[original_trace_array_size - 1].administrative_user, admin_user);


    original_trace_array[original_trace_array_size - 1].config_array_before_size = 0;
    original_trace_array[original_trace_array_size - 1].config_array_before = 0;

    original_trace_array[original_trace_array_size - 1].config_array_size = 1;
    original_trace_array[original_trace_array_size - 1].config_array = malloc(sizeof(int));
    original_trace_array[original_trace_array_size - 1].config_array[0] = ca_array[rule_index].target_role_index;
}

static void
generate_trace_CR(Trace t)
{
    int * temp_config_array = 0;
    int temp_config_array_size = 0;

    int trace_index = find_trace_index_same_user(original_trace_array, original_trace_array_size, t.target_user);
    if (trace_index == -1)   // First time this user show up on the trace
    {
        temp_config_array = 0;
        temp_config_array_size = 0;

        int user_index = find_user_from_dict(t.target_user);
        if (user_index > -1)    // Super user
        {
            int y;
            for (y = 0; y < ua_array_size; y++)
            {
                if (ua_array[y].user_index == user_index)
                {
                    temp_config_array_size++;
                    temp_config_array = realloc(temp_config_array, temp_config_array_size * sizeof(int));
                    temp_config_array[temp_config_array_size - 1] = ua_array[y].role_index;
                }
            }
        }
    }
    else
    {
        temp_config_array = original_trace_array[trace_index].config_array;
        temp_config_array_size = original_trace_array[trace_index].config_array_size;
    }

    int role_target_index = belong_to(temp_config_array, temp_config_array_size, cr_array[t.rule_number].target_role_index);

    if (role_target_index != -1)
    {
        // Make a trace
        int administrative_user_index = get_admin_user_index(cr_array[t.rule_number].admin_role_index);

        char * admin_user = 0;
        if (administrative_user_index == -1) // Cannot find administrative user
        {
            admin_user = find_admin_user_from_trace(original_trace_array, original_trace_array_size, ca_array[t.rule_number].admin_role_index);
        }
        else
        {
            admin_user = user_array[administrative_user_index];
        }

        original_trace_array_size++;
        original_trace_array = realloc(original_trace_array, original_trace_array_size * sizeof(Trace));
        original_trace_array[original_trace_array_size - 1].rule_number = t.rule_number;
        original_trace_array[original_trace_array_size - 1].rule_type = 1;

        original_trace_array[original_trace_array_size - 1].target_user = malloc(strlen(t.target_user) + 1);
        strcpy(original_trace_array[original_trace_array_size - 1].target_user, t.target_user);

        original_trace_array[original_trace_array_size - 1].administrative_user = malloc(strlen(admin_user) + 1);
        strcpy(original_trace_array[original_trace_array_size - 1].administrative_user, admin_user);

        // Copy configuration
        original_trace_array[original_trace_array_size - 1].config_array_before_size = temp_config_array_size;
        original_trace_array[original_trace_array_size - 1].config_array_before = malloc(original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));
        memcpy(original_trace_array[original_trace_array_size - 1].config_array_before, temp_config_array, original_trace_array[original_trace_array_size - 1].config_array_before_size * sizeof(int));

        original_trace_array[original_trace_array_size - 1].config_array_size = temp_config_array_size;
        original_trace_array[original_trace_array_size - 1].config_array = malloc(original_trace_array[original_trace_array_size - 1].config_array_size * sizeof(int));
        memcpy(original_trace_array[original_trace_array_size - 1].config_array, temp_config_array, original_trace_array[original_trace_array_size - 1].config_array_size * sizeof(int));
        original_trace_array[original_trace_array_size - 1].config_array[role_target_index] = -13;  // Mark as removed
    }
}

static int
can_apply(int *curr_conf, int curr_conf_size, int rule_number, int rule_type, char * target_user)
{
    if (rule_type == 0) // Can Assign
    {
        if (check_precondition_CA(rule_number, curr_conf, curr_conf_size, target_user))
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }
    else // Can revoke
    {
        if (belong_to(curr_conf, curr_conf_size, cr_array[rule_number].target_role_index) != -1)
        {
            return 1;
        }
        else
        {
            return 0;
        }
    }
}

// Global vars for counter example trace
int success_path[1000];   // How can a counter example has 1000 tract
int success_path_len;
int found_success_path;

static int
check_success_path_reverse(int path[], int pathLen, int * curr_config, int curr_config_size, char* target_user)
{
    int i, flag = 1;

    int * current_config = 0;
    int current_config_size = curr_config_size;
    current_config = malloc(current_config_size * sizeof(int));
    memcpy(current_config, curr_config, current_config_size * sizeof(int));

    for (i = 0; i < pathLen; i++)
    {
        if (path[i] != -13)
        {
            if (can_apply(current_config, current_config_size, path[i], 0, target_user))
            {
                if (belong_to(current_config, current_config_size, ca_array[path[i]].target_role_index) == -1)
                {
                    current_config_size++;
                    current_config = realloc(current_config, current_config_size * sizeof(int));
                    current_config[current_config_size - 1] = ca_array[path[i]].target_role_index;
                }
                else
                {
                    path[i] = -13;
                }
            }
            else
            {
                flag = 0;
                break;
            }
        }
    }

    free(current_config);
    current_config = 0;
    current_config_size = 0;

    if (flag)
    {
        return 1;
    }
    else
    {
        return 0;
    }
}

static void
generate_and_check_trace_reverse(Node *traces, int trace_size, int path[], int pathLen, int depth, int * current_config, int current_config_size, char * target_user)
{
    int i;

    if (!found_success_path)
    {
        if (depth == trace_size)
        {
            if (check_success_path_reverse(path, pathLen, current_config, current_config_size, target_user))
            {
                // Store success path
                success_path_len = pathLen;
                for (i = 0; i < pathLen; i++)
                {
                    success_path[i] = path[i];
                }
                found_success_path = 1;
            }
            return;
        }
        else
        {
            for (i = 0; i < traces[depth].siblings_size; i++)
            {
                if (depth == 0)
                {
                    path[pathLen] = traces[depth].siblings[i];
                    generate_and_check_trace_reverse(traces, trace_size, path, pathLen + 1, depth + 1, current_config, current_config_size, target_user);
                }
                else
                {
                    if (pathLen >= 1 && !check_success_path_reverse(path, pathLen, current_config, current_config_size, target_user))
                    {
                        return;
                    }
                    if (belong_to(path, pathLen, traces[depth].siblings[i]) == -1)
                    {
                        path[pathLen] = traces[depth].siblings[i];
                        generate_and_check_trace_reverse(traces, trace_size, path, pathLen + 1, depth + 1, current_config, current_config_size, target_user);
                    }
                    else
                    {
                        generate_and_check_trace_reverse(traces, trace_size, path, pathLen, depth + 1, current_config, current_config_size, target_user);
                    }
                }
            }
        }
    }
}

static Pair
find_node(Node *trace, int trace_size, int rule_index)
{
    Pair ret;
    int i;
    for (i = 0; i < trace_size; i++)
    {
        int index = belong_to(trace[i].siblings, trace[i].siblings_size, rule_index);
        if (index != -1)
        {
            ret.v1 = i;
            ret.v2 = index;
            return ret;
        }
    }
    ret.v1 = -1;
    return ret;
}

Node *related_traces;
int related_traces_size;

static void
find_related_traces_reverse(Node *traces, int traces_size)
{
    int i, j;
    related_traces = 0;
    related_traces_size = 0;

    related_traces_size = traces_size;
    related_traces = malloc(related_traces_size * sizeof(Node));

    for (i = 0; i < related_traces_size; i++)
    {
        related_traces[i].siblings = 0;
        related_traces[i].siblings_size = 0;
    }

    for (i = 0; i < ca_array_size; i++)
    {
        for (j = 0; j < related_traces_size; j++)
        {
            if (traces[j].siblings_size > 0 && ca_array[i].target_role_index == ca_array[traces[j].siblings[0]].target_role_index)
            {
                related_traces[j].siblings_size++;
                related_traces[j].siblings = realloc(related_traces[j].siblings, related_traces[j].siblings_size * sizeof(int));
                related_traces[j].siblings[related_traces[j].siblings_size - 1] = i;
            }
        }
    }
}

/**
 * Core of tracking back algorithm
 */
static int
generate_additional_traces(Trace t)
{
    int i, j, success_index = -1, return_val = 1;
    int path[1000], max_level = -1, flag, success_path_index = -1;

    // A Trace
    Node *atraces = 0;
    int atraces_size = 0;

    // Node *final_traces = 0;
    // int final_traces_size = 0;

    Node *reverse_final_traces = 0;
    int reverse_final_traces_size = 0;

    Array *arrange_trace = 0;
    int arrange_trace_size = 0;

    success_path_len = 0;

    // Create first node
    atraces_size = 1;
    atraces = malloc(sizeof(Node));
    atraces[0].siblings_size = 1;
    atraces[0].siblings = malloc(sizeof(int));
    atraces[0].siblings[0] = t.rule_number;
    atraces[0].level = 0;
    max_level = 0;

    int * temp_config_array = 0;
    int temp_config_array_size = 0;

    int trace_index = find_trace_index_same_user(original_trace_array, original_trace_array_size, t.target_user);
    if (trace_index == -1)   // First time this user show up on the trace
    {
        temp_config_array = 0;
        temp_config_array_size = 0;

        int user_index = find_user_from_dict(t.target_user);
        if (user_index > -1)    // Super user
        {
            int y;
            for (y = 0; y < ua_array_size; y++)
            {
                if (ua_array[y].user_index == user_index)
                {
                    temp_config_array_size++;
                    temp_config_array = realloc(temp_config_array, temp_config_array_size * sizeof(int));
                    temp_config_array[temp_config_array_size - 1] = ua_array[y].role_index;
                }
            }
        }
    }
    else
    {
        temp_config_array_size = original_trace_array[trace_index].config_array_size;
        temp_config_array = original_trace_array[trace_index].config_array;
    }


    // Generate addditional trace from simplify rules
    for (i = simplify_steps_size - 1; i >= 0; i--)
    {
        // Add child node
        if (simplify_steps[i].simplify_rule == 3 || simplify_steps[i].simplify_rule == 4)
        {
            Pair ret = find_node(atraces, atraces_size, simplify_steps[i].affected_rule_index);
            int index = ret.v1;
            if (index != -1)
            {
                int flag = 1;
                int index1 = simplify_steps[i].related_rule_index;

                // Check if this node is the child of all siblings
                for (j = 0; j < atraces[index].siblings_size; j++)
                {
                    int index2 = atraces[index].siblings[j];

                    if (belong_to(ca_array[index2].negative_role_array, ca_array[index2].negative_role_array_size, ca_array[index1].target_role_index) != -1)
                    {
                        flag = 0;
                    }
                }
                if (flag)
                {
                    Pair ret1 = find_node(atraces, atraces_size, simplify_steps[i].related_rule_index);
                    int index3 = ret1.v1;
                    if (index3 != -1)
                    {
                        if (atraces[index3].level < atraces[index].level + 1)
                        {
                            atraces[index3].level = atraces[index].level + 1;
                            Node temp;
                            temp = atraces[atraces_size - 1];
                            atraces[atraces_size - 1] = atraces[index3];
                            atraces[index3] = temp;
                        }
                    }
                    else
                    {
                        atraces_size++;
                        atraces = realloc(atraces, atraces_size * sizeof(Node));
                        atraces[atraces_size - 1].siblings_size = 1;
                        atraces[atraces_size - 1].siblings = malloc(sizeof(int));
                        atraces[atraces_size - 1].siblings[0] = simplify_steps[i].related_rule_index;
                        atraces[atraces_size - 1].level = atraces[index].level + 1;
                    }
                    if (max_level < atraces[atraces_size - 1].level)
                    {
                        max_level = atraces[atraces_size - 1].level;
                    }
                }
            }
        }
        // Sibling nodes
        if (simplify_steps[i].simplify_rule == 5)
        {
            Pair ret = find_node(atraces, atraces_size, simplify_steps[i].affected_rule_index);

            if (ret.v1 != -1)
            {
                int index = ret.v1;
                atraces[index].siblings_size++;
                atraces[index].siblings = realloc(atraces[index].siblings, atraces[index].siblings_size * sizeof(int));
                atraces[index].siblings[atraces[index].siblings_size - 1] = simplify_steps[i].related_rule_index;
            }
        }
    }

    arrange_trace_size = max_level + 1;
    arrange_trace = malloc(arrange_trace_size * sizeof(Array));

    for (i = 0; i < arrange_trace_size; i++)
    {
        arrange_trace[i].array = 0;
        arrange_trace[i].array_size = 0;
    }

    // Rearrange
    for (i = 0; i < atraces_size; i++)
    {
        int index = atraces[i].level;
        arrange_trace[index].array_size++;
        arrange_trace[index].array = realloc(arrange_trace[index].array, arrange_trace[index].array_size * sizeof(int));
        arrange_trace[index].array[arrange_trace[index].array_size - 1] = i;
    }

    // Rewrite
    // for (i = 0; i < arrange_trace_size; i++)
    // {
    //     for (j = arrange_trace[i].array_size - 1; j >= 0; j--)
    //     {
    //         int index = arrange_trace[i].array[j];
    //         final_traces_size++;
    //         final_traces = realloc(final_traces, final_traces_size * sizeof(Node));
    //         final_traces[final_traces_size - 1] = atraces[index];
    //     }
    // }

    for (i = arrange_trace_size - 1; i >= 0; i--)
    {
        // Reverse trace
        for (j = 0; j < arrange_trace[i].array_size; j++)
        {
            int index = arrange_trace[i].array[j];
            reverse_final_traces_size++;
            reverse_final_traces = realloc(reverse_final_traces, reverse_final_traces_size * sizeof(Node));
            reverse_final_traces[reverse_final_traces_size - 1] = atraces[index];
        }
    }

    // Debugging purpose
    // for (i = 0; i < reverse_final_traces_size; i++)
    // {
    //     printf("Node %d: ", i);
    //     for (j = 0; j < reverse_final_traces[i].siblings_size; j++)
    //     {
    //         printf("%d :", reverse_final_traces[i].siblings[j]);
    //         print_ca_debug(reverse_final_traces[i].siblings[j]);
    //     }
    //     printf("\n");
    // }

    // Find success path
    found_success_path = 0;
    // generate_and_check_trace(final_traces, final_traces_size, path, 0, 0);

    generate_and_check_trace_reverse(reverse_final_traces, reverse_final_traces_size, path, 0, 0, temp_config_array, temp_config_array_size, t.target_user);

    if (found_success_path)
    {
        for (i = 0; i < success_path_len; i++)
        {
            if (success_path[i] != -13)
            {
                generate_trace_CA_version2(success_path[i], t.target_user);
            }
        }
    }
    else
    {
        // find_related_traces(final_traces, final_traces_size);
        find_related_traces_reverse(reverse_final_traces, reverse_final_traces_size);

        // generate_and_check_trace(related_traces, related_traces_size, path, 0, 0);
        generate_and_check_trace_reverse(related_traces, related_traces_size, path, 0, 0, temp_config_array, temp_config_array_size, t.target_user);

        if (found_success_path)
        {
            for (i = 0; i < success_path_len; i++)
            {
                if (success_path[i] != -13)
                {
                    generate_trace_CA_version2(success_path[i], t.target_user);
                }
            }
        }
        else
        {
            // Cannot found additional traces
            return_val = 0;
        }
    }

    for (i = 0; i < atraces_size; i++)
    {
        free(atraces[i].siblings);
    }
    free(atraces);
    atraces = 0;
    // free(final_traces);
    // final_traces = 0;

    free(reverse_final_traces);
    reverse_final_traces = 0;

    // Free related trace size for second try
    if (related_traces_size > 0)
    {
        for (i = 0; i < related_traces_size; i++)
        {
            free(related_traces[i].siblings);
        }
    }
    free(related_traces);
    related_traces = 0;
    related_traces_size = 0;

    for (i = 0; i < arrange_trace_size; i++)
    {
        free(arrange_trace[i].array);
    }
    free(arrange_trace);
    arrange_trace = 0;
    arrange_trace_size = 0;

    return return_val;
}

static void
free_second_phase_data()
{
    int i;
    free(role_map_array);
    free(user_map_array);
    free(cr_map_array);
    free(ca_map_array);
    for (i = 0; i < trace_array_size; i++)
    {
        free(trace_array[i].administrative_user);
        free(trace_array[i].config_array);
    }
    free(trace_array);
    free_ARBAC_data();
}


RelatedRules *related_rules;
int related_rules_size;

static void
find_related_rules(Trace *traces, int traces_size)
{
    int i, j;
    related_rules_size = traces_size;
    related_rules = malloc(related_rules_size * sizeof(RelatedRules));

    for (i = 0; i < traces_size; i++)
    {
        if (i == 0 || traces[i].rule_type == 1)
        {
            related_rules[i].rule_index = -1;
            related_rules[i].related = 0;
            related_rules[i].related_size = 0;
        }
        else
        {
            related_rules[i].rule_index = ca_array[traces[i].rule_number].target_role_index;
            related_rules[i].related = 0;
            related_rules[i].related_size = 0;
        }
    }

    for (i = 0; i < ca_array_size; i++)
    {
        for (j = 1; j < related_rules_size; j++)
        {
            if (ca_array[i].target_role_index == related_rules[j].rule_index && i != related_rules[j].rule_index)
            {
                related_rules[j].related_size++;
                related_rules[j].related = realloc(related_rules[j].related, related_rules[j].related_size * sizeof(int));
                related_rules[j].related[related_rules[j].related_size - 1] = i;
            }
        }
    }
}

static int
produce_original_counter_example_help(void)
{
    int original_target_user_index, i, j, return_val = 1;

    // Set of related rules to a rule
    related_rules = 0;
    related_rules_size = 0;

    original_trace_array = 0;
    original_trace_array_size = 0;

    int * temp_config_array = 0;
    int temp_config_array_size = 0;

    // From the trace of SIMPLIFIED counter example, find the original rule
    int super_index = find_real_user_from_SUPER_USER();

    // Change target user and administrative user if they are SUPER_USER
    for (i = 0; i < trace_array_size; i++)
    {
        // Assign the original rule index to the SIMPLIFIED TRACE
        trace_array[i].rule_number = get_original_rule_index(trace_array[i].rule_number, trace_array[i].rule_type);
        // Change user
        if (super_index != -1)
        {   if (strcmp(trace_array[i].administrative_user, "SUPER_USER") == 0)
            {
                free(trace_array[i].administrative_user);
                trace_array[i].administrative_user = malloc(strlen(user_array[super_index]) + 1);
                strcpy(trace_array[i].administrative_user, user_array[super_index]);
            }
            if (strcmp(trace_array[i].target_user, "SUPER_USER") == 0)
            {
                free(trace_array[i].target_user);
                trace_array[i].target_user = malloc(strlen(user_array[super_index]) + 1);
                strcpy(trace_array[i].target_user, user_array[super_index]);
            }
        }
    }

    char * original_target_user = 0;

    // From the trace already obtained
    if (trace_array_size == 0)
    {
        fprintf(stderr, "error: there is something wrong with original counterexample\n");
        abort();
    }
    else
    {
        original_target_user = malloc(strlen(trace_array[trace_array_size - 1].target_user) + 1);
        strcpy(original_target_user, trace_array[trace_array_size - 1].target_user);
    }

    // If original target user is a new user
    if (!countNEWAlready && original_target_user != NULL && strstr(original_target_user, "NEW_USER") != NULL)
    {
        int new_trace_index = -1;
        for (i = 0; i < trace_array_size; i++)
        {
            if (strstr(trace_array[i].target_user, "NEW_USER") != NULL)
            {
                new_trace_index = i;
                break;
            }
        }

        if (new_trace_index == -1) // There is only one trace
        {
            // Never happen
            fprintf(stderr, "error: there is something wrong with the trace\n");
            abort();
        }
        else
        {
            // Build up to the first trace since NEW_USER are assign a role in the beginning of time
            int ca_rule = trace_array[new_trace_index].rule_number;
            int succeeded = 0;
            for (i = 0; i < new_rule_array_size; i++)
            {
                if (
                    (belong_to(ca_array[ca_rule].positive_role_array, ca_array[ca_rule].positive_role_array_size, ca_array[new_rule_array[i]].target_role_index) != -1 || ca_array[ca_rule].positive_role_array_size == 0)
                    && belong_to(ca_array[ca_rule].negative_role_array, ca_array[ca_rule].negative_role_array_size, ca_array[new_rule_array[i]].target_role_index) == -1
                )
                {
                    succeeded = 1;
                    generate_trace_CA_NEW_USER(new_rule_array[i], original_target_user);
                    break;
                }
            }

            if (!succeeded)
            {
                int i;
                for (i = simplify_steps_size - 1; i >= 0; i--)
                {
                    // Sibling nodes
                    if (simplify_steps[i].simplify_rule == 5)
                    {
                        if (simplify_steps[i].affected_rule_index == ca_rule)
                        {
                            int new_ca_rule = simplify_steps[i].related_rule_index;
                            for (i = 0; i < new_rule_array_size; i++)
                            {
                                if (
                                    (belong_to(ca_array[new_ca_rule].positive_role_array, ca_array[new_ca_rule].positive_role_array_size, ca_array[new_rule_array[i]].target_role_index) != -1 || ca_array[new_ca_rule].positive_role_array_size == 0)
                                    && belong_to(ca_array[new_ca_rule].negative_role_array, ca_array[new_ca_rule].negative_role_array_size, ca_array[new_rule_array[i]].target_role_index) == -1
                                )
                                {
                                    succeeded = 1;
                                    generate_trace_CA_NEW_USER(new_rule_array[i], original_target_user);
                                    goto SUCC;
                                }
                            }
                        }
                    }
                }
            }

            if (!succeeded)
            {
                if (new_rule_array_size > 0)
                {
                    // Any rule with NEW in precondition can be applied
                    generate_trace_CA_NEW_USER(new_rule_array[0], original_target_user);
                }
            }

SUCC:;
        }
    }


    // Loop on trace till the end
    for (i = 0; i < trace_array_size; i++)
    {
        // Can revoke rule
        if (trace_array[i].rule_type == 1)
        {
            generate_trace_CR(trace_array[i]);
        }
        // Can assign rule
        if (trace_array[i].rule_type == 0)
        {
            int trace_index = find_trace_index_same_user(original_trace_array, original_trace_array_size, trace_array[i].target_user);

            if (trace_index == -1)   // First time this user show up on the trace
            {
                temp_config_array = 0;
                temp_config_array_size = 0;

                int user_index = find_user_from_dict(trace_array[i].target_user);
                if (user_index > -1)    // Super user
                {
                    int y;
                    for (y = 0; y < ua_array_size; y++)
                    {
                        if (ua_array[y].user_index == user_index)
                        {
                            temp_config_array_size++;
                            temp_config_array = realloc(temp_config_array, temp_config_array_size * sizeof(int));
                            temp_config_array[temp_config_array_size - 1] = ua_array[y].role_index;
                        }
                    }
                }
            }
            else
            {
                temp_config_array = original_trace_array[trace_index].config_array;
                temp_config_array_size = original_trace_array[trace_index].config_array_size;
            }

            // Normal CA rule
            if (ca_array[trace_array[i].rule_number].type == 0)
            {
                if (check_precondition_CA(trace_array[i].rule_number, temp_config_array, temp_config_array_size, trace_array[i].target_user))
                {
                    // This precondition for the rule can be apply with current user
                    if (belong_to(temp_config_array, temp_config_array_size, ca_array[trace_array[i].rule_number].target_role_index) == -1)
                    {
                        generate_trace_CA(trace_array[i]);
                    }
                }
                else
                {
                    // Generate additional traces when this is not satisfiable
                    if (!generate_additional_traces(trace_array[i]))
                    {
                        if (related_rules_size == 0)
                        {
                            find_related_rules(trace_array, trace_array_size);
                        }
                        // Use brute force method if the first attempt failure
                        int check = 0;
                        for (j = 0; j < related_rules[i].related_size; j++)
                        {
                            if (check_precondition_CA(related_rules[i].related[j], temp_config_array, temp_config_array_size, trace_array[i].target_user))
                            {
                                if (belong_to(temp_config_array, temp_config_array_size, ca_array[related_rules[i].related[j]].target_role_index) == -1)
                                {
                                    check = 1;
                                    generate_trace_CA_version2(related_rules[i].related[j], trace_array[i].target_user);
                                    break;
                                }
                            }
                        }
                        if (!check)
                        {
                            return_val = 0;
                            break;
                        }
                    }
                }
            }
            /*Always can apply the rule since the precondition is TRUE*/
            else if (ca_array[trace_array[i].rule_number].type == 1)
            {
                if (belong_to(temp_config_array, temp_config_array_size, ca_array[trace_array[i].rule_number].target_role_index) == -1)
                {
                    generate_trace_CA(trace_array[i]);
                }
            }
            else
            {
                if (check_precondition_NEW_CA(temp_config_array_size, trace_array[i].target_user))
                {
                    generate_trace_CA_NEW_USER(trace_array[i].rule_number, trace_array[i].target_user);
                }
                else
                {
                    return_val = 0;
                    break;
                }
            }
        }

        // Stop when figuring out the last step
        if (original_trace_array_size > 0)
        {
            if (belong_to(original_trace_array[original_trace_array_size - 1].config_array, original_trace_array[original_trace_array_size - 1].config_array_size, goal_role_index) != -1)
            {
                return_val = 1;
                break;
            }
        }
    }

    // Free things

    for (i = 0; i < related_rules_size; i++)
    {
        if (related_rules[i].related_size != 0)
        {
            free(related_rules[i].related);
        }
    }
    free(related_rules);

    return return_val;
}

/**
 * Produce original counter example from counter example of simplified ARBAC
 */
static void
produce_original_counter_example(FILE *ceFILE)
{
    if (reached_initially)
    {
        print_trace_special(ceFILE);
        goto END;
    }

    if (produce_original_counter_example_help())
    {
        // Generate result trace
        print_trace(original_trace_array, original_trace_array_size, ceFILE);

        // free data
        int i;
        for (i = 0; i < original_trace_array_size; i++)
        {
            free(original_trace_array[i].config_array_before);
            free(original_trace_array[i].config_array);
            free(original_trace_array[i].administrative_user);
            free(original_trace_array[i].target_user);
        }
        free(original_trace_array);
    }
    else
    {
        print_cant_find_counter_example(ceFILE);
    }
END:
    free_second_phase_data();
}


// Generating counter example from all the files (full version)
void
generate_counter_example(int argc, char **argv)
{
    char *cefilename = 0;
    FILE *ceFILE;

    char *debugFilename = "cex_debug.log";
    debugFile = fopen(debugFilename, "w");

    cefilename = malloc(strlen(argv[5]) + strlen("_CounterExample") + 2);
    sprintf(cefilename, "%s_CounterExample", argv[5]);
    ceFILE = fopen(cefilename, "w");

    // Read CBMC Log XML
    readCBMCXMLLog(argv[1]);

    // No counter example found
    if (!hasCounterExample)
    {
        // Read ARBAC file
        readARBAC(argv[3]);
        print_no_counter_example(ceFILE);
        fclose(ceFILE);
        redirect_stdout(cefilename);
        free(cefilename);
        free_ARBAC_data();
        return;
    }

    // Read CBMC translated file
    readCBMCTranslated(argv[2]);

    // Read ARBAC file
    readARBAC(argv[3]);

    // Produce Counter Example from simplified ARBAC policies
    produce_counter_example(ceFILE, 0);

    fclose(ceFILE);
    redirect_stdout(cefilename);
    free(cefilename);

    fclose(debugFile);

    // Remove debug file
    remove(debugFilename);
}

// Generating counter example from all the files (full version)
void
generate_counter_example_full(int argc, char **argv)
{
    char *cefilename = 0;
    FILE *ceFILE;

    char *debugFilename = "cex_debug.log";
    debugFile = fopen(debugFilename, "w");

    cefilename = malloc(strlen(argv[5]) + strlen("_CounterExample") + 2);
    sprintf(cefilename, "%s_CounterExample", argv[5]);
    ceFILE = fopen(cefilename, "w");

    // Read CBMC Log XML
    readCBMCXMLLog(argv[1]);

    // No counter example found
    if (!hasCounterExample)
    {
        // Read ARBAC file
        readARBAC(argv[3]);
        print_no_counter_example(ceFILE);
        fclose(ceFILE);
        redirect_stdout(cefilename);
        free(cefilename);
        free_ARBAC_data();
        return;
    }

    // Read CBMC translated file
    readCBMCTranslated(argv[2]);

    // Read ARBAC file
    readARBAC(argv[3]);

    // Produce Counter Example from simplified ARBAC policies
    produce_counter_example(ceFILE, 1);

    // Read simplify log file
    readSimplifyLog(argv[4]);
    // // Read original ARBAC file
    readARBAC(argv[5]);

    // Produce Counter Example from original ARBAC policies
    produce_original_counter_example(ceFILE);

    fclose(ceFILE);
    redirect_stdout(cefilename);
    free(cefilename);

    fclose(debugFile);

    // Remove debug file
    if (!debug)
    {
        remove(debugFilename);
    }
}