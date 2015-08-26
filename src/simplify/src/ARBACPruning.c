#include "ARBACSimplify.h"

// // Debugging purpose
// static void
// print_ca_debug(int ca_index)
// {
//     int j, has_head = 0;
//     // Check for the precondition of each role
//     if (ca_array[ca_index].type == 0)
//     {
//         printf("<%s,", get_role(ca_array[ca_index].admin_role_index));
//         for (j = 0; j < ca_array[ca_index].positive_role_array_size; j++)
//         {
//             if (ca_array[ca_index].positive_role_array[j] != -13)
//             {
//                 if (has_head)
//                 {
//                     printf("&%s", get_role(ca_array[ca_index].positive_role_array[j]));
//                 }
//                 else
//                 {
//                     printf("%s", get_role(ca_array[ca_index].positive_role_array[j]));
//                     has_head = 1;
//                 }
//             }
//         }

//         for (j = 0; j < ca_array[ca_index].negative_role_array_size; j++)
//         {
//             if (ca_array[ca_index].negative_role_array[j] != -13)
//             {
//                 if (has_head)
//                 {
//                     printf("&-%s", get_role(ca_array[ca_index].negative_role_array[j]));
//                 }
//                 else
//                 {
//                     printf("-%s", get_role(ca_array[ca_index].negative_role_array[j]));
//                     has_head = 1;
//                 }
//             }
//         }
//         printf(",%s> ", get_role(ca_array[ca_index].target_role_index));
//         has_head = 0;
//     }
//     else if (ca_array[ca_index].type == 1)
//     {
//         printf("<%s,TRUE,%s> ", get_role(ca_array[ca_index].admin_role_index), get_role(ca_array[ca_index].target_role_index));
//     }
//     else if (ca_array[ca_index].type == 2)
//     {
//         printf("<%s,NEW,%s> ", get_role(ca_array[ca_index].admin_role_index), get_role(ca_array[ca_index].target_role_index));
//     }
//     printf("\n");
// }

// Copy a temporary trace array
void
copy_trace_array(Trace *temp_trace, int temp_trace_size)
{
    int i, temp;
    temp = trace_array_size;
    trace_array_size += temp_trace_size;
    trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
    for (i = 0; i < temp_trace_size; i++)
    {
        //Copy one to one
        trace_array[temp + i].simplify_rule = temp_trace[i].simplify_rule;
        trace_array[temp + i].affected_role_index = temp_trace[i].affected_role_index;
        trace_array[temp + i].affected_rule_index = temp_trace[i].affected_rule_index;
        trace_array[temp + i].affected_rule_type = temp_trace[i].affected_rule_type;
        trace_array[temp + i].related_rule_index = temp_trace[i].related_rule_index;
        trace_array[temp + i].related_rule_type = temp_trace[i].related_rule_type;
    }
}

int *deleted_roles;
int deleted_roles_size;
// Remove an irrelevant role from the system
static void
remove_roles()
{
    int i, j;

    // Remove role from the user role relation, marked as removal
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -13 && deleted_roles[ua_array[i].role_index] == 1)
        {
            fprintf(tmplog, "USER ASSIGNMENT relation number %d <%s,%s> is removed by the above rule\n", i, get_user(ua_array[i].user_index), get_role(ua_array[i].role_index));

            ua_array[i].user_index = -13; /* Mark as removal */
        }
    }

    // Process can_assign rules
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13)
        {
            if (deleted_roles[ca_array[i].target_role_index] == 1)
            {
                fprintf(tmplog, "CAN ASSIGN rule number %d ", i);
                print_ca_rule(i);
                fprintf(tmplog, "is removed by the above rule.\n");
                ca_array[i].admin_role_index = -13;
            }
            else /* Drop this role from the precondition */
            {
                for (j = 0; j < ca_array[i].negative_role_array_size; j++)
                {
                    if (deleted_roles[ca_array[i].negative_role_array[j]])
                    {
                        drop_role_precondition(ca_array[i].negative_role_array[j], i);
                        j--;
                    }
                }
                for (j = 0; j < ca_array[i].positive_role_array_size; j++)
                {
                    if (deleted_roles[ca_array[i].positive_role_array[j]])
                    {
                        drop_role_precondition(ca_array[i].positive_role_array[j], i);
                        j--;
                    }
                }
            }
        }
    }

    // Process all can revoke rule
    for (i = 0; i < cr_array_size; i++)
    {
        if (cr_array[i].admin_role_index != -13 && deleted_roles[cr_array[i].target_role_index] == 1)
        {
            fprintf(tmplog, "CAN REVOKE rule number %d <%s,%s> is removed by the above rule\n", i, get_role(cr_array[i].admin_role_index), get_role(cr_array[i].target_role_index));
            cr_array[i].admin_role_index = -13;
        }
    }

    for (i = 0; i < role_array_size; i++)
    {
        if (deleted_roles[i])
        {
            // Remove role from role array
            free(role_array[i]);
            role_array[i] = 0;
            role_array[i] = malloc(strlen("removed_role") + 1);
            strcpy(role_array[i], "removed_role");
        }
    }
}

// Determine if a role is non positive
static int
non_positive_role(int role_index)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13)
        {
            if (belong_to(ca_array[i].positive_role_array, ca_array[i].positive_role_array_size, role_index) != -1)
            {
                return 0;
            }
        }
    }
    return 1;
}

// Determine if a role is non negative
static int
non_negative_role(int role_index)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13)
        {
            if (belong_to(ca_array[i].negative_role_array, ca_array[i].negative_role_array_size, role_index) != -1)
            {
                return 0;
            }
        }
    }
    return 1;
}

// Determine a property of a non positive role to be irrelevant
static int
non_positive_property(int role_index)
{
    int i;

    // No super role exist
    if (!super_exist)
    {
        return 0;
    }
    for (i = 0; i < cr_array_size; i++)
    {
        if (cr_array[i].admin_role_index == -10 && cr_array[i].target_role_index == role_index)
        {
            trace_array_size++;
            trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
            trace_array[trace_array_size - 1].simplify_rule = 2;
            trace_array[trace_array_size - 1].affected_role_index = role_index;
            trace_array[trace_array_size - 1].affected_rule_index = -1;
            trace_array[trace_array_size - 1].affected_rule_type = 0;
            trace_array[trace_array_size - 1].related_rule_index = i;
            trace_array[trace_array_size - 1].related_rule_type = 1;
            return 1;
        }
    }
    return 0;
}

// Helper function of non negative property
static int
non_negative_property_help(int role_index, int ca_rule_index)
{
    int i, j;
    int result = -1;
    set P, N, P_prime, N_prime, tmp_P, tmp_N;

    // Initialise
    P.array = 0;
    N.array = 0;
    P_prime.array = 0;
    N_prime.array = 0;
    tmp_P.array = 0;
    tmp_N.array = 0;

    // Build P, N set
    P = build_set(ca_array[ca_rule_index].positive_role_array, ca_array[ca_rule_index].positive_role_array_size);
    N = build_set(ca_array[ca_rule_index].negative_role_array, ca_array[ca_rule_index].negative_role_array_size);

    // Check for the other can assign rule
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13 && i != ca_rule_index)
        {
            if (ca_array[i].admin_role_index != -10 && ca_array[i].admin_role_index != ca_array[ca_rule_index].admin_role_index)
            {
                continue;
            }

            if (ca_array[i].target_role_index != role_index)
            {
                continue;
            }

            if (ca_array[i].type == 2)
            {
                continue;
            }

            tmp_P = duplicate_set(P);
            tmp_N = duplicate_set(N);

            // Build P_prime and N_prime
            P_prime = build_set(ca_array[i].positive_role_array, ca_array[i].positive_role_array_size);
            N_prime = build_set(ca_array[i].negative_role_array, ca_array[i].negative_role_array_size);

            tmp_P = remove_element(tmp_P, role_index);
            tmp_N = add_last_element(tmp_N, ca_array[ca_rule_index].target_role_index);

            if (subset_of(P_prime, tmp_P) && subset_of(N_prime, tmp_N))
            {
                // Free variable
                free(tmp_P.array);
                free(tmp_N.array);
                free(P_prime.array);
                free(N_prime.array);
                result = i;
                break;
            }
            free(tmp_P.array);
            free(tmp_N.array);
            free(P_prime.array);
            free(N_prime.array);
        }
    }

    free(P.array);
    free(N.array);
    return result;
}

// Determine if a non negative role is irrelevant
static int
non_negative_property(int role_index)
{
    int i;
    Trace *temp_trace = 0;
    int temp_trace_size = 0;

    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13 && belong_to(ca_array[i].positive_role_array, ca_array[i].positive_role_array_size, role_index) != -1)
        {
            int index = non_negative_property_help(role_index, i);
            if (index == -1)
            {
                free(temp_trace);
                return 0;
            }
            else
            {
                // Store a trace
                temp_trace_size++;
                temp_trace = realloc(temp_trace, temp_trace_size * sizeof(Trace));
                temp_trace[temp_trace_size - 1].simplify_rule = 3; // Non negative rule
                temp_trace[temp_trace_size - 1].affected_role_index = role_index; // Affected Role
                temp_trace[temp_trace_size - 1].affected_rule_index = i;
                temp_trace[temp_trace_size - 1].affected_rule_type = 0;
                temp_trace[temp_trace_size - 1].related_rule_index = index;
                temp_trace[temp_trace_size - 1].related_rule_type = 0;
            }
        }
    }
    // Copy to trace array
    copy_trace_array(temp_trace, temp_trace_size);
    free(temp_trace);
    return 1;
}

// Helper function of mixed property
static int
mixed_property_help(int role_index, int ca_rule_index)
{
    int i;

    int index = non_negative_property_help(role_index, ca_rule_index);
    if (index != -1)
    {
        if (non_positive_property(role_index))
        {
            return index;
        }
        for (i = 0; i < cr_array_size; i++)
        {
            if (cr_array[i].admin_role_index != -13 && cr_array[i].target_role_index == role_index && cr_array[i].admin_role_index == ca_array[ca_rule_index].admin_role_index)
            {
                return index;
            }
        }
        return -1;
    }
    else
    {
        return -1;
    }
}

// Determine if a mixed role is irrelevant
static int
mixed_property(int role_index)
{
    int i;
    Trace *temp_trace = 0;
    int temp_trace_size = 0;

    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13 && belong_to(ca_array[i].positive_role_array, ca_array[i].positive_role_array_size, role_index) != -1)
        {
            int index = mixed_property_help(role_index, i);
            if (index == -1)
            {
                free(temp_trace);
                return 0;
            }
            else
            {
                temp_trace_size++;
                temp_trace = realloc(temp_trace, temp_trace_size * sizeof(Trace));
                temp_trace[temp_trace_size - 1].simplify_rule = 4; // Non negative rule
                temp_trace[temp_trace_size - 1].affected_role_index = role_index; // Affected Role
                temp_trace[temp_trace_size - 1].affected_rule_index = i;
                temp_trace[temp_trace_size - 1].affected_rule_type = 0;
                temp_trace[temp_trace_size - 1].related_rule_index = index;
                temp_trace[temp_trace_size - 1].related_rule_type = 0;
            }
        }
    }
    copy_trace_array(temp_trace, temp_trace_size);
    free(temp_trace);
    return 1;
}

// Simplification rule to remove irrelevant role from ARBAC system
static int
rule_irrelevant_role()
{
    int i;
    int change = 0;
    int t1, t2;

    deleted_roles_size = role_array_size;
    deleted_roles = malloc(deleted_roles_size * sizeof(int));
    for (i = 0; i < deleted_roles_size; i++)
    {
        deleted_roles[i] = 0;
    }

    fprintf(tmplog, "Pruning rule R 1-2-3 check--------------------------\n");

    for (i = 0; i < role_array_size; i++)
    {
        // If this role is administrative role or a removed role -> skip
        if (belong_to(admin_role_array_index, admin_role_array_index_size, i) != -1 || strcmp(role_array[i], "removed_role") == 0 || i == goal_role_index)
        {
            continue;
        }

        t1 = non_negative_role(i);
        t2 = non_positive_role(i);

        if (t1 == 1 && t2 == 1)
        {
            fprintf(tmplog, "This role (%s) is not appear in any precondition so that this can be removed\n", get_role(i));
            change = 1;
            deleted_roles[i] = 1;
            // remove_role(i, 0);
        }
        // If this is a non-negative role
        else if (t1 == 1 && t2 == 0)
        {
            fprintf(tmplog, "This role (%s) is a non-negative role\n", get_role(i));
            if (non_negative_property(i))
            {
                fprintf(tmplog, "This role (%s) also satisfies the R2 property\n", get_role(i));
                fprintf(tmplog, "RULE R2 Remove role (%s) from the system\n", get_role(i));

                change = 1;
                deleted_roles[i] = 1;
                // remove_role(i, 3);
                fprintf(tmplog, "-----------------------------------\n");
            }
        }
        // If this is a non-positive role
        else if (t1 == 0 && t2 == 1)
        {
            fprintf(tmplog, "This role (%s) is a non-positive role\n", get_role(i));
            if (non_positive_property(i))
            {
                fprintf(tmplog, "This role (%s) also satisfies the R1 property\n", get_role(i));
                fprintf(tmplog, "RULE R1 Remove role (%s) from the system\n", get_role(i));

                change = 1;
                deleted_roles[i] = 1;
                // remove_role(i, 2);
                fprintf(tmplog, "-----------------------------------\n");
            }
        }
        // If this is a mixed role
        else
        {
            fprintf(tmplog, "This role (%s) is a mixed role\n", get_role(i));
            if (mixed_property(i))
            {
                fprintf(tmplog, "This role (%s) also satisfies the R3 property\n", get_role(i));
                fprintf(tmplog, "RULE R3 Remove role (%s) from the system\n", get_role(i));

                change = 1;
                deleted_roles[i] = 1;
                // remove_role(i, 4);
                fprintf(tmplog, "-----------------------------------\n");
            }
        }
    }

    if (change)
    {
        remove_roles();
    }

    free(deleted_roles);
    deleted_roles = 0;
    deleted_roles_size = 0;

    fprintf(tmplog, "End--------------------------\n");

    return change;
}

// Variables defined for the rule non fireable
set init_roles;
set *Q_super;
int Q_super_size;

// Compute initial configuration
static void
compute_init_config()
{
    int i;

    init_roles.array = 0;
    init_roles.array_size = 0;

    if (ua_array_size == 0)
    {
        return;
    }

    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -13)
        {
            if (belong_to(init_roles.array, init_roles.array_size, ua_array[i].role_index) == -1)
            {
                init_roles = add_last_element(init_roles, ua_array[i].role_index);
            }
        }
    }
}

static set
compute_Q_set(int ca_rule_index, set init_roles)
{
    set Q;
    int i;

    Q.array = 0;
    Q.array_size = 0;

    if (ca_array[ca_rule_index].positive_role_array_size == 0)
    {
        return Q;
    }

    for (i = 0; i < ca_array[ca_rule_index].positive_role_array_size; i++)
    {
        if (ca_array[ca_rule_index].positive_role_array[i] != -13 && belong_to(init_roles.array, init_roles.array_size, ca_array[ca_rule_index].positive_role_array[i]) == -1)
        {
            Q = add_last_element(Q, ca_array[ca_rule_index].positive_role_array[i]);
        }
    }
    return Q;
}

static void
superset_compute_recur(set Q, int *temp, int depth, int start)
{
    int i, j;
    for (i = start; i < Q.array_size; i++)
    {
        temp[depth] = Q.array[i];

        Q_super_size++;
        Q_super = realloc(Q_super, Q_super_size * sizeof(set));

        Q_super[Q_super_size - 1].array_size = depth + 1;
        Q_super[Q_super_size - 1].array = malloc(Q_super[Q_super_size - 1].array_size * sizeof(int));

        for (j = 0; j <= depth; j++)
        {
            Q_super[Q_super_size - 1].array[j] = temp[j];
        }

        if (i < Q.array_size - 1)
        {
            superset_compute_recur(Q, temp, depth + 1, i + 1);
        }
    }
}

static void
superset_compute(set Q)
{
    int *temp = 0;
    temp = malloc(Q.array_size * sizeof(int));

    Q_super = 0;
    Q_super_size = 0;

    Q_super_size++;
    Q_super = malloc(sizeof(set));
    Q_super[0].array = 0;
    Q_super[0].array_size = 0;
    superset_compute_recur(Q, temp, 0, 0);
    free(temp);
}

static int
non_fireable_property_help_term(set Q, set Z, int rule_index)
{
    int *PuQ = 0; /* P \/ Q set */
    int PuQ_size = 0;
    int i;

    if (belong_to(Q.array, Q.array_size, ca_array[rule_index].target_role_index) == -1 || belong_to(Z.array, Z.array_size, ca_array[rule_index].target_role_index) != -1)
    {
        return 0;
    }

    for (i = 0; i < Q.array_size; i++)
    {
        if (belong_to(ca_array[rule_index].positive_role_array, ca_array[rule_index].positive_role_array_size, Q.array[i]) != -1)
        {
            PuQ_size++;
            PuQ = realloc(PuQ, PuQ_size * sizeof(int));
            PuQ[PuQ_size - 1] = Q.array[i];
        }
    }

    // Test if (P /\ Q) subset of Z
    for (i = 0; i < PuQ_size; i++)
    {
        if (belong_to(Z.array, Z.array_size, PuQ[i]) == -1)
        {
            free(PuQ);
            return 0;
        }
    }

    // Test if Z /\ N = empty set
    for (i = 0; i < Z.array_size; i++)
    {
        if (belong_to(ca_array[rule_index].negative_role_array, ca_array[rule_index].negative_role_array_size, Z.array[i]) != -1)
        {
            free(PuQ);
            return 0;
        }
    }
    free(PuQ);
    return 1;
}

static int
non_fireable_property_help(set Q, set Z, int ca_rule_index)
{
    int i;
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13 && i != ca_rule_index && non_fireable_property_help_term(Q, Z, i) == 1)
        {
            return 0;
        }
    }
    return 1;
}

static int
non_fireable_property(int ca_rule_index)
{
    set Q;
    set *subset_Z = 0;
    int subset_Z_size = 0;
    int result;
    int i, j, k;

    // Compute Q
    Q = compute_Q_set(ca_rule_index, init_roles);

    // If Q is empty
    if (Q.array_size == 0)
    {
        return 0;
    }

    // Compute superset
    superset_compute(Q);

    // For i from 0 to |Q|-1, compute all Z such that |Z| = i
    for (i = 0; i < Q.array_size; i++)
    {
        for (j = 0; j < Q_super_size; j++)
        {
            // Compute all Z with the cardinality of i
            if (Q_super[j].array_size == i)
            {
                subset_Z_size++;
                subset_Z = realloc(subset_Z, subset_Z_size * sizeof(set));
                subset_Z[subset_Z_size - 1] = build_set(Q_super[j].array, Q_super[j].array_size);
            }
        }

        result = 1;
        // Check if exist i for every Z subset of Q with |Z| = i
        for (k = 0; k < subset_Z_size; k++)
        {
            // Check for each Z on can assign rules
            if (non_fireable_property_help(Q, subset_Z[k], ca_rule_index) == 0)
            {
                result = 0;
                break;
            }
        }
        // Free to reuse
        for (j = 0; j < subset_Z_size; j++)
        {
            free(subset_Z[j].array);
        }
        free(subset_Z);
        subset_Z = 0;
        subset_Z_size = 0;

        // If exist i
        if (result)
        {
            free(Q.array);
            for (j = 0; j < Q_super_size; j++)
            {
                free(Q_super[j].array);
            }
            free(Q_super);
            return result;
        }
        result = 1;
    }

    // Manually free variables
    free(Q.array);
    for (i = 0; i < Q_super_size; i++)
    {
        free(Q_super[i].array);
    }
    free(Q_super);
    return 0;
}

// Simplification rule to remove non fireable rule from the ARBAC system
static int
rule_non_fireable()
{
    int i;
    int change = 0;

    fprintf(tmplog, "Pruning rule R4 check--------------------------\n");

    compute_init_config();

    for (i = 0; i < ca_array_size; i++)
    {
        // Test the property R4 for each can assign rule
        if (ca_array[i].admin_role_index != -13 && non_fireable_property(i))
        {
            fprintf(tmplog, "CAN ASSIGN rule number %d ", i);
            print_ca_rule(i);
            fprintf(tmplog, "is removed by Non-Fireable rule.\n");

            change = 1;
            ca_array[i].admin_role_index = -13;
        }
    }

    // Free variable needed for this rule
    free(init_roles.array);
    init_roles.array = 0;
    init_roles.array_size = 0;

    fprintf(tmplog, "End--------------------------\n");

    return change;
}

static int
implied_property_help(int ca1, int ca2)
{
    int result = 0;
    set P1, P2, N1, N2;

    P1 = build_set(ca_array[ca1].positive_role_array, ca_array[ca1].positive_role_array_size);
    P2 = build_set(ca_array[ca2].positive_role_array, ca_array[ca2].positive_role_array_size);

    N1 = build_set(ca_array[ca1].negative_role_array, ca_array[ca1].negative_role_array_size);
    N2 = build_set(ca_array[ca2].negative_role_array, ca_array[ca2].negative_role_array_size);

    if (subset_of(P1, P2) && subset_of(N1, N2))
    {
        result = 1;
    }
    free(P1.array);
    free(P2.array);
    free(N1.array);
    free(N2.array);
    return result;
}

static int
implied_property(int ca1, int ca2)
{
    if (ca_array[ca1].target_role_index != ca_array[ca2].target_role_index)
    {
        return 0;
    }

    if (ca_array[ca1].admin_role_index != ca_array[ca2].admin_role_index)
    {
        return 0;
    }

    // Rule with TRUE in the precondition can implie every other rules
    if (ca_array[ca1].type == 1)
    {
        return 1;
    }

    if (ca_array[ca1].type != 0 && ca_array[ca2].type != 0)
    {
        return 0;
    }

    return implied_property_help(ca1, ca2);
}

// // Simplification rule to remove implied rule from ARBAC system
// static int
// rule_implied()
// {
//     int i, j;
//     int change = 0;

//     fprintf(tmplog, "Pruning rule R6 check--------------------------\n");

//     for (i = 0; i < ca_array_size; i++)
//     {
//         if (ca_array[i].admin_role_index != -13)
//         {
//             for (j = i + 1; j < ca_array_size; j++)
//             {
//                 if (ca_array[j].admin_role_index != -13)
//                 {
//                     if (implied_property(i, j))
//                     {
//                         change = 1;

//                         fprintf(tmplog, "CAN ASSIGN rule number %d ", j);
//                         print_ca_rule(j);
//                         fprintf(tmplog, "is an implied rule of CAN ASSIGN rule number %d ", i);
//                         print_ca_rule(i);
//                         fprintf(tmplog, "\n");

//                         // Remove this implied rule
//                         ca_array[j].admin_role_index = -13;
//                     }
//                     else if (implied_property(j, i))
//                     {
//                         change = 1;

//                         fprintf(tmplog, "CAN ASSIGN rule number %d ", i);
//                         print_ca_rule(i);
//                         fprintf(tmplog, "is an implied rule of CAN ASSIGN rule number %d ", j);
//                         print_ca_rule(j);
//                         fprintf(tmplog, "\n");

//                         // Remove this implied rule
//                         ca_array[i].admin_role_index = -13;
//                         break;
//                     }
//                 }
//             }
//         }
//     }

//     fprintf(tmplog, "End--------------------------\n");

//     return change;
// }

static int
combinable_property_help(int ca1, int ca2)
{
    set P1, P2, N1, N2, tmp1, tmp2;

    P1 = build_set(ca_array[ca1].positive_role_array, ca_array[ca1].positive_role_array_size);
    P2 = build_set(ca_array[ca2].positive_role_array, ca_array[ca2].positive_role_array_size);

    if (P1.array_size != P2.array_size + 1 || !subset_of(P2, P1))
    {
        free(P1.array);
        free(P2.array);
        return -1;
    }

    tmp1 = different_set(P1, P2);
    if (tmp1.array_size != 1)
    {
        free(tmp1.array);
        return -1;
    }

    N1 = build_set(ca_array[ca1].negative_role_array, ca_array[ca1].negative_role_array_size);
    N2 = build_set(ca_array[ca2].negative_role_array, ca_array[ca2].negative_role_array_size);

    if (N1.array_size != N2.array_size - 1 || !subset_of(N1, N2))
    {
        free(N1.array);
        free(N2.array);
        free(tmp1.array);
        return -1;
    }

    tmp2 = different_set(N2, N1);
    if (tmp2.array_size != 1)
    {
        free(tmp1.array);
        free(tmp2.array);
        return -1;
    }

    if (equal_set(tmp1, tmp2) && strcmp(role_array[tmp1.array[0]], "removed_rule") != 0 && tmp1.array[0] != -13)
    {
        int tmp = tmp1.array[0];
        free(tmp1.array);
        free(tmp2.array);
        return tmp;
    }
    else
    {
        free(tmp1.array);
        free(tmp2.array);
        return -1;
    }
}

static int
combinable_property(int ca1, int ca2)
{
    // Extra fix
    if (ca_array[ca1].type != 0 ||  ca_array[ca2].type != 0 )
    {
        return -1;
    }

    if (ca_array[ca1].target_role_index != ca_array[ca2].target_role_index)
    {
        return -1;
    }
    if (ca_array[ca1].admin_role_index != ca_array[ca2].admin_role_index)
    {
        return -1;
    }

    return combinable_property_help(ca1, ca2);
}

static void
combining_2_rules(int ca1, int ca2, int role_index)
{
    // Drop the role in the precondition
    drop_role_precondition(role_index, ca1);
    // Delete the second rule
    ca_array[ca2].admin_role_index = -13;
}

// // Simplification rule to remove combinable rule from ARBAC system
// static int
// rule_combinable()
// {
//     int i, j;
//     int change = 0;

//     fprintf(tmplog, "Pruning rule R5 check--------------------------\n");

//     for (i = 0; i < ca_array_size; i++)
//     {
//         if (ca_array[i].admin_role_index != -13 && ca_array[i].type == 0)
//         {
//             for (j = i + 1; j < ca_array_size; j++)
//             {
//                 if (ca_array[j].admin_role_index != -13 && ca_array[j].type == 0)
//                 {
//                     int role_index = combinable_property(i, j);
//                     if (role_index != -1)
//                     {
//                         change = 1;

//                         fprintf(tmplog, "TWO CAN ASSIGN rule number %d ", i);
//                         print_ca_rule(i);
//                         fprintf(tmplog, "and %d ", j);
//                         print_ca_rule(j);
//                         fprintf(tmplog, "are combinable rules by role %s.\n", get_role(role_index));

//                         trace_array_size++;
//                         trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
//                         trace_array[trace_array_size - 1].simplify_rule = 5;
//                         trace_array[trace_array_size - 1].affected_role_index = role_index;
//                         trace_array[trace_array_size - 1].affected_rule_index = i;
//                         trace_array[trace_array_size - 1].affected_rule_type = 0;
//                         trace_array[trace_array_size - 1].related_rule_index = j;
//                         trace_array[trace_array_size - 1].related_rule_type = 0;

//                         // Combine two can assign rules
//                         combining_2_rules(i, j, role_index);
//                         i--;
//                         break;
//                     }
//                     else
//                     {
//                         role_index = combinable_property(j, i);
//                         if (role_index != -1)
//                         {
//                             change = 1;

//                             fprintf(tmplog, "TWO CAN ASSIGN rule number %d ", i);
//                             print_ca_rule(i);
//                             fprintf(tmplog, "and %d ", j);
//                             print_ca_rule(j);
//                             fprintf(tmplog, "are combinable rules by role %s.\n", get_role(role_index));

//                             trace_array_size++;
//                             trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
//                             trace_array[trace_array_size - 1].simplify_rule = 5;
//                             trace_array[trace_array_size - 1].affected_role_index = role_index;
//                             trace_array[trace_array_size - 1].affected_rule_index = j;
//                             trace_array[trace_array_size - 1].affected_rule_type = 0;
//                             trace_array[trace_array_size - 1].related_rule_index = i;
//                             trace_array[trace_array_size - 1].related_rule_type = 0;

//                             // Combine two can assign rules
//                             combining_2_rules(j, i, role_index);

//                             break;
//                         }
//                     }
//                 }
//             }
//         }
//     }

//     fprintf(tmplog, "End--------------------------\n");

//     return change;
// }

// Simplification rule to remove combinable rule from ARBAC system
static int
rule_combinable_and_implied()
{
    int i, j;
    int change = 0;

    fprintf(tmplog, "Pruning rule R5 and R6 check--------------------------\n");

    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].admin_role_index != -13)
        {
            for (j = i + 1; j < ca_array_size; j++)
            {
                if (ca_array[j].admin_role_index != -13)
                {
                    int role_index = combinable_property(i, j);
                    if (role_index != -1)
                    {
                        change = 1;

                        fprintf(tmplog, "TWO CAN ASSIGN rule number %d ", i);
                        print_ca_rule(i);
                        fprintf(tmplog, "and %d ", j);
                        print_ca_rule(j);
                        fprintf(tmplog, "are combinable rules by role %s.\n", get_role(role_index));

                        trace_array_size++;
                        trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
                        trace_array[trace_array_size - 1].simplify_rule = 5;
                        trace_array[trace_array_size - 1].affected_role_index = role_index;
                        trace_array[trace_array_size - 1].affected_rule_index = i;
                        trace_array[trace_array_size - 1].affected_rule_type = 0;
                        trace_array[trace_array_size - 1].related_rule_index = j;
                        trace_array[trace_array_size - 1].related_rule_type = 0;

                        // Combine two can assign rules
                        combining_2_rules(i, j, role_index);
                        i--;
                        break;
                    }
                    else
                    {
                        role_index = combinable_property(j, i);
                        if (role_index != -1)
                        {
                            change = 1;

                            fprintf(tmplog, "TWO CAN ASSIGN rule number %d ", i);
                            print_ca_rule(i);
                            fprintf(tmplog, "and %d ", j);
                            print_ca_rule(j);
                            fprintf(tmplog, "are combinable rules by role %s.\n", get_role(role_index));

                            trace_array_size++;
                            trace_array = realloc(trace_array, trace_array_size * sizeof(Trace));
                            trace_array[trace_array_size - 1].simplify_rule = 5;
                            trace_array[trace_array_size - 1].affected_role_index = role_index;
                            trace_array[trace_array_size - 1].affected_rule_index = j;
                            trace_array[trace_array_size - 1].affected_rule_type = 0;
                            trace_array[trace_array_size - 1].related_rule_index = i;
                            trace_array[trace_array_size - 1].related_rule_type = 0;

                            // Combine two can assign rules
                            combining_2_rules(j, i, role_index);
                            break;
                        }
                        else // Check for implied property
                        {
                            if (implied_property(i, j))
                            {
                                change = 1;

                                fprintf(tmplog, "CAN ASSIGN rule number %d ", j);
                                print_ca_rule(j);
                                fprintf(tmplog, "is an implied rule of CAN ASSIGN rule number %d ", i);
                                print_ca_rule(i);
                                fprintf(tmplog, "\n");

                                // Remove this implied rule
                                ca_array[j].admin_role_index = -13;
                            }
                            else if (implied_property(j, i))
                            {
                                change = 1;

                                fprintf(tmplog, "CAN ASSIGN rule number %d ", i);
                                print_ca_rule(i);
                                fprintf(tmplog, "is an implied rule of CAN ASSIGN rule number %d ", j);
                                print_ca_rule(j);
                                fprintf(tmplog, "\n");

                                // Remove this implied rule
                                ca_array[i].admin_role_index = -13;
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    fprintf(tmplog, "End--------------------------\n");

    return change;
}

// Aggressive pruning procedure
int
aggressive_pruning()
{
    fprintf(tmplog, "----------------------------\n");
    fprintf(tmplog, "-----  PRUNING  CHECK  -----\n");
    fprintf(tmplog, "----------------------------\n");

    // The system does not make sense if there are no user
    if (user_array_size == 0 || role_array_size == 0)
    {
        return 0;
    }

    return (rule_irrelevant_role() + rule_combinable_and_implied() + rule_non_fireable());
}
