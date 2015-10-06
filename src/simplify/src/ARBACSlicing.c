#include "ARBACSimplify.h"

static
char *int2str(int value)
{
    char temp[20];

    sprintf(temp, "%d", value);

    return strdup(temp);
}

static
int belong_dict(Dictionary *dict, int value)
{
    int *i;
    char temp[20];

    sprintf(temp, "%d", value);

    i = (int *) iDictionary.GetElement(dict, temp);

    if (i == NULL)
    {
        return 0;
    }
    else
    {
        return 1;
    }
}

// Remove a set of irrelevant roles
static void
remove_roles(Dictionary *dict)
{
    int i, j, k;

    // Remove can_assign rules that have in positive precondition a role of X or have as target
    for (j = 0; j < ca_array_size; j++)
    {
        if (ca_array[j].admin_role_index != -13)
        {
            if (belong_dict(dict, ca_array[j].target_role_index) ||
                    belong_dict(dict, ca_array[j].admin_role_index) )
            {
                fprintf(tmplog, "CAN ASSIGN rule number %d ", j);
                print_ca_rule(j);
                fprintf(tmplog, "is removed by slicing procedure\n");

                ca_array[j].admin_role_index = -13; /* Mark as removal */
                ca_array[j].target_role_index = -13; /* Mark as removal */
            }
            else
            {
                k = 0;
                for (i = 0; i < ca_array[j].positive_role_array_size; i++)
                {
                    if (belong_dict(dict, ca_array[j].positive_role_array[i]))
                    {

                        fprintf(tmplog, "CAN ASSIGN rule number %d ", j);
                        print_ca_rule(j);
                        fprintf(tmplog, "is removed by slicing procedure\n");

                        ca_array[j].admin_role_index = -13; /* Mark as removal */
                        ca_array[j].target_role_index = -13; /* Mark as removal */
                        k = 1;
                        break;
                    }
                }
                if (!k)
                {
                    for (i = 0; i < ca_array[j].negative_role_array_size; i++)
                    {
                        if (belong_dict(dict, ca_array[j].negative_role_array[i]))
                        {
                            drop_role_precondition(ca_array[j].negative_role_array[i], j);
                            i--;
                        }
                    }
                }
            }
        }
    }

    // Remove can_revoke rules that have a role of X as target
    for (j = 0; j < cr_array_size; j++)
    {
        if (cr_array[j].admin_role_index != -13)
        {
            if (belong_dict(dict, cr_array[j].admin_role_index) ||
                    belong_dict(dict, cr_array[j].target_role_index))
            {
                fprintf(tmplog, "CAN REVOKE rule number %d <%s,%s> is removed by slicing\n", j, get_role(cr_array[j].admin_role_index), get_role(cr_array[j].target_role_index));

                cr_array[j].admin_role_index = -13; /* Mark as removal */
                cr_array[j].target_role_index = -13; /* Mark as removal */
            }
        }
    }

    // Remove role of X from the user role relation, marked as removal
    for (j = 0; j < ua_array_size; j++)
    {
        if (ua_array[j].user_index != -13)
        {
            if (belong_dict(dict, ua_array[j].role_index))
            {
                fprintf(tmplog, "USER ASSIGNMENT relation number %d <%s,%s> is removed by slicing\n", j, get_user(ua_array[j].user_index), get_role(ua_array[j].role_index));

                ua_array[j].user_index = -13; /* Mark as removal */
                ua_array[j].role_index = -13; /* Mark as removal */
            }
        }
    }

    // Remove role of X from the set of administrative roles, marked ask removal
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (belong_dict(dict, admin_role_array_index[i]))
        {
            // Mark as removal
            admin_role_array_index[i] = -13;
        }
    }

    // Remove role of X from the set of roles, marked as removal
    for (j = 0; j < role_array_size; j++)
    {
        if (strcmp(role_array[j], "removed_role") != 0)
        {
            if (belong_dict(dict, j))
            {
                // Mark as removal : assign removed_rule to the role's name
                free(role_array[j]);
                role_array[j] = 0;
                role_array[j] = malloc(strlen("removed_role") + 1);
                strcpy(role_array[j], "removed_role");
            }
        }
    }
}

static set
current_roles_set()
{
    set R;
    int i;
    R.array_size = 0;
    R.array = 0;
    for (i = 0; i < role_array_size; i++)
    {
        if (strcmp(role_array[i], "removed_role") != 0)
        {
            R = add_last_element(R, i);
        }
    }
    return R;
}

static int
property_forward(int ca_index, set S)
{
    set P, ad;
    set tmp;
    int result = 0;

    ad.array = 0;
    ad.array_size = 0;

    // Do not include the super role
    if (ca_array[ca_index].admin_role_index != -10)
    {
        ad.array_size = 1;
        ad.array = malloc(sizeof(int));
        ad.array[0] = ca_array[ca_index].admin_role_index;
    }

    P = build_set(ca_array[ca_index].positive_role_array, ca_array[ca_index].positive_role_array_size);

    tmp = union_set(P, ad);

    if (subset_of(tmp, S))
    {
        result = 1;
    }

    // Free data
    free(tmp.array);
    tmp.array = 0;

    return result;
}

static int
slicing_forward()
{
    Dictionary *sliced_role_dict;
    set S_star, R, X;
    int i;
    int size_S = 0;

    R = current_roles_set();

    // The admin roles set
    set admins;
    admins.array = 0;
    admins.array_size = 0;

    // Compute initial S*
    S_star.array = 0;
    S_star.array_size = 0;
    if (ua_array_size == 0)
    {
        // Do not perform slicing forward or may?
        return 0;
    }

    // Add role to the S* set
    for (i = 0; i < ua_array_size; i++)
    {
        if (ua_array[i].user_index != -13)
        {
            if (belong_to(S_star.array, S_star.array_size, ua_array[i].role_index) == -1)
            {
                S_star.array_size++;
                S_star.array = realloc(S_star.array, S_star.array_size * sizeof(int));
                S_star.array[S_star.array_size - 1] = ua_array[i].role_index;
            }
        }
    }

    // Compute S* till fixed point
    while (1)
    {
        size_S = S_star.array_size;
        for (i = 0; i < ca_array_size; i++)
        {
            // Not a removed rules
            if (ca_array[i].admin_role_index != -13)
            {
                // Always keep admin roles first
                if (ca_array[i].admin_role_index != -10)
                {
                    admins = add_element(admins, ca_array[i].admin_role_index);
                }
                if (property_forward(i, S_star))
                {
                    S_star = add_element(S_star, ca_array[i].target_role_index);
                }
            }
        }
        // S_star reach fixed point
        if (size_S == S_star.array_size || S_star.array_size == R.array_size)
        {
            break;
        }
    }

    // Also include the target role
    S_star = add_element(S_star, goal_role_index);

    // Compute S* \/ admin roles
    S_star = union_set(S_star, admins);

    // Compute useless role set X = R\S*
    X = different_set(R, S_star);
    size_S = X.array_size;

    fprintf(tmplog, "Set of useless roles from SLICING FORWARD\n");
    for (i = 0; i < X.array_size; i++)
    {
        fprintf(tmplog, "%s ", get_role(X.array[i]));
    }
    fprintf(tmplog, "\nSlicing Forward Removing-------------\n");

    sliced_role_dict = iDictionary.Create(sizeof(int *), role_array_size);
    for (i = 0; i < X.array_size; i++)
    {
        if (X.array[i] != -13)
        {
            iDictionary.Add(sliced_role_dict, int2str(X.array[i]), &(X.array[i]));
        }
    }

    // Remove useless roles set from the system
    remove_roles(sliced_role_dict);
    // purify_roles(X.array, X.array_size);

    fprintf(tmplog, "\n-------------------------------------\n");

    // Free data
    free(X.array);
    iDictionary.Finalize(sliced_role_dict);

    return size_S;
}

static set
union_precondition(int ca_index)
{
    set result;
    set P, N;

    P.array = 0;
    P.array_size = 0;
    N.array = 0;
    N.array_size = 0;

    P = build_set(ca_array[ca_index].positive_role_array, ca_array[ca_index].positive_role_array_size);
    N = build_set(ca_array[ca_index].negative_role_array, ca_array[ca_index].negative_role_array_size);

    // Special treatment for rule with NEW in precondition
    if (ca_array[ca_index].type == 2)
    {
        P = add_element(P, ca_array[ca_index].target_role_index);
    }

    result = union_set(P, N);

    return result;
}

static int
slicing_backward()
{
    Dictionary *sliced_role_dict;
    set S_star, R, X;
    set tmp;
    int i;
    int size_S;

    // The set of current roles
    R = current_roles_set();

    // The admin roles set
    set admins;
    admins.array = 0;
    admins.array_size = 0;

    // Initial the S*
    S_star.array_size = 1;
    S_star.array = malloc(sizeof(int));
    S_star.array[0] = goal_role_index;

    // Compute S* till fixed point
    while (1)
    {
        size_S = S_star.array_size;
        for (i = 0; i < ca_array_size; i++)
        {
            if (ca_array[i].admin_role_index != -13)
            {
                // Always keep admin roles first
                if (ca_array[i].admin_role_index != -10)
                {
                    admins = add_element(admins, ca_array[i].admin_role_index);
                }
                if (belong_to(S_star.array, S_star.array_size, ca_array[i].target_role_index) != -1)
                {
                    tmp = union_precondition(i);
                    S_star = union_set(S_star, tmp);
                    // New change, now the admin should be in consideration otherwise things go wrong
                    if (ca_array[i].admin_role_index != -10)
                    {
                        S_star = add_element(S_star, ca_array[i].admin_role_index);
                    }
                }
            }
        }
        // S* reach fixed point
        if (size_S == S_star.array_size || S_star.array_size == R.array_size)
        {
            break;
        }
    }

    // Compute S* \/ admin roles
    S_star = union_set(S_star, admins);

    // Compute X = R\S*
    X = different_set(R, S_star);
    size_S = X.array_size;

    fprintf(tmplog, "Set of useless roles from SLICING BACKWARD\n");
    for (i = 0; i < X.array_size; i++)
    {
        fprintf(tmplog, "%s ", get_role(X.array[i]));
    }
    fprintf(tmplog, "\nSlicing Backward Removing------------\n");


    sliced_role_dict = iDictionary.Create(sizeof(int *), role_array_size);
    for (i = 0; i < X.array_size; i++)
    {
        if (X.array[i] != -13)
        {
            iDictionary.Add(sliced_role_dict, int2str(X.array[i]), &(X.array[i]));
        }
    }
    // Remove useless roles from the system
    remove_roles(sliced_role_dict);
    // purify_roles(X.array, X.array_size);

    fprintf(tmplog, "\n-------------------------------------\n");

    // Free data
    free(X.array);
    iDictionary.Finalize(sliced_role_dict);

    return size_S;
}

// Slicing procedure
int
slicing()
{
    fprintf(tmplog, "----------------------------\n");
    fprintf(tmplog, "-----  SLICING  CHECK  -----\n");
    fprintf(tmplog, "----------------------------\n");

    // The system does not make sense if there are no user
    if (user_array_size == 0 || role_array_size == 0)
    {
        return 0;
    }

    return (slicing_forward() + slicing_backward());
}
