#include "ARBACExact.h"
#include "varOrd.h"
#define EXPLODE_THREADID

// #define HEURISTIC_ORDER

#define OPTIMIZED_ADMIN

// TODO:
//    1. Add optimization by only considering updating target of can_revoke rules
//    2. Add ordering option by consider can assign rules (using GETAFIX ordering blindly)
//    3. Design frontier algorithm

// UPDATE globals in updateglobal
#define TRANSLATION_TYPE4
//#define ROUNDS 4

// #define TRANSLATION_TYPE5

/*
    ALGORITHMS OUTLINE

    1. ARBAC becomes concurrent programs, where
        - Admin role are global varible
        - Each user is represent by each thread where
            + Local variable is role (Normal + Admin)
            + Each rule will be statement
            + Update admin role by these statement


    2. Transformation to MUCKE
        - Init global variable
        - In each thread
            + Init local variables
            + Program internal is rule transformation and updating global variable
            + Early termination by reaching target role

        - Simulation of fixpoint algorithm

    3. Optimization
       - Ordering of roles
       - merging CanRevoke and CanAssign

 */

static int rounds = -1;

static int N_BIT_THREADID = 0;

static int NumBits(int pc) {
    int i = 1, bit = 0;

    if (pc <= 2 ) return 1;

    while (pc >= i) {
        i = i * 2;
        bit++;
    }

    return (bit);
}

static void
print_ID(FILE* outputFile, char *str, int pc, int num_bits) {
    int i = 1, j, k;

    fprintf(outputFile, "(/* id=%d */ ", pc);

    while (pc > 0) {
        j = pc % 2;
        pc = pc / 2;
        if (i > 1) fprintf(outputFile, " & ");
        fprintf(outputFile, "%s.b%d=%d", str, i, j);
        i++;
    }

    for (k = i; k <= num_bits; k++) {
        if (k > 1) fprintf(outputFile, " & ");
        fprintf(outputFile, "%s.b%d=0", str, k);
    }

    fprintf(outputFile, ")");

}

static void
print_variable_order(FILE * outputFile)
{
    graph *g;
    linkedList *orderedVertexList;
    item *curr, *prev, *first;

    int i;

    g = newGraph();
    // add node to dependency graph
    for (i = 0; i < role_array_size; i++)
    {
        addNode(g, i);
    }

    // Go through the list of can assign rule to find dependency graph
    for (i = 0; i < ca_array_size; i++)
    {
        if (ca_array[i].type == 0)
        {
            // Add relation between target role and admin role
            addEdge(g, ca_array[i].admin_role_index, ca_array[i].target_role_index);
            // Add relation between each role in precond and target role
            int j;
            for (j = 0; j < ca_array[i].positive_role_array_size; j++)
            {
                addEdge(g, ca_array[i].positive_role_array[j], ca_array[i].target_role_index);
            }
        }
        else
        {
            // Add relation between target role and admin role
            addEdge(g, ca_array[i].admin_role_index, ca_array[i].target_role_index);
        }
    }

    // Variable ordering
    orderedVertexList = variableOrdering(g, 0);

    first = curr = orderedVertexList->head;
    while (curr != NULL) {
        fprintf(outputFile, "   bool %s;\n", role_array[curr->vert->val]);
        curr = curr->next;
    }

}

static void
declare_variables(FILE *outputFile)
{
    int i;

    fprintf(outputFile, "/********************************************************/\n");
    fprintf(outputFile, "/******                DECLARATION                *******/\n");
    fprintf(outputFile, "/********************************************************/\n");

    // Declaration of numer of threads, also thread id
// #ifndef EXPLODE_THREADID
//     fprintf(outputFile, "enum ThreadID {0..%d};\n\n", user_array_size - 1);
// #else
//     N_BIT_THREADID = NumBits(user_array_size);
//     fprintf(outputFile, "class ThreadID {\n");
//     for (i = 1; i <= N_BIT_THREADID; i++)
//     {
//         fprintf(outputFile, "    bool b%d;\n", i);
//     }
//     fprintf(outputFile, "};\n\n");
// #endif
    // Declaration of Global variable
    fprintf(outputFile, "class Roles {\n");
#ifndef HEURISTIC_ORDER
    for (i = 0; i < role_array_size; ++i)
    {
        fprintf(outputFile, "    bool %s;\n", role_array[i]);
    }
#else
    print_variable_order(outputFile);
#endif
    fprintf(outputFile, "};\n\n");

#ifdef TRANSLATION_TYPE4
    fprintf(outputFile, "class Globals{     // Thread interface\n");
    for (i = 0; i < user_array_size; i++)
    {
        fprintf(outputFile, " Roles  g%d;\n", i);
        // fprintf(outputFile, " Roles  h%d;\n", i);
    }
    // fprintf(outputFile, " Roles  L;\n");
    // fprintf(outputFile, " Roles  LP;\n");
    fprintf(outputFile, "}\n");

    if (user_array_size >= 2) {
        fprintf(outputFile, " g%d  ~+  g%d", 0, 1);
        for (i = 1; i < user_array_size - 1; i++)
        {
            fprintf(outputFile, ",\n g%d  ~+  g%d", i, i + 1);
        }
    }
    // for (i = 0; i < rounds / 2 - 1; i++)
    // {
    //     fprintf(outputFile, " h%d  ~+  g%d,\n", i, i + 1);
    // }
    // for (i = rounds / 2; i < rounds - 1; i++)
    // {
    //     fprintf(outputFile, " h%d  ~+  g%d,\n", i, i + 1);

    // }
    // int cond = rounds / 2 - 1;
    // if (cond >= 0){
    //     fprintf(outputFile, " h%d  ~+  L,\n", cond);
    // }
    // fprintf(outputFile, " L   ~+  LP,\n");
    // fprintf(outputFile, " LP   ~+  g%d;\n", rounds / 2);
    fprintf(outputFile, ";\n");
#endif

}

static void
initialize_variables(FILE *outputFile)
{
    int i, j, flag;

    // fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n");
    // fprintf(outputFile, "bool GlobalInit(\n");
    // fprintf(outputFile, "   Roles g\n");
    // fprintf(outputFile, ")\n");
    // fprintf(outputFile, "(true \n");
    // for (i = 0; i < admin_role_array_index_size; i++)
    // {
    //     flag = 0;
    //     // Check if an admin role is already in some user
    //     for (j = 0; j < user_config_array_size; j++)
    //     {
    //         if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i]))
    //         {
    //             flag = 1;
    //             break;
    //         }
    //     }
    //     if (flag)
    //     {
    //         fprintf(outputFile, "& g.%s=true", role_array[admin_role_array_index[i]]);
    //     }
    //     else
    //     {
    //         fprintf(outputFile, "& g.%s=false", role_array[admin_role_array_index[i]]);
    //     }
    // }
    // fprintf(outputFile, ");\n");
    // fprintf(outputFile, "#size GlobalInit;\n\n");


    fprintf(outputFile, "/*---------- INIT LOCAL VARIABLES ---------*/\n");
    fprintf(outputFile, "bool INIT(\n");
    // fprintf(outputFile, "   ThreadID t,\n");
    fprintf(outputFile, "   Globals G\n");
    fprintf(outputFile, ")\n");
    // fprintf(outputFile, "  t < l\n");
    fprintf(outputFile, "(true \n");
    // Simulate initialization for each user
    for (i = 0; i < user_array_size; i++)
    {
        fprintf(outputFile, "& (true");
        for (j = 0; j < role_array_size; j++)
        {
            if (belong_to(user_config_array[i].array, user_config_array[i].array_size, j))
            {
                fprintf(outputFile, "& G.g%d.%s=true", i, role_array[j]);
            }
            else
            {
                fprintf(outputFile, "& G.g%d.%s=false", i, role_array[j]);
            }
        }
        fprintf(outputFile, ")\n");
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size INIT;\n\n");
}


// ######## ##    ## ########  ########    ##
//    ##     ##  ##  ##     ## ##          ##    ##
//    ##      ####   ##     ## ##          ##    ##
//    ##       ##    ########  ######      ##    ##
//    ##       ##    ##        ##          #########
//    ##       ##    ##        ##                ##
//    ##       ##    ##        ########          ##


#ifdef TRANSLATION_TYPE4
static void
simulate_can_assign_rule(FILE *outputFile, int ca_rule, int user_id)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    {
        fprintf(outputFile, "(");
    // Admin role must be available
        {
            fprintf(outputFile, "(false");
            for (i = 0; i < user_array_size; i++) {
                fprintf(outputFile, " | cG.g%d.%s=true", i, role_array[ca_array[ca_rule].admin_role_index]);
            }
            fprintf(outputFile, ")\n");
        }
        // Precondition must be satisfied
        if (ca_array[ca_rule].type == 0)      // Has precondition
        {
            for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
            {
                fprintf(outputFile, " & cG.g%d.%s=true", user_id, role_array[ca_array[ca_rule].positive_role_array[j]]);
            }
            for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
            {
                fprintf(outputFile, " & cG.g%d.%s=false", user_id, role_array[ca_array[ca_rule].negative_role_array[j]]);
            }
        }
        // Optional this user is not in this target role yet
        fprintf(outputFile, " & cG.g%d.%s=false", user_id, role_array[ca_array[ca_rule].target_role_index]);
        fprintf(outputFile, ") & /* Applying this rule */\n");
        // Applying this rule
        // if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
        // {
        //     fprintf(outputFile, " (dG.L.%s=true) & (dG.h%d.%s=true)\n", role_array[ca_array[ca_rule].target_role_index], round, role_array[ca_array[ca_rule].target_role_index]);
        // }
        // else
        // {
        fprintf(outputFile, " (dG.g%d.%s=true)\n", user_id, role_array[ca_array[ca_rule].target_role_index]);
        // }
        // Copy other variables
        fprintf(outputFile, "/* Copy variables */\n");
        for (i = 0; i < role_array_size; i++)
        {
            if (i != ca_array[ca_rule].target_role_index)
            {
                fprintf(outputFile, "& (dG.g%d.%s=cG.g%d.%s)", user_id, role_array[i], user_id, role_array[i]);
            }
        }
        // for (i = 0; i < admin_role_array_index_size; i++)
        // {
        //     if (admin_role_array_index[i] != ca_array[ca_rule].target_role_index)
        //     {
        //         fprintf(outputFile, "& (dG.h%d.%s=cG.h%d.%s)", round, role_array[admin_role_array_index[i]], round, role_array[admin_role_array_index[i]]);
        //     }
        // }
    }

    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i, l;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    for (l = 0; l < user_array_size; l++)
    {
        fprintf(outputFile, "bool CanAssign_t%d(\n", l);
        fprintf(outputFile, "   Globals cG,\n");
        fprintf(outputFile, "   Globals dG\n");
        fprintf(outputFile, ")\n");
        fprintf(outputFile, "  cG  ~+  dG\n");
        fprintf(outputFile, "(false \n");
        for (i = 0; i < ca_array_size; i++)
        {
            print_ca_comment(outputFile, i);
            if (ca_array[i].type != 2)
            {
                simulate_can_assign_rule(outputFile, i, l);
            }
            else
            {
                fprintf(outputFile, "\t/ *Rule with NEW in the precondition are already involved in initialization */\n");
            }
        }
        fprintf(outputFile, ");\n");
        fprintf(outputFile, "#size CanAssign_t%d;\n\n", l);
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule, int user_id)
{
    int i;

    // Condition to apply a can_revoke rule
    fprintf(outputFile, "| ( /* condition */\n");
    // Admin role must be available
    if (cr_array[cr_rule].admin_role_index < 0)
    {
        fprintf(outputFile, " (true");
    }
    else
    {
        fprintf(outputFile, "((false");
        for (i = 0; i < user_array_size; i++) {
            fprintf(outputFile, " | cG.g%d.%s=true", i, role_array[cr_array[cr_rule].admin_role_index]);
        }
        fprintf(outputFile, ")\n");
    }
    // The user must be in that target role
    fprintf(outputFile, " & cG.g%d.%s=true", user_id, role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    // if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    // {
    //     fprintf(outputFile, "(dG.L.%s=false) & (dG.h%d.%s=false)\n", role_array[cr_array[cr_rule].target_role_index], round, role_array[cr_array[cr_rule].target_role_index]);
    // }
    // else
    // {
    fprintf(outputFile, "(dG.g%d.%s=false)\n", user_id, role_array[cr_array[cr_rule].target_role_index]);
    // }
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.g%d.%s=cG.g%d.%s)", user_id, role_array[i], user_id, role_array[i]);
        }
    }
    // for (i = 0; i < admin_role_array_index_size; i++)
    // {
    //     if (admin_role_array_index[i] != cr_array[cr_rule].target_role_index)
    //     {
    //         fprintf(outputFile, "& (dG.h%d.%s=cG.h%d.%s)", round, role_array[admin_role_array_index[i]], round, role_array[admin_role_array_index[i]]);
    //     }
    // }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i, l;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    for (l = 0; l < user_array_size; l++)
    {
        fprintf(outputFile, "bool CanRevoke_t%d(\n", l);
        fprintf(outputFile, "   Globals cG,\n");
        fprintf(outputFile, "   Globals dG\n");
        fprintf(outputFile, ")\n");
        fprintf(outputFile, "  cG  ~+  dG\n");
        fprintf(outputFile, "(false \n");

        for (i = 0; i < cr_array_size; i++)
        {
            print_cr_comment(outputFile, i);
            simulate_can_revoke_rule(outputFile, i, l);
        }
        fprintf(outputFile, ");\n");
        fprintf(outputFile, "#size CanRevoke_t%d;\n\n", l);
    }

}

// static void
// simulate_admin_roles(FILE *outputFile)
// {
//     int i, l;

//     fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
//     for (l = 0; l < rounds ; l++)
//     {
//         fprintf(outputFile, "bool UpdateGlobal_%d(\n", l);
//         fprintf(outputFile, "   Globals cG,\n");
//         fprintf(outputFile, "   Globals dG\n");
//         fprintf(outputFile, ")\n");
//         fprintf(outputFile, "  cG  ~+  dG\n");
//         fprintf(outputFile, "(true \n");
// #ifndef OPTIMIZED_ADMIN
//         for (i = 0; i < admin_role_array_index_size; i++)
//         {
//             fprintf(outputFile, "& (dG.h%d.%s<->(cG.h%d.%s|dG.L.%s))\n", l, role_array[admin_role_array_index[i]], l, role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
//         }
// #else
//         for (i = 0; i < admin_role_array_index_size; i++)
//         {
//             int flag = 0, j;
//             for (j = 0; j < cr_array_size; j++)
//             {
//                 if (admin_role_array_index[i] == cr_array[j].target_role_index)
//                 {
//                     flag = 1;
//                     break;
//                 }
//             }
//             if (flag)
//             {
//                 fprintf(outputFile, "& (dG.h%d.%s<->(cG.h%d.%s|dG.L.%s))\n", l, role_array[admin_role_array_index[i]], l, role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
//             }
//             else
//             {
//                 fprintf(outputFile, "& (dG.h%d.%s=cG.h%d.%s)\n", l, role_array[admin_role_array_index[i]], l, role_array[admin_role_array_index[i]]);
//             }
//         }
// #endif
//         for (i = 0; i < role_array_size; i++)
//         {
//             fprintf(outputFile, "& (dG.L.%s=cG.L.%s)\n", role_array[i], role_array[i]);
//         }

//         fprintf(outputFile, ");\n");
//         fprintf(outputFile, "#size UpdateGlobal_%d;\n\n", l);
//     }
// }

#endif



//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////


static void
simulate_error(FILE * outputFile)
{
    fprintf(outputFile, "/*--- REACHABILITY CHECK ----*/\n");
    fprintf(outputFile, "bool targetReach(\n");
    fprintf(outputFile, "   Globals G\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "(false \n");
    if (hasGoalUserMode)
    {
        fprintf(outputFile, "| (G.g%d.%s=true)\n", goal_user_index, role_array[goal_role_index]);
    }
    else
    {
        for (int i = 0; i < user_array_size; ++i)
        {
            fprintf(outputFile, "| (G.g%d.%s=true)\n", i, role_array[goal_role_index]);
        }
    }
    fprintf(outputFile, ");\n");
}

static void
simulate_rules(FILE * outputFile)
{
    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);
    // simulate_admin_roles(outputFile);
    simulate_error(outputFile);
}

static void
simulate_internal_transitions(FILE * outputFile)
{
    int i;

    fprintf(outputFile, "mu bool Sequ_Reach(\n");
    fprintf(outputFile, " bool       s_fr,\n");
    fprintf(outputFile, " blocktype  s_block,\n");
    fprintf(outputFile, " CS         s_r,\n");
    fprintf(outputFile, " ThreadID   s_ID,\n");
    fprintf(outputFile, " Globals    s_G\n");
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "\n");

    fprintf(outputFile, "mu bool Frontier(\n");
    fprintf(outputFile, " bool       s_fr,\n");
    fprintf(outputFile, " blocktype  s_block,\n");
    fprintf(outputFile, " CS         s_r,\n");
    fprintf(outputFile, " ThreadID   s_ID,\n");
    fprintf(outputFile, " Globals    s_G\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, " s_fr    <  s_block,\n");
    fprintf(outputFile, " s_block <  s_r,\n");
    fprintf(outputFile, " s_r     <  s_ID,\n");
    fprintf(outputFile, " s_ID    <  s_G\n");
    fprintf(outputFile, "(\n");
    fprintf(outputFile, "  (exists\n");
    fprintf(outputFile, "      Globals  t_G.\n");
    fprintf(outputFile, "   (\n");
    fprintf(outputFile, "       Sequ_Reach(1, s_block, s_r, s_ID, t_G)        // s is reachable\n");
    fprintf(outputFile, "    & !Sequ_Reach(0, s_block, s_r, s_ID, t_G)\n");
    fprintf(outputFile, "    & ( false\n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, "      //*************** Round %d\n", i);
        fprintf(outputFile, "        | ( s_r = %d\n", i);
        fprintf(outputFile, "            & t_G.L = s_G.LP\n");
        fprintf(outputFile, "            & s_G.LP = s_G.L\n");
        fprintf(outputFile, "            & t_G.h%d = s_G.g%d\n", i, i);
        fprintf(outputFile, "            & s_G.g%d = s_G.h%d\n", i, i);
        fprintf(outputFile, "        )\n\n");
    }
    fprintf(outputFile, "      )\n");
    fprintf(outputFile, "    )\n");
    fprintf(outputFile, "  )\n");
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "\n");


    fprintf(outputFile, "mu bool Internal_Trans(\n");
    fprintf(outputFile, " blocktype  s_block,\n");
    fprintf(outputFile, " CS         s_r,\n");
    fprintf(outputFile, " ThreadID   s_ID,\n");
    fprintf(outputFile, " Globals    s_G\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, " s_block <  s_r,\n");
    fprintf(outputFile, " s_r     <  s_ID,\n");
    fprintf(outputFile, " s_ID    <  s_G\n");
    fprintf(outputFile, "( false\n");
    fprintf(outputFile, "  | Frontier(1, thread, s_r, s_ID, s_G)\n");
    fprintf(outputFile, "\n");
    for (i = 0; i < rounds; ++i)
    {
        fprintf(outputFile, "//*************** Round %d\n", i);
        fprintf(outputFile, "  | ( true\n");
        fprintf(outputFile, "      & ( s_r=%d      // Round %d\n", i, i);
        fprintf(outputFile, "        )\n");
        fprintf(outputFile, "      & (exists     // There exists an internal state that\n");
        fprintf(outputFile, "           Globals t_G.\n");
        fprintf(outputFile, "           (  (  Internal_Trans( s_block, %d, s_ID, t_G )\n", i);
        fprintf(outputFile, "                & s_G.LP = t_G.LP\n");
        fprintf(outputFile, "                & t_G.g%d = s_G.g%d\n", i, i);
        fprintf(outputFile, "              )\n");
        fprintf(outputFile, "            & (   CanAssign_%d( t_G, s_G )\n", i);
        fprintf(outputFile, "                | CanRevoke_%d( t_G, s_G )\n", i);
        fprintf(outputFile, "                | UpdateGlobal_%d( t_G, s_G )\n", i);
        fprintf(outputFile, "              )\n");
        fprintf(outputFile, "           )\n");
        fprintf(outputFile, "        )\n");
        fprintf(outputFile, "    )\n");
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size Internal_Trans;\n");
}


static void
copy_formula(FILE * outputFile, char* formula_filename)
{
    FILE *formula;
    char line[1000];

    if ((formula = fopen(formula_filename, "r")) == NULL)
    {
        fprintf(stderr, "Cannot open file: %s\n", formula_filename);
    }

    while (fgets(line, sizeof line, formula) != NULL)
    {
        fputs(line, outputFile);
    }
}

static void
gen_internal_trans(FILE * outputFile, int user_id) {
    fprintf(outputFile, "   | ( true\n");
    fprintf(outputFile, "      & (exists     // There exists an internal state that\n");
    fprintf(outputFile, "           Globals t_G.\n");
    fprintf(outputFile, "           (   Sequ_Reach(1, t_G)\n");
    fprintf(outputFile, "              &  \n");
    fprintf(outputFile, "            (\n");
    fprintf(outputFile, "              ( true\n");
    for (int i = 0; i < user_array_size; ++i)
    {
        if (i != user_id)
            fprintf(outputFile, "                &  s_G.g%d = t_G.g%d\n", i, i);
    }
    fprintf(outputFile, "                )\n");
    fprintf(outputFile, "             &  ( CanAssign_t%d( t_G, s_G )\n", user_id);
    fprintf(outputFile, "                | CanRevoke_t%d( t_G, s_G )\n", user_id);
    fprintf(outputFile, "                | t_G.g%d = s_G.g%d \n", user_id, user_id);
    fprintf(outputFile, "               )\n");
    fprintf(outputFile, "              )\n");
    fprintf(outputFile, "           )\n");
    fprintf(outputFile, "        )\n");
    fprintf(outputFile, "    )\n");
}


static void
gen_formula(FILE * outputFile)
{
    fprintf(outputFile, "mu bool Sequ_Reach(\n");
    fprintf(outputFile, " bool       s_fr,                  // Frontier bit\n");
    fprintf(outputFile, " Globals    s_G                    // Global variable & Local variables\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, " s_fr    <  s_G\n");
    fprintf(outputFile, "( false\n");
    fprintf(outputFile, "   | (Sequ_Reach(1, s_G))\n");
    fprintf(outputFile, "   | (INIT(s_G) & s_fr=1)\n");
    fprintf(outputFile, "      // early termination\n");
    fprintf(outputFile, "  | ( exists    /* Sequ_Reach::@Exists0 */               // There exists a state such that\n");
    fprintf(outputFile, "            Globals    t_G.\n");
    fprintf(outputFile, "        (\n");
    fprintf(outputFile, "            Sequ_Reach(1, t_G )    // That state is in fixed point and ...\n");
    fprintf(outputFile, "          & targetReach( t_G )                  // target is reached\n");
    fprintf(outputFile, "        )\n");
    fprintf(outputFile, "     )\n");
    fprintf(outputFile, "\n");

    for (int i = 0; i < user_array_size; ++i)
    {
        gen_internal_trans(outputFile, i);
    }

    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size Sequ_Reach;\n");
    fprintf(outputFile, "#timer;\n");
    fprintf(outputFile, "\n");
    fprintf(outputFile, "/******************************************************************************************************/\n");
    fprintf(outputFile, "//                                       Reachabibility check                                         *\n");
    fprintf(outputFile, "/******************************************************************************************************/\n");
    fprintf(outputFile, "\n");
    fprintf(outputFile, "// Uncomment the below line to show witness (if the query is true)\n");
    fprintf(outputFile, "//#wit\n");
    fprintf(outputFile, "( exists\n");
    fprintf(outputFile, "    Globals    t_G.\n");
    fprintf(outputFile, "    (   Sequ_Reach(1, t_G )\n");
    fprintf(outputFile, "      & (\n");
    fprintf(outputFile, "            targetReach( t_G )\n");
    fprintf(outputFile, "        )\n");
    fprintf(outputFile, "    )\n");
    fprintf(outputFile, ");\n");



}


static void
mucke_simulate(FILE* outputFile)
{
    int i;
    int j;

    fprintf(outputFile, "/*--- THREAD FUNCTIONS ----*/\n");
    fprintf(outputFile, "bool increaseThreadID(\n");
    fprintf(outputFile, "   ThreadID s,\n");
    fprintf(outputFile, "   ThreadID t\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  s  ~+  t\n");
    fprintf(outputFile, "(false \n");
#ifndef EXPLODE_THREADID
    for (i = 0; i < user_array_size - 1; i++)
    {
        fprintf(outputFile, "| (s=%d & t=%d)\n", i, i + 1);
    }
    // fprintf(outputFile, "| (s=%d & t=0)\n", i);
#else
    for (i = 0; i < user_array_size - 1; i++)
    {
        fprintf(outputFile, "| (");
        print_ID(outputFile, "s", i, N_BIT_THREADID);
        fprintf(outputFile, " & ");
        print_ID(outputFile, "t", i + 1, N_BIT_THREADID);
        fprintf(outputFile, ")\n");
    }
    // fprintf(outputFile, "| (");
    // print_ID(outputFile, "s", i, N_BIT_THREADID);
    // fprintf(outputFile, " & ");
    // print_ID(outputFile, "t", 0, N_BIT_THREADID);
    // fprintf(outputFile, ")\n");
#endif
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size increaseThreadID;\n\n");

    fprintf(outputFile, "bool maxThreadID(\n");
    fprintf(outputFile, "   ThreadID t\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "( \n");
#ifndef EXPLODE_THREADID
    fprintf(outputFile, "  t=%d\n", user_array_size - 1);
#else
    print_ID(outputFile, "t", user_array_size - 1, N_BIT_THREADID);
#endif
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size maxThreadID;\n\n");

    // Init threadid
    fprintf(outputFile, "bool InitID0(\n");
    fprintf(outputFile, "   ThreadID t\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "( \n");
#ifndef EXPLODE_THREADID
    fprintf(outputFile, "  t=0\n");
#else
    print_ID(outputFile, "t", 0, N_BIT_THREADID);
#endif
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size InitID0;\n\n");

    // Init threadid
    fprintf(outputFile, "bool InitID1(\n");
    fprintf(outputFile, "   ThreadID t\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "(false \n");
    for (i = 1; i < user_array_size; i++)
    {
#ifndef EXPLODE_THREADID
        fprintf(outputFile, " | t=%d\n", i);
#else
        fprintf(outputFile, " | (");
        print_ID(outputFile, "t", i, N_BIT_THREADID);
        fprintf(outputFile, ")\n");
#endif
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size InitID1;\n\n");

    fprintf(outputFile, "bool nonMaxThreadID(\n");
    fprintf(outputFile, "   ThreadID t\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "(false \n");
    for (i = 1; i < user_array_size - 1; i++)
    {
#ifndef EXPLODE_THREADID
        fprintf(outputFile, " | t=%d\n", i);
#else
        fprintf(outputFile, " | (");
        print_ID(outputFile, "t", i, N_BIT_THREADID);
        fprintf(outputFile, ")\n");
#endif
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size nonMaxThreadID;\n\n");


    fprintf(outputFile, "enum CS {0..%d}; // Round or context switch\n\n", rounds - 1);

    fprintf(outputFile, "bool increaseCS(CS s, CS t) // Increase context-switch counter\n");
    fprintf(outputFile, "   s ~+ t\n");
    fprintf(outputFile, "( false\n");
    for (i = 0; i < rounds - 1; i++)
    {
        fprintf(outputFile, "| ( s=%d & t=%d)\n", i, i + 1);
    }
    fprintf(outputFile, ");\n\n");


    fprintf(outputFile, "bool copy_g_g(Globals s, Globals t, CS r)\n");
    fprintf(outputFile, " r  <  s,\n");
    fprintf(outputFile, " s  ~+ t\n");
    fprintf(outputFile, "( true\n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, "& ( s.g%d=t.g%d | (false", i, i);
        for (j = 0; j < i; j++)
        {
            fprintf(outputFile, "| r=%d ", j);
        }
        fprintf(outputFile, " ) )\n");
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool copy_h_h(Globals s, Globals t, CS r)\n");
    fprintf(outputFile, " r  <  s,\n");
    fprintf(outputFile, " s  ~+ t\n");
    fprintf(outputFile, "( true\n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, "& ( s.h%d=t.h%d | (false", i, i);
        for (j = 0; j < i; j++)
        {
            fprintf(outputFile, "| r=%d ", j);
        }
        fprintf(outputFile, " ) )\n");
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool copy_g_h(Globals s, Globals t, CS r)\n");
    fprintf(outputFile, " r  <  s,\n");
    fprintf(outputFile, " s  ~+ t\n");
    fprintf(outputFile, "( true\n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, "& ( s.g%d=t.h%d | (false", i, i);
        for (j = 0; j < i; j++)
        {
            fprintf(outputFile, "| r=%d ", j);
        }
        fprintf(outputFile, " ) )\n");
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool folding( Globals G,  Globals H, CS r )\n");
    fprintf(outputFile, " r  < G,\n");
    fprintf(outputFile, " G ~+ H\n");
    fprintf(outputFile, "( true\n");
    for (i = 0; i < rounds - 1; i++)
    {
        fprintf(outputFile, "& ( H.h%d=G.g%d ", i, i + 1);
        for (j = 0; j <= i; j++)
        {
            fprintf(outputFile, "| r=%d ", j);
        }
        fprintf(outputFile, " )\n");
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool copy_folding_same_round( Globals G, Globals H, CS r )\n");
    fprintf(outputFile, " r  < G,\n");
    fprintf(outputFile, " G ~+ H\n");
    fprintf(outputFile, "(   true\n");
    for (i = 0; i < rounds; i++)
    {
        if (i == 0)
        {
            fprintf(outputFile, "& ( H.g0=G.h0 | (false ))\n");
        }
        else
        {
            fprintf(outputFile, "& ( (H.g%d=G.h%d & H.h%d=G.g%d) | (false ", i, i, i - 1, i);
            for (j = 0; j < i; j++)
            {
                fprintf(outputFile, "| r=%d ", j);
            }
            fprintf(outputFile, " ) )\n");
        }
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool copy_folding_diff_round( Globals G, Globals H, CS r )\n");
    fprintf(outputFile, " r  < G,\n");
    fprintf(outputFile, " G ~+ H\n");
    fprintf(outputFile, "(   true\n");
    for (i = 0; i < rounds - 1; i++)
    {
        fprintf(outputFile, "& ( (H.g%d=G.h%d & H.h%d=G.g%d) | (false ", i, i, i, i + 1);
        for (j = 0; j <= i; j++)
        {
            fprintf(outputFile, "| r=%d ", j);
        }
        fprintf(outputFile, " ) )\n");
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool InitGlobals ( Globals G )\n");
    fprintf(outputFile, "(true \n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, " & G.h%d=G.g%d\n", i, i);
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "enum blocktype {\n");
    fprintf(outputFile, "                thread,                // TLI\n");
    fprintf(outputFile, "                threadnoloc,           // TLI with no local\n");
    fprintf(outputFile, "                want,                  // WRLI\n");
    fprintf(outputFile, "                have                   // RLI\n");
    fprintf(outputFile, "               };\n\n");


    fprintf(outputFile, "bool copy_g( Globals G, Globals H )\n");
    fprintf(outputFile, " G ~+ H\n");
    fprintf(outputFile, "(true\n");
    for (i = 0; i < rounds; i++)
    {
        fprintf(outputFile, "& G.g%d=H.g%d\n", i, i);
    }
    fprintf(outputFile, ");\n\n");

    fprintf(outputFile, "bool copy_no_h( Globals G, Globals H, CS r )\n");
    fprintf(outputFile, "  r  <  G,\n");
    fprintf(outputFile, "  G  ~+ H\n");
    fprintf(outputFile, "(true\n");
    for ( i = 0; i < rounds; ++i)
    {
        fprintf(outputFile, "  & ( G.h%d = H.h%d | r=%d )\n", i, i, i);
    }
    fprintf(outputFile, ");\n");

    fprintf(outputFile, "bool fixed_in_out( Globals s_G, Globals t_G, Globals z_G , CS r )\n");
    fprintf(outputFile, "  r    <   s_G,\n");
    fprintf(outputFile, "  s_G  ~+  t_G,\n");
    fprintf(outputFile, "  t_G  ~+  z_G\n");
    fprintf(outputFile, "(false\n");
    for ( i = 0; i < rounds; ++i)
    {
        fprintf(outputFile, "  | ( r=%d & t_G.h%d =z_G.g%d & z_G.h%d =s_G.h%d & t_G.h%d =t_G.g%d)\n",
            i, i, i, i, i, i, i);
    }
    fprintf(outputFile, ");\n");


    simulate_internal_transitions(outputFile);

}


void
transform_2_MUCKE_ExactAlg(char *inputFile, FILE *outputFile/*, char* formula_filename*/)
{
    /*FILE *outputFile;
    char *newfile = 0;*/

    // if (_rounds < 1) {
    //     fprintf(stderr, "Cannot simulate a number of rounds < 1\n");
    //     exit(EXIT_FAILURE);
    // }

    // rounds = _rounds;

    /*newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_MUCKE.mu") + 2);
    sprintf(newfile, "%s_ExactAlg_MUCKE.mu", inputFile);
    outputFile = fopen(newfile, "w");
    */

    read_ARBAC(inputFile);
    // Preprocess the ARBAC Policies
    preprocess(0);
    build_config_array();

    //Declare variables
    declare_variables(outputFile);

    // Init variables
    initialize_variables(outputFile);

    // Rule simulation functions
    simulate_rules(outputFile);

    // Thread simulation
    // mucke_simulate(outputFile);

    // Copy formula here
    // copy_formula(outputFile, formula_filename);

    // Generate formula here
    gen_formula(outputFile);

    //fclose(outputFile);
    //free(newfile);
    free_data();
    free_precise_temp_data();
}
