#include "ARBACExact.h"
#define EXPLODE_THREADID
#define FORMULA_NEW

// TODO:
//    1. Add optimization by only considering updating target of can_revoke rules
//    2. Add ordering option by consider can assign rules

// UPDATE globals in updateglobal
#define TRANSLATION_TYPE4
#define ROUNDS 4

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

static int N_BIT_THREADID = 0;

static int NumBits(int pc) {
    int i = 1, bit = 1;

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
declare_variables(FILE *outputFile)
{
    int i;

    fprintf(outputFile, "/********************************************************/\n");
    fprintf(outputFile, "/******                DECLARATION                *******/\n");
    fprintf(outputFile, "/********************************************************/\n");

    // Declaration of numer of threads, also thread id
#ifndef EXPLODE_THREADID
    fprintf(outputFile, "enum ThreadID {0..%d};\n\n", user_array_size-1);
#else
    N_BIT_THREADID = NumBits(user_array_size);
    fprintf(outputFile, "class ThreadID {\n");
    for (i = 1; i <= N_BIT_THREADID; i++)
    {
        fprintf(outputFile, "    bool b%d;\n", i);
    }
    fprintf(outputFile, "};\n\n");
#endif
    // Declaration of Global variable
    fprintf(outputFile, "class Roles {\n");
    for (i = 0; i < role_array_size; ++i)
    {
        fprintf(outputFile, "    bool %s;\n", role_array[i]);
    }
    fprintf(outputFile, "};\n\n");

#ifdef TRANSLATION_TYPE4
    fprintf(outputFile, "class Globals{     // Thread interface\n");
    fprintf(outputFile, " Roles  g0;    // round 0\n");
    fprintf(outputFile, " Roles  h0;    // round 0\n");
    fprintf(outputFile, " Roles  g1;    // round 1\n");
    fprintf(outputFile, " Roles  h1;    // round 1\n");
    fprintf(outputFile, " Roles  g2;    // round 2\n");
    fprintf(outputFile, " Roles  h2;    // round 2\n");
    fprintf(outputFile, " Roles  g3;    // round 3\n");
    fprintf(outputFile, " Roles  h3;    // round 3\n");
    fprintf(outputFile, " Roles  L;\n");
    fprintf(outputFile, "}\n");
    fprintf(outputFile, " g0  ~+ h0,\n");
    fprintf(outputFile, " h0  ~+  g1,\n");
    fprintf(outputFile, " g1  ~+ h1,\n");
    fprintf(outputFile, " h1  ~+  L,\n");
    fprintf(outputFile, " L  ~+  g2,\n");
    fprintf(outputFile, " g2  ~+ h2,\n");
    fprintf(outputFile, " h2  ~+  g3,\n");
    fprintf(outputFile, " g3  ~+ h3;\n");
#endif

}

static void
initialize_variables(FILE *outputFile)
{
    int i, j, flag;

    fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n");
    fprintf(outputFile, "bool GlobalInit(\n");
    fprintf(outputFile, "   Roles g\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "(true \n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        flag = 0;
        // Check if an admin role is already in some user
        for (j = 0; j < user_config_array_size; j++)
        {
            if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i]))
            {
                flag = 1;
                break;
            }
        }
        if (flag)
        {
            fprintf(outputFile, "& g.%s=true", role_array[admin_role_array_index[i]]);
        }
        else
        {
            fprintf(outputFile, "& g.%s=false", role_array[admin_role_array_index[i]]);
        }
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size GlobalInit;\n\n");


    fprintf(outputFile, "/*---------- INIT LOCAL VARIABLES ---------*/\n");
    fprintf(outputFile, "bool LocalInit(\n");
    fprintf(outputFile, "   ThreadID t,\n");
    fprintf(outputFile, "   Roles l\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  t < l\n");
    fprintf(outputFile, "(false \n");
    // Simulate initialization for each user
    for (i = 0; i < user_array_size; i++)
    {
        fprintf(outputFile, "| (");
#ifndef EXPLODE_THREADID
        fprintf(outputFile, "t=%d\n", i);
#else
        print_ID(outputFile, "t", i, N_BIT_THREADID);
#endif
        for (j = 0; j < role_array_size; j++)
        {
            if (belong_to(user_config_array[i].array, user_config_array[i].array_size, j))
            {
                fprintf(outputFile, "& l.%s=true", role_array[j]);
            }
            else
            {
                fprintf(outputFile, "& l.%s=false", role_array[j]);
            }
        }
        fprintf(outputFile, ")\n");
    }
    fprintf(outputFile, ");\n");
    fprintf(outputFile, "#size LocalInit;\n\n");
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
simulate_can_assign_rule(FILE *outputFile, int ca_rule, int round)
{
    int i, j;

    // Condition to apply a can_assign rule
    fprintf(outputFile, "| (/* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "(cG.h%d.%s=true", round, role_array[ca_array[ca_rule].admin_role_index]);
    // Precondition must be satisfied
    if (ca_array[ca_rule].type == 0)      // Has precondition
    {
        for (j = 0; j < ca_array[ca_rule].positive_role_array_size; j++)
        {
            fprintf(outputFile, " & cG.L.%s=true", role_array[ca_array[ca_rule].positive_role_array[j]]);
        }
        for (j = 0; j < ca_array[ca_rule].negative_role_array_size; j++)
        {
            fprintf(outputFile, " & cG.L.%s=false", role_array[ca_array[ca_rule].negative_role_array[j]]);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, " & cG.L.%s=false", role_array[ca_array[ca_rule].target_role_index]);
    fprintf(outputFile, ") & /* Applying this rule */\n");
    // Applying this rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_rule].target_role_index))
    {
        fprintf(outputFile, " (dG.L.%s=true) & (dG.h%d.%s=true)\n", role_array[ca_array[ca_rule].target_role_index], round, role_array[ca_array[ca_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, " (dG.L.%s=true)\n", role_array[ca_array[ca_rule].target_role_index]);
    }
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.L.%s=cG.L.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != ca_array[ca_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.h%d.%s=cG.h%d.%s)", round, role_array[admin_role_array_index[i]], round, role_array[admin_role_array_index[i]]);
        }
        // else
        // {
        //     fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        // }
    }

    fprintf(outputFile, ")\n");
}

static void
simulate_can_assigns(FILE *outputFile)
{
    int i, l;
    fprintf(outputFile, "/*---------- CAN ASSIGN SIMULATION ---------*/\n");
    for (l = 0; l < ROUNDS; l++)
    {
        fprintf(outputFile, "bool CanAssign_%d(\n", l);
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
        fprintf(outputFile, "#size CanAssign_%d;\n\n", l);
    }
}

static void
simulate_can_revoke_rule(FILE *outputFile, int cr_rule, int round)
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
        fprintf(outputFile, " (cG.h%d.%s=true", round, role_array[cr_array[cr_rule].admin_role_index]);
    }
    // The user must be in that target role
    fprintf(outputFile, " & cG.L.%s=true", role_array[cr_array[cr_rule].target_role_index]);
    fprintf(outputFile, ") & /* apply this rule */\n");
    // Applying can_revoke rule
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_rule].target_role_index))
    {
        fprintf(outputFile, "(dG.L.%s=false) & (dG.h%d.%s=false)\n", role_array[cr_array[cr_rule].target_role_index], round, role_array[cr_array[cr_rule].target_role_index]);
    }
    else
    {
        fprintf(outputFile, "(dG.L.%s=false)\n", role_array[cr_array[cr_rule].target_role_index]);
    }
    // Copy variables
    // Copy other variables
    fprintf(outputFile, "/* Copy variables */\n");
    for (i = 0; i < role_array_size; i++)
    {
        if (i != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.L.%s=cG.L.%s)", role_array[i], role_array[i]);
        }
    }
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        if (admin_role_array_index[i] != cr_array[cr_rule].target_role_index)
        {
            fprintf(outputFile, "& (dG.h%d.%s=cG.h%d.%s)", round, role_array[admin_role_array_index[i]], round, role_array[admin_role_array_index[i]]);
        }
        // else
        // {
        //     fprintf(outputFile, "& ((dG.%s=cG.%s)|(dG.%s=dL.%s))\n", role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        // }
    }
    fprintf(outputFile, ")\n");
}

static void
simulate_can_revokes(FILE *outputFile)
{
    int i, l;
    fprintf(outputFile, "/*---------- CAN REVOKE SIMULATION ---------*/\n");
    for (l = 0; l < ROUNDS; l++)
    {
        fprintf(outputFile, "bool CanRevoke_%d(\n", l);
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
        fprintf(outputFile, "#size CanRevoke_%d;\n\n", l);
    }

}

static void
simulate_admin_roles(FILE *outputFile)
{
    int i, l;

    fprintf(outputFile, "/*--- ADMIN ROLE CONSISTENCY ----*/\n");
    for (l = 0; l < ROUNDS ; l++)
    {
        fprintf(outputFile, "bool UpdateGlobal_%d(\n", l);
        fprintf(outputFile, "   Globals cG,\n");
        fprintf(outputFile, "   Globals dG\n");
        fprintf(outputFile, ")\n");
        fprintf(outputFile, "  cG  ~+  dG\n");
        fprintf(outputFile, "(true \n");
        for (i = 0; i < admin_role_array_index_size; i++)
        {
            fprintf(outputFile, "& ((dG.h%d.%s=cG.h%d.%s)|(dG.h%d.%s=dG.L.%s))\n", l, role_array[admin_role_array_index[i]], l, role_array[admin_role_array_index[i]], l, role_array[admin_role_array_index[i]], role_array[admin_role_array_index[i]]);
        }
        for (i = 0; i < role_array_size; i++)
        {
            fprintf(outputFile, "& (dG.L.%s=cG.L.%s)\n", role_array[i], role_array[i]);
        }

        fprintf(outputFile, ");\n");
        fprintf(outputFile, "#size UpdateGlobal_%d;\n\n", l);
    }
}

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
    fprintf(outputFile, "   ThreadID t,\n");
    fprintf(outputFile, "   Roles L\n");
    fprintf(outputFile, ")\n");
    fprintf(outputFile, "  t  < L\n");
    fprintf(outputFile, "(true \n");
    if (hasGoalUserMode)
    {
        fprintf(outputFile, "& ");
#ifndef EXPLODE_THREADID
        fprintf(outputFile, "(t=%d)", goal_user_index);
#else
        print_ID(outputFile, "t", goal_user_index, N_BIT_THREADID);
#endif
        fprintf(outputFile, "& (L.%s=true)\n", role_array[goal_role_index]);
    }
    else
    {
        fprintf(outputFile, "& (L.%s=true)\n", role_array[goal_role_index]);
    }
    fprintf(outputFile, ");\n");
}

static void
simulate_rules(FILE * outputFile)
{
    simulate_can_assigns(outputFile);
    simulate_can_revokes(outputFile);
    simulate_admin_roles(outputFile);
    simulate_error(outputFile);
}


static void
mucke_simulate(FILE* outputFile)
{
    int i;
    FILE *formula;
    char line[400];    // Increase the length of formula line

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
        fprintf(outputFile, "| (s=%d & t=%d)\n", i, i+1);
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

    // Copy formula here

#ifndef FORMULA_NEW
    if ((formula = fopen("formula.mu", "r")) == NULL)
#else
    if ((formula = fopen("formula-new.mu", "r")) == NULL)
#endif
    {
        fprintf(stderr, "Cannot open formula file\n");
    }

    while (fgets(line, sizeof line, formula) != NULL)
    {
        fputs(line, outputFile);
    }
}


void
transform_2_MUCKE_ExactAlg(char *inputFile)
{
    FILE *outputFile;
    char *newfile = 0;

    newfile = malloc(strlen(inputFile) + strlen("_ExactAlg_MUCKE.mu") + 2);
    sprintf(newfile, "%s_ExactAlg_MUCKE.mu", inputFile);
    outputFile = fopen(newfile, "w");
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
    mucke_simulate(outputFile);

    fclose(outputFile);
    free(newfile);
    free_data();
    free_precise_temp_data();
}
