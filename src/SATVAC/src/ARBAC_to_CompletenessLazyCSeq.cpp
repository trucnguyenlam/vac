#include "ARBACExact.h"
#include <time.h>

// #ifndef GLOBALS_INT
// #define GLOBALS_INT 1
// #endif

#ifndef GLOBALS_ALL_USERS
#define GLOBALS_ALL_USERS 1
#endif

// #ifndef MERGE_RULES
// #define MERGE_RULES 1
// #endif

#define TYPE "_Bool"

static char const *and_op = "&&";
static char const *or_op = "||";

static char const *assume = "__VERIFIER_assume";

static int threads_count;
static int use_tracks;

#ifdef MERGE_RULES
int *roles_ca_counts = NULL;
int *roles_cr_counts = NULL;
int **per_role_ca_indexes = NULL;
int **per_role_cr_indexes = NULL;

static void precompute_merge() {

    roles_ca_counts = (int *) malloc(sizeof(int) * role_array_size);
    roles_cr_counts = (int *) malloc(sizeof(int) * role_array_size);
    per_role_ca_indexes = (int **) malloc(sizeof(int *) * role_array_size);
    per_role_cr_indexes = (int **) malloc(sizeof(int *) * role_array_size);

    for (int i = 0; i < role_array_size; ++i) {
        //INSTANTIATING roles_ca_counts and per_role_ca_indexes
        roles_ca_counts[i] = 0;
        per_role_ca_indexes[i] = NULL;

        // COUNTING CAs
        for (int j = 0; j < ca_array_size; ++j) {
            if (ca_array[j].target_role_index == i) {
                roles_ca_counts[i]++;
            }
        }
        //INSTANTIATING per_role_ca_indexes CONTENT
        if (roles_ca_counts[i] > 0) {
            int k = 0;
            per_role_ca_indexes[i] = (int *) malloc(sizeof(int) * roles_ca_counts[i]);

            for (int j = 0; j < ca_array_size; ++j) {
                if (ca_array[j].target_role_index == i) {
                    if (k >= roles_ca_counts[i])
                        fprintf(stderr, "Something went wrong in ca count. Segfaulting\n");
                    per_role_ca_indexes[i][k++] = j;
                }
            }
        }


        //INSTANTIATING roles_cr_counts and per_role_cr_indexes
        roles_cr_counts[i] = 0;
        per_role_cr_indexes[i] = NULL;

        // COUNTING CRs
        for (int j = 0; j < cr_array_size; ++j) {
            if (cr_array[j].target_role_index == i) {
                roles_cr_counts[i]++;
            }
        }
        //INSTANTIATING per_role_cr_indexes CONTENT
        if (roles_cr_counts[i] > 0) {
            int k = 0;
            per_role_cr_indexes[i] = (int *) malloc(sizeof(int) * roles_cr_counts[i]);

            for (int j = 0; j < cr_array_size; ++j) {
                if (cr_array[j].target_role_index == i) {
                    if (k >= roles_cr_counts[i])
                        fprintf(stderr, "Something went wrong in cr count. Segfaulting\n");
                    per_role_cr_indexes[i][k++] = j;
                }
            }
        }
    }

    return;
}

static void
deallocate_precomputated_values() {
    for (int i = 0; i < role_array_size; ++i) {
        if (per_role_ca_indexes[i] != NULL)
            free(per_role_ca_indexes[i]);
        if (per_role_cr_indexes[i] != NULL)
            free(per_role_cr_indexes[i]);
    }
    free(roles_ca_counts);
    free(roles_cr_counts);
    free(per_role_ca_indexes);
    free(per_role_cr_indexes);
}

#endif

static int NumBits(int pc) {
    int i = 1, bit = 0;

    if (pc < 2 ) return 1;

    while (pc >= i) {
        i = i * 2;
        bit++;
    }

    return (bit);
}

static int
get_pc_count(){
    #ifdef MERGE_RULES
        int n = 0;
        for (int i = 0; i < role_array_size; ++i) {
            if (roles_ca_counts[i] > 0)
                n++;
            if (roles_cr_counts[i] > 0)
                n++;
        }
        return NumBits(n + 1);
    #else
        return NumBits(ca_array_size + cr_array_size + 1);
    #endif
}

static void
generate_header(FILE *outputFile, char *inputFile, int rounds, int steps) {
	time_t mytime;
    mytime = time(NULL);
	fprintf(outputFile, "/*\n");
	fprintf(outputFile, "*  generated by VAC [ 0000 / 0000 ]\n");
	fprintf(outputFile, "*\n");
	fprintf(outputFile, "*  instance version    {}\n");
	fprintf(outputFile, "*\n");
	fprintf(outputFile, "*  %s\n", ctime(&mytime));
	fprintf(outputFile, "*\n");
	fprintf(outputFile, "*  params:\n");
	fprintf(outputFile, "*    %s, --rounds %d --steps %d\n", inputFile, rounds, steps);
    #ifdef GLOBALS_INT
    fprintf(outputFile, "* GLOBALS_INT\n");
    #else
    fprintf(outputFile, "* GLOBALS_BOOL\n");
    #endif
    #ifdef GLOBALS_ALL_USERS
    fprintf(outputFile, "* GLOBALS_ALL_USERS\n");
    #else
    fprintf(outputFile, "* GLOBALS_THREADS_ONLY\n");
    #endif
    #ifdef MERGE_RULES
    fprintf(outputFile, "* MERGE_RULES\n");
    #else
    fprintf(outputFile, "* UNMERGE_RULES\n");
    #endif
    fprintf(outputFile, "*\n");
    fprintf(outputFile, "*  users: %d\n", user_array_size);
    fprintf(outputFile, "*  roles: %d\n", role_array_size);
    fprintf(outputFile, "*  adminroles: %d\n", admin_role_array_index_size);
    fprintf(outputFile, "*  CA: %d\n", ca_array_size);
    fprintf(outputFile, "*  CR: %d\n", cr_array_size);
    fprintf(outputFile, "*  ThreadCount: %d\n", threads_count);
	fprintf(outputFile, "*\n");
	fprintf(outputFile, "*/\n");

	fprintf(outputFile, "\n\n");

	//fprintf(outputFile, "#include <assert.h>\n");
    fprintf(outputFile, "#define THREADS %d\n", threads_count);
	fprintf(outputFile, "#define THREADS_CONFIGURATIONS %d\n", user_array_size);
    fprintf(outputFile, "#define ROUNDS %d\n", rounds);
	fprintf(outputFile, "#define STEPS %d\n", steps);
	// fprintf(outputFile, "#define STOP_VOID(A) return;\n");
	// fprintf(outputFile, "#define STOP_NONVOID(A) return;\n");
	fprintf(outputFile, "// #define IF(T,A,B) if (__cs_pc != A) goto B;\n");
	
    // fprintf(outputFile, "#define IF(T,A,B,E) if (((__cs_pc1 != A) && (__cs_pc2 != A)) || (!(E)) ) goto B;\n");

    fprintf(outputFile, "#define IF(PC,NPC,COND,APPL) if (");
    fprintf(outputFile, "((__cs_pc%d != PC)", 0);
    for (int i = 1; i < steps; ++i)
    {
        fprintf(outputFile, " %s (__cs_pc%d != PC)", and_op, i);
    }
    fprintf(outputFile, ") || (!(COND)) ) { goto NPC; } APPL;\n");

	// fprintf(outputFile, "#ifndef NULL\n");
	// fprintf(outputFile, "#define NULL 0\n");
	// fprintf(outputFile, "#endif	\n");

	// fprintf(outputFile, "void __VERIFIER_error();\n");

	fprintf(outputFile, "\n");

	int nbits = get_pc_count();

    fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] nondet_bitvector();\n", nbits);
	fprintf(outputFile, "_Bool nondet_bool();\n");

	fprintf(outputFile, "\n");

    for (int i = 0; i < steps; ++i) {
        fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] __cs_pc%d;\n", nbits, i);
    }

	fprintf(outputFile, "\n");

	return;
}

static void
generate_globals(FILE *outputFile) {
	int i = 0, j = 0, count = 0;

    fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n\n");
    for (i = 0; i < admin_role_array_index_size; i++)
    {
        count = 0;
        // Check if an admin role is already in some user
        for (j = 0; j < user_config_array_size; j++)
        {
            if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i]))
            {
                count++;
                #ifndef GLOBALS_INT
                    break;
                #endif
            }
        }
        #ifdef GLOBALS_ALL_USERS
        #ifdef GLOBALS_INT
            fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] glob_%s = %d;\n", NumBits(user_array_size), role_array[admin_role_array_index[i]], count);
        #else
            fprintf(outputFile, "%s glob_%s = %d;\n", TYPE, role_array[admin_role_array_index[i]], count);
        #endif
        #else
        #ifdef GLOBALS_INT
            fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] glob_%s = 0;\n", NumBits(user_array_size), role_array[admin_role_array_index[i]]);
        #else
            fprintf(outputFile, "%s glob_%s = 0;\n", TYPE, role_array[admin_role_array_index[i]]);
        #endif
        #endif
    }
    fprintf(outputFile, "\n");
}

static void
generate_thread_locals(FILE *outputFile, int thread_id) {
    fprintf(outputFile, "\n/*---------- THREAD %d LOCAL VARIABLES ---------*/\n", thread_id);
    for (int i = 0; i < role_array_size; i++)
    {	
        if (use_tracks) {
            fprintf(outputFile, "static %s local_Thread_%d_loc_%s = %d;\n", TYPE, thread_id, role_array[i], 0);
        }
        else {
            fprintf(outputFile, "static %s local_Thread_%d_loc_%s = %d;\n", TYPE, thread_id, role_array[i], 
                belong_to(user_config_array[thread_id].array, user_config_array[thread_id].array_size, i));
        }
    }
}

static void
generate_locals(FILE *outputFile) {
    fprintf(outputFile, "/*---------- THREADS LOCAL VARIABLES ---------*/\n\n");
    for (int i = 0; i < threads_count; ++i)
    {
        generate_thread_locals(outputFile, i);
    }
}

static void
generate_CA_cond(FILE *outputFile, int thread_id, int ca_index) {
    int i, j;
    // fprintf(outputFile, "        /*Thread %d is assinged to some user*/\n", thread_id);
    // fprintf(outputFile, "        thread_%d_assigned\n", thread_id);
    // Condition to apply a can_assign rule
    fprintf(outputFile, "        /* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "        (glob_%s %s\n", role_array[ca_array[ca_index].admin_role_index], and_op);
    // Precondition must be satisfied
    if (ca_array[ca_index].type == 0)      // Has precondition
    {   
        if (ca_array[ca_index].positive_role_array_size > 0) {
            fprintf(outputFile, "        /* Positive preconditions */\n");
            fprintf(outputFile, "        (      local_Thread_%d_loc_%s\n", thread_id, role_array[ca_array[ca_index].positive_role_array[0]]);
            for (j = 1; j < ca_array[ca_index].positive_role_array_size; j++)
            {
                fprintf(outputFile, "            %s local_Thread_%d_loc_%s\n", and_op, thread_id, role_array[ca_array[ca_index].positive_role_array[j]]);
            }
            fprintf(outputFile, "        ) %s\n", and_op);
        }
        if (ca_array[ca_index].negative_role_array_size > 0) {
            fprintf(outputFile, "        /* Negative preconditions */\n");
            fprintf(outputFile, "        (      (!local_Thread_%d_loc_%s)\n", thread_id, role_array[ca_array[ca_index].negative_role_array[0]]);
            for (j = 1; j < ca_array[ca_index].negative_role_array_size; j++)
            {
                fprintf(outputFile, "            %s (!local_Thread_%d_loc_%s)\n", and_op, thread_id, role_array[ca_array[ca_index].negative_role_array[j]]);
            }
            fprintf(outputFile, "        ) %s\n", and_op);
        }
    }
    // Optional this user is not in this target role yet
    fprintf(outputFile, "        /* Role not assigned yet */\n");
    fprintf(outputFile, "        (!local_Thread_%d_loc_%s)\n", thread_id, role_array[ca_array[ca_index].target_role_index]);
    fprintf(outputFile, "        )");    
}

static void
generate_CR_cond(FILE *outputFile, int thread_id, int cr_index) {
    int i, j;
    // fprintf(outputFile, "        /*Thread %d is assinged to some user*/\n", thread_id);
    // fprintf(outputFile, "        thread_%d_assigned\n", thread_id);
    // Condition to apply a can_assign rule
    fprintf(outputFile, "        /* Precondition */\n");
    // Admin role must be available
    fprintf(outputFile, "        (glob_%s %s\n", role_array[cr_array[cr_index].admin_role_index], and_op);    
    // Optional this user is in this target role yet
    fprintf(outputFile, "        /*Role assigned*/\n");
    fprintf(outputFile, "        local_Thread_%d_loc_%s)", thread_id, role_array[cr_array[cr_index].target_role_index]);
}

static void
generate_updates(FILE *outputFile, int thread_id) {
    #ifdef GLOBALS_INT
    fprintf(outputFile, "    /*--- GLOBAL ROLE ARE EXACT SINCE INT ---*/\n");
    #else
    fprintf(outputFile, "    /*--- GLOBAL ROLE CONSISTENCY UPDATE ---*/\n");
    for (int i = 0; i < admin_role_array_index_size; i++) {
        for (int j = 0; j < cr_array_size; j++) {
                if (admin_role_array_index[i] == cr_array[j].target_role_index) {
                    char *role = role_array[admin_role_array_index[i]];
                    fprintf(outputFile, "    glob_%s = glob_%s %s local_Thread_%d_loc_%s;\n", role, role, or_op, thread_id, role);
                    break;
                }
            }
    }
    // glob_Author_d = glob_Author_d || __cs_local_Thread_user3_loc_Author_d;
    #endif
}

static void
simulate_can_assign(FILE *outputFile, int thread_id, int ca_index, int label_index) {
    fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    print_ca_comment(outputFile, ca_index);
    fprintf(outputFile, "    IF( %d,\n", label_index);
    fprintf(outputFile, "        tThread_%d_%d,\n", thread_id, label_index + 1);
    generate_CA_cond(outputFile, thread_id, ca_index);
    fprintf(outputFile, ",\n");
    if (belong_to(admin_role_array_index, admin_role_array_index_size, ca_array[ca_index].target_role_index)) {
        #ifdef GLOBALS_INT
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 1;\n", thread_id, role_array[ca_array[ca_index].target_role_index]);
        fprintf(outputFile, "        glob_%s++\n", role_array[ca_array[ca_index].target_role_index]);
        #else
        fprintf(outputFile, "        glob_%s = local_Thread_%d_loc_%s = 1\n", role_array[ca_array[ca_index].target_role_index], thread_id, role_array[ca_array[ca_index].target_role_index]);
        #endif
    }
    else {
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 1\n", thread_id, role_array[ca_array[ca_index].target_role_index]);
    }
    fprintf(outputFile, "    )\n\n");
}

static void
simulate_can_revoke(FILE *outputFile, int thread_id, int cr_index, int label_index) {
    fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    print_cr_comment(outputFile, cr_index);
    fprintf(outputFile, "    IF( %d,\n", label_index);
    fprintf(outputFile, "        tThread_%d_%d,\n", thread_id, label_index + 1);
    generate_CR_cond(outputFile, thread_id, cr_index);
    fprintf(outputFile, ",\n");
    if (belong_to(admin_role_array_index, admin_role_array_index_size, cr_array[cr_index].target_role_index)) {
        #ifdef GLOBALS_INT
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 0;\n", thread_id, role_array[cr_array[cr_index].target_role_index]);
        fprintf(outputFile, "        glob_%s--\n", role_array[cr_array[cr_index].target_role_index]);
        #else
        fprintf(outputFile, "        glob_%s = local_Thread_%d_loc_%s = 0\n", role_array[cr_array[cr_index].target_role_index], thread_id, role_array[cr_array[cr_index].target_role_index]);
        #endif
    }
    else {
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 0\n", thread_id, role_array[cr_array[cr_index].target_role_index]);
    }
    fprintf(outputFile, "    )\n\n");
}

#ifdef MERGE_RULES
static void
simulate_can_assigns_by_role(FILE *outputFile, int thread_id, int target_role_index, int label_index) {
    // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
    int i = 0;
    fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
    fprintf(outputFile, "    IF( %d,\n", label_index);
    fprintf(outputFile, "        tThread_%d_%d,", thread_id, label_index + 1);

    for (i = 0; i < roles_ca_counts[target_role_index] - 1; ++i) {
        int ca_idx = per_role_ca_indexes[target_role_index][i];
        print_ca_comment(outputFile, ca_idx);
        generate_CA_cond(outputFile, thread_id, ca_idx);
        fprintf(outputFile, " ||\n");
    }

    print_ca_comment(outputFile, per_role_ca_indexes[target_role_index][i]);
    generate_CA_cond(outputFile, thread_id, per_role_ca_indexes[target_role_index][i]);

    fprintf(outputFile, ",\n");
    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        #ifdef GLOBALS_INT
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 1;\n", thread_id, role_array[target_role_index]);
        fprintf(outputFile, "        glob_%s++\n", role_array[target_role_index]);
        #else
        fprintf(outputFile, "        glob_%s = local_Thread_%d_loc_%s = 1\n", role_array[target_role_index], thread_id, role_array[target_role_index]);
        #endif
    }
    else {
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 1\n", thread_id, role_array[target_role_index]);
    }
    fprintf(outputFile, "    )\n\n");
}

static void
simulate_can_revokes_by_role(FILE *outputFile, int thread_id, int target_role_index, int label_index) {
    // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
    int i = 0;
    fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
    fprintf(outputFile, "    IF( %d,\n", label_index);
    fprintf(outputFile, "        tThread_%d_%d,", thread_id, label_index + 1);

    for (i = 0; i < roles_cr_counts[target_role_index] - 1; ++i) {
        int cr_idx = per_role_cr_indexes[target_role_index][i];
        print_cr_comment(outputFile, cr_idx);
        generate_CR_cond(outputFile, thread_id, cr_idx);
        fprintf(outputFile, " ||\n");
    }

    print_cr_comment(outputFile, per_role_cr_indexes[target_role_index][i]);
    generate_CR_cond(outputFile, thread_id, per_role_cr_indexes[target_role_index][i]);

    fprintf(outputFile, ",\n");
    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        #ifdef GLOBALS_INT
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 0;\n", thread_id, role_array[target_role_index]);
        fprintf(outputFile, "        glob_%s--\n", role_array[target_role_index]);
        #else
        fprintf(outputFile, "        glob_%s = local_Thread_%d_loc_%s = 0\n", role_array[target_role_index], thread_id, role_array[target_role_index]);
        #endif
    }
    else {
        fprintf(outputFile, "        local_Thread_%d_loc_%s = 0\n", thread_id, role_array[target_role_index]);
    }
    fprintf(outputFile, "    )\n\n");
}
#endif

static void
generate_check(FILE *outputFile, int thread_id, int label_index) {
    fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    fprintf(outputFile, "    0;");
    // fprintf(outputFile, "    /*---------------ERROR CHECK------------*/\n");
    // fprintf(outputFile, "    if (");
    // fprintf(outputFile, "local_Thread_%d_loc_%s", thread_id, role_array[goal_role_index]);
    // fprintf(outputFile, ") {\n");
    // fprintf(outputFile, "        assert(0);\n");
    // fprintf(outputFile, "    }\n");
}

static void
generate_thread(FILE *outputFile, int thread_id) {
    fprintf(outputFile, "void Thread_%d() {\n\n", thread_id);

    // Not used anymore since is declared at top level
    // generate_locals(outputFile, thread_id, thread_id);
    // fprintf(outputFile, "\n");
    
    generate_updates(outputFile, thread_id);

    int label_idx = 0;
    fprintf(outputFile, "    /*---------- IDLE ROUND REMOVED SINCE PC MAY BE GREATER THAN PC_MAX ---------*/\n");
    // fprintf(outputFile, "    /*---------- IDLE ROUND ---------*/\n");
    // fprintf(outputFile, "    IF(%d, tThread_%d_%d, 1, 0)\n\n", label_idx, thread_id, label_idx + 1);
    // label_idx++;

    int i;
    fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
    #ifdef MERGE_RULES
    fprintf(outputFile, "    /*---------- MERGED PER ROLE ---------*/\n");
    for (int i = 0; i < role_array_size; ++i) {
        // printf("CA idx: %d, role: %s: count: %d\n", i, role_array[i], roles_ca_counts[i]);
        if (roles_ca_counts[i] > 0) {
            simulate_can_assigns_by_role(outputFile, thread_id, i, label_idx++);
        }
    }
    #else
    for (i = 0; i < ca_array_size; i++) {
        simulate_can_assign(outputFile, thread_id, i, label_idx++);
    }
    #endif

    fprintf(outputFile, "\n\n");

    fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
    #ifdef MERGE_RULES
    fprintf(outputFile, "    /*---------- MERGED PER ROLE ---------*/\n");
    for (int i = 0; i < role_array_size; ++i) {
        // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
        if (roles_cr_counts[i] > 0) {
            simulate_can_revokes_by_role(outputFile, thread_id, i, label_idx++);
        }
    }
    #else
    for (i = 0; i < cr_array_size; i++) {
        simulate_can_revoke(outputFile, thread_id, i, label_idx++);
    }
    #endif

    generate_check(outputFile, thread_id, label_idx);
    fprintf(outputFile, "\n\n");
    fprintf(outputFile, "    return;\n");
    fprintf(outputFile, "}\n");
}

static void
generate_threads(FILE *outputFile) {
    for (int i = 0; i < threads_count; ++i) {
        generate_thread(outputFile, i);
        fprintf(outputFile, "\n");
    }
}

static void
initialize_threads_locals(FILE *outputFile) {
    fprintf(outputFile, "/*--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------*/\n");
    for (int i = 0; i < threads_count; ++i) {
        fprintf(outputFile, "%s thread_%d_assigned = 0;\n", TYPE, i);
    }
}

static void
initialize_threads_assignments(FILE *outputFile, int user_id)
{
    int i, j;

    fprintf(outputFile, "    /*--------------- CONFIGURATION OF %s ------------*/\n", user_array[user_id]);

    fprintf(outputFile, "    if (nondet_bool()) {\n");

    for (i = 0; i < threads_count; i++) {
        if (i == 0) {
            fprintf(outputFile, "        if (!thread_%d_assigned) {\n", i);
        }
        else {
            fprintf(outputFile, "        else if (!thread_%d_assigned) {\n", i);
        }

        fprintf(outputFile, "            thread_%d_assigned = 1;\n", i);

        for (j = 0; j < user_config_array[user_id].array_size; j++)
        {
            #ifndef GLOBALS_ALL_USERS
            // if GLOBALS_ALL_USERS is NOT set than we have to set the globals for this role
            if (belong_to(admin_role_array_index, admin_role_array_index_size, user_config_array[user_id].array[j])) {
                #ifdef GLOBALS_INT
                fprintf(outputFile, "            glob_%s++;\n", role_array[user_config_array[user_id].array[j]]);
                #else
                fprintf(outputFile, "            glob_%s = 1;\n", role_array[user_config_array[user_id].array[j]]);
                #endif
            }
            #endif
            fprintf(outputFile, "            local_Thread_%d_loc_%s = 1;\n", i, role_array[user_config_array[user_id].array[j]]);
        }
        fprintf(outputFile, "        }\n");
    }
    fprintf(outputFile, "    }\n\n");
}

static void
initialize_threads(FILE *outputFile) {
    int i;
    fprintf(outputFile, "void initialize_threads() {\n");

    for (i = 0; i < user_array_size; ++i) {
        initialize_threads_assignments(outputFile, i);
    }

    fprintf(outputFile, "    %s(\n", assume);
    
    for (i = 0; i < threads_count - 1; ++i) { 
        fprintf(outputFile, "        thread_%d_assigned %s\n", i, and_op);
    }
    fprintf(outputFile, "        thread_%d_assigned);\n", i);

    fprintf(outputFile, "}\n\n");
}

static void
generate_thread_step(FILE *outputFile, int thread_id, int steps) {
    fprintf(outputFile, "    /* Thread_%d */\n", thread_id);
    for (int i = 0; i < steps; ++i)
    {
        fprintf(outputFile, "    __cs_pc%d = nondet_bitvector();\n", i);
        //fprintf(outputFile, "    // __CPROVER_assume(__cs_pc%d <= %d);\n");
    }
    fprintf(outputFile, "    Thread_%d();\n", thread_id);
}

static void
generate_round(FILE *outputFile, int round, int steps) {
    fprintf(outputFile, "    /* round %d */\n", round);
    for (int i = 0; i < threads_count; ++i) {
        generate_thread_step(outputFile, i, steps);
    }
    fprintf(outputFile, "\n");
}

static void
generate_backup_variables(FILE* outputFile, int rounds){
    for (int round = 0; round < rounds + 1; ++round) {
        fprintf(outputFile, "\n    /*---------- BEFORE ROUND %d BACKUP VARIABLES ---------*/\n", round);
        for (int th_id = 0; th_id < threads_count; ++th_id) {
            fprintf(outputFile, "\n    /*---------- THREAD %d BACKUP VARIABLES ---------*/\n", th_id);
            for (int role = 0; role < role_array_size; role++) {   
                fprintf(outputFile, "    %s round_%d_local_Thread_%d_loc_%s;\n", TYPE, round, th_id, role_array[role]);
            }
        }
    }
}

static void
save_state(FILE* outputFile, int round_id) {
    fprintf(outputFile, "\n    /*---------- SAVE STATE TO ROUND %d BACKUP VARIABLES ---------*/\n", round_id);
    for (int th_id = 0; th_id < threads_count; ++th_id) {
        fprintf(outputFile, "\n    /*---------- SAVE THREAD %d STATUS ---------*/\n", th_id);
        for (int role = 0; role < role_array_size; role++) {
            fprintf(outputFile, "    round_%d_local_Thread_%d_loc_%s = local_Thread_%d_loc_%s;\n", round_id, 
                th_id, role_array[role], th_id, role_array[role]);
        }
    }
}

static void
check_distincts(FILE* outputFile, int round_1, int round_2) {
    fprintf(outputFile, "        /*---------- CHECKING ROUNDS %d and %d ---------*/\n", round_1, round_2);
    for (int th_id = 0; th_id < threads_count; ++th_id) {
        fprintf(outputFile, "        ((round_%d_local_Thread_%d_loc_%s != round_%d_local_Thread_%d_loc_%s)", 
            round_1, th_id, role_array[0],
            round_2, th_id, role_array[0]);
        for (int role = 1; role < role_array_size; role++) {
            fprintf(outputFile, " %s (round_%d_local_Thread_%d_loc_%s != round_%d_local_Thread_%d_loc_%s)", or_op, 
                round_1, th_id, role_array[role],
                round_2, th_id, role_array[role]);
        }
        if (th_id != threads_count - 1) {
            fprintf(outputFile, ") %s\n", or_op);
        }
        else {
            fprintf(outputFile, ")\n");
        }
    }
}

static void
check_completeness(FILE* outputFile, int rounds) {
    fprintf(outputFile, "    /*---------- FINAL DISTINCT ASSERTION ---------*/\n");
    fprintf(outputFile, "    %s complete = \n", TYPE);
    fprintf(outputFile, "        (\n");
    check_distincts(outputFile, 0, 1);
    for (int round_1 = 1; round_1 < rounds; ++round_1) {
        for (int round_2 = round_1 + 1; round_2 < rounds + 1; ++round_2) {
            fprintf(outputFile, "        ) %s (\n", and_op);
            check_distincts(outputFile, round_1, round_2);
        }
    }
    fprintf(outputFile, "        );\n");
    fprintf(outputFile, "\n");
    fprintf(outputFile, "    assert(!complete);\n");
}

static void
generate_main(FILE* outputFile, int rounds, int steps) {
    int i = 0;
    fprintf(outputFile, "int main(void) {\n\n");

    generate_backup_variables(outputFile, rounds);

    if (use_tracks) {
        fprintf(outputFile, "    /*------------THREAD INITIALIZATION-----------*/\n");
        fprintf(outputFile, "    initialize_threads();\n\n");
    }

    for (i = 0; i < rounds; ++i) {
        save_state(outputFile, i);
        generate_round(outputFile, i, steps);
    }

    save_state(outputFile, i);

    check_completeness(outputFile, rounds);

    fprintf(outputFile, "    return 0;\n");
    fprintf(outputFile, "}\n");
}

void
transform_2_lazycseq_completeness_query(char *inputFile, FILE *outputFile, int rounds, int steps, int wanted_threads_count) {

    if (rounds < 1) {
        fprintf(stderr, "Cannot simulate a number of rounds < 1\n");
        exit(EXIT_FAILURE);
    }
    if (steps < 1) {
        fprintf(stderr, "Cannot simulate a number of steps < 1\n");
        exit(EXIT_FAILURE);
    }

    
    read_ARBAC(inputFile);
    // Preprocess the ARBAC Policies
    preprocess(0);
    build_config_array();

    #ifdef MERGE_RULES
    precompute_merge();
    #endif

    //Set the number of user to track
    if (wanted_threads_count < 1) {
        if (user_array_size <= admin_role_array_index_size + 1) {
            threads_count = user_array_size;
            use_tracks = 0;
        }
        else {
            threads_count = admin_role_array_index_size + 1;
            use_tracks = 1;
        }
    }
    else {
        if (user_array_size <= wanted_threads_count) {
            fprintf(stderr, "Cannot spawn %d threads because are more than user count (%d)\n", wanted_threads_count, user_array_size);
            exit(EXIT_FAILURE);
        }
        else {
            threads_count = admin_role_array_index_size + 1;
            use_tracks = 1;
        }   
    }

    //Generate header with common funtions and comments
    generate_header(outputFile, inputFile, rounds, steps);
    
    //Declare global variables
    generate_globals(outputFile);

    //Declare threads local variables
    generate_locals(outputFile);

    if (use_tracks) {
        //Declare thread initialization variables
        initialize_threads_locals(outputFile);
        initialize_threads(outputFile);
    }

    //Generate thread functions
    generate_threads(outputFile);

    //Generate Main funtion
    generate_main(outputFile, rounds, steps);

    //fclose(outputFile);
    //free(newfile);
    #ifdef MERGE_RULES
    deallocate_precomputated_values();
    #endif
    free_data();
    free_precise_temp_data();
}
