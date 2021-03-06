#include "ARBACExact.h"
#include <time.h>
#include <vector>

namespace SMT {
    #define TYPE "unsigned __CPROVER_bitvector[1]"

    static char const *and_op = "&&";
    static char const *or_op = "||";

    static char const *assume = "__VERIFIER_assume";

    static int *core_roles = NULL;
    static int core_roles_size = 0;

    static int *roles_ca_counts = NULL;
    static int *roles_cr_counts = NULL;
    static int **per_role_ca_indexes = NULL;
    static int **per_role_cr_indexes = NULL;

    static void allocate_core_role_array(int ca_index, int is_ca) {
        core_roles = (int*) calloc(sizeof(int), role_array_size);
        for (int i = 0; i < role_array_size; i++) {
            core_roles[i] = 0;
        }

        if (is_ca) {
            for (int i = 0; i < ca_array[ca_index].positive_role_array_size; i++) {
                core_roles[ca_array[ca_index].positive_role_array[i]] = 1;
                core_roles_size++;
            }
            for (int i = 0; i < ca_array[ca_index].negative_role_array_size; i++) {
                core_roles[ca_array[ca_index].negative_role_array[i]] = 1;
                core_roles_size++;
            }
        }
        else {
            //DO NOTHING FOR THE MOMENT
        }
        
    }

    static void free_core_role_array() {
        free(core_roles);
    }

    static void precompute_merge() {

        float assignable_roles_count = 0;
        float removable_roles_count = 0;

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
                assignable_roles_count++;
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

    static int numBits(int pc) {
        int i = 1, bit = 0;

        if (pc < 2) return 1;

        while (pc >= i) {
            i = i * 2;
            bit++;
        }

        return (bit);
    }

    static void
    generate_header(FILE *outputFile, char *inputFile, int rule_id, int is_ca) {
        time_t mytime;
        mytime = time(NULL);
        fprintf(outputFile, "/*\n");
        fprintf(outputFile, "*  generated by VAC pruning-R6 [ 0000 / 0000 ]\n");
        fprintf(outputFile, "*\n");
        fprintf(outputFile, "*  instance version    {}\n");
        fprintf(outputFile, "*\n");
        fprintf(outputFile, "*  %s\n", ctime(&mytime));
        fprintf(outputFile, "*\n");
        fprintf(outputFile, "*  params:\n");
        fprintf(outputFile, "*    %s, --rounds %d\n", inputFile, core_roles_size + 1);
        fprintf(outputFile, "* MERGE_RULES\n");
        fprintf(outputFile, "*\n");
        fprintf(outputFile, "*  users: %d\n", user_array_size);
        fprintf(outputFile, "*  roles: %d\n", role_array_size);
        fprintf(outputFile, "*  adminroles: %d\n", admin_role_array_index_size);
        fprintf(outputFile, "*  CA: %d\n", ca_array_size);
        fprintf(outputFile, "*  CR: %d\n", cr_array_size);
        fprintf(outputFile, "*\n");
        fprintf(outputFile, "*  Rule: %s, id: %d:\n", is_ca ? "CA" : "CR", rule_id);
        if (is_ca) {
            print_ca_comment(outputFile, rule_id);
        }
        else {
            print_cr_comment(outputFile, rule_id);
        }
        fprintf(outputFile, "*/\n");
        fprintf(outputFile, "\n\n");

        // fprintf(outputFile, "#define IF(PC,COND,APPL) if (");
        // fprintf(outputFile, "(__cs_pc0 == PC) && (COND) ) { APPL; }\n");

        fprintf(outputFile, "\n");

        int pc_count = numBits(core_roles_size + 1);

        fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] nondet_bitvector();\n", pc_count);
        fprintf(outputFile, "%s nondet_bool();\n", TYPE);

        fprintf(outputFile, "\n");

        fprintf(outputFile, "unsigned __CPROVER_bitvector[%d] __cs_pc;\n", pc_count);
        

        fprintf(outputFile, "\n");

        return;
    }

    static void
    generate_globals(FILE *outputFile) {
        int i = 0, j = 0, count = 0;

        fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n\n");
        fprintf(outputFile, "/*---------- CORE ROLES ---------*/\n");
        for (i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                fprintf(outputFile, "%s core_%s = 0;\n", TYPE, role_array[i]);
            }
        }
        fprintf(outputFile, "/*---------- EXTERNAL ROLES ---------*/\n");
        for (i = 0; i < role_array_size; i++) {
            if (!core_roles[i]) {
                fprintf(outputFile, "%s ext_%s = 0;\n", TYPE, role_array[i]);
            }
        }
        fprintf(outputFile, "/*---------- SET CHECKS ---------*/\n");
        for (i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                fprintf(outputFile, "%s set_%s = 0;\n", TYPE, role_array[i]);
            }
        }
        fprintf(outputFile, "/*---------- SET 0-1 CHECKS ---------*/\n");
        for (i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                fprintf(outputFile, "%s value_false_%s = 0;\n", TYPE, role_array[i]);
                fprintf(outputFile, "%s value_true_%s = 0;\n", TYPE, role_array[i]);
            }
        }
        fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
        fprintf(outputFile, "%s skip = 0;\n", TYPE);
        
        fprintf(outputFile, "\n");
    }

    static void
    generate_if_PC(FILE *outputFile, int pc) {
        fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
    }

    static void
    generate_CA_cond(FILE *outputFile, int ca_index) {
        int i, j;
        const char* prefix;
        // fprintf(outputFile, "        /* Precondition */\n");
        // Precondition must be satisfied
        if (ca_array[ca_index].type == 0) {     // Has precondition
            fprintf(outputFile, "          /* Positive preconditions */\n");
            fprintf(outputFile, "          (");
            if (ca_array[ca_index].positive_role_array_size > 0) {
                prefix = core_roles[ca_array[ca_index].positive_role_array[0]] ? "core" : "ext";
                fprintf(outputFile, "(%s_%s\n", prefix, role_array[ca_array[ca_index].positive_role_array[0]]);
                for (j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                    prefix = core_roles[ca_array[ca_index].positive_role_array[j]] ? "core" : "ext";
                    fprintf(outputFile, "            %s %s_%s\n", and_op, prefix, role_array[ca_array[ca_index].positive_role_array[j]]);
                }
                fprintf(outputFile, "          )\n");
            }
            else {
                fprintf(outputFile, "1\n");
            }
            if (ca_array[ca_index].negative_role_array_size > 0) {
                fprintf(outputFile, "          /* Negative preconditions */\n");
                prefix = core_roles[ca_array[ca_index].negative_role_array[0]] ? "core" : "ext";
                fprintf(outputFile, "          %s ((!%s_%s)\n", and_op, prefix, role_array[ca_array[ca_index].negative_role_array[0]]);
                for (j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                    prefix = core_roles[ca_array[ca_index].negative_role_array[j]] ? "core" : "ext";
                    fprintf(outputFile, "              %s (!%s_%s)\n", and_op, prefix, role_array[ca_array[ca_index].negative_role_array[j]]);
                }
                fprintf(outputFile, "            )\n");
            }
            fprintf(outputFile, "          )\n");            
        }
        else {
            fprintf(outputFile, "        (1)\n");
        }
    }

    static void
    generate_CR_cond(FILE *outputFile, int cr_index) {
        int i, j;
        // fprintf(outputFile, "        /*Thread %d is assinged to some user*/\n", thread_id);
        // fprintf(outputFile, "        thread_%d_SET\n", thread_id);
        // Condition to apply a can_assign rule
        fprintf(outputFile, "        /* Positive preconditions */\n");
        // Admin role must be available
        fprintf(outputFile, "        (1)\n");
    }

    static void
    simulate_can_assigns_by_role(FILE *outputFile, int target_role_index, int label_index, int excluded_rule) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        int i = 0;
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        generate_if_PC(outputFile, label_index);
        //fprintf(outputFile, "        tThread_%d_%d,", thread_id, label_index + 1);
        fprintf(outputFile, "        (\n");
        for (i = 0; i < roles_ca_counts[target_role_index]; ++i) {
            int ca_idx = per_role_ca_indexes[target_role_index][i];
            if (ca_idx != excluded_rule) {
                print_ca_comment(outputFile, ca_idx);
                generate_CA_cond(outputFile, ca_idx);
                fprintf(outputFile, "        ||\n");
            }
        }

        // print_ca_comment(outputFile, per_role_ca_indexes[target_role_index][i]);
        // generate_CA_cond(outputFile, per_role_ca_indexes[target_role_index][i]);
        fprintf(outputFile, "        0");
        // This user is not in this target role yet
        fprintf(outputFile, ") %s\n", and_op);
        fprintf(outputFile, "        /* Role not SET yet */\n");
        fprintf(outputFile, "        (!set_%s)", role_array[target_role_index]);

        fprintf(outputFile, ") {\n");

        fprintf(outputFile, "            core_%s = 1;\n", role_array[target_role_index]);
        fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        
        fprintf(outputFile, "    }\n\n");
    }

    static void
    simulate_can_revokes_by_role(FILE *outputFile, int target_role_index, int label_index, int excluded_rule) {
        // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
        int i = 0;
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        generate_if_PC(outputFile, label_index);
        //fprintf(outputFile, "        tThread_%d_%d,", thread_id, label_index + 1);

        fprintf(outputFile, "        (\n");

        for (i = 0; i < roles_cr_counts[target_role_index]; ++i) {
            int cr_idx = per_role_cr_indexes[target_role_index][i];
            if (cr_idx != excluded_rule) {
                print_cr_comment(outputFile, cr_idx);
                generate_CR_cond(outputFile, cr_idx);            
                fprintf(outputFile, "        ||\n");
            }
        }

        // print_cr_comment(outputFile, per_role_cr_indexes[target_role_index][i]);
        // generate_CR_cond(outputFile, per_role_cr_indexes[target_role_index][i]);
        fprintf(outputFile, "        0");
        // This user is not in this target role yet
        fprintf(outputFile, ") %s\n", and_op);
        fprintf(outputFile, "        /* Role not SET yet */\n");
        fprintf(outputFile, "        (!set_%s)", role_array[target_role_index]);

        fprintf(outputFile, ") {\n");

        fprintf(outputFile, "            core_%s = 0;\n", role_array[target_role_index]);
        fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);

        fprintf(outputFile, "    }\n\n");
    }

    static void
    generate_check_implication(FILE *outputFile, int role_index, int user_id) {
        // a ==> b
        // (!a || (a && b))
        // b || !a
        // ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i)
        int init_r_i = 0;
        for (int j = 0; j < user_config_array[user_id].array_size; j++) {
            if (user_config_array[user_id].array[j] == role_index) {
                init_r_i = 1;
                break;
            }
        }    

        char* role = role_array[role_index];
        //FIXME: continue here!!!!
        fprintf(outputFile, "(set_%s || ", role);
        fprintf(outputFile, "!((core_%s != %d) || ", role, init_r_i);
        fprintf(outputFile, "(value_false_%s && %d == 1) || (value_true_%s && %d == 0)))", role, init_r_i, role, init_r_i);
        // fprintf(outputFile, "((core_%s == %d) || ", role, init_r_i);
        // fprintf(outputFile, "((core_%s != %d) && set_%s))", role, init_r_i, role);
    }

    static void
    generate_check(FILE *outputFile, int rule_index, int is_ca) {
        fprintf(outputFile, "    /*--------------- ERROR CHECK ------------*/\n");
        fprintf(outputFile, "    /*--------------- assume(\\phi) ------------*/\n");
        fprintf(outputFile, "    %s(\n", assume);
        if (is_ca) {
            generate_CA_cond(outputFile, rule_index);
        }
        else {
            generate_CR_cond(outputFile, rule_index);
        }
        fprintf(outputFile, "        );\n\n");

        int user_id = 0;
        //         \  /          /\
        // assume(  \/        ( /  \          ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i)))
        //        u_i \in U    r_i \in \phi
        fprintf(outputFile, "//         \\  /          /\\\n");
        fprintf(outputFile, "// assume(  \\/        ( /  \\          ((core_r_i != init_r_i) \\/ ((set_false_r_i /\\ init_r_i = 1) \\/ (set_true_r_i /\\ init_r_i = 0)) => set_r_i)))\n");
        fprintf(outputFile, "//        u_i \\in U    r_i \\in \\phi\n");
        fprintf(outputFile, "    %s(0\n", assume);
        for (int u = 0; u < user_array_size; u++) {
            fprintf(outputFile, "       %s (", or_op);
            for (int i = 0; i < role_array_size; i++) {
                if (core_roles[i]) {
                    generate_check_implication(outputFile, i, u);
                    fprintf(outputFile, " %s ", and_op);
                }
            }
            fprintf(outputFile, "1)\n");
        }
        fprintf(outputFile, "    );\n");
        fprintf(outputFile, "    assert(0);\n");
    }

    static void
    generate_value_true_false(FILE *outputFile, int role_id) {
        char* role = role_array[role_id];
        fprintf(outputFile, "        if (!set_%s && core_%s == 1) {\n", role, role);
        fprintf(outputFile, "            value_true_%s = 1;\n", role);
        fprintf(outputFile, "        }\n");
        fprintf(outputFile, "        if (!set_%s && core_%s == 0) {\n", role, role);
        fprintf(outputFile, "            value_false_%s = 1;\n", role);
        fprintf(outputFile, "        }\n");
    }

    static void
    generate_update_state(FILE *outputFile) {
        fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
        for (int i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                char* role = role_array[i];
                fprintf(outputFile, "    core_%s = set_%s ? core_%s : nondet_bool();\n", role, role, role);
                generate_value_true_false(outputFile, i);
            }
        }
        for (int i = 0; i < role_array_size; i++) {
            if (!core_roles[i]) {
                char* role = role_array[i];
                fprintf(outputFile, "    ext_%s = nondet_bool();\n", role);
            }
        }

        fprintf(outputFile, "    __cs_pc = nondet_bv();\n");
        
    }

    static void
    generate_round(FILE *outputFile, int exclude_idx, int excluded_is_ca) {
        int label_idx = 0;
        fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_update_state(outputFile);


        fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (int i = 0; i < role_array_size; ++i) {
            if (core_roles[i] && roles_ca_counts[i] > 0) {
                int exclude = excluded_is_ca ? exclude_idx : -1;
                simulate_can_assigns_by_role(outputFile, i, label_idx++, exclude);
            }
        }

        fprintf(outputFile, "\n\n");

        fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
        for (int i = 0; i < role_array_size; ++i) {
            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
            if (core_roles[i] && roles_cr_counts[i] > 0) {
                int exclude = !excluded_is_ca ? exclude_idx : -1;
                simulate_can_revokes_by_role(outputFile, i, label_idx++, exclude);
            }
        }

        // Do not apply any translation and set skip to true
        fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
        fprintf(outputFile, "        skip = 1;");
        fprintf(outputFile, "    }");

        fprintf(outputFile, "\n\n");
    }

    static void
    generate_main(FILE* outputFile, int rule_id, int is_ca) {
        fprintf(outputFile, "int main(void) {\n\n");
        
        for (int i = 0; i < core_roles_size; ++i) {
            generate_round(outputFile, rule_id, is_ca);
        }
        generate_check(outputFile, rule_id, is_ca);
        fprintf(outputFile, "    return 0;\n");
        fprintf(outputFile, "}\n");
    }

    void
    transform_2_lazycseq_r6(char* inputFile, FILE *outputFile, int rule_index, int is_ca) {
        
        precompute_merge();
        allocate_core_role_array(rule_index, is_ca);

        //Generate header with common funtions and comments
        generate_header(outputFile, inputFile, rule_index, is_ca);
        
        //Declare global variables
        generate_globals(outputFile);

        //Generate Main funtion
        generate_main(outputFile, rule_index, is_ca);

        //fclose(outputFile);
        //free(newfile);
        deallocate_precomputated_values();
        free_core_role_array();
    }
}
