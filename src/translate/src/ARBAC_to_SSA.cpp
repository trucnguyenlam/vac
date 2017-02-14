#include "ARBACExact.h"
#include "SSA_Structs.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <memory>
//#include "dummy_esbmc.h"
    
using std::vector;

using std::shared_ptr;

static int threads_count;
static int use_tracks;

/*SHOULD BE REMOVED*/
static char* strbuf = (char*) calloc(1000, sizeof(char));

/*--- SSA VARIABLE INDEXES ---*/
/*--- VALUES ARE  ---*/
static Variable* *globals;
static Variable* *thread_assigneds;
static Variable* *program_counters;
static Variable* **locals;
static Variable* guard = NULL;
static Variable* nondet_bool = NULL;
static Variable* nondet_int = NULL;
static int steps = 0;
static vector<Stmt> out_stmts;

// #ifdef MERGE_RULES
static int *roles_ca_counts = NULL;
static int *roles_cr_counts = NULL;
static int **per_role_ca_indexes = NULL;
static int **per_role_cr_indexes = NULL;
static float ca_merge_ratio = 0;
static float cr_merge_ratio = 0;

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

// #endif

static void
free_stmts() {
    std::vector<Stmt>::iterator ite = out_stmts.begin();
    for (ite = out_stmts.begin(); ite != out_stmts.end(); ++ite) {        
        Stmt elem = *ite;
        freeStmt(elem);
    }
    out_stmts.clear();
}

static void
initialize_var_counters() {

    guard = 0;
    nondet_bool = 0;

    globals = (Variable**) calloc(sizeof(Variable*), role_array_size);
    for (int i = 0; i < role_array_size; ++i) {
        globals[i] = NULL;    
    }

    thread_assigneds = (Variable**) calloc(sizeof(Variable*), threads_count);
    for (int i = 0; i < threads_count; ++i) {
        thread_assigneds[i] = NULL;
    }

    program_counters = (Variable**) calloc(sizeof(Variable*), steps);
    for (int i = 0; i < steps; ++i) {
        program_counters[i] = NULL;    
    }

    locals = (Variable***) calloc(sizeof(Variable**), threads_count);
    for (int i = 0; i < threads_count; ++i) {
        locals[i] = (Variable**) calloc(sizeof(Variable*), role_array_size);
        for (int j = 0; j < role_array_size; ++j) {
            locals[i][j] = NULL;
        }
    }
}

static void
free_var_counters() {
    for (int i = 0; i < threads_count; ++i) {
        free(locals[i]);
    }
    free(locals);
    free(globals);
    free(thread_assigneds);
    free(program_counters);
}

static void
emit(Stmt stmt) {
    out_stmts.push_back(stmt);
}

static void
emitComment(const char* comment) {
    emit(createComment(comment));
}

static Variable*
createFrom(Variable* var, Expr value) {
    createVariable(var->name, var->idx + 1, value, var->no_simplify);
}

static void
generate_header(char *inputFile, int rounds) {
    time_t mytime;
    mytime = time(NULL);
    emitComment("*  generated by VAC [ 0000 / 0000 ]");
    emitComment("*");
    emitComment("*  instance version    {}");
    emitComment("*");
    sprintf(strbuf, "*  %s", ctime(&mytime));
    emitComment(strbuf);
    emitComment("*");
    emitComment("*  params:");
    emitComment("*    --format ssa");
    sprintf(strbuf, "*    --rounds %d", rounds);
    emitComment(strbuf);
    sprintf(strbuf, "*    --steps %d", steps);
    emitComment(strbuf);
    sprintf(strbuf, "*    %s", inputFile);
    emitComment(strbuf);
    emitComment("*");
    sprintf(strbuf, "*  users: %d", user_array_size);
    emitComment(strbuf);
    sprintf(strbuf, "*  roles: %d", role_array_size);
    emitComment(strbuf);
    sprintf(strbuf, "*  adminroles: %d", admin_role_array_index_size);
    emitComment(strbuf);
    sprintf(strbuf, "*  CA: %d", ca_array_size);
    emitComment(strbuf);
    sprintf(strbuf, "*  CR: %d", cr_array_size);
    emitComment(strbuf);
    sprintf(strbuf, "*  ThreadCount: %d", threads_count);
    emitComment(strbuf);
    emitComment("*");
    emitComment("");
    emitComment("");

    Expr zero = createConstantExpr(0);
    Variable* __ESBMC_rounding_mode = createVariable("__ESBMC_rounding_mode", 0, zero, 1);

    emit(generateAssignment(__ESBMC_rounding_mode));

    return;
}

static void
generate_PCs() {
    for (int i = 0; i < steps; i++) {
        sprintf(strbuf, "__cs_pc_%d", i);
        Variable* var = createVariable(strbuf, 0, createConstantExpr(0), true);
        emit(generateAssignment(var));
        program_counters[i] = var;
    }
}

static void 
generate_globals() {
     int i = 0, j = 0;
     int count = 0;
     emitComment("---------- INIT GLOBAL VARIABLES ---------");
     for (i = 0; i < admin_role_array_index_size; i++) {
         count = 0;
         // Check if an admin role is already in some user
         for (j = 0; j < user_config_array_size; j++) {
             if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i])) {
                 count = 1;
                 break;
             }
         }
         sprintf(strbuf, "glob_%s", role_array[admin_role_array_index[i]]);
         Variable* var = createVariable(strbuf, 0, createConstantExpr(count), 0);
         globals[admin_role_array_index[i]] = var;
         emit(generateAssignment(var));
     }
     emitComment("\n");
}

static void
generate_thread_locals(int thread_id) {
    sprintf(strbuf, "---------- THREAD %d LOCAL VARIABLES ---------", thread_id);
    emitComment(strbuf);
    for (int i = 0; i < role_array_size; i++) {
        sprintf(strbuf, "local_Thread_%d_loc_%s", thread_id, role_array[i]);
        if (use_tracks) {
            Variable* var = createVariable(strbuf, 0, createConstantExpr(0), 0);
            locals[thread_id][i] = var;
            emit(generateAssignment(var));
        }
        else {//locals[thread_id][i]++
            Variable* var = createVariable(strbuf, 0, createConstantExpr(belong_to(user_config_array[thread_id].array, user_config_array[thread_id].array_size, i)), 0);
            locals[thread_id][i] = var;
            emit(generateAssignment(var));
        }
    }
}

static void
generate_locals() {
    emitComment("---------- THREADS LOCAL VARIABLES ---------");
    for (int i = 0; i < threads_count; ++i) {
        generate_thread_locals(i);
    }
}

static void
init_PCs_guards_nondet() {
    generate_PCs();
    guard = createVariable("guard", 0, createConstantExpr(0), 1);
    nondet_bool = createVariable("nondet_bool", 0, createConstantExpr(0), 1);
    nondet_int = createVariable("nondet_int", 0, createConstantExpr(0), 1);
    emit(generateAssignment(guard));
    emit(generateAssignment(nondet_bool));
    emit(generateAssignment(nondet_int));
}

static void
generate_thread_assigned_locals() {
    emitComment("--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------");
    for (int i = 0; i < threads_count; ++i) {
        sprintf(strbuf, "thread_%d_assigned", i);
        Variable* var = createVariable(strbuf, 0, createConstantExpr(0), 0);
        thread_assigneds[i] = var;
        emit(generateAssignment(var));
    }
}

static void
thread_assignment_if(int thread_id, int user_id/*, Expr guard*/) {
    sprintf(strbuf, "-------THREAD %d TO USER %d-------", thread_id, user_id);
    emitComment(strbuf);

    Expr if_guard = createAndExpr(
        createEqExpr(exprFromVar(nondet_int), createConstantExpr(thread_id)), 
        createNotExpr(exprFromVar(thread_assigneds[thread_id])));
    Variable* n_guard = createFrom(guard, if_guard);
    emit(generateAssignment(n_guard));
    guard = n_guard;

    Expr ass_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), exprFromVar(thread_assigneds[thread_id]));

    Variable* assigned = createFrom(thread_assigneds[thread_id], ass_val);
    emit(generateAssignment(assigned));
    thread_assigneds[thread_id] = assigned;

    for (int j = 0; j < user_config_array[user_id].array_size; j++) {
        // if (belong_to(admin_role_array_index, admin_role_array_index_size, user_config_array[user_id].array[j])) {
        //     Expr glob_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), exprFromVar(globals[user_config_array[user_id].array[j]]));
        //     Variable* glob = createFrom(globals[user_config_array[user_id].array[j]], glob_val);
        //     emit(generateAssignment(glob));
        //     globals[user_config_array[user_id].array[j]] = glob;
        // }
        Expr loc_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), exprFromVar(locals[thread_id][user_config_array[user_id].array[j]]));
        Variable* loc = createFrom(locals[thread_id][user_config_array[user_id].array[j]], loc_val);
        emit(generateAssignment(loc));
        locals[thread_id][user_config_array[user_id].array[j]] = loc;
    }
}

static void
assign_thread_to_user(int user_id) {
    sprintf(strbuf, "--------------- CONFIGURATION OF %d ------------", user_id);
    emitComment(strbuf);
    Variable* nondet = createFrom(nondet_int, createNondetExpr(INT));
    emit(generateAssignment(nondet));
    nondet_int = nondet;

    for (int i = 0; i < threads_count; i++) {
        thread_assignment_if(i, user_id);
    }
}

static void
assign_threads() {
    for (int i = 0; i < threads_count; i++) {
        assign_thread_to_user(i);
    }

    Expr assume_body = exprFromVar(thread_assigneds[0]);
    for (int i = 1; i < threads_count; i++) {
        assume_body = createAndExpr(exprFromVar(thread_assigneds[i]), assume_body);
    }
    emit(createAssumption(assume_body));
}

static void
generate_updates(int thread_id) {
    emitComment("---- GLOBAL ROLE CONSISTENCY UPDATE ----");
    for (int i = 0; i < admin_role_array_index_size; i++) {
        for (int j = 0; j < cr_array_size; j++) {
            if (admin_role_array_index[i] == cr_array[j].target_role_index) {
                int r_index = admin_role_array_index[i];
                char *role = role_array[r_index];
                Expr value = createOrExpr(exprFromVar(globals[r_index]), exprFromVar(locals[thread_id][r_index]));
                Variable* n_glob = createFrom(globals[r_index], value);
                emit(generateAssignment(n_glob));
                globals[r_index] = n_glob;
                break;
            }
        }
    }
    // glob_Author_d = glob_Author_d || __cs_local_Thread_user3_loc_Author_d;
}

static Expr
generate_CA_cond(int thread_id, int ca_index) {
    int j;
    Expr cond = NULL;
    // Admin role must be available
    Expr admin_cond = exprFromVar(globals[ca_array[ca_index].admin_role_index]);
    cond = admin_cond;

    // Precondition must be satisfied
    if (ca_array[ca_index].type == 0) {     // Has precondition
        if (ca_array[ca_index].positive_role_array_size > 0) {
            int* ca_array_p = ca_array[ca_index].positive_role_array;
            Expr ca_cond = exprFromVar(locals[thread_id][ca_array_p[0]]);
            for (j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                ca_cond = createAndExpr(ca_cond, exprFromVar(locals[thread_id][ca_array_p[j]]));
            }
            cond = createAndExpr(cond, ca_cond);
        }
        if (ca_array[ca_index].negative_role_array_size > 0) {
            int* ca_array_n = ca_array[ca_index].negative_role_array;
            Expr cr_cond = createNotExpr(exprFromVar(locals[thread_id][ca_array_n[0]]));
            for (j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                cr_cond = createAndExpr(cr_cond, createNotExpr(exprFromVar(locals[thread_id][ca_array_n[j]])));
            }
            cond = createAndExpr(cond, cr_cond);
        }
    }
    // Optional this user is not in this target role yet
    Expr not_ass = createNotExpr(exprFromVar(locals[thread_id][ca_array[ca_index].target_role_index]));
    cond = createAndExpr(cond, not_ass);
    return cond;
}

static Expr
generate_CR_cond(int thread_id, int cr_index) {
    int i;
    Expr cond = NULL;
    // Admin role must be available
    Expr admin_cond = exprFromVar(globals[cr_array[cr_index].admin_role_index]);
    // Optional this user is in this target role yet
    Expr not_ass = exprFromVar(locals[thread_id][cr_array[cr_index].target_role_index]);
    cond = admin_cond;
    cond = createAndExpr(admin_cond, not_ass);
    return cond;
}

static Expr
generate_PC_cond(int rule_id){
    Expr cond = createEqExpr(exprFromVar(program_counters[0]), createConstantExpr(rule_id));
    for (int i = 1; i < steps; i++) {
        cond = createOrExpr(cond, createEqExpr(exprFromVar(program_counters[i]), createConstantExpr(rule_id)));
    }
    return cond;
}

// Print the comment of a CA rule
static void
emit_ca_comment(int ca_rule) {
	int i;
	int has_head = 0;
    char* out = strbuf;

    sprintf(strbuf, "------------------ CAN_ASSIGN RULE NUMBER %d -----------------", ca_rule);
	emitComment(strbuf);

	if (ca_array[ca_rule].type == 0) {
		sprintf(out, "  <%s,", role_array[ca_array[ca_rule].admin_role_index]);
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++) {
			if (has_head) {
				sprintf(out, "%s&%s", out, role_array[ca_array[ca_rule].positive_role_array[i]]);
			}
			else {
				sprintf(out, "%s%s", out, role_array[ca_array[ca_rule].positive_role_array[i]]);
				has_head = 1;
			}
		}
		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++) {
			if (has_head) {
				sprintf(out, "%s&-%s", out, role_array[ca_array[ca_rule].negative_role_array[i]]);
			}
			else {
				sprintf(out, "%s-%s", out, role_array[ca_array[ca_rule].negative_role_array[i]]);
				has_head = 1;
			}
		}
		sprintf(out, "%s,%s>  ", out, role_array[ca_array[ca_rule].target_role_index]);
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1) {
		sprintf(out, "  <%s,TRUE,%s>  ", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
	else if (ca_array[ca_rule].type == 2) {
		sprintf(out, "  <%s,NEW,%s>  ", role_array[ca_array[ca_rule].admin_role_index], role_array[ca_array[ca_rule].target_role_index]);
	}
    emitComment(out);
	emitComment("------------------------------------------------------------------");
}

// Print the comment of a CR rule
static void
emit_cr_comment(int cr_rule) {
    char* out = strbuf;
	sprintf(out, "------------------- CAN_REVOKE RULE NUMBER %d ---------------------", cr_rule);
    emitComment(out);
	sprintf(out, "  <%s,%s>  ", role_array[cr_array[cr_rule].admin_role_index], role_array[cr_array[cr_rule].target_role_index]);
    emitComment(out);
	emitComment("------------------------------------------------------------------");
}

static void
simulate_can_assigns_by_role(int thread_id, int target_role_index, int rule_id) {
    // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
    int i = 0;
    Expr pc_cond = NULL, ca_cond = NULL, all_cond = NULL;
    //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    sprintf(strbuf, "--- ASSIGNMENT RULES FOR ROLE %s ---", role_array[target_role_index]);
    emitComment(strbuf);

    if (roles_ca_counts[target_role_index] < 1) {
        sprintf(strbuf, "--- ROLE %s IS NOT ASSIGNABLE... SHOULD CRASH ---", role_array[target_role_index]);
        emitComment(strbuf);
        fprintf(stderr, "%s", strbuf);
        return;
    }

    pc_cond = generate_PC_cond(rule_id);

    emit_ca_comment(per_role_ca_indexes[target_role_index][0]);
    ca_cond = generate_CA_cond(thread_id, per_role_ca_indexes[target_role_index][0]);

    for (i = 1; i < roles_ca_counts[target_role_index]; ++i) {
        int ca_idx = per_role_ca_indexes[target_role_index][i];
        Expr ith_cond = generate_CA_cond(thread_id, ca_idx);
        emit_ca_comment(ca_idx);
        ca_cond = createOrExpr(ca_cond, ith_cond);
    }

    all_cond = createAndExpr(pc_cond, ca_cond);
    Variable* ca_guard = createFrom(guard, all_cond);
    emit(generateAssignment(ca_guard));
    guard = ca_guard;

    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        Expr ngval = createCondExpr(exprFromVar(ca_guard), createConstantExpr(1), exprFromVar(globals[target_role_index]));
        Variable* nglob = createFrom(globals[target_role_index], ngval);
        Expr nlval = createCondExpr(exprFromVar(ca_guard), createConstantExpr(1), exprFromVar(locals[thread_id][target_role_index]));
        Variable* nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emit(generateAssignment(nglob));
        emit(generateAssignment(nloc));
        globals[target_role_index] = nglob;
        locals[thread_id][target_role_index] = nloc;
    }
    else {
        Expr nlval = createCondExpr(exprFromVar(ca_guard), createConstantExpr(1), exprFromVar(locals[thread_id][target_role_index]));
        Variable* nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emit(generateAssignment(nloc));
        locals[thread_id][target_role_index] = nloc;
    }
}

static void
simulate_can_revokes_by_role(int thread_id, int target_role_index, int rule_id) {
    // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
    int i = 0;
    Expr pc_cond = NULL, cr_cond = NULL, all_cond = NULL;
    //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    sprintf(strbuf, "--- REVOKE RULES FOR ROLE %s ---", role_array[target_role_index]);
    emitComment(strbuf);

    if (roles_cr_counts[target_role_index] < 1) {
        sprintf(strbuf, "--- ROLE %s IS NOT REVOKABLE... SHOULD CRASH ---", role_array[target_role_index]);
        emitComment(strbuf);
        fprintf(stderr, "%s", strbuf);
        return;
    }

    pc_cond = generate_PC_cond(rule_id);

    emit_cr_comment(per_role_cr_indexes[target_role_index][0]);
    cr_cond = generate_CR_cond(thread_id, per_role_cr_indexes[target_role_index][0]);

    for (i = 1; i < roles_cr_counts[target_role_index]; ++i) {
        int cr_idx = per_role_cr_indexes[target_role_index][i];
        Expr ith_cond = generate_CR_cond(thread_id, cr_idx);
        emit_cr_comment(cr_idx);
        cr_cond = createOrExpr(cr_cond, ith_cond);
    }

    all_cond = createAndExpr(pc_cond, cr_cond);
    Variable* cr_guard = createFrom(guard, all_cond);
    emit(generateAssignment(cr_guard));
    guard = cr_guard;

    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        Expr ngval = createCondExpr(exprFromVar(cr_guard), createConstantExpr(0), exprFromVar(globals[target_role_index]));
        Variable* nglob = createFrom(globals[target_role_index], ngval);
        Expr nlval = createCondExpr(exprFromVar(cr_guard), createConstantExpr(0), exprFromVar(locals[thread_id][target_role_index]));
        Variable* nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emit(generateAssignment(nglob));
        emit(generateAssignment(nloc));
        globals[target_role_index] = nglob;
        locals[thread_id][target_role_index] = nloc;
    }
    else {
        Expr nlval = createCondExpr(exprFromVar(cr_guard), createConstantExpr(0), exprFromVar(locals[thread_id][target_role_index]));
        Variable* nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emit(generateAssignment(nloc));
        locals[thread_id][target_role_index] = nloc;
    }
}

static void
generate_check(int thread_id) {
    //TODO: Could be optimized here
    sprintf(strbuf, "---------------ERROR CHECK THREAD %d ROLE %s------------", thread_id, role_array[goal_role_index]); 
    emitComment(strbuf);
    Expr term_cond = exprFromVar(locals[thread_id][goal_role_index]);
    Variable* term_guard = createFrom(guard, term_cond);
    emit(generateAssignment(term_guard));
    guard = term_guard;
    Expr assertion_cond = createCondExpr(exprFromVar(term_guard), createConstantExpr(0), createConstantExpr(1));
    emit(createAssertion(assertion_cond));
}

static void
simulate_thread(int thread_id) {
    sprintf(strbuf, "--------------- APPLICATION OF THREAD %d ------------", thread_id); 
    emitComment(strbuf);
    
    generate_updates(thread_id);

    int label_idx = 0;
    emitComment("---------- IDLE ROUND REMOVED SINCE PC MAY BE GREATER THAN PC_MAX ---------");

    int i;
    emitComment("---------- CAN ASSIGN SIMULATION ---------");
    emitComment("---------- MERGED PER ROLE ---------");
    for (int i = 0; i < role_array_size; ++i) {
        // printf("CA idx: %d, role: %s: count: %d\n", i, role_array[i], roles_ca_counts[i]);
        if (roles_ca_counts[i] > 0) {
            simulate_can_assigns_by_role(thread_id, i, label_idx++);
        }
    }

    emitComment("---------- CAN REVOKE SIMULATION ---------");
    emitComment("---------- MERGED PER ROLE ---------");
    for (int i = 0; i < role_array_size; ++i) {
        // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
        if (roles_cr_counts[i] > 0) {
            simulate_can_revokes_by_role(thread_id, i, label_idx++);
        }
    }

    generate_check(thread_id);
}

static void
assign_PCs() {
    for (int step = 0; step < steps; step++) {
        Variable* nondet_res = createFrom(nondet_int, createNondetExpr(INT));
        emit(generateAssignment(nondet_res));
        nondet_int = nondet_res;
        Variable* npc_n = createFrom(program_counters[step], exprFromVar(nondet_res));
        emit(generateAssignment(npc_n));
        program_counters[step] = npc_n;
    }
}

static void
simulate_threads() {
    for (int i = 0; i < threads_count; i++) {
        assign_PCs();
        simulate_thread(i);
    }
}

static void
generate_main(int rounds) {
    for (int r = 0; r < rounds; r++) {
        sprintf(strbuf, "--------------- SIMULATION OF ROUND %d ------------", r); 
        emitComment(strbuf); 
        simulate_threads();
    }
}

static void
write_to_file(FILE* outputFile) {
    unsigned long i = 0;
    vector<Stmt>::iterator ite = out_stmts.begin();
    for (ite = out_stmts.begin(); ite != out_stmts.end(); ++ite) {
        Stmt elem = *ite;
        char* str = printStmt(elem);
        fprintf(outputFile, "%s\n", str);
        free(str);
        if (elem->type != COMMENT) {
            i++;
        }
    }
    fprintf(stderr, "------------ GENERATED %lu STATEMENTS ------------\n", i);
}



static void
print_var_decls(FILE* outputFile) {
    int i, t, c;

    fprintf(outputFile, "unsigned int nondet_int();\n");
    fprintf(outputFile, "_Bool nondet_bool();\n");

    fprintf(outputFile, "_Bool __ESBMC_rounding_mode_0");
    
    for (i = 0; i < threads_count; i++) {
        int to = thread_assigneds[i]->idx;
        for (c = 0; c <= to; c++) {
            thread_assigneds[i]->idx = c;
            char* str = printVariable(thread_assigneds[i]);
            fprintf(outputFile, ", %s", str);
            free(str);
        }
    }

    for (int  i = 0; i < role_array_size; i++) {
        if (globals[i] != NULL) {
            int to = globals[i]->idx;
            for (c = 0; c <= to; c++) {
                globals[i]->idx = c;
                char* str = printVariable(globals[i]);
                fprintf(outputFile, ", %s", str);
                free(str);
            }
        }
    }

    for (t = 0; t < threads_count; t++) {
        for (int  i = 0; i < role_array_size; i++) {
            int to = locals[t][i]->idx;
            for (c = 0; c <= to; c++) {
                locals[t][i]->idx = c;
                char* str = printVariable(locals[t][i]);
                fprintf(outputFile, ", %s", str);
                free(str);
            }
        }
    }

    {
        int to = guard->idx;
        for (c = 0; c <= to; c++) {
            guard->idx = c;
            char* str = printVariable(guard);
            fprintf(outputFile, ", %s", str);
            free(str);
        }
    }

    {
        int to = nondet_bool->idx;
        for (c = 0; c <= to; c++) {
            nondet_bool->idx = c;
            char* str = printVariable(nondet_bool);
            fprintf(outputFile, ", %s", str);
            free(str);
        }
    }
    fprintf(outputFile, ";\n");

    fprintf(outputFile, "int dummy_int");

    for (i = 0; i < steps; i++) {
        int to = program_counters[i]->idx;
        for (c = 0; c <= to; c++) {
            program_counters[i]->idx = c;
            char* str = printVariable(program_counters[i]);
            fprintf(outputFile, ", %s", str);
            free(str);
        }
    }

    {
        int to = nondet_int->idx;
        for (c = 0; c <= to; c++) {
            nondet_int->idx = c;
            char* str = printVariable(nondet_int);
            fprintf(outputFile, ", %s", str);
            free(str);
        }
    }
    fprintf(outputFile, ";\n");
}

static void
generate_program(char *inputFile, FILE *outputFile, int rounds) {
    initialize_var_counters();

    // TODO: this should be merged in initialize_var_counters to avoid NULL in counters
    // TODO: Usare shared pointer per tutto o trackare le stronzate condivise (mai ricorsive ;) 
    init_PCs_guards_nondet();
    //Generate header with comments
    generate_header(inputFile, rounds);

        
    generate_globals();
    generate_locals();

    generate_thread_assigned_locals();
    assign_threads();

    generate_main(rounds);

    emitComment(strbuf);

    print_var_decls(outputFile);

    fprintf(outputFile, "int main() {\n");

    write_to_file(outputFile);

    fprintf(outputFile, "return 0;\n}\n");
}

void
transform_2_ssa(char *inputFile, FILE *outputFile, int rounds, int _steps, int wanted_threads_count) {
    steps = _steps;
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

    precompute_merge();

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
    
    generate_program(inputFile, outputFile, rounds);

    
    std::cout << "Press enter to continue ..."; 
    std::cin.get();
    exit(0);
    
    free(strbuf);
    deallocate_precomputated_values();

    free_stmts();
    free_data();
    free_precise_temp_data();
    free_var_counters();

}

