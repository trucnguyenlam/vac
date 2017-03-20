#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream> 
#include <memory>

#include <yices.h>

#include <chrono>
//#include "dummy_esbmc.h"

namespace SSA {

using std::vector;
using std::shared_ptr;
using std::stringstream;
using std::string;

static int threads_count;
static int use_tracks;

// /*SHOULD BE REMOVED*/
// static char* strbuf = (char*) calloc(1000, sizeof(char));
static stringstream fmt;

static void clean_fmt() {
    fmt.str(std::string());
}

context_t* yices_ctx;

typedef 
    struct _variable {
        term_t yices_var;
        term_t yices_val;
        int bv_size;
        string name;
        int idx;
    } variable;

static variable dummy_var;

/*--- SMT VARIABLE INDEXES ---*/
/*--- VALUES ARE  ---*/
static variable* globals;
static variable* thread_assigneds;
static variable* program_counters;
static variable** locals;
static variable guard;
static variable nondet_bool;
static variable nondet_int;
static int steps = 0;
static vector<term_t> assertions;
// static vector<SSA::Stmt> out_stmts;
// static SSAProgram ssa_prog;
static term_t zero = -1;
static term_t one = -1;

// #ifdef MERGE_RULES
static int *roles_ca_counts = nullptr;
static int *roles_cr_counts = nullptr;
static int **per_role_ca_indexes = nullptr;
static int **per_role_cr_indexes = nullptr;
static int pc_size = -1;
static float ca_merge_ratio = 0;
static float cr_merge_ratio = 0;



// #endif

static int NumBits(int pc) {
    int i = 1, bit = 0;

    if (pc <= 2 ) return 1;

    while (pc >= i) {
        i = i * 2;
        bit++;
    }

    return (bit);
}

static int
get_pc_count() {
    int n = 0;
    for (int i = 0; i < role_array_size; ++i) {
        if (roles_ca_counts[i] > 0)
            n++;
        if (roles_cr_counts[i] > 0)
            n++;
    }
    return NumBits(n + 1);
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

    pc_size = get_pc_count() + 1;

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

static void
initialize_var_counters() {

    guard = dummy_var;
    nondet_bool = dummy_var;

    globals = new variable[role_array_size];
    for (int i = 0; i < role_array_size; ++i) {
        globals[i] = dummy_var;
    }

    thread_assigneds = new variable[threads_count];
    for (int i = 0; i < threads_count; ++i) {
        thread_assigneds[i] = dummy_var;
    }

    program_counters = new variable[steps];
    for (int i = 0; i < steps; ++i) {
        program_counters[i] = dummy_var;    
    }

    locals = new variable*[threads_count];
    for (int i = 0; i < threads_count; ++i) {
        locals[i] = new variable[role_array_size];
        for (int j = 0; j < role_array_size; ++j) {
            locals[i][j] = dummy_var;
        }
    }
}

static void
free_var_counters() {
    for (int i = 0; i < threads_count; ++i) {
        delete[] locals[i];
    }
    delete[] locals;
    delete[] globals;
    delete[] thread_assigneds;
    delete[] program_counters;
}

static vector<term_t> assignments;

static void
emitAssignment(variable var) {
    if (var.yices_val == -2) {
        // fprintf(stderr, "Warning, variable %s%d is assumed nondeterministic\n", var.name.c_str(), var.idx);
        return;
    }
    if (var.yices_val == -1) {
        fprintf(stderr, "Warning, variable %s%d is broken\n", var.name.c_str(), var.idx);
        return;
    }
    term_t tmp = yices_eq(var.yices_var, var.yices_val);
    assignments.push_back(tmp);
    // yices_assert_formula(yices_ctx, tmp);
}

static void
emitComment(const string comment) {
    // ssa_prog.addComment(createComment(comment));
}

static void
emitAssertion(term_t assertion) {
    assertions.push_back(assertion);
    // yices_assert_formula(yices_ctx, assertion);
}

static void
emitAssumption(term_t assumption) {
    yices_assert_formula(yices_ctx, assumption);
}

static variable
create_variable(const string name, int idx, term_t value, int bv_size) {
    variable ret;
    ret.name = name;
    ret.idx = idx;
    ret.bv_size = bv_size;

    term_t type = yices_bool_type();
    if (bv_size > 1) {
        type = yices_bv_type(bv_size);
    }
    ret.yices_var = yices_new_uninterpreted_term(type);
    ret.yices_val = value;
    string yices_name = (ret.name + std::to_string(ret.idx));
    // yices_set_term_name(ret.yices_var, yices_name.c_str());

    return ret;
}

static variable
createFrom(variable var, term_t nvalue) {
    variable nvar = create_variable(var.name, var.idx + 1, nvalue, var.bv_size);
    return nvar;
}

static term_t
create_constant(int value, int bv_size) {
    term_t ret;

    if (bv_size > 1) {
        ret = yices_bvconst_uint32(bv_size, value);
    }
    else if (value) {
        ret = one;
    }
    else {
        ret = zero;
    }

    return ret;
}

static void
generate_header(char *inputFile, int rounds) {
    time_t mytime;
    mytime = time(NULL);
    string eol = "\n";
    clean_fmt();
    fmt << eol;
    fmt << "*  generated by VAC [ 0000 / 0000 ]" << eol;
    fmt << "*" << eol;
    fmt << "*  instance version    {}" << eol;
    fmt << "*" << eol;
    fmt << "*  " << ctime(&mytime);
    fmt << "*" << eol;
    fmt << "*  params:" << eol;
    fmt << "*    --format ssa" << eol;
    fmt << "*    --rounds " << rounds << eol;
    fmt << "*    --steps " << steps << eol;
    fmt << "*   " << inputFile << eol;
    fmt << "*" << eol;
    fmt << "*  users: " << user_array_size << eol;
    fmt << "*  roles: " << role_array_size << eol;
    fmt << "*  adminroles: " << admin_role_array_index_size << eol;
    fmt << "*  CA: " << ca_array_size << eol;
    fmt << "*  CR: " << cr_array_size << eol;
    fmt << "*  ThreadCount: " << threads_count << eol;
    emitComment(fmt.str());
    emitComment("");
    emitComment("");

    // Variablep __ESBMC_rounding_mode = createVariablep("__ESBMC_rounding_mode", 0, zero, 1);

    // emitAssignment(__ESBMC_rounding_mode);

    return;
}

static variable
generate_empty_variable(const string name, int idx, int bv_size) {
    variable ret;
    ret.name = name;
    ret.idx = idx;
    ret.bv_size = bv_size;
    return ret;
}

static void
generate_zero_one(){
    zero = yices_false();
    one = yices_true();
}

static void
generate_PCs() {
    for (int i = 0; i < steps; i++) {
        clean_fmt();
        fmt << "__cs_pc_" << i;
        variable var = generate_empty_variable(fmt.str(), -1, pc_size);
        // emitAssignment(var);
        program_counters[i] = var;
    }
}

static void
init_PCs_guards_nondet() {
    generate_PCs();
    guard = generate_empty_variable("guard", -1, 1);
    nondet_bool = generate_empty_variable("nondet_bool", -2, 1);
    nondet_int = generate_empty_variable("nondet_int", -2, pc_size);
    // emitAssignment(guard);
    // emitAssignment(nondet_bool);
    // emitAssignment(nondet_int);
}

static void 
generate_globals() {
     int i = 0, j = 0;
     int count = 0;
     emitComment("---------- INIT GLOBAL VARIABLES ---------");
     for (i = 0; i < admin_role_array_index_size; i++) {
         count = 0;
         // Check if an admin role is already assigned to some user
         for (j = 0; j < user_config_array_size; j++) {
             if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i])) {
                 count = 1;
                 break;
             }
         }
         clean_fmt();
         fmt << "glob_" << role_array[admin_role_array_index[i]];
         variable var = create_variable(fmt.str(), 0, count ? one : zero, 1);
         globals[admin_role_array_index[i]] = var;
         emitAssignment(var);
     }
     emitComment("");
}

static void
generate_thread_locals(int thread_id) {
    clean_fmt();
    fmt << "---------- THREAD " << thread_id << " LOCAL VARIABLES ---------";
    emitComment(fmt.str());
    for (int i = 0; i < role_array_size; i++) {
        clean_fmt();
        fmt << "local_Thread_" << thread_id << "_loc_" << role_array[i];
        if (use_tracks) {
            variable var = create_variable(fmt.str(), 0, zero, 1);
            locals[thread_id][i] = var;
            emitAssignment(var);
        }
        else {//locals[thread_id][i]++
            int contains = belong_to(user_config_array[thread_id].array, user_config_array[thread_id].array_size, i);
            variable var = create_variable(fmt.str(), 0, contains ? one : zero, 1);
            locals[thread_id][i] = var;
            emitAssignment(var);
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
generate_thread_assigned_locals() {
    emitComment("--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------");
    for (int i = 0; i < threads_count; ++i) {
        clean_fmt();
        fmt << "thread_" << i << "_assigned";
        variable var = create_variable(fmt.str(), 0, zero, 1);
        thread_assigneds[i] = var;
        emitAssignment(var);
    }
}

static void
thread_assignment_if(int thread_id, int user_id) {
    clean_fmt();
    fmt << "-------THREAD " << thread_id << " TO USER " << user_id << " (" << user_array[user_id] << ")-------";
    emitComment(fmt.str());

    term_t con_e = create_constant(thread_id, pc_size);
    term_t eq_e = yices_eq(nondet_int.yices_var, con_e);
    term_t not_e = yices_not(thread_assigneds[thread_id].yices_var);
    term_t if_guard = yices_and2(
        eq_e , 
        not_e );
    variable n_guard = createFrom(guard, if_guard);
    emitAssignment(n_guard);
    guard = n_guard;

    term_t ass_val = yices_ite(guard.yices_var, one, thread_assigneds[thread_id].yices_var);

    variable assigned = createFrom(thread_assigneds[thread_id], ass_val);
    emitAssignment(assigned);
    thread_assigneds[thread_id] = assigned;

    for (int j = 0; j < user_config_array[user_id].array_size; j++) {
        // if (belong_to(admin_role_array_index, admin_role_array_index_size, user_config_array[user_id].array[j])) {
        //     Expr glob_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), globals[user_config_array[user_id].array[j]]));
        //     Variablep glob = createFrom(globals[user_config_array[user_id].array[j]], glob_val);
        //     emit(generateAssignment(glob));
        //     globals[user_config_array[user_id].array[j]] = glob;
        // }
        term_t loc_val = yices_ite(guard.yices_var, one, locals[thread_id][user_config_array[user_id].array[j]].yices_var);
        variable loc = createFrom(locals[thread_id][user_config_array[user_id].array[j]], loc_val);
        emitAssignment(loc);
        locals[thread_id][user_config_array[user_id].array[j]] = loc;
    }
}

static void
assign_thread_to_user(int user_id) {
    clean_fmt();
    fmt << "--------------- CONFIGURATION OF USER " << user_id << " (" << user_array[user_id] << ") ------------";
    emitComment(fmt.str());
    variable nondet = createFrom(nondet_int, -2);
    emitAssignment(nondet);
    nondet_int = nondet;

    for (int i = 0; i < threads_count; i++) {
        thread_assignment_if(i, user_id);
    }
}

static void
assign_threads() {
    for (int i = 0; i < user_config_array_size; i++) {
        assign_thread_to_user(i);
    }

    term_t assume_body = thread_assigneds[0].yices_var;
    for (int i = 1; i < threads_count; i++) {
        assume_body = yices_and2(thread_assigneds[i].yices_var, assume_body);
    }
    emitAssumption(assume_body);
}

static void
generate_updates(int thread_id) {
    emitComment("---- GLOBAL ROLE CONSISTENCY UPDATE ----");
    for (int i = 0; i < admin_role_array_index_size; i++) {
        for (int j = 0; j < cr_array_size; j++) {
            if (admin_role_array_index[i] == cr_array[j].target_role_index) {
                int r_index = admin_role_array_index[i];
                term_t value = yices_or2(globals[r_index].yices_var, locals[thread_id][r_index].yices_var);
                variable n_glob = createFrom(globals[r_index], value);
                emitAssignment(n_glob);
                globals[r_index] = n_glob;
                break;
            }
        }
    }
    // glob_Author_d = glob_Author_d || __cs_local_Thread_user3_loc_Author_d;
}

static term_t
generate_CA_cond(int thread_id, int ca_index) {
    int j;
    term_t cond = -1;
    // Admin role must be available
    term_t admin_cond = globals[ca_array[ca_index].admin_role_index].yices_var;
    cond = admin_cond;

    // Precondition must be satisfied
    if (ca_array[ca_index].type == 0) {     // Has precondition
        if (ca_array[ca_index].positive_role_array_size > 0) {
            int* ca_array_p = ca_array[ca_index].positive_role_array;
            term_t ca_cond = locals[thread_id][ca_array_p[0]].yices_var;
            for (j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                ca_cond = yices_and2(ca_cond, locals[thread_id][ca_array_p[j]].yices_var);
            }
            cond = yices_and2(cond, ca_cond);
        }
        if (ca_array[ca_index].negative_role_array_size > 0) {
            int* ca_array_n = ca_array[ca_index].negative_role_array;
            term_t cr_cond = yices_not(locals[thread_id][ca_array_n[0]].yices_var);
            for (j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                cr_cond = yices_and2(cr_cond, yices_not(locals[thread_id][ca_array_n[j]].yices_var));
            }
            cond = yices_and2(cond, cr_cond);
        }
    }
    // Optional this user is not in this target role yet
    term_t not_ass = yices_not(locals[thread_id][ca_array[ca_index].target_role_index].yices_var);
    cond = yices_and2(cond, not_ass);
    return cond;
}

static term_t
generate_CR_cond(int thread_id, int cr_index) {
    int i;
    term_t cond = -1;
    // Admin role must be available
    term_t admin_cond = globals[cr_array[cr_index].admin_role_index].yices_var;
    // Optional this user is in this target role yet
    term_t not_ass = locals[thread_id][cr_array[cr_index].target_role_index].yices_var;
    cond = admin_cond;
    cond = yices_and2(admin_cond, not_ass);
    return cond;
}

static term_t
generate_PC_cond(int rule_id) {
    term_t cond = yices_eq(program_counters[0].yices_var, create_constant(rule_id, pc_size));
    for (int i = 1; i < steps; i++) {
        cond = yices_or2(cond, yices_eq(program_counters[i].yices_var, create_constant(rule_id, pc_size)));
    }
    return cond;
}

// Print the comment of a CA rule
static void
emit_ca_comment(int ca_rule) {
	int i;
	int has_head = 0;
    clean_fmt();

    fmt << "------------------ CAN_ASSIGN RULE NUMBER " << ca_rule << " -----------------";
	emitComment(fmt.str());

    clean_fmt();
	if (ca_array[ca_rule].type == 0) {
		fmt << "  <" << role_array[ca_array[ca_rule].admin_role_index] << ",";
		for (i = 0; i < ca_array[ca_rule].positive_role_array_size; i++) {
			if (has_head) {
				fmt << "&" << role_array[ca_array[ca_rule].positive_role_array[i]];
			}
			else {
				fmt << role_array[ca_array[ca_rule].positive_role_array[i]];
				has_head = 1;
			}
		}
		for (i = 0; i < ca_array[ca_rule].negative_role_array_size; i++) {
			if (has_head) {
				fmt << "&-" << role_array[ca_array[ca_rule].negative_role_array[i]];
			}
			else {
				fmt << "-" << role_array[ca_array[ca_rule].negative_role_array[i]];
				has_head = 1;
			}
		}
		fmt << "," << role_array[ca_array[ca_rule].target_role_index] << ">  ";
		has_head = 0;
	}
	else if (ca_array[ca_rule].type == 1) {
		fmt << "  <" << role_array[ca_array[ca_rule].admin_role_index] << ",TRUE," << role_array[ca_array[ca_rule].target_role_index] << ">  ";
	}
	else if (ca_array[ca_rule].type == 2) {
        fmt << "  <" << role_array[ca_array[ca_rule].admin_role_index] << ",NEW," << role_array[ca_array[ca_rule].target_role_index] << ">  ";
	}
    emitComment(fmt.str());
	emitComment("------------------------------------------------------------------");
}

// Print the comment of a CR rule
static void
emit_cr_comment(int cr_rule) {
    clean_fmt();
	fmt << "------------------- CAN_REVOKE RULE NUMBER " << cr_rule << " ---------------------";
    emitComment(fmt.str());
    clean_fmt();
	fmt << "  <" << role_array[cr_array[cr_rule].admin_role_index] << "," << role_array[cr_array[cr_rule].target_role_index] << ">  ";
    emitComment(fmt.str());
	emitComment("------------------------------------------------------------------");
}

static void
simulate_can_assigns_by_role(int thread_id, int target_role_index, int rule_id) {
    // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
    int i = 0;
    term_t pc_cond = -1, ca_cond = -1, all_cond = -1;
    //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    clean_fmt();
    fmt << "--- ASSIGNMENT RULES FOR ROLE " << role_array[target_role_index] << " ---";
    emitComment(fmt.str());

    if (roles_ca_counts[target_role_index] < 1) {
        clean_fmt();
        fmt << "--- ROLE " << role_array[target_role_index] << " IS NOT ASSIGNABLE... SHOULD CRASH ---";
        string msg = fmt.str();
        emitComment(msg);
        fprintf(stderr, "%s", msg.c_str());
        return;
    }

    pc_cond = generate_PC_cond(rule_id);

    emit_ca_comment(per_role_ca_indexes[target_role_index][0]);
    ca_cond = generate_CA_cond(thread_id, per_role_ca_indexes[target_role_index][0]);

    for (i = 1; i < roles_ca_counts[target_role_index]; ++i) {
        int ca_idx = per_role_ca_indexes[target_role_index][i];
        term_t ith_cond = generate_CA_cond(thread_id, ca_idx);
        emit_ca_comment(ca_idx);
        ca_cond = yices_or2(ca_cond, ith_cond);
    }

    all_cond = yices_and2(pc_cond, ca_cond);
    variable ca_guard = createFrom(guard, all_cond);
    emitAssignment(ca_guard);
    guard = ca_guard;

    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        term_t ngval = yices_ite(ca_guard.yices_var, one, globals[target_role_index].yices_var);
        variable nglob = createFrom(globals[target_role_index], ngval);
        term_t nlval = yices_ite(ca_guard.yices_var, one, locals[thread_id][target_role_index].yices_var);
        variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emitAssignment(nglob);
        emitAssignment(nloc);
        globals[target_role_index] = nglob;
        locals[thread_id][target_role_index] = nloc;
    }
    else {
        term_t nlval = yices_ite(ca_guard.yices_var, one, locals[thread_id][target_role_index].yices_var);
        variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emitAssignment(nloc);
        locals[thread_id][target_role_index] = nloc;
    }
}

static void
simulate_can_revokes_by_role(int thread_id, int target_role_index, int rule_id) {
    // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
    int i = 0;
    term_t pc_cond = -1, cr_cond = -1, all_cond = -1;
    //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
    clean_fmt();
    fmt << "--- REVOKE RULES FOR ROLE " << role_array[target_role_index] << " ---";
    emitComment(fmt.str());

    if (roles_cr_counts[target_role_index] < 1) {
        clean_fmt();
        fmt << "--- ROLE " << role_array[target_role_index] << " IS NOT REVOKABLE... SHOULD CRASH ---";
        string msg = fmt.str();
        emitComment(msg);
        fprintf(stderr, "%s", msg.c_str());
        return;
    }

    pc_cond = generate_PC_cond(rule_id);

    emit_cr_comment(per_role_cr_indexes[target_role_index][0]);
    cr_cond = generate_CR_cond(thread_id, per_role_cr_indexes[target_role_index][0]);

    for (i = 1; i < roles_cr_counts[target_role_index]; ++i) {
        int cr_idx = per_role_cr_indexes[target_role_index][i];
        term_t ith_cond = generate_CR_cond(thread_id, cr_idx);
        emit_cr_comment(cr_idx);
        cr_cond = yices_or2(cr_cond, ith_cond);
    }

    all_cond = yices_and2(pc_cond, cr_cond);
    variable cr_guard = createFrom(guard, all_cond);
    emitAssignment(cr_guard);
    guard = cr_guard;

    if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
        term_t ngval = yices_ite(cr_guard.yices_var, zero, globals[target_role_index].yices_var);
        variable nglob = createFrom(globals[target_role_index], ngval);
        term_t nlval = yices_ite(cr_guard.yices_var, zero, locals[thread_id][target_role_index].yices_var);
        variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emitAssignment(nglob);
        emitAssignment(nloc);
        globals[target_role_index] = nglob;
        locals[thread_id][target_role_index] = nloc;
    }
    else {
        term_t nlval = yices_ite(cr_guard.yices_var, zero, locals[thread_id][target_role_index].yices_var);
        variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
        emitAssignment(nloc);
        locals[thread_id][target_role_index] = nloc;
    }
}

static void
generate_check(int thread_id) {
    //TODO: Could be optimized here
    clean_fmt();
    fmt << "---------------ERROR CHECK THREAD " << thread_id << " ROLE " << role_array[goal_role_index] << "------------"; 
    emitComment(fmt.str());
    term_t term_cond = locals[thread_id][goal_role_index].yices_var;
    variable term_guard = createFrom(guard, term_cond);
    emitAssignment(term_guard);
    guard = term_guard;
    term_t assertion_cond = yices_ite(term_guard.yices_var, zero, one);
    emitAssertion(assertion_cond);
}

static void
simulate_thread(int thread_id) {
    clean_fmt();
    fmt << "--------------- APPLICATION OF THREAD " << thread_id << " ------------"; 
    emitComment(fmt.str());
    
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
assign_PCs(int thread_id, int round) {
    clean_fmt();
    fmt << "---------- ASSIGNING PC FOR THREAD " << thread_id << " ROUND " << round << " ---------";
    emitComment(fmt.str());
    for (int step = 0; step < steps; step++) {
        variable nondet_res = createFrom(nondet_int, -2);
        emitAssignment(nondet_res);
        nondet_int = nondet_res;
        variable npc_n = createFrom(program_counters[step], nondet_res.yices_var);
        emitAssignment(npc_n);
        program_counters[step] = npc_n;
    }
}

static void
simulate_threads(int round) {
    for (int i = 0; i < threads_count; i++) {
        assign_PCs(i, round);
        simulate_thread(i);
    }
}

static void
generate_main(int rounds) {
    for (int r = 0; r < rounds; r++) {
        clean_fmt();
        fmt << "--------------- SIMULATION OF ROUND " << r << " ------------"; 
        emitComment(fmt.str());
        simulate_threads(r); 
    }
}

// static void
// print_var_decls(FILE* outputFile) {
//     int i, t, c;
//     clean_fmt();

//     fmt << "int"; //"unsigned __CPROVER_bitvector[" << get_pc_count() << "]";

//     string int_type = fmt.str();
//     char bool_type[] = "_Bool"; // "unsigned __CPROVER_bitvector[1]";

//     fprintf(outputFile, "%s nondet_int();\n", int_type.c_str());
//     fprintf(outputFile, "%s nondet__Bool();\n", bool_type);
//     fprintf(outputFile, "%s __ESBMC_rounding_mode_0", bool_type);
    
//     for (i = 0; i < threads_count; i++) {
//         int to = thread_assigneds[i]->idx;
//         for (c = 0; c <= to; c++) {
//             thread_assigneds[i]->idx = c;
//             string str = thread_assigneds[i]->print();
//             fprintf(outputFile, ", %s", str.c_str());
//         }
//     }

//     for (int  i = 0; i < role_array_size; i++) {
//         if (globals[i] != NULL) {
//             int to = globals[i]->idx;
//             for (c = 0; c <= to; c++) {
//                 globals[i]->idx = c;
//                 string str = globals[i]->print();
//                 fprintf(outputFile, ", %s", str.c_str());
//             }
//         }
//     }

//     for (t = 0; t < threads_count; t++) {
//         for (int  i = 0; i < role_array_size; i++) {
//             int to = locals[t][i]->idx;
//             for (c = 0; c <= to; c++) {
//                 locals[t][i]->idx = c;
//                 string str = locals[t][i]->print();
//                 fprintf(outputFile, ", %s", str.c_str());
//             }
//         }
//     }

//     {
//         int to = guard->idx;
//         for (c = 0; c <= to; c++) {
//             guard->idx = c;
//             string str = guard->print();
//             fprintf(outputFile, ", %s", str.c_str());
//         }
//     }

//     {
//         int to = nondet_bool->idx;
//         for (c = 0; c <= to; c++) {
//             nondet_bool->idx = c;
//             string str = nondet_bool->print();
//             fprintf(outputFile, ", %s", str.c_str());
//         }
//     }
//     fprintf(outputFile, ";\n");

//     fprintf(outputFile, "%s dummy_int", int_type.c_str());

//     for (i = 0; i < steps; i++) {
//         int to = program_counters[i]->idx;
//         for (c = 0; c <= to; c++) {
//             program_counters[i]->idx = c;
//             string str = program_counters[i]->print();
//             fprintf(outputFile, ", %s", str.c_str());
//         }
//     }

//     {
//         int to = nondet_int->idx;
//         for (c = 0; c <= to; c++) {
//             nondet_int->idx = c;
//             string str = nondet_int->print();
//             fprintf(outputFile, ", %s", str.c_str());
//         }
//     }
//     fprintf(outputFile, ";\n");
// }

static void
add_all_assignments() {
    // int last = 0, i = 0;
    // unsigned long l = assignments.size();

    // std::cout << "[";

    auto aite = assignments.begin();
    term_t body = *aite;

    for ( ; aite != assignments.end(); ++aite) {
        body = yices_and2(body, *aite);
        // i++;
        // int perc = (i * 50) / l;
        // if (perc != last) {
        //     last = perc;
        //     std::cout << "#";
        //     std::cout.flush();
        // }
    }

    // std::cout << "]\n";

    yices_assert_formula(yices_ctx, body);

    // std::cout << "Asserted!\n\n";
}

static void
create_final_assert() {
    auto aite = assertions.begin();
    term_t assert_body = yices_not((*aite));
    for ( ; aite != assertions.end(); ++aite) {
        assert_body = yices_or2(assert_body, yices_not((*aite)));
    }
    yices_assert_formula(yices_ctx, assert_body);
}

static void
generate_program(char *inputFile, FILE *outputFile, int rounds) {
    yices_init();
    generate_zero_one();

    yices_ctx = yices_new_context(NULL);
    
    auto start = std::chrono::high_resolution_clock::now();

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


    auto end = std::chrono::high_resolution_clock::now();
    auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    std::cout << "------------ SMT GENERATED IN " << milliseconds.count() << " ms ------------\n";
    start = std::chrono::high_resolution_clock::now();

    add_all_assignments();

    create_final_assert();


    // fprintf(outputFile, "int main() {\n");

    // print_var_decls(outputFile);

    // ssa_prog.printStats(0);
    // ssa_prog.simplify(Simplifier::CONST_VARS); // CONST_VARS
    // ssa_prog.printStats(1);
    // ssa_prog.writeSMTDeclarations(outputFile, 1);
    // ssa_prog.writeSMT(outputFile, 1, Simplifier::CONST_VARS);

    

    // ssa_prog.loadSMTSolver(yices, Simplifier::CONST_VARS);

    end = std::chrono::high_resolution_clock::now();
    milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    std::cout << "------------ SMT LOADED IN " << milliseconds.count() << " ms ------------\n";


    start = std::chrono::high_resolution_clock::now();

    smt_status_t res = yices_check_context(yices_ctx, NULL);

    end = std::chrono::high_resolution_clock::now();
    milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
    std::cout << "------------ SMT SOLVED IN " << milliseconds.count() << " ms ------------\n";

    switch (res) {
        case STATUS_SAT:
            printf("SAT\n\n");
            break;
        case STATUS_UNSAT:
            printf("UNSAT\n\n");
            break;
        case STATUS_UNKNOWN:
            printf("The status is unknown\n");
            break;

        case STATUS_IDLE:
            fprintf(stderr, "Idle...\n");
            break;
        case STATUS_SEARCHING:
        case STATUS_INTERRUPTED:
        case STATUS_ERROR:
            fprintf(stderr, "Error in check_context\n");
            yices_print_error(stderr);
            break;
    }

    yices_exit();

    // fprintf(outputFile, "return 0;\n}\n");
}

// static void
// free_stmts() {
//     ssa_prog.clear();
// }

void
transform_2_yices(char *inputFile, FILE *outputFile, int rounds, int _steps, int wanted_threads_count) {
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


    deallocate_precomputated_values();

    // free_stmts();
    free_data();
    free_precise_temp_data();
    free_var_counters();
}

}