//#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream> 
#include <memory>

#include "Logics.h"
#include "SMT.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "Policy.h"

#include <chrono>

// #include "Templated.h"
// #include "dummy_esbmc.h"

namespace SMT {

//using std::vector;
//using std::shared_ptr;
//using std::stringstream;
//using std::string;

//template <typename TVar, typename TExpr>
//class BMCTransformer {
//    private:
//
//    int threads_count;
//    int use_tracks;
//    int pc_size;
//
//    std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
//
//    std::stringstream fmt;
//
//    void clean_fmt() {
//        fmt.str(std::string());
//    }
//
//    struct variable : public TVarWrapper<TVar> {
//        SMTFactory<TVar, TExpr>* solver;
//        int bv_size;
//        std::string name;
//        std::string full_name;
//        int idx;
//
//        variable() :
//                TVarWrapper<TVar>(nullptr),
//                bv_size(-1), name(""), full_name(""), idx(-1), solver(nullptr) { }
//
//        variable(const std::string _name, int _idx, int _bv_size, SMTFactory<TVar, TExpr>* _solver) :
//                TVarWrapper<TVar>(nullptr),
//                bv_size(_bv_size), name(_name), full_name(_name + "_" + std::to_string(_idx)), idx(_idx), solver(_solver) {
//            // printf("CN: %s\n", full_name.c_str());
//            this->solver_varp = std::make_shared<TVar>(solver->createVar2(full_name, bv_size));
//
//            // TVar var_val = solver->createVar2(full_name, bv_size);
//            // printf("%s: %d\n", name.c_str(), var_val);
//            // int res = yices_pp_term(stdout, var_val, 160, 40, 0);
//            // if (res < 0 || var_val == 0) {
//            //     printf("wtf??\n");
//            // }
//            // printf("%s: %d\n", name.c_str(), *solver_varp);
//            // res = yices_pp_term(stdout, *solver_varp, 160, 40, 0);
//            // if (res < 0 || *solver_varp == 0) {
//            //     printf("wtf??\n");
//            // }
//
//        }
//
//        friend std::ostream& operator<< (std::ostream& stream, const variable& var) {
//            stream << var.full_name;
//            return stream;
//        }
//
//        // ~variable() {
//        //     delete[] solver_varp;
//        // }
//
//        // variable(std::string _name, int _idx, int _bv_size, TExpr value) :
//        //     bv_size(_bv_size), name(_name), idx(_idx),
//        //     solver_var(solver->createVar2(_name + "_" + std::to_string(_idx)), _bv_size)  { }
//
////        inline TVar get_solver_var() {
////            if (solver_varp == nullptr)
////                throw new std::runtime_error("Null variable");
////            else {
////                return *solver_varp;
////            }
////        }
//
//        variable createFrom() {
//            // printf("GF: %s\n", this->full_name.c_str());
//            auto res = variable(this->name, this->idx + 1, this->bv_size, this->solver);
//            return res;
//        }
//
//        static variable dummy() {
//            variable res;
//            res.name = std::string("dummy");
//            res.idx = -1;
//            res.bv_size = -1;
//            return res;
//        }
//
//        // TExpr getAssignment() {
//        //     if (solver_val == nullptr) {
//        //         return solver->createTrue();
//        //     }
//        //     else {
//        //         return solver->createEqExpr(solver_var, *solver_val);
//        //     }
//        // }
//
//    };
//
//    variable dummy_var = variable::dummy();
//
//    /*--- SMT VARIABLE INDEXES ---*/
//    /*--- VALUES ARE  ---*/
//    std::vector<variable> globals;
//    std::vector<variable> thread_assigneds;
//    std::vector<variable> program_counters;
//    std::vector<std::vector<variable>> locals;
//    variable guard;
//    variable nondet_bool;
//    variable nondet_int;
//    int steps;
//
//    // vector<SSA::Stmt> out_stmts;
//
//    std::shared_ptr<arbac_policy> policy;
//
//    TExpr zero;
//    TExpr one;
//
//    // #ifdef MERGE_RULES
//    std::vector<std::shared_ptr<rule>>* per_role_ca_rules = nullptr;
//    std::vector<std::shared_ptr<rule>>* per_role_cr_rules = nullptr;
//
//    std::vector<TExpr> final_assertions;
//
//    // #endif
//
//    inline void emit_assignment(variable& variable, TExpr value) {
//        TExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
//        solver->assertLater(assign);
//    }
//
//    inline void emit_assumption(TExpr expr) {
//        solver->assertLater(expr);
//    }
//
//    inline void emitAssertion(TExpr assertion) {
//        final_assertions.push_back(assertion);
//    }
//
//    int NumBits(int pc) {
//        int i = 1, bit = 0;
//
//        if (pc < 2 ) return 1;
//
//        while (pc >= i) {
//            i = i * 2;
//            bit++;
//        }
//
//        return (bit);
//    }
//
//    void precompute_merge() {
//
//        float assignable_roles_count = 0;
//        float removable_roles_count = 0;
//
////        roles_ca_counts = new int[role_array_size];
////        roles_cr_counts = new int[role_array_size];
//        per_role_ca_rules = new std::vector<std::shared_ptr<rule>>[policy->atom_count()];
//        per_role_cr_rules = new std::vector<std::shared_ptr<rule>>[policy->atom_count()];
//
//        for (int i = 0; i < policy->atom_count(); ++i) {
//            //INSTANTIATING per_role_ca_indexes
////            per_role_ca_indexes[i];
//
//            //INSTANTIATING per_role_ca_indexes CONTENT
//            for (auto ite = policy->can_assign_rules().begin(); ite != policy->can_assign_rules().end(); ++ite) {
//                if ((*ite)->target->role_array_index == i) {
//                    per_role_ca_rules[i].push_back(*ite);
//                }
//            }
//            if (per_role_ca_rules[i].size() > 0) {
//                assignable_roles_count++;
//            }
//
//
//            //INSTANTIATING per_role_cr_indexes
//            for (auto ite = policy->can_revoke_rules().begin(); ite != policy->can_revoke_rules().end(); ++ite) {
//                if ((*ite)->target->role_array_index == i) {
//                    per_role_cr_rules[i].push_back(*ite);
//                }
//            }
//            if (per_role_cr_rules[i].size() > 0) {
//                assignable_roles_count++;
//            }
//        }
//        return;
//    }
//
//    void deallocate_precomputated_values() {
//        delete[] per_role_ca_rules;
//        delete[] per_role_cr_rules;
//    }
//
//    int get_pc_count() {
//        int n = 0;
//        for (int i = 0; i < policy->atom_count(); ++i) {
//            if (per_role_ca_rules[i].size() != 0)
//                n++;
//            if (per_role_cr_rules[i].size() != 0)
//                n++;
//        }
//        return NumBits(n + 1);
//    }
//
//    void initialize_var_counters() {
//
//        guard = dummy_var;
//        nondet_bool = dummy_var;
//
//        globals = std::vector<variable>((unsigned long) policy->atom_count());
//        for (int i = 0; i < policy->atom_count(); ++i) {
//            globals[i] = dummy_var;
//        }
//
//        thread_assigneds = std::vector<variable>((unsigned long) threads_count);
//        for (int i = 0; i < threads_count; ++i) {
//            thread_assigneds[i] = dummy_var;
//        }
//
//        program_counters = std::vector<variable>((unsigned long) steps);
//        for (int i = 0; i < steps; ++i) {
//            program_counters[i] = dummy_var;
//        }
//
//        locals = std::vector<std::vector<variable>>((unsigned long) threads_count);
//        for (int i = 0; i < threads_count; ++i) {
//            locals[i] = std::vector<variable>((unsigned long) policy->atom_count());
//            for (int j = 0; j < policy->atom_count(); ++j) {
//                locals[i][j] = dummy_var;
//            }
//        }
//
//        pc_size = get_pc_count();
//    }
//
//    void free_var_counters() {
////        for (int i = 0; i < threads_count; ++i) {
////            delete[] locals[i];
////        }
////        delete[] locals;
////        delete[] globals;
////        delete[] thread_assigneds;
////        delete[] program_counters;
//    }
//
//    void emitComment(const std::string comment) {
//        // ssa_prog.addComment(createComment(comment));
//    }
//
////    variable create_variable(const string name, int idx, TExpr value, int bv_size) {
////        variable ret;
////        ret.name = name;
////        ret.idx = idx;
////        ret.bv_size = bv_size;
////
////        std::shared_ptr<TExpr> valp = std::make_shared<TExpr>(value);
////
////        ret.solver_var = std::make_shared<TVar>(solver->createVar2(ret.name + std::to_string(ret.idx), bv_size));
////        ret.solver_val = valp;
////
////        return ret;
////    }
////
////    variable create_variable(const string name, int idx, int bv_size) {
////        variable ret;
////        ret.name = name;
////        ret.idx = idx;
////        ret.bv_size = bv_size;
////
////        ret.solver_var = std::make_shared<TVar>(solver->createVar2(ret.name + std::to_string(ret.idx), bv_size));
////        ret.solver_val = nullptr;
////
////        return ret;
////    }
//
////    variable
////    createFrom(variable var, TExpr nvalue) {
////        variable nvar = create_variable(var.name, var.idx + 1, nvalue, var.bv_size);
////        return nvar;
////    }
//
////    variable
////    createFrom(variable var) {
////        variable nvar = create_variable(var.name, var.idx + 1, var.bv_size);
////        return nvar;
////    }
//
//    TExpr create_constant(int value, int bv_size) {
//        TExpr ret;
//
//        if (bv_size > 1) {
//            ret = solver->createBVConst(value, bv_size);
//        }
//        else if (value) {
//            ret = one;
//        }
//        else {
//            ret = zero;
//        }
//        return ret;
//    }
//
//    void generate_header(char *inputFile, int rounds) {
//        time_t mytime;
//        mytime = time(NULL);
//        clean_fmt();
//        fmt << std::endl;
//        fmt << "*  generated by VAC [ 0000 / 0000 ]" << std::endl;
//        fmt << "*" << std::endl;
//        fmt << "*  instance version    {}" << std::endl;
//        fmt << "*" << std::endl;
//        fmt << "*  " << ctime(&mytime);
//        fmt << "*" << std::endl;
//        fmt << "*  params:" << std::endl;
//        fmt << "*    --format ssa" << std::endl;
//        fmt << "*    --rounds " << rounds << std::endl;
//        fmt << "*    --steps " << steps << std::endl;
//        fmt << "*   " << inputFile << std::endl;
//        fmt << "*" << std::endl;
//        fmt << "*  users: " << policy->users().size() << std::endl;
//        fmt << "*  roles: " << policy->atom_count() << std::endl;
//        fmt << "*  adminroles: " << admin_role_array_index_size << std::endl;
//        fmt << "*  CA: " << policy->can_assign_rules().size() << std::endl;
//        fmt << "*  CR: " << policy->can_revoke_rules().size() << std::endl;
//        fmt << "*  ThreadCount: " << threads_count << std::endl;
//        emitComment(fmt.str());
//        emitComment("");
//        emitComment("");
//
//        // Variablep __ESBMC_rounding_mode = createVariablep("__ESBMC_rounding_mode", 0, zero, 1);
//
//        // emitAssignment(__ESBMC_rounding_mode);
//
//        return;
//    }
//
////    variable generate_empty_variable(const string name, int idx, int bv_size) {
////        variable ret;
////        ret.name = name;
////        ret.idx = idx;
////        ret.bv_size = bv_size;
////        ret.solver_var = std::make_shared<TVar>(solver->createVar2(ret.name + std::to_string(ret.idx), bv_size));
////        ret.solver_val = nullptr;
////        return ret;
////    }
//
//    void generate_zero_one_dummy(){
//        zero = solver->createBoolConst(false);
//        one = solver->createBoolConst(true);
//    }
//
//    void generate_PCs() {
//        pc_size = get_pc_count();
//        for (int i = 0; i < steps; i++) {
//            clean_fmt();
//            fmt << "__cs_pc_" << i;
//            variable var = variable(fmt.str(), -1, pc_size, solver.get());
//            // emitAssignment(var);
//            program_counters[i] = var;
//        }
//    }
//
//    void init_PCs_guards_nondet() {
//        generate_PCs();
//        guard = variable("guard", -1, 1, solver.get());
//        nondet_bool = variable("nondet_bool", -2, 1, solver.get());
//        nondet_int = variable("nondet_int", -2, pc_size, solver.get());
//        // emitAssignment(guard);
//        // emitAssignment(nondet_bool);
//        // emitAssignment(nondet_int);
//    }
//
//    void
//    generate_globals() {
//        int i = 0, j = 0;
//        int count = 0;
//        emitComment("---------- INIT GLOBAL VARIABLES ---------");
//        for (i = 0; i < admin_role_array_index_size; i++) {
//            count = 0;
//            // Check if an admin role is already assigned to some user
//            for (j = 0; j < user_config_array_size; j++) {
//                if (belong_to(user_config_array[j].array, user_config_array[j].array_size, admin_role_array_index[i])) {
//                    count = 1;
//                    break;
//                }
//            }
//            clean_fmt();
//            fmt << "glob_" << role_array[admin_role_array_index[i]];
//            variable var = create_variable(fmt.str(), 0, count ? one : zero, 1);
//            globals[admin_role_array_index[i]] = var;
//            emitAssignment(var);
//        }
//        emitComment("");
//    }
//
//    void generate_thread_locals(int thread_id) {
//        clean_fmt();
//        fmt << "---------- THREAD " << thread_id << " LOCAL VARIABLES ---------";
//        emitComment(fmt.str());
//        for (int i = 0; i < policy->atom_count(); i++) {
//            clean_fmt();
//            fmt << "local_Thread_" << thread_id << "_loc_" << policy->atoms(i)->name;
//            if (use_tracks) {
//                variable var = variable(fmt.str(), 0, 1, solver.get());
//                locals[thread_id][i] = var;
//                emit_assignment(var, zero);
//            }
//            else {//locals[thread_id][i]++
//                bool _contains = contains(policy->users(thread_id)->config(), policy->atoms(i));
//                variable var = variable(fmt.str(), 0, 1, solver.get());
//                locals[thread_id][i] = var;
//                emit_assignment(var, _contains ? one : zero);
//            }
//        }
//    }
//
//    void generate_locals() {
//        emitComment("---------- THREADS LOCAL VARIABLES ---------");
//        for (int i = 0; i < threads_count; ++i) {
//            generate_thread_locals(i);
//        }
//    }
//
//    void generate_thread_assigned_locals() {
//        emitComment("--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------");
//        for (int i = 0; i < threads_count; ++i) {
//            clean_fmt();
//            fmt << "thread_" << i << "_assigned";
//            variable var = variable(fmt.str(), 0, 1, solver.get());
//            thread_assigneds[i] = var;
//            emit_assignment(var, zero);
//        }
//    }
//
//    void thread_assignment_if(int thread_id, int user_id) {
//        clean_fmt();
//        fmt << "-------THREAD " << thread_id << " TO USER " << user_id << " (" << policy->users(user_id) << ")-------";
//        emitComment(fmt.str());
//
//        TExpr con_e = create_constant(thread_id, pc_size);
//        TExpr eq_e = solver->createEqExpr(nondet_int.get_solver_var(), con_e);
//        TExpr not_e = solver->createNotExpr(thread_assigneds[thread_id].get_solver_var());
//        TExpr if_guard = solver->createAndExpr(
//            eq_e ,
//            not_e );
//        variable n_guard = guard.createFrom();
//        emit_assignment(n_guard, if_guard);
//        guard = n_guard;
//
//        TExpr ass_val = solver->createCondExpr(guard.get_solver_var(), one, thread_assigneds[thread_id].get_solver_var());
//
//        variable assigned = thread_assigneds[thread_id].createFrom();
//        emit_assignment(assigned, ass_val);
//        thread_assigneds[thread_id] = assigned;
//
//        for (auto &&atom : policy->users(user_id)->config()) {
//            // if (belong_to(admin_role_array_index, admin_role_array_index_size, user_config_array[user_id].array[j])) {
//            //     Expr glob_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), globals[user_config_array[user_id].array[j]]));
//            //     Variablep glob = createFrom(globals[user_config_array[user_id].array[j]], glob_val);
//            //     emit(generateAssignment(glob));
//            //     globals[user_config_array[user_id].array[j]] = glob;
//            // }
//            TExpr loc_val = solver->createCondExpr(guard.get_solver_var(), one, locals[thread_id][atom->role_array_index].get_solver_var());
//            variable loc = locals[thread_id][atom->role_array_index].createFrom();
//            emit_assignment(loc, loc_val);
//            locals[thread_id][atom->role_array_index] = loc;
//        }
//    }
//
//    void assign_thread_to_user(int user_id) {
//        clean_fmt();
//        fmt << "--------------- CONFIGURATION OF USER " << user_id << " (" << policy->users(user_id) << ") ------------";
//        emitComment(fmt.str());
//        variable nondet = nondet_int.createFrom();
////        emitAssignment(nondet);
//        nondet_int = nondet;
//
//        for (int i = 0; i < threads_count; i++) {
//            thread_assignment_if(i, user_id);
//        }
//    }
//
//    void assign_threads() {
//        for (int i = 0; i < policy->users().size(); i++) {
//            assign_thread_to_user(i);
//        }
//
//        TExpr assume_body = thread_assigneds[0].get_solver_var();
//        for (int i = 1; i < threads_count; i++) {
//            assume_body = solver->createAndExpr(thread_assigneds[i].get_solver_var(), assume_body);
//        }
//        emit_assumption(assume_body);
//    }
//
//    void
//    generate_updates(int thread_id) {
//        emitComment("---- GLOBAL ROLE CONSISTENCY UPDATE ----");
//        for (int i = 0; i < admin_role_array_index_size; i++) {
//            for (int j = 0; j < cr_array_size; j++) {
//                if (admin_role_array_index[i] == cr_array[j].target_role_index) {
//                    int r_index = admin_role_array_index[i];
//                    TExpr value = solver->createOrExpr(globals[r_index].get_solver_var(), locals[thread_id][r_index].get_solver_var());
//                    variable n_glob = createFrom(globals[r_index], value);
//                    emitAssignment(n_glob);
//                    globals[r_index] = n_glob;
//                    break;
//                }
//            }
//        }
//        // glob_Author_d = glob_Author_d || __cs_local_Thread_user3_loc_Author_d;
//    }
//
//    TExpr generate_from_prec(int thread_id, const Expr &precond) {
//
//        TExpr res = generateSMTFunction2(solver, precond, locals[thread_id], "");
//
//        return res;
//    }
//
//    TExpr generate_rule_cond(int thread_id, rulep rule) {
//        int j;
//        // TExpr cond = -1;
//        // Admin role must be available
//        TExpr admin_cond = globals[ca->admin].get_solver_var();
//
//        // Precondition must be satisfied
//        TExpr prec_cond = generate_from_prec(thread_id, rule->prec);
//
//        // Optional this user is not in this target role yet
//        TExpr not_ass =
//                rule->is_ca ?
//                solver->createNotExpr(locals[thread_id][rule->target->role_array_index].get_solver_var()) :
//                locals[thread_id][rule->target->role_array_index].get_solver_var();
//        TExpr final_cond = solver->createAndExpr(solver->createAndExpr(admin_cond, prec_cond), not_ass);
//        return final_cond;
//    }
//
//    TExpr generate_PC_cond(int rule_id) {
//        TExpr cond = solver->createEqExpr(program_counters[0].get_solver_var(), create_constant(rule_id, pc_size));
//        for (int i = 1; i < steps; i++) {
//            cond = solver->createOrExpr(cond, solver->createEqExpr(program_counters[i].get_solver_var(), create_constant(rule_id, pc_size)));
//        }
//        return cond;
//    }
//
//    void simulate_can_assigns_by_role(int thread_id, int target_role_index, int rule_id) {
//        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
//        int i = 0;
//        TExpr pc_cond, ca_cond, all_cond;
//        // TExpr pc_cond = -1, ca_cond = -1, all_cond = -1;
//        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
//        clean_fmt();
//        fmt << "--- ASSIGNMENT RULES FOR ROLE " << policy->atoms(target_role_index) << " ---";
//        emitComment(fmt.str());
//
//        if (roles_ca_counts[target_role_index] < 1) {
//            clean_fmt();
//            fmt << "--- ROLE " << role_array[target_role_index] << " IS NOT ASSIGNABLE... SHOULD CRASH ---";
//            string msg = fmt.str();
//            emitComment(msg);
//            fprintf(stderr, "%s", msg.c_str());
//            return;
//        }
//
//        pc_cond = generate_PC_cond(rule_id);
//
//        emit_ca_comment(per_role_ca_indexes[target_role_index][0]);
//        ca_cond = generate_CA_cond(thread_id, per_role_ca_indexes[target_role_index][0]);
//
//        for (i = 1; i < roles_ca_counts[target_role_index]; ++i) {
//            int ca_idx = per_role_ca_indexes[target_role_index][i];
//            TExpr ith_cond = generate_CA_cond(thread_id, ca_idx);
//            emit_ca_comment(ca_idx);
//            ca_cond = solver->createOrExpr(ca_cond, ith_cond);
//        }
//
//        all_cond = solver->createAndExpr(pc_cond, ca_cond);
//        variable ca_guard = createFrom(guard, all_cond);
//        emitAssignment(ca_guard);
//        guard = ca_guard;
//
//        if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
//            TExpr ngval = solver->createCondExpr(ca_guard.get_solver_var(), one, globals[target_role_index].get_solver_var());
//            variable nglob = createFrom(globals[target_role_index], ngval);
//            TExpr nlval = solver->createCondExpr(ca_guard.get_solver_var(), one, locals[thread_id][target_role_index].get_solver_var());
//            variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
//            emitAssignment(nglob);
//            emitAssignment(nloc);
//            globals[target_role_index] = nglob;
//            locals[thread_id][target_role_index] = nloc;
//        }
//        else {
//            TExpr nlval = solver->createCondExpr(ca_guard.get_solver_var(), one, locals[thread_id][target_role_index].get_solver_var());
//            variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
//            emitAssignment(nloc);
//            locals[thread_id][target_role_index] = nloc;
//        }
//    }
//
//    void
//    simulate_can_revokes_by_role(int thread_id, int target_role_index, int rule_id) {
//        // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
//        int i = 0;
//        TExpr pc_cond, cr_cond, all_cond;
//        // TExpr pc_cond = -1, cr_cond = -1, all_cond = -1;
//        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
//        clean_fmt();
//        fmt << "--- REVOKE RULES FOR ROLE " << role_array[target_role_index] << " ---";
//        emitComment(fmt.str());
//
//        if (roles_cr_counts[target_role_index] < 1) {
//            clean_fmt();
//            fmt << "--- ROLE " << role_array[target_role_index] << " IS NOT REVOKABLE... SHOULD CRASH ---";
//            string msg = fmt.str();
//            emitComment(msg);
//            fprintf(stderr, "%s", msg.c_str());
//            return;
//        }
//
//        pc_cond = generate_PC_cond(rule_id);
//
//        emit_cr_comment(per_role_cr_indexes[target_role_index][0]);
//        cr_cond = generate_CR_cond(thread_id, per_role_cr_indexes[target_role_index][0]);
//
//        for (i = 1; i < roles_cr_counts[target_role_index]; ++i) {
//            int cr_idx = per_role_cr_indexes[target_role_index][i];
//            TExpr ith_cond = generate_CR_cond(thread_id, cr_idx);
//            emit_cr_comment(cr_idx);
//            cr_cond = solver->createOrExpr(cr_cond, ith_cond);
//        }
//
//        all_cond = solver->createAndExpr(pc_cond, cr_cond);
//        variable cr_guard = createFrom(guard, all_cond);
//        emitAssignment(cr_guard);
//        guard = cr_guard;
//
//        if (belong_to(admin_role_array_index, admin_role_array_index_size, target_role_index)) {
//            TExpr ngval = solver->createCondExpr(cr_guard.get_solver_var(), zero, globals[target_role_index].get_solver_var());
//            variable nglob = createFrom(globals[target_role_index], ngval);
//            TExpr nlval = solver->createCondExpr(cr_guard.get_solver_var(), zero, locals[thread_id][target_role_index].get_solver_var());
//            variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
//            emitAssignment(nglob);
//            emitAssignment(nloc);
//            globals[target_role_index] = nglob;
//            locals[thread_id][target_role_index] = nloc;
//        }
//        else {
//            TExpr nlval = solver->createCondExpr(cr_guard.get_solver_var(), zero, locals[thread_id][target_role_index].get_solver_var());
//            variable nloc = createFrom(locals[thread_id][target_role_index], nlval);
//            emitAssignment(nloc);
//            locals[thread_id][target_role_index] = nloc;
//        }
//    }
//
//    void
//    generate_check(int thread_id) {
//        //TODO: Could be optimized here
//        clean_fmt();
//        fmt << "---------------ERROR CHECK THREAD " << thread_id << " ROLE " << role_array[goal_role_index] << "------------";
//        emitComment(fmt.str());
//        TExpr term_cond = locals[thread_id][goal_role_index].get_solver_var();
//        variable term_guard = createFrom(guard, term_cond);
//        emitAssignment(term_guard);
//        guard = term_guard;
//        TExpr assertion_cond = solver->createCondExpr(term_guard.get_solver_var(), zero, one);
//        emitAssertion(assertion_cond);
//    }
//
//    void
//    simulate_thread(int thread_id) {
//        clean_fmt();
//        fmt << "--------------- APPLICATION OF THREAD " << thread_id << " ------------";
//        emitComment(fmt.str());
//
//        generate_updates(thread_id);
//
//        int label_idx = 0;
//        emitComment("---------- IDLE ROUND REMOVED SINCE PC MAY BE GREATER THAN PC_MAX ---------");
//
//        int i;
//        emitComment("---------- CAN ASSIGN SIMULATION ---------");
//        emitComment("---------- MERGED PER ROLE ---------");
//        for (int i = 0; i < role_array_size; ++i) {
//            // printf("CA idx: %d, role: %s: count: %d\n", i, role_array[i], roles_ca_counts[i]);
//            if (roles_ca_counts[i] > 0) {
//                simulate_can_assigns_by_role(thread_id, i, label_idx++);
//            }
//        }
//
//        emitComment("---------- CAN REVOKE SIMULATION ---------");
//        emitComment("---------- MERGED PER ROLE ---------");
//        for (int i = 0; i < role_array_size; ++i) {
//            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
//            if (roles_cr_counts[i] > 0) {
//                simulate_can_revokes_by_role(thread_id, i, label_idx++);
//            }
//        }
//
//        generate_check(thread_id);
//    }
//
//    void
//    assign_PCs(int thread_id, int round) {
//        clean_fmt();
//        fmt << "---------- ASSIGNING PC FOR THREAD " << thread_id << " ROUND " << round << " ---------";
//        emitComment(fmt.str());
//        for (int step = 0; step < steps; step++) {
//            variable nondet_res = createFrom(nondet_int);
//            emitAssignment(nondet_res);
//            nondet_int = nondet_res;
//            variable npc_n = createFrom(program_counters[step], nondet_res.get_solver_var());
//            emitAssignment(npc_n);
//            program_counters[step] = npc_n;
//        }
//    }
//
//    void
//    simulate_threads(int round) {
//        for (int i = 0; i < threads_count; i++) {
//            assign_PCs(i, round);
//            simulate_thread(i);
//        }
//    }
//
//    void
//    generate_main(int rounds) {
//        for (int r = 0; r < rounds; r++) {
//            clean_fmt();
//            fmt << "--------------- SIMULATION OF ROUND " << r << " ------------";
//            emitComment(fmt.str());
//            simulate_threads(r);
//        }
//    }
//
//    void
//    create_final_assert() {
//        auto aite = final_assertions.begin();
//        TExpr assert_body = solver->createNotExpr((*aite));
//        for ( ; aite != final_assertions.end(); ++aite) {
//            assert_body = solver->createOrExpr(assert_body, solver->createNotExpr((*aite)));
//        }
//        solver->assertLater(assert_body);
//    }
//
//    void generate_program(int rounds) {
//        generate_zero_one_dummy();
//
//        auto start = std::chrono::high_resolution_clock::now();
//
//        initialize_var_counters();
//
//        // TODO: this should be merged in initialize_var_counters to avoid NULL in counters
//        // TODO: Usare shared pointer per tutto o trackare le stronzate condivise (mai ricorsive ;)
//        init_PCs_guards_nondet();
//        //Generate header with comments
//        // generate_header(inputFile, rounds);
//
//
//        generate_globals();
//        generate_locals();
//
//        generate_thread_assigned_locals();
//        assign_threads();
//
//
//        generate_main(rounds);
//
//
//        auto end = std::chrono::high_resolution_clock::now();
//        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//        std::cout << "------------ SMT GENERATED IN " << milliseconds.count() << " ms ------------\n";
//        start = std::chrono::high_resolution_clock::now();
//
//        // add_all_assignments();
//
//        create_final_assert();
//
//
//        end = std::chrono::high_resolution_clock::now();
//        milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//        std::cout << "------------ SMT LOADED IN " << milliseconds.count() << " ms ------------\n";
//
//
//        start = std::chrono::high_resolution_clock::now();
//
//        SMTResult res = solver->solve();
//
//        end = std::chrono::high_resolution_clock::now();
//        milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//        std::cout << "------------ SMT SOLVED IN " << milliseconds.count() << " ms ------------\n";
//
//        switch (res) {
//            case SAT:
//                printf("SAT\n\n");
//                break;
//            case UNSAT:
//                printf("UNSAT\n\n");
//                break;
//            case UNKNOWN:
//                printf("The status is unknown\n");
//                break;
//            case ERROR:
//                fprintf(stderr, "Error in check_context\n");
//                break;
//        }
//    }
//
//    // void
//    // free_stmts() {
//    //     ssa_prog.clear();
//    // }
//
//    public:
//    Transformer(std::shared_ptr<SMTFactory<TVar, TExpr>> _solver) :
//        solver(_solver) { }
//
//    void transform_2_bounded_smt(std::shared_ptr<SMTFactory<TVar, TExpr>> _solver,
//                                 int rounds, int _steps, int wanted_threads_count) {
//        // solver = _solver;
//        steps = _steps;
//
//
//        precompute_merge();
//
//        //Set the number of user to track
//        if (wanted_threads_count < 1) {
//            if (user_array_size <= admin_role_array_index_size + 1) {
//                threads_count = user_array_size;
//                use_tracks = 0;
//            }
//            else {
//                threads_count = admin_role_array_index_size + 1;
//                use_tracks = 1;
//            }
//        }
//        else {
//            if (user_array_size <= wanted_threads_count) {
//                fprintf(stderr, "Cannot spawn %d threads because are more than user count (%d)\n", wanted_threads_count, user_array_size);
//                exit(EXIT_FAILURE);
//            }
//            else {
//                threads_count = admin_role_array_index_size + 1;
//                use_tracks = 1;
//            }
//        }
//
//        generate_program(rounds);
//
//
//        deallocate_precomputated_values();
//
//
//        free_var_counters();
//
//        // free_stmts();
//
//    }
//};
//
//template <typename TVar, typename TExpr>
//static void polymorphic_transform(std::shared_ptr<SMTFactory<TVar, TExpr>> solver,
//                                 int rounds, int steps, int wanted_threads_count) {
//            Transformer<TVar, TExpr> core(solver);
//            core.transform_2_bounded_smt(solver, rounds, steps, wanted_threads_count);
//}
//
//void transform_2_bounded_smt(char *inputFile, FILE* outputFile, int rounds, int steps, int wanted_threads_count) {
//    if (rounds < 1) {
//        fprintf(stderr, "Cannot simulate a number of rounds < 1\n");
//        exit(EXIT_FAILURE);
//    }
//    if (steps < 1) {
//        fprintf(stderr, "Cannot simulate a number of steps < 1\n");
//        exit(EXIT_FAILURE);
//    }
//
//    read_ARBAC(inputFile);
//    // Preprocess the ARBAC Policies
//    preprocess(0);
//    build_config_array();
//
//    AvailableSolvers::Solver solver(AvailableSolvers::Z3);
//
//    switch (solver) {
//        case AvailableSolvers::YICES: {
//            std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
//            // auto core(solver);
//            polymorphic_transform(solver, rounds, steps, wanted_threads_count);
//            break;
//        }
//        case AvailableSolvers::Z3: {
//            std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
//            // auto core(solver);
//            polymorphic_transform(solver, rounds, steps, wanted_threads_count);
//            break;
//        }
//        break;
//    }
//
//    free_data();
//    free_precise_temp_data();
//}



}