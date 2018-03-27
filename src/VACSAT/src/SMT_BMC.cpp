//#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <memory>

#include "Logics.h"
#include "SMT_BMC_Struct.h"
#include "SMT_Analysis_functions.h"
#include "SMT.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "SMTSolvers/boolector.h"
#include "SMTSolvers/mathsat.h"
#include "Policy.h"

#include <chrono>

// #include "Templated.h"
// #include "dummy_esbmc.h"

namespace SMT {

//    using std::vector;
//    using std::shared_ptr;
//    using std::stringstream;
//    using std::string;

    class BMCTransformer {
        private:

        typedef generic_variable variable;

        int threads_count;
        int use_tracks;
        int pc_size;
        int thread_pc_size;

        std::shared_ptr<SMTFactory> solver;

        std::stringstream fmt;

        void clean_fmt() {
            fmt.str(std::string());
        }

        variable dummy_var = variable::dummy();

        /*--- SMT VARIABLE INDEXES ---*/
        /*--- VALUES ARE  ---*/
    //    std::vector<variable> globals;
        std::vector<variable> thread_assigneds;
        std::vector<variable> program_counters;
        std::vector<std::vector<variable>> locals;
        variable guard;
        variable nondet_bool;
        variable nondet_int;
        variable thread_assignment_nondet_int;
        int steps;

        // vector<SSA::Stmt> out_stmts;

        std::shared_ptr<arbac_policy> policy;

        SMTExpr zero;
        SMTExpr one;

        std::vector<SMTExpr> final_assertions;

        std::vector<Expr> per_rule_admin_expr;
        std::map<Expr, variable> globals_map;

        // #endif

        inline void emit_assignment(const variable& variable, SMTExpr value) {
            SMTExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
            solver->assertLater(assign);
        }

        inline void emit_assumption(SMTExpr expr) {
            solver->assertLater(expr);
        }

        inline void emit_assertion(SMTExpr assertion) {
            final_assertions.push_back(assertion);
        }

        inline void emit_comment(const std::string& comment) {
            //Working automatically and only in Z3
            if (solver->solver_name == Solver::Z3) {
                if (Config::dump_smt_formula == "")
                    return;
                solver->assertNow(solver->createBoolVar(comment));
                log->critical("Emitting comment... {}", comment);
            }
        }

        /* ANALYSIS INFOS */
        int get_pc_count() const {
            int n = 0;
            for (auto &&atom :policy->atoms()) {
                if (policy->per_role_can_assign_rule(atom).size() > 0)
                    n++;
                if (policy->per_role_can_revoke_rule(atom).size() > 0)
                    n++;
            }
            return bits_count(n + 1);
        }

        /*  */
        void initialize_var_counters() {

            guard = dummy_var;
            nondet_bool = dummy_var;

//        globals = std::vector<variable>((unsigned long) policy->atom_count());
//        for (int i = 0; i < policy->atom_count(); ++i) {
//            globals[i] = dummy_var;
//        }

            thread_assigneds = std::vector<variable>((ulong) threads_count);
            for (int i = 0; i < threads_count; ++i) {
                thread_assigneds[i] = dummy_var;
            }

            program_counters = std::vector<variable>((ulong) steps);
            for (int i = 0; i < steps; ++i) {
                program_counters[i] = dummy_var;
            }

            locals = std::vector<std::vector<variable>>((unsigned long) threads_count);
            for (int i = 0; i < threads_count; ++i) {
                locals[i] = std::vector<variable>((unsigned long) policy->atom_count());
                for (int j = 0; j < policy->atom_count(); ++j) {
                    locals[i][j] = dummy_var;
                }
            }

            pc_size = get_pc_count();
            thread_pc_size = bits_count(threads_count);
        }

        bool equivalent_exprs(const Expr& e1, const Expr& e2) {
            solver->clean();

            std::vector<SMTExpr> var_vec((ulong) policy->atom_count());
            SMTExpr se1 = generateSMTFunction(solver, e1, var_vec, "eq");
            SMTExpr se2 = generateSMTFunction(solver, e2, var_vec, "eq");

            // e1 /\ not e2
            SMTExpr e1_not_e2 = solver->createAndExpr(se1,
                                                    solver->createNotExpr(se2));
            // not e1 /\ e2
            SMTExpr not_e1_e2 = solver->createAndExpr(solver->createNotExpr(se1),
                                                    se2);

            // (e1 /\ not e2) \/ (not e1 /\ e2)
            SMTExpr final = solver->createOrExpr(e1_not_e2,
                                               not_e1_e2);

            solver->assertNow(final);

            bool res = solver->solve() == SMTResult::UNSAT;

            return res;
        }

        const std::list<std::list<rulep>> partition_equivalent(const std::list<rulep>& targetings) {
            if (targetings.empty()) {
                return std::list<std::list<rulep>>();
            }
            auto ite = targetings.begin();
            std::list<std::list<rulep>> partitions;
            partitions.emplace_back(std::list<rulep>());
            partitions.begin()->push_back(*ite);

            for (++ite; ite != targetings.end(); ++ite) {
                rulep r1 = *ite;
                bool inserted = false;
                for (auto &&_class : partitions) {
                    rulep r2 = *_class.begin();
                    bool can_merge = equivalent_exprs(r1->admin, r2->admin);
                    if (can_merge) {
                        _class.push_back(r1);
                        inserted = true;
                        break;
                    }
                }
                if (!inserted) {
                    std::list<rulep> new_partition;
                    new_partition.push_back(r1);
                    partitions.push_back(new_partition);
                }
            }
            return partitions;
        }

        void generate_admin_partitions() {
            std::list<rulep> rules(policy->rules().begin(), policy->rules().end());
            std::list<std::list<rulep>> partitions = partition_equivalent(rules);
            per_rule_admin_expr = std::vector<Expr>(policy->rules().size());
    //        std::list<Expr> parts;

            for (auto &&part : partitions) {
                rulep candidate_rule = *part.begin();
                Expr adm = candidate_rule->admin;
    //            parts.push_back(adm);
                std::string glob_name = adm->atoms().size() > 0 ?
                                            (*adm->atoms().begin())->name :
                                            "TRUE";
                globals_map[adm] = variable("global_" + glob_name, -1, 1, solver.get(), BOOLEAN);
                for (auto &&rule : part) {
                    per_rule_admin_expr[rule->original_idx] = adm;
                }
            }

            solver->clean();

    //        return std::pair<std::vector<Expr>, std::list<Expr>>(admin_map, parts);
        }

        void generate_zero_one_dummy(){
            zero = solver->createBoolConst(false);
            one = solver->createBoolConst(true);
        }

        void generate_PCs() {
            pc_size = get_pc_count();
            for (int i = 0; i < steps; i++) {
                clean_fmt();
                fmt << "__cs_pc_" << i;
                variable var = variable(fmt.str(), -1, pc_size, solver.get(), BIT_VECTOR);
                // emitAssignment(var);
                program_counters[i] = var;
            }
        }

        void init_PCs_guards_nondet() {
            generate_PCs();
            guard = variable("guard", -1, 1, solver.get(), BOOLEAN);
            nondet_bool = variable("nondet_bool", -2, 1, solver.get(), BOOLEAN);
            nondet_int = variable("nondet_int", -2, pc_size, solver.get(), BIT_VECTOR);
            thread_assignment_nondet_int = variable("thread_assignment_nondet_int", -2, thread_pc_size, solver.get(), BIT_VECTOR);
            // emitAssignment(guard);
            // emitAssignment(nondet_bool);
            // emitAssignment(nondet_int);
        }

        std::vector<SMTExpr> user_to_lookup_vect(const userp& user) {
            std::vector<SMTExpr> vect((ulong) policy->atom_count());
            for (int i = 0; i < policy->atom_count(); ++i) {
                vect[i] = solver->createFalse();
            }
            for (auto &&atom : user->config()) {
                vect[atom->role_array_index] = solver->createTrue();
            }

            return vect;
        }

        void generate_globals() {
            emit_comment("---------- INIT GLOBAL VARIABLES ---------");
            for (auto &&global_pair : globals_map) {
                Expr adm_expr = global_pair.first;
                variable global_var = global_pair.second;
                SMTExpr global_value = solver->createFalse();
                for (auto &&user : policy->unique_configurations()) {
                    std::vector<SMTExpr> var_vect = user_to_lookup_vect(user);
                    SMTExpr sadm_expr = generateSMTFunction(solver, adm_expr, var_vect, user->name);

                    SMTExpr final_expr = sadm_expr;
                    if (Config::dump_smt_formula != "") {
                        //FIXME: add user->name just for debug purposes
                        SMTExpr user_name = solver->createBoolVar(user->name);
                        final_expr = solver->createAndExpr(user_name, sadm_expr);
                    }
                    global_value = solver->createOrExpr(global_value, final_expr);
                }

                variable new_glob = global_var.createFrom();
                emit_assignment(new_glob, global_value);
                //FIXME: changing a collection while iterating it is considered harmfull
                globals_map[adm_expr] = new_glob;
            }
        }

        void generate_thread_locals(int thread_id) {
            clean_fmt();
            fmt << "---------- THREAD " << thread_id << " LOCAL VARIABLES ---------";
            emit_comment(fmt.str());
            for (int i = 0; i < policy->atom_count(); i++) {
                clean_fmt();
                fmt << "local_Thread_" << thread_id << "_loc_" << policy->atoms(i)->name;
                if (use_tracks) {
                    variable var = variable(fmt.str(), 0, 1, solver.get(), BOOLEAN);
                    locals[thread_id][i] = var;
                    emit_assignment(var, zero);
                }
                else {//locals[thread_id][i]++
                    bool _contains = contains(policy->users(thread_id)->config(), policy->atoms(i));
                    variable var = variable(fmt.str(), 0, 1, solver.get(), BOOLEAN);
                    locals[thread_id][i] = var;
                    emit_assignment(var, _contains ? one : zero);
                }
            }
        }

        void generate_locals() {
            emit_comment("---------- THREADS LOCAL VARIABLES ---------");
            for (int i = 0; i < threads_count; ++i) {
                generate_thread_locals(i);
            }
        }

        void generate_thread_assigned_locals() {
            emit_comment("--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------");
            for (int i = 0; i < threads_count; ++i) {
                clean_fmt();
                fmt << "thread_" << i << "_assigned";
                variable var = variable(fmt.str(), 0, 1, solver.get(), BOOLEAN);
                thread_assigneds[i] = var;
                emit_assignment(var, zero);
            }
        }

        void thread_assignment_if(int thread_id, int user_id) {
            clean_fmt();
            fmt << "-------THREAD " << thread_id << " TO USER " << user_id << " (" << policy->users(user_id) << ")-------";
            emit_comment(fmt.str());

            SMTExpr con_e = solver->createBVConst(thread_id, thread_pc_size);
            SMTExpr eq_e = solver->createEqExpr(thread_assignment_nondet_int.get_solver_var(), con_e);
            SMTExpr not_e = solver->createNotExpr(thread_assigneds[thread_id].get_solver_var());
            SMTExpr if_guard = solver->createAndExpr(eq_e,
                                                   not_e);
            variable n_guard = guard.createFrom();
            emit_assignment(n_guard, if_guard);
            guard = n_guard;

            SMTExpr ass_val = solver->createCondExpr(guard.get_solver_var(), one, thread_assigneds[thread_id].get_solver_var());

            variable assigned = thread_assigneds[thread_id].createFrom();
            emit_assignment(assigned, ass_val);
            thread_assigneds[thread_id] = assigned;

            for (auto &&atom : policy->users(user_id)->config()) {
                // if (belong_to(admin_role_array_index, admin_role_array_index_size, user_config_array[user_id].array[j])) {
                //     Expr glob_val = createCondExpr(exprFromVar(guard), createConstantExpr(1), globals[user_config_array[user_id].array[j]]));
                //     Variablep glob = createFrom(globals[user_config_array[user_id].array[j]], glob_val);
                //     emit(generateAssignment(glob));
                //     globals[user_config_array[user_id].array[j]] = glob;
                // }
                SMTExpr loc_val = solver->createCondExpr(guard.get_solver_var(), one, locals[thread_id][atom->role_array_index].get_solver_var());
                variable loc = locals[thread_id][atom->role_array_index].createFrom();
                emit_assignment(loc, loc_val);
                locals[thread_id][atom->role_array_index] = loc;
            }
        }

        void assign_thread_to_user(int user_id) {
            clean_fmt();
            fmt << "--------------- CONFIGURATION OF USER " << user_id << " (" << policy->users(user_id) << ") ------------";
            emit_comment(fmt.str());

            thread_assignment_nondet_int = thread_assignment_nondet_int.createFrom();

            for (int i = 0; i < threads_count; i++) {
                thread_assignment_if(i, user_id);
            }
        }

        void assign_threads() {
            if (!use_tracks) {
                log->info("Cannot assign threads if no tracks are used.");
                throw std::runtime_error("Cannot assign threads if no tracks are used.");
            }
            for (int i = 0; i < policy->users().size(); i++) {
                assign_thread_to_user(i);
            }

            SMTExpr assume_body = thread_assigneds[0].get_solver_var();
            for (int i = 1; i < threads_count; i++) {
                assume_body = solver->createAndExpr(thread_assigneds[i].get_solver_var(), assume_body);
            }
            emit_assumption(assume_body);
        }

        void generate_updates(int thread_id) {
            emit_comment("---- GLOBAL ROLE CONSISTENCY UPDATE ----");
            for (auto &&global_pair :globals_map) {
                Expr global_expr = global_pair.first;
                variable global_var = global_pair.second;
                for (auto &&canRevokeRule : policy->can_revoke_rules()) {
                    if (contains(global_expr->atoms(), canRevokeRule->target)) {
                        SMTExpr respects = generateSMTFunction(solver, global_expr, locals[thread_id], std::to_string(thread_id));
                        SMTExpr value = solver->createOrExpr(global_var.get_solver_var(), respects);
                        variable n_glob = global_var.createFrom();
                        emit_assignment(n_glob, value);
                        //FIXME changing a collection while iterating it is considered harmfull
                        globals_map[global_expr] = n_glob;
                        break;
                    }
                }
            }
            // glob_Author_d = glob_Author_d || __cs_local_Thread_user3_loc_Author_d;
        }

        SMTExpr generate_from_prec(int thread_id, const Expr &precond) {

            SMTExpr res = generateSMTFunction(solver, precond, locals[thread_id], "");

            return res;
        }

        // FUNCTION USED IF GLOBALS ARE NOT USED
        SMTExpr generate_admin_disjunction(const Expr& cond) {
            SMTExpr res = solver->createFalse();
            for (int thread_id = 0; thread_id < locals.size(); ++thread_id) {
                SMTExpr thread_cond = generateSMTFunction(solver, cond, locals[thread_id], "");
                res = solver->createOrExpr(res, thread_cond);
            }
            return res;
        }

        SMTExpr generate_rule_cond(int thread_id, const rulep& rule) {
            int j;
            // SMTExpr cond = -1;
            // Admin role must be available
            //Could be dfferent even if it has the same configurations
            Expr globals_map_key = per_rule_admin_expr[rule->original_idx];

            SMTExpr admin_cond = globals_map[globals_map_key].get_solver_var();
//            SMTExpr admin_cond = generate_admin_disjunction(rule->admin);

            // Precondition must be satisfied
            SMTExpr prec_cond = generate_from_prec(thread_id, rule->prec);

            // Optional this user is not in this target role yet
            SMTExpr not_ass =
                    rule->is_ca ?
                    solver->createNotExpr(locals[thread_id][rule->target->role_array_index].get_solver_var()) :
                    locals[thread_id][rule->target->role_array_index].get_solver_var();
            SMTExpr final_cond = solver->createAndExpr(solver->createAndExpr(admin_cond, prec_cond), not_ass);
            return final_cond;
        }

        SMTExpr generate_PC_cond(int rule_id) {
            SMTExpr cond = solver->createEqExpr(program_counters[0].get_solver_var(),
                                              solver->createBVConst(rule_id, pc_size));
            for (int i = 1; i < steps; i++) {
                cond = solver->createOrExpr(cond,
                                            solver->createEqExpr(program_counters[i].get_solver_var(),
                                                                 solver->createBVConst(rule_id, pc_size)));
            }
            return cond;
        }

        void simulate_can_assigns_by_atom(int thread_id, const atomp& target, int rule_id) {
            // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
            int i = 0;
            SMTExpr pc_cond, ca_cond, all_cond;
            // SMTExpr pc_cond = -1, ca_cond = -1, all_cond = -1;
            //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
            clean_fmt();
            fmt << "--- ASSIGNMENT RULES FOR ROLE " << *target << " ---";
            emit_comment(fmt.str());

            if (policy->per_role_can_assign_rule(target).size() < 1) {
                clean_fmt();
                log->warn("--- ATOM {} IS NOT ASSIGNABLE... SHOULD CRASH ---", target->to_string());
    //            emit_comment(msg);
                return;
            }

            pc_cond = generate_PC_cond(rule_id);

    //        emit_ca_comment(per_role_ca_indexes[target_role_index][0]);

            ca_cond = solver->createFalse();

            for (auto &&rule : policy->per_role_can_assign_rule(target)) {
                SMTExpr ith_cond = generate_rule_cond(thread_id, rule);
    //            emit_ca_comment(ca_idx);
                ca_cond = solver->createOrExpr(ca_cond, ith_cond);
            }

            all_cond = solver->createAndExpr(pc_cond, ca_cond);
            variable ca_guard = guard.createFrom();
            emit_assignment(ca_guard, all_cond);
            guard = ca_guard;

            // UPDATE LOCALS FIRST
            SMTExpr nlval = solver->createCondExpr(ca_guard.get_solver_var(), one, locals[thread_id][target->role_array_index].get_solver_var());
            variable nloc = locals[thread_id][target->role_array_index].createFrom();
            emit_assignment(nloc, nlval);
            locals[thread_id][target->role_array_index] = nloc;

            // Recompute globals according to updated locals (if necessary)
            for (auto &&glob_pair : globals_map) {
                Expr adm_expr = glob_pair.first;
                variable glob_var = glob_pair.second;
                if (contains(adm_expr->atoms(), target)) {
                    SMTExpr ngval = generateSMTFunction(solver, adm_expr, locals[thread_id], std::to_string(thread_id));
                    SMTExpr n_cond_gval = solver->createCondExpr(ca_guard.get_solver_var(), ngval, glob_var.get_solver_var());
                    variable nglob = glob_var.createFrom();
                    emit_assignment(nglob, n_cond_gval);
                    //FIXME changing a collection while iterating it is considered harmfull
                    globals_map[adm_expr] = nglob;
                }
            }
        }

        void simulate_can_revokes_by_atom(int thread_id, const atomp &target, int rule_id) {
            // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
            int i = 0;
            SMTExpr pc_cond, cr_cond, all_cond;
            // SMTExpr pc_cond = -1, cr_cond = -1, all_cond = -1;
            //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
            clean_fmt();
            fmt << "--- REVOKE RULES FOR ROLE " << *target << " ---";
            emit_comment(fmt.str());

            if (policy->per_role_can_revoke_rule(target).size() < 1) {
                log->warn("--- ROLE {} IS NOT REVOKABLE... SHOULD CRASH ---", target->to_string());
    //            string msg = fmt.str();
    //            emit_comment(msg);
    //            fprintf(stderr, "%s", msg.c_str());
                return;
            }

            pc_cond = generate_PC_cond(rule_id);

    //        emit_cr_comment(per_role_cr_indexes[target_role_index][0]);

            cr_cond = solver->createFalse();

            for (auto &&rule : policy->per_role_can_revoke_rule(target)) {
                SMTExpr ith_cond = generate_rule_cond(thread_id, rule);
    //            emit_cr_comment(cr_idx);
                cr_cond = solver->createOrExpr(cr_cond, ith_cond);
            }

            all_cond = solver->createAndExpr(pc_cond, cr_cond);
            variable cr_guard = guard.createFrom();
            emit_assignment(cr_guard, all_cond);
            guard = cr_guard;

            // UPDATE LOCALS FIRST
            SMTExpr nlval = solver->createCondExpr(cr_guard.get_solver_var(), zero, locals[thread_id][target->role_array_index].get_solver_var());
            variable nloc = locals[thread_id][target->role_array_index].createFrom();
            emit_assignment(nloc, nlval);
            locals[thread_id][target->role_array_index] = nloc;

            // Recompute globals according to updated locals (if necessary)
            for (auto &&global_pair : globals_map) {
                Expr glob_expr = global_pair.first;
                variable glob_var = global_pair.second;
                if (contains(glob_expr->atoms(), target)) {
                    SMTExpr ngval = generateSMTFunction(solver, glob_expr, locals[thread_id], std::to_string(thread_id));
                    SMTExpr n_cond_gval = solver->createCondExpr(cr_guard.get_solver_var(), ngval, glob_var.get_solver_var());
                    variable nglob_var = glob_var.createFrom();
                    emit_assignment(nglob_var, n_cond_gval);
                    //FIXME changing a collection while iterating it is considered harmfull
                    globals_map[glob_expr] = nglob_var;

                }
            }
        }

        void generate_check(int thread_id) {
            //TODO: Could be optimized here
    //        clean_fmt();
    //        fmt << "---------------ERROR CHECK THREAD " << thread_id << " ROLE " << role_array[goal_role_index] << "------------";
    //        emit_comment(fmt.str());
            SMTExpr term_cond = locals[thread_id][policy->goal_role->role_array_index].get_solver_var();
            variable term_guard = guard.createFrom();
            emit_assignment(term_guard, term_cond);
            guard = term_guard;
            SMTExpr assertion_cond = solver->createCondExpr(term_guard.get_solver_var(), zero, one);
            emit_assertion(assertion_cond);
        }

        void simulate_thread(int thread_id) {
    //        clean_fmt();
    //        fmt << "--------------- APPLICATION OF THREAD " << thread_id << " ------------";
    //        emit_comment(fmt.str());

            generate_updates(thread_id);

            int label_idx = 0;
            emit_comment("---------- IDLE ROUND REMOVED SINCE PC MAY BE GREATER THAN PC_MAX ---------");

            int i;
            emit_comment("---------- CAN ASSIGN SIMULATION ---------");
            emit_comment("---------- MERGED PER ROLE ---------");
            for (auto &&atom : policy->atoms()) {
                // printf("CA idx: %d, role: %s: count: %d\n", i, role_array[i], roles_ca_counts[i]);
                if (policy->per_role_can_assign_rule(atom).size() > 0) {
                    simulate_can_assigns_by_atom(thread_id, atom, label_idx++);
                }
            }

            emit_comment("---------- CAN REVOKE SIMULATION ---------");
            emit_comment("---------- MERGED PER ROLE ---------");
            for (auto &&atom : policy->atoms()) {
                // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
                if (policy->per_role_can_revoke_rule(atom).size() > 0) {
                    simulate_can_revokes_by_atom(thread_id, atom, label_idx++);
                }
            }

            generate_check(thread_id);
        }

        void assign_PCs(int thread_id, int round) {
            clean_fmt();
            fmt << "---------- ASSIGNING PC FOR THREAD " << thread_id << " ROUND " << round << " ---------";
            emit_comment(fmt.str());
            for (int step = 0; step < steps; step++) {
    //            variable nondet_res = createFrom(nondet_int);
    //            emitAssignment(nondet_res);
    //            nondet_int = nondet_res;
                // NONDET INT IS NOT REQUIRED SINCE ANY CREATED VARIABLE IS NONDET IF NOT CONSTRAINED
                variable npc_n = program_counters[step].createFrom();
    //            emitAssignment(npc_n);
                program_counters[step] = npc_n;
            }
        }

        void simulate_threads(int round) {
            for (int i = 0; i < threads_count; i++) {
                assign_PCs(i, round);
                simulate_thread(i);
            }
        }

        void generate_main(int rounds) {
            for (int r = 0; r < rounds; r++) {
                clean_fmt();
                fmt << "--------------- SIMULATION OF ROUND " << r << " ------------";
                emit_comment(fmt.str());
                simulate_threads(r);
            }
        }

        void create_final_assert() {
            auto aite = final_assertions.begin();
            SMTExpr assert_body = solver->createNotExpr(*aite);
            for (++aite; aite != final_assertions.end(); ++aite) {
                assert_body = solver->createOrExpr(assert_body, solver->createNotExpr((*aite)));
            }
            solver->assertLater(assert_body);
        }

        void generate_program(int rounds) {
            generate_zero_one_dummy();

            auto start = std::chrono::high_resolution_clock::now();

            initialize_var_counters();

            // TODO: this should be merged in initialize_var_counters to avoid NULL in counters
            init_PCs_guards_nondet();
            //Generate header with comments
            // generate_header(inputFile, rounds);


            generate_globals();
            generate_locals();

            if (use_tracks) {
                generate_thread_assigned_locals();
                assign_threads();
            }


            generate_main(rounds);


            auto end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            log->debug("------------ SMT GENERATED IN {} ms ------------", milliseconds.count());
            start = std::chrono::high_resolution_clock::now();

            // add_all_assignments();

            create_final_assert();


            end = std::chrono::high_resolution_clock::now();
            milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            log->debug("------------ SMT LOADED IN {} ms ------------", milliseconds.count());

        }

        bool solve_program() const {
            auto start = std::chrono::high_resolution_clock::now();

            if (Config::show_solver_statistics) {
                solver->print_statistics();
            }

            if (Config::dump_smt_formula != "") {
                solver->printContext(Config::dump_smt_formula);
                log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
            }

            SMTResult res = solver->solve();

            auto end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            log->debug("------------ SMT SOLVED IN {} ms ------------", milliseconds.count());

            switch (res) {
                case SMTResult::SAT:
                    log->debug("SAT\n");
                    return true;
                    break;
                case SMTResult::UNSAT:
                    log->debug("UNSAT\n");
                    return false;
                    break;
                case SMTResult::UNKNOWN:
                    log->warn("The status is unknown\n");
                    break;
                case SMTResult::ERROR:
                    log->error("Error in check_context");
                    throw std::runtime_error("BMC: Error in check_context");
                    break;
            }
            return false;
        }

        // void
        // free_stmts() {
        //     ssa_prog.clear();
        // }

        public:
        BMCTransformer(const std::shared_ptr<SMTFactory>& _solver,
                       const std::shared_ptr<arbac_policy>& _policy) :
            solver(_solver), policy(_policy) { }

        bool transform_2_bounded_smt(int rounds, int _steps, int wanted_threads_count) {
    //        solver->deep_clean();
            // solver = _solver;
            solver->deep_clean();

            steps = _steps;

            generate_admin_partitions();

            //Set the number of user to track
            if (wanted_threads_count < 1) {
                if (policy->users().size() <= globals_map.size() + 1) {
                    threads_count = (int) policy->users().size();
                    use_tracks = false;
                }
                else {
                    threads_count = (int) globals_map.size() + 1;
                    use_tracks = true;
                }
            }
            else {
                if ((int) policy->users().size() <= wanted_threads_count) {
                    std::stringstream fmt;
                    fmt << "Cannot spawn " << wanted_threads_count <<
                              " threads because are more than user count (" << policy->users().size() << ")";
                    log->error(fmt.str());
                    throw std::runtime_error(fmt.str());
                }
                else {
                    threads_count = wanted_threads_count;
                    use_tracks = true;
                }
            }

            generate_program(rounds);

            return solve_program();


            // free_stmts();

        }
    };

    bool arbac_to_smt_bmc(const std::shared_ptr<SMTFactory>& solver,
                          const std::shared_ptr<arbac_policy>& policy,
                          int steps,
                          int rounds,
                          int wanted_threads_count) {

        log->debug("\n\nPERFORMING BMC ON POLICY...\n");

        // Checking if target is already assigned at the beginning
        for (auto &&conf : policy->unique_configurations()) {
            if (contains(conf->config(), policy->goal_role)) {
                log->info("Target role is assignable assigned to user: {} in the initial configuration!", conf->name);
                log->info("Target role is reachable");
                return true;
            }
        }

        // Checking if target is not assignable
        if (policy->per_role_can_assign_rule(policy->goal_role).size() < 1) {
            log->info("Target role is not assignable!");
            log->info("Target role is not reachable");
            return false;
        }

        if (rounds < 1) {
            log->error("Cannot simulate a number of rounds < 1");
            throw std::runtime_error("Cannot simulate a number of rounds < 1");
        }
        if (steps < 1) {
            log->error("Cannot simulate a number of steps < 1");
            throw std::runtime_error("Cannot simulate a number of steps < 1");
        }

        BMCTransformer core(solver, policy);
        bool ret = core.transform_2_bounded_smt(rounds, steps, wanted_threads_count);

        if (ret) {
            log->info("Target role is reachable");
        }
        else {
            log->info("Target role may not be reachable");
        }

        return ret;
    }

}
