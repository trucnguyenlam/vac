//#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <memory>

#include "Logics.h"
#include "BMC_Struct.h"
#include "ARBAC_to_SMT_BMC.h"
#include "SMT.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "Policy.h"

#include <chrono>

// #include "Templated.h"
// #include "dummy_esbmc.h"

namespace SMT {

//    using std::vector;
//    using std::shared_ptr;
//    using std::stringstream;
//    using std::string;

    template <typename TVar, typename TExpr>
    class BMCTransformer {
    private:

        typedef generic_variable<TVar, TExpr> variable;

        int rounds;
        int threads_count;
        int use_tracks;
        int pc_size;
        int thread_pc_size;

        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

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
        std::vector<variable> round_saves;
        std::vector<std::vector<variable>> locals;
        variable guard;
        variable nondet_bool;
        variable nondet_int;
        variable thread_assignment_nondet_int;
        int steps;

        // vector<SSA::Stmt> out_stmts;

        std::shared_ptr<arbac_policy> policy;

        TExpr zero;
        TExpr one;

        std::vector<TExpr> final_assertions;

        std::vector<Expr> per_rule_admin_expr;
        std::map<Expr, variable> globals_map;

        // #endif

        inline void emit_assignment(const variable& variable, TExpr value) {
            TExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
            solver->assertLater(assign);
        }

        inline void emit_assumption(TExpr expr) {
            solver->assertLater(expr);
        }

        inline void emit_assertion(TExpr assertion) {
            final_assertions.push_back(assertion);
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

            round_saves = std::vector<variable>((unsigned long) rounds);
            for (int i = 0; i < rounds; ++i) {
                round_saves[i] = dummy_var;
            }

            pc_size = get_pc_count();
            thread_pc_size = bits_count(threads_count);
        }

        void emitComment(const std::string& comment) {
            // ssa_prog.addComment(createComment(comment));
        }

        bool equivalent_exprs(const Expr& e1, const Expr& e2) {
            solver->clean();

            std::vector<std::shared_ptr<TVar>> var_vec((ulong) policy->atom_count());
            TExpr se1 = generateSMTFunction2(solver, e1, var_vec, "eq");
            TExpr se2 = generateSMTFunction2(solver, e2, var_vec, "eq");

            // e1 /\ not e2
            TExpr e1_not_e2 = solver->createAndExpr(se1,
                                                    solver->createNotExpr(se2));
            // not e1 /\ e2
            TExpr not_e1_e2 = solver->createAndExpr(solver->createNotExpr(se1),
                                                    se2);

            // (e1 /\ not e2) \/ (not e1 /\ e2)
            TExpr final = solver->createOrExpr(e1_not_e2,
                                               not_e1_e2);

            solver->assertNow(final);

            bool res = solver->solve() == UNSAT;

            return res;
        }

        const std::list<std::list<rulep>> partition_equivalent(const std::list<rulep>& targetings) {
            if (targetings.size() == 0) {
                return std::list<std::list<rulep>>();
            }
            auto ite = targetings.begin();
            std::list<std::list<rulep>> partitions;
            partitions.push_back(std::list<rulep>());
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
                std::string glob_name = adm->literals().size() > 0 ?
                                        (*adm->literals().begin()).lock()->name :
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
            for (int i = 0; i < rounds; ++i) {
                round_saves[i] = variable("save_" + std::to_string(i), -2, threads_count * policy->atom_count(), solver.get(), BIT_VECTOR);
            }
            // emitAssignment(guard);
            // emitAssignment(nondet_bool);
            // emitAssignment(nondet_int);
        }

        std::vector<std::shared_ptr<TExpr>> user_to_lookup_vect(const userp& user) {
            std::vector<std::shared_ptr<TExpr>> vect((ulong) policy->atom_count());
            for (int i = 0; i < policy->atom_count(); ++i) {
                vect[i] = std::make_shared<TExpr>(solver->createFalse());
            }
            for (auto &&atom : user->config()) {
                vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createTrue());
            }

            return vect;
        }

        void generate_globals() {
            emitComment("---------- INIT GLOBAL VARIABLES ---------");
            for (auto &&global_pair : globals_map) {
                Expr adm_expr = global_pair.first;
                variable global_var = global_pair.second;
                TExpr global_value = solver->createFalse();
                for (auto &&user : policy->unique_configurations()) {
                    std::vector<std::shared_ptr<TVar>> var_vect = user_to_lookup_vect(user);
                    TExpr sadm_expr = generateSMTFunction2(solver, adm_expr, var_vect, user->name);
                    //FIXME: added just for debug purposes
                    TVar user_name = solver->createBoolVar(user->name);
                    TExpr final_expr = solver->createAndExpr(user_name, sadm_expr);
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
            emitComment(fmt.str());
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
            emitComment("---------- THREADS LOCAL VARIABLES ---------");
            for (int i = 0; i < threads_count; ++i) {
                generate_thread_locals(i);
            }
        }

        void generate_thread_assigned_locals() {
            emitComment("--------------- THREAD ASSIGNMENT LOCAL VARIABLES ------------");
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
            emitComment(fmt.str());

            TExpr con_e = solver->createBVConst(thread_id, thread_pc_size);
            TExpr eq_e = solver->createEqExpr(thread_assignment_nondet_int.get_solver_var(), con_e);
            TExpr not_e = solver->createNotExpr(thread_assigneds[thread_id].get_solver_var());
            TExpr if_guard = solver->createAndExpr(eq_e,
                                                   not_e);
            variable n_guard = guard.createFrom();
            emit_assignment(n_guard, if_guard);
            guard = n_guard;

            TExpr ass_val = solver->createCondExpr(guard.get_solver_var(), one, thread_assigneds[thread_id].get_solver_var());

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
                TExpr loc_val = solver->createCondExpr(guard.get_solver_var(), one, locals[thread_id][atom->role_array_index].get_solver_var());
                variable loc = locals[thread_id][atom->role_array_index].createFrom();
                emit_assignment(loc, loc_val);
                locals[thread_id][atom->role_array_index] = loc;
            }
        }

        void assign_thread_to_user(int user_id) {
            clean_fmt();
            fmt << "--------------- CONFIGURATION OF USER " << user_id << " (" << policy->users(user_id) << ") ------------";
            emitComment(fmt.str());

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

            TExpr assume_body = thread_assigneds[0].get_solver_var();
            for (int i = 1; i < threads_count; i++) {
                assume_body = solver->createAndExpr(thread_assigneds[i].get_solver_var(), assume_body);
            }
            emit_assumption(assume_body);
        }

        void generate_updates(int thread_id) {
            emitComment("---- GLOBAL ROLE CONSISTENCY UPDATE ----");
            for (auto &&global_pair :globals_map) {
                Expr global_expr = global_pair.first;
                variable global_var = global_pair.second;
                for (auto &&canRevokeRule : policy->can_revoke_rules()) {
                    if (contains_ptr(global_expr->literals(), canRevokeRule->target)) {
                        TExpr respects = generateSMTFunction2(solver, global_expr, locals[thread_id], std::to_string(thread_id));
                        TExpr value = solver->createOrExpr(global_var.get_solver_var(), respects);
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

        TExpr generate_from_prec(int thread_id, const Expr &precond) {

            TExpr res = generateSMTFunction2(solver, precond, locals[thread_id], "");

            return res;
        }

        TExpr generate_rule_cond(int thread_id, const rulep& rule) {
            int j;
            // TExpr cond = -1;
            // Admin role must be available
            //Could be dfferent even if it has the same configurations
            Expr globals_map_key = per_rule_admin_expr[rule->original_idx];

            TExpr admin_cond = globals_map[globals_map_key].get_solver_var();

            // Precondition must be satisfied
            TExpr prec_cond = generate_from_prec(thread_id, rule->prec);

            // Optional this user is not in this target role yet
            TExpr not_ass =
                    rule->is_ca ?
                    solver->createNotExpr(locals[thread_id][rule->target->role_array_index].get_solver_var()) :
                    locals[thread_id][rule->target->role_array_index].get_solver_var();
            TExpr final_cond = solver->createAndExpr(solver->createAndExpr(admin_cond, prec_cond), not_ass);
            return final_cond;
        }

        TExpr generate_PC_cond(int rule_id) {
            TExpr cond = solver->createEqExpr(program_counters[0].get_solver_var(),
                                              solver->createBVConst(rule_id, pc_size));
            for (int i = 1; i < steps; i++) {
                cond = solver->createOrExpr(cond,
                                            solver->createEqExpr(program_counters[i].get_solver_var(),
                                                                 solver->createBVConst(rule_id, pc_size)));
            }
            return cond;
        }

        void simulate_can_assigns_by_atom(int thread_id, const atom& target, int rule_id) {
            // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
            int i = 0;
            TExpr pc_cond, ca_cond, all_cond;
            // TExpr pc_cond = -1, ca_cond = -1, all_cond = -1;
            //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
            clean_fmt();
            fmt << "--- ASSIGNMENT RULES FOR ROLE " << *target << " ---";
            emitComment(fmt.str());

            if (policy->per_role_can_assign_rule(target).size() < 1) {
                clean_fmt();
                log->warn("--- ATOM {} IS NOT ASSIGNABLE... SHOULD CRASH ---", target->to_string());
                //            emitComment(msg);
                return;
            }

            pc_cond = generate_PC_cond(rule_id);

            //        emit_ca_comment(per_role_ca_indexes[target_role_index][0]);

            ca_cond = solver->createFalse();

            for (auto &&rule : policy->per_role_can_assign_rule(target)) {
                TExpr ith_cond = generate_rule_cond(thread_id, rule);
                //            emit_ca_comment(ca_idx);
                ca_cond = solver->createOrExpr(ca_cond, ith_cond);
            }

            all_cond = solver->createAndExpr(pc_cond, ca_cond);
            variable ca_guard = guard.createFrom();
            emit_assignment(ca_guard, all_cond);
            guard = ca_guard;

            // UPDATE LOCALS FIRST
            TExpr nlval = solver->createCondExpr(ca_guard.get_solver_var(), one, locals[thread_id][target->role_array_index].get_solver_var());
            variable nloc = locals[thread_id][target->role_array_index].createFrom();
            emit_assignment(nloc, nlval);
            locals[thread_id][target->role_array_index] = nloc;

            // Recompute globals according to updated locals (if necessary)
            for (auto &&glob_pair : globals_map) {
                Expr adm_expr = glob_pair.first;
                variable glob_var = glob_pair.second;
                if (contains_ptr(adm_expr->literals(), target)) {
                    TExpr ngval = generateSMTFunction2(solver, adm_expr, locals[thread_id], std::to_string(thread_id));
                    TExpr n_cond_gval = solver->createCondExpr(ca_guard.get_solver_var(), ngval, glob_var.get_solver_var());
                    variable nglob = glob_var.createFrom();
                    emit_assignment(nglob, n_cond_gval);
                    //FIXME changing a collection while iterating it is considered harmfull
                    globals_map[adm_expr] = nglob;
                }
            }
        }

        void simulate_can_revokes_by_atom(int thread_id, const atom &target, int rule_id) {
            // Precondition: exists always at least one CR that assign the role i.e.: roles_cr_counts[target_role_index] > 1
            int i = 0;
            TExpr pc_cond, cr_cond, all_cond;
            // TExpr pc_cond = -1, cr_cond = -1, all_cond = -1;
            //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
            clean_fmt();
            fmt << "--- REVOKE RULES FOR ROLE " << *target << " ---";
            emitComment(fmt.str());

            if (policy->per_role_can_revoke_rule(target).size() < 1) {
                log->warn("--- ROLE {} IS NOT REVOKABLE... SHOULD CRASH ---", target->to_string());
                //            string msg = fmt.str();
                //            emitComment(msg);
                //            fprintf(stderr, "%s", msg.c_str());
                return;
            }

            pc_cond = generate_PC_cond(rule_id);

            //        emit_cr_comment(per_role_cr_indexes[target_role_index][0]);

            cr_cond = solver->createFalse();

            for (auto &&rule : policy->per_role_can_revoke_rule(target)) {
                TExpr ith_cond = generate_rule_cond(thread_id, rule);
                //            emit_cr_comment(cr_idx);
                cr_cond = solver->createOrExpr(cr_cond, ith_cond);
            }

            all_cond = solver->createAndExpr(pc_cond, cr_cond);
            variable cr_guard = guard.createFrom();
            emit_assignment(cr_guard, all_cond);
            guard = cr_guard;

            // UPDATE LOCALS FIRST
            TExpr nlval = solver->createCondExpr(cr_guard.get_solver_var(), zero, locals[thread_id][target->role_array_index].get_solver_var());
            variable nloc = locals[thread_id][target->role_array_index].createFrom();
            emit_assignment(nloc, nlval);
            locals[thread_id][target->role_array_index] = nloc;

            // Recompute globals according to updated locals (if necessary)
            for (auto &&global_pair : globals_map) {
                Expr glob_expr = global_pair.first;
                variable glob_var = global_pair.second;
                if (contains_ptr(glob_expr->literals(), target)) {
                    TExpr ngval = generateSMTFunction2(solver, glob_expr, locals[thread_id], std::to_string(thread_id));
                    TExpr n_cond_gval = solver->createCondExpr(cr_guard.get_solver_var(), ngval, glob_var.get_solver_var());
                    variable nglob_var = glob_var.createFrom();
                    emit_assignment(nglob_var, n_cond_gval);
                    //FIXME changing a collection while iterating it is considered harmfull
                    globals_map[glob_expr] = nglob_var;

                }
            }
        }

        void save_state(int round) {
            //SAVING SNAPSHOT OF CURRENT THREAD
            variable save_var = round_saves[round];
            TExpr saved = solver->createTrue();
            for (int i = 0; i < threads_count; ++i) {
                std::vector<variable> thread_locals = locals[i];
                for (int j = 0; j < policy->atom_count(); ++j) {
                    ulong index = (ulong) (i * policy->atom_count()) + j;
                    variable atom_status = thread_locals[j];
                    TExpr value = atom_status.get_solver_var();
                    TExpr set_op = solver->createBitSet(save_var.get_solver_var(), index, value);
                    saved = solver->createAndExpr(saved,
                                                  set_op);
                }
            }
            solver->assertLater(saved);
        }

        void generate_check() {
            std::list<TExpr> savestates;
            for (auto &&round_save : round_saves) {
                savestates.push_back(round_save.get_solver_var());
            }
            TExpr term_cond = solver->createDistinct(savestates);

            solver->assertLater(term_cond);
        }

        void simulate_thread(int thread_id) {
            //        clean_fmt();
            //        fmt << "--------------- APPLICATION OF THREAD " << thread_id << " ------------";
            //        emitComment(fmt.str());

            generate_updates(thread_id);

            int label_idx = 0;
            emitComment("---------- IDLE ROUND REMOVED SINCE PC MAY BE GREATER THAN PC_MAX ---------");

            int i;
            emitComment("---------- CAN ASSIGN SIMULATION ---------");
            emitComment("---------- MERGED PER ROLE ---------");
            for (auto &&atom : policy->atoms()) {
                // printf("CA idx: %d, role: %s: count: %d\n", i, role_array[i], roles_ca_counts[i]);
                if (policy->per_role_can_assign_rule(atom).size() > 0) {
                    simulate_can_assigns_by_atom(thread_id, atom, label_idx++);
                }
            }

            emitComment("---------- CAN REVOKE SIMULATION ---------");
            emitComment("---------- MERGED PER ROLE ---------");
            for (auto &&atom : policy->atoms()) {
                // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
                if (policy->per_role_can_revoke_rule(atom).size() > 0) {
                    simulate_can_revokes_by_atom(thread_id, atom, label_idx++);
                }
            }
        }

        void assign_PCs(int thread_id, int round) {
            clean_fmt();
            fmt << "---------- ASSIGNING PC FOR THREAD " << thread_id << " ROUND " << round << " ---------";
            emitComment(fmt.str());
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
                emitComment(fmt.str());
                simulate_threads(r);
                save_state(r);
            }
            generate_check();
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

//            create_final_assert();


            end = std::chrono::high_resolution_clock::now();
            milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            log->debug("------------ SMT LOADED IN {} ms ------------", milliseconds.count());

        }

        bool solve_program() const {
            auto start = std::chrono::high_resolution_clock::now();

            SMTResult res = solver->solve();

            if (Config::dump_smt_formula != "") {
                solver->printContext(Config::dump_smt_formula);
                log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
            }

            auto end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            log->debug("------------ SMT SOLVED IN {} ms ------------", milliseconds.count());

            switch (res) {
                case SAT:
                    log->debug("SAT\n");
                    return true;
                    break;
                case UNSAT:
                    log->debug("UNSAT\n");
                    return false;
                    break;
                case UNKNOWN:
                    log->warn("The status is unknown\n");
                    break;
                case ERROR:
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
        BMCTransformer(const std::shared_ptr<SMTFactory<TVar, TExpr>>& _solver,
                       const std::shared_ptr<arbac_policy>& _policy,
                       int _rounds) :
                rounds(_rounds), solver(_solver), policy(_policy) { }

        bool transform_2_bounded_smt(int _steps, int wanted_threads_count) {
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

    template <typename TVar, typename TExpr>
    bool arbac_to_smt_bmc(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
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

        BMCTransformer<TVar, TExpr> core(solver, policy, rounds);
        bool ret = core.transform_2_bounded_smt(steps, wanted_threads_count);

        if (ret) {
            log->info("Target role is reachable");
        }
        else {
            log->info("Target role may not be reachable");
        }

        return ret;
    }

    template bool arbac_to_smt_bmc<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                                   const std::shared_ptr<arbac_policy>& policy,
                                                   int steps,
                                                   int rounds,
                                                   int wanted_threads_count);

    template bool arbac_to_smt_bmc<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                               const std::shared_ptr<arbac_policy>& policy,
                                               int steps,
                                               int rounds,
                                               int wanted_threads_count);

}