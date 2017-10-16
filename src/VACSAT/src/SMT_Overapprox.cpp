//#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <memory>

#include "SMT.h"
#include "SMT_Analysis_functions.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "Logics.h"
#include "SMT_BMC_Struct.h"
#include "Policy.h"
#include "SMTSolvers/boolector.h"

#include <chrono>
#include <stack>
#include <mathsat.h>

namespace SMT {


    static int ovr_porr = 0;

template <typename TVar, typename TExpr>
class OverapproxTransformer {
    private:
    typedef generic_variable<TVar, TExpr> variable;

    static int get_pc_size(std::shared_ptr<arbac_policy> policy, const std::set<Atomp>& atoms) {
        int count = 1;

        for (auto &&atom : atoms) {
            if (SMT::iterable_exists(policy->can_assign_rules().begin(), policy->can_assign_rules().end(),
                                     [&](const rulep rule) { return rule->target == atom; } )) {
                count++;
            }
            if (SMT::iterable_exists(policy->can_revoke_rules().begin(), policy->can_revoke_rules().end(),
                                     [&](const rulep rule) { return rule->target == atom; } )) {
                count++;
            }
        }
        int bits = bits_count(count);
        return bits;
    }

    struct overapprox_status;
    class variables {
        friend struct overapprox_status;
    private:
        variable guard;
    public:
        /*const*/ std::vector<variable> role_vars;
        /*const*/ std::vector<variable> core_value_true;
        /*const*/ std::vector<variable> core_value_false;
        /*const*/ std::vector<variable> core_sets;

        variable program_counter;
        variable skip;
        variable nondet_bool;

        variables(std::shared_ptr<arbac_policy> policy, SMTFactory<TVar, TExpr>* solver) :
                role_vars (std::vector<variable>((unsigned long) policy->atom_count())),
                core_value_true (std::vector<variable>((unsigned long) policy->atom_count())),
                core_value_false (std::vector<variable>((unsigned long) policy->atom_count())),
                core_sets (std::vector<variable>((unsigned long) policy->atom_count())) {
            program_counter = variable("pc", -1, 1, solver, BIT_VECTOR);

            nondet_bool = variable("nondet_bool", -1, 1, solver, BOOLEAN);
            // fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
            skip = variable("skip", 0, 1, solver, BOOLEAN);

            guard = variable("guard", 0, 1, solver, BOOLEAN);

            for (int i = 0; i < policy->atom_count(); i++) {
                role_vars[i] = variable(policy->atoms()[i]->name.c_str(), 0, 1, solver, BOOLEAN);
                // fprintf(outputFile, "/*---------- CHECKS ---------*/\n");
                core_sets[i] = variable(("set_" + policy->atoms()[i]->name).c_str(), 0, 1, solver, BOOLEAN);
                // fprintf(outputFile, "/*---------- VALUE TRUE CHECKS ---------*/\n");
                core_value_true[i] = variable(("value_true_" + policy->atoms()[i]->name).c_str(), 0, 1, solver, BOOLEAN);
                // fprintf(outputFile, "/*---------- VALUE FALSE CHECKS ---------*/\n");
                core_value_false[i] = variable(("value_false_" + policy->atoms()[i]->name).c_str(), 0, 1, solver, BOOLEAN);
            }
        }
    };

    struct overapprox_status {
        friend class variables;
//        std::vector<variable> actual_core_value_true;
//        std::vector<variable> actual_core_value_false;
//        std::vector<variable> actual_core_sets;
        SMTFactory<TVar, TExpr>* solver;
        std::shared_ptr<arbac_policy> policy;
        /*--- VALUES ---*/
        variables state;
        std::set<rulep> target_rules;
        Expr target_expr;
        std::vector<bool> tracked_roles;
        std::vector<bool> core_roles;
        int tracked_roles_size;
        int core_roles_size;
        int pc_size;
        int deep;

        /*--- SAVED ---*/
        std::stack<variables> saved_state;
        std::stack<std::set<rulep>> saved_target_rules;
        std::stack<Expr> saved_target_expr;
        std::stack<std::vector<bool>> saved_tracked_roles;
        std::stack<std::vector<bool>> saved_core_roles;
        std::stack<int> saved_tracked_roles_size;
        std::stack<int> saved_core_roles_size;
        std::stack<int> saved_pc_size;
        std::stack<int> saved_deep;

        void save_all() {
            // cloning and saving...
            variables old_state = state;
            saved_state.push(old_state);
            std::set<rulep> old_target_rules = target_rules;
            saved_target_rules.push(old_target_rules);
            Expr old_target_expr = target_expr;
            saved_target_expr.push(old_target_expr);
            std::vector<bool> old_tracked_roles = tracked_roles;
            saved_tracked_roles.push(old_tracked_roles);
            std::vector<bool> old_core_roles = core_roles;
            saved_core_roles.push(old_core_roles);
            int old_tracked_roles_size = tracked_roles_size;
            saved_tracked_roles_size.push(old_tracked_roles_size);
            int old_core_roles_size = core_roles_size;
            saved_core_roles_size.push(old_core_roles_size);
            int old_pc_size = pc_size;
            saved_pc_size.push(old_pc_size);
            int old_deep = deep;
            saved_deep.push(old_deep);
        }

        void restore_all_but_state() {
            // restoring and popping all but state...
            target_rules = saved_target_rules.top();
            saved_target_rules.pop();
            target_expr = saved_target_expr.top();
            saved_target_expr.pop();
            tracked_roles = saved_tracked_roles.top();
            saved_tracked_roles.pop();
            core_roles = saved_core_roles.top();
            saved_core_roles.pop();
            tracked_roles_size = saved_tracked_roles_size.top();
            saved_tracked_roles_size.pop();
            core_roles_size = saved_core_roles_size.top();
            saved_core_roles_size.pop();
            pc_size = saved_pc_size.top();
            saved_pc_size.pop();
            deep = saved_deep.top();
            saved_deep.pop();
        }

        void update_conditionally() {
            //FIXME: really not necessary?
            for (auto &&item : state.core_value_false) {

            }
        }

        void restore_state() {
            variables old_state = saved_state.top();

            //RESTORE GUARDS
            TVar old_guard = old_state.guard.get_solver_var();
            TVar frame_guard = state.guard.get_solver_var();
            variable new_guard = state.guard.createFrom();
//            this->emit_assignment(new_guard, old_guard);
            solver->assertLater(solver->createEqExpr(new_guard.get_solver_var(), old_guard));
            state.guard = new_guard;

            // RESTORING OLD STEP SET STATE
            for (int i = 0; i < core_roles.size(); ++i) {
                bool c_status = core_roles[i];
                if (!c_status) {
                    //UNTRACKED: SET VARIABLE TO FALSE (NEXT USAGE WILL FIND UNSET!)
                    state.core_sets[i] = state.core_sets[i].createFrom();
                    this->emit_assignment(state.core_sets[i], solver->createFalse());
                } else {
                    //TRACKED: RESTORE OLD VALUE
                    TVar old_set_state = old_state.core_sets[i].get_solver_var();
                    variable new_set_state = state.core_sets[i].createFrom();
                    this->emit_assignment(new_set_state, old_set_state);
                    state.core_sets[i] = new_set_state;
                }
            }

            update_program_counter();
            //RESTORE OLD SKIP
            TVar old_skip = old_state.skip.get_solver_var();
            variable new_skip = state.skip.createFrom();
            this->emit_assignment(new_skip, old_skip);
            state.skip = new_skip;

            //UPDATING TRUE FALSE MEMORY
            for (int i = 0; i < policy->atom_count(); ++i) {
                variable new_true = state.core_value_true[i].createFrom();
                variable old_true = old_state.core_value_true[i];
                TExpr new_true_value = solver->createOrExpr(old_true.get_solver_var(), state.core_value_true[i].get_solver_var());
                emit_assignment(new_true, new_true_value);
                state.core_value_true[i] = new_true;

                variable new_false = state.core_value_false[i].createFrom();
                variable old_false = old_state.core_value_false[i];
                TExpr new_false_value = solver->createOrExpr(old_false.get_solver_var(), state.core_value_false[i].get_solver_var());
                emit_assignment(new_false, new_false_value);
                state.core_value_false[i] = new_false;
            }

            //MAKE CONSISTENT COPYING ALL VALUE WITH ITE ON GUARD
            for (int i = 0; i < policy->atom_count(); ++i) {
                // role_vars
                variable sync_role_var = state.role_vars[i].createFrom();
                TExpr cond_sync_role_var = solver->createCondExpr(frame_guard,
                                                                  state.role_vars[i].get_solver_var(),
                                                                  old_state.role_vars[i].get_solver_var());
                emit_assignment(sync_role_var, cond_sync_role_var);
                state.role_vars[i] = sync_role_var;
                /*// core_value_true
                variable sync_core_value_true = state.core_value_true[i].createFrom();
                TExpr cond_sync_core_value_true = solver->createCondExpr(frame_guard,
                                                                         state.core_value_true[i].get_solver_var(),
                                                                         old_state.core_value_true[i].get_solver_var());
                emit_assignment(sync_core_value_true, cond_sync_core_value_true);
                state.core_value_true[i] = sync_core_value_true;
                // core_value_false
                variable sync_core_value_false = state.core_value_false[i].createFrom();
                TExpr cond_sync_core_value_false = solver->createCondExpr(frame_guard,
                                                                          state.core_value_false[i].get_solver_var(),
                                                                          old_state.core_value_false[i].get_solver_var());
                emit_assignment(sync_core_value_false, cond_sync_core_value_false);
                state.core_value_false[i] = sync_core_value_false;
                // core_sets
                variable sync_core_set = state.core_sets[i].createFrom();
                TExpr cond_sync_core_set = solver->createCondExpr(frame_guard,
                                                                  state.core_sets[i].get_solver_var(),
                                                                  old_state.core_sets[i].get_solver_var());
                emit_assignment(sync_core_set, cond_sync_core_set);
                state.core_sets[i] = sync_core_set;*/
            }


            saved_state.pop();
        }

        void update_tracked_core_role_array_set_pc_size(const Expr &target_expr) {
            tracked_roles_size = 0;
            for (auto &&tracked_i : policy->atoms()) {
                if (contains(target_expr->atoms(), tracked_i)) {
                    tracked_roles_size++;
                    tracked_roles[tracked_i->role_array_index] = true;
                } else {
                    tracked_roles[tracked_i->role_array_index] = false;
                }
            }

            for (auto &&core_i : target_expr->atoms()) {
                if (core_roles[core_i->role_array_index] == false) {
                    core_roles_size++;
                }
                core_roles[core_i->role_array_index] = true;
            }

            // let f(r) = 0 if not assignable nor revokable, 2 if both assignable and revokable, 1 otherwise  \sum_{r \in core_roles}(f(r))
//        std::cout << "################################################################################################" << std::endl;
//        std::cout << "Working on: " << *target_rule << std::endl;
//        std::cout << "Expr:       " << *target_expr << std::endl;
//        std::cout << "Minimal:    " << get_pc_size(cores) << std::endl;
//        std::cout << "Overapprox: " << numBits((core_roles_size * 2) + 1) << std::endl;
//        std::cout << "################################################################################################" << std::endl;

            pc_size = get_pc_size(policy, target_expr->atoms());

        }

        void update_program_counter() {
            if (pc_size == 0) {
                log->critical("pc is zero in overapprox...");
//                state.program_counter = variable(state.program_counter.name,
//                                                 state.program_counter.idx + 1,
//                                                 pc_size + 1,
//                                                 solver,
//                                                 BIT_VECTOR);
                throw std::runtime_error("pc is zero in overapprox...");
            } else {
                state.program_counter = variable(state.program_counter.name,
                                                 state.program_counter.idx + 1,
                                                 pc_size,
                                                 solver,
                                                 BIT_VECTOR);
            }
        }
        
        void clean_true_false_memory() {
            for (int i = 0; i < policy->atom_count(); ++i) {
                variable new_core_value_true = state.core_value_true[i].createFrom();
                this->emit_assignment(new_core_value_true, solver->createFalse());
                state.core_value_true[i] = new_core_value_true;

                variable new_core_value_false = state.core_value_false[i].createFrom();
                this->emit_assignment(new_core_value_false, solver->createFalse());
                state.core_value_false[i] = new_core_value_false;
            }
        }

        void init_new_frame(const Expr& _target_expr, const std::set<rulep>& _target_rule) {
            deep = deep - 1;
            target_rules.insert(_target_rule.begin(), _target_rule.end());
            target_expr = _target_expr;
            update_tracked_core_role_array_set_pc_size(target_expr);
            update_program_counter();
            clean_true_false_memory();
        }

        void set_guard(TExpr guard) {
            variable old_guard = state.guard;
            variable new_guard = old_guard.createFrom();
            TExpr new_val = solver->createAndExpr(old_guard.get_solver_var(), guard);
            solver->assertLater(solver->createEqExpr(new_guard.get_solver_var(), new_val));
            state.guard = new_guard;
        }

        void internal_init() {
            TExpr _false = solver->createFalse();
            TExpr _true = solver->createTrue();
            for (int i = 0; i < policy->atom_count(); ++i) {
                TExpr init_core_value_true = solver->createEqExpr(state.core_value_true[i].get_solver_var(), _false);
                solver->assertLater(init_core_value_true);
                TExpr init_core_value_false = solver->createEqExpr(state.core_value_false[i].get_solver_var(), _false);
                solver->assertLater(init_core_value_false);
                TExpr init_core_sets = solver->createEqExpr(state.core_sets[i].get_solver_var(), _false);
                solver->assertLater(init_core_sets);
            }

            TExpr init_skip = solver->createEqExpr(state.skip.get_solver_var(), _false);
            solver->assertLater(init_skip);
            TExpr init_guard = solver->createEqExpr(state.guard.get_solver_var(), _true);
            solver->assertLater(init_guard);
        }

    public:

        overapprox_status(SMTFactory<TExpr, TVar>* _solver, std::shared_ptr<arbac_policy> _policy, int _deep) :
                solver(_solver),
                policy(_policy),
                state(policy, solver),
                target_rules(std::set<rulep>()),
                target_expr(nullptr),
                tracked_roles((ulong) policy->atom_count()),
                core_roles((ulong) policy->atom_count()),
                tracked_roles_size(0),
                core_roles_size(0),
                pc_size(1),
                deep(_deep) {
            for (int i = 0; i < policy->atom_count(); ++i) {
                core_roles[i] = false;
            }
            internal_init();
        }

        inline void emit_assignment(const variable& var, const TVar& value) {
            TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
            //TODO: maybe put a XOR instead of OR
            TExpr guarded_ass = solver->createOrExpr(solver->createNotExpr(state.guard.get_solver_var()), ass);
            solver->assertLater(guarded_ass);

        }

        inline void emit_assumption(const TExpr& value) {
            TExpr guarded_ass = solver->createOrExpr(solver->createNotExpr(state.guard.get_solver_var()), value);
            solver->assertLater(guarded_ass);
        }

        inline void emit_comment(const std::string& comment) {
//            //Working only in Z3
//            solver->assertNow(solver->createBoolVar(comment));
//            log->critical("Emitting comment...");
        }

        void push(Expr _target_expr, std::set<rulep> _target_rule, TExpr guard) {
            log->critical(++ovr_porr);
            log->warn("Pushing {}", *_target_expr);
            emit_comment("PUSH" + _target_expr->to_string());
            save_all();
            set_guard(guard);
            init_new_frame(_target_expr, _target_rule);
        }

        void pop() {
//            log->warn("Popping {}", *target_expr);
            Expr tgt = target_expr;
            restore_all_but_state();
            restore_state();
            emit_comment("POP" + tgt->to_string());
        }

    };


    std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
    std::shared_ptr<arbac_policy> policy;


    overapprox_status state;

    TExpr zero;
    TExpr one;


    inline void emit_assignment(const variable& var, const TExpr& value) {
//        TExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
        state.emit_assignment(var, value);
    }

    inline void emit_assumption(const TExpr& expr) {
        state.emit_assumption(expr);
    }

    inline void emit_comment(std::string comment) {
        state.emit_comment(comment);
    }


    void init_threads() {
        TExpr init = solver->createFalse();
        for (auto &&conf :policy->unique_configurations()) {
            TExpr conf_expr = solver->createTrue();
            for (auto &&atom :policy->atoms()) {
                bool has = contains(conf->config(), atom);
                conf_expr = solver->createAndExpr(conf_expr,
                                                  solver->createEqExpr(state.state.role_vars[atom->role_array_index].get_solver_var(),
                                                                       has ? one : zero));
            }
            init = solver->createOrExpr(init, conf_expr);
        }
        solver->assertLater(init);
    }

    TExpr generate_if_SKIP_PC(int pc) {
        // fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
        return solver->createAndExpr(solver->createNotExpr(state.state.skip.get_solver_var()),
                                     solver->createEqExpr(state.state.program_counter.get_solver_var(),
                                                          solver->createBVConst(pc, state.pc_size)));
    }

    TExpr generate_from_prec(const Expr &precond) {
//        std::shared_ptr<TVar>* array = get_t_array(precond->literals());

//        if (log) {
//            target_rule->print();
//            for (int i = 0; i < policy->atom_count(); ++i) {
//                std::cout << role_vars[i] << "; ";
//            }
//            std::cout << std::endl << std::endl;
//        }

        TExpr res = generateSMTFunction(solver, precond, state.state.role_vars, "");

//        delete[] array;
//        std::cout << "\t" << res << std::endl;
//        for (auto ite = map.begin(); ite != map.end(); ++ite) {
//            std::cout << ite->first << ": " << ite->second << std::endl;
//        }
        return res;
    }

    TExpr generate_CA_cond(const Expr& ca_precond) {
        return generate_from_prec(ca_precond);
    }

    TExpr generate_CR_cond(const Expr& cr_precond) {
        return generate_from_prec(cr_precond);
    }

    TExpr get_assignment_cond_by_role(const atomp& target_role, int label_index) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        TExpr if_prelude = generate_if_SKIP_PC(label_index);
        Expr ca_expr;
        if (policy->per_role_can_assign_rule(target_role).size() < 1) {
            ca_expr = createConstantFalse();
        } else {
            policy->per_role_can_assign_rule(target_role);
            auto ite = policy->per_role_can_assign_rule(target_role).begin();
            ca_expr = (*ite)->prec;
            for (++ite; ite != policy->per_role_can_assign_rule(target_role).end(); ++ite) {
                rulep rule = *ite;
                if (contains(state.target_rules, rule)) {
                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                    continue;
                }
                // print_ca_comment(outputFile, ca_idx);
                ca_expr = createOrExpr(ca_expr, rule->prec);
                // fprintf(outputFile, "        ||\n");
            }
        }

        if (state.deep > 0) {
            for (auto &&ca :policy->per_role_can_assign_rule(target_role)) {
                log->warn("pushing {} ca: {}", state.deep, *ca);
            }
            state.push(ca_expr, state.target_rules, if_prelude);
            generate_main();
            state.pop();
        }
        TExpr ca_guards = generate_CA_cond(ca_expr);

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(state.state.core_sets[target_role->role_array_index].get_solver_var());
        TExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, ca_guards), not_set);
        return cond;
    }

    TExpr get_revoke_cond_by_role(const atomp& target_role, int label_index) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        TExpr if_prelude = generate_if_SKIP_PC(label_index);
        Expr cr_expr;

        if (policy->per_role_can_revoke_rule(target_role).size() < 1) {
            cr_expr = createConstantFalse();
        } else {
            auto ite = policy->per_role_can_revoke_rule(target_role).begin();
            cr_expr = (*ite)->prec;
            for (++ite; ite != policy->per_role_can_revoke_rule(target_role).end(); ++ite) {
                rulep rule = *ite;
                if (contains(state.target_rules, rule)) {
                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                    continue;
                }
                cr_expr = createOrExpr(cr_expr, rule->prec);
            }
        }

        if (state.deep > 0) {
            //TODO: recursion!!
            state.push(cr_expr, state.target_rules, if_prelude);
            generate_main();
            state.pop();
        }

        TExpr cr_guards = generate_CR_cond(cr_expr);


        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(state.state.core_sets[target_role->role_array_index].get_solver_var());
        TExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, cr_guards), not_set);
        return cond;
    }

    void simulate_can_assigns_by_role(const atomp& target_role, int label_index) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        TExpr cond = get_assignment_cond_by_role(target_role, label_index);

        int target_role_index = target_role->role_array_index;

        TExpr new_role_val = solver->createCondExpr(cond, one, state.state.role_vars[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(cond, one, state.state.core_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            core_%s = 1;\n", role_array[target_role_index]);
        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        state.state.role_vars[target_role_index] = new_role_var;


        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = state.state.core_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        state.state.core_sets[target_role_index] = new_set_var;
    }

    void simulate_can_revokes_by_role(const atomp& target_role, int label_index) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        TExpr cond = get_revoke_cond_by_role(target_role, label_index);

        int target_role_index = target_role->role_array_index;

        TExpr new_role_val = solver->createCondExpr(cond, zero, state.state.role_vars[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(cond, one, state.state.core_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            core_%s = 0;\n", role_array[target_role_index]);
        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        state.state.role_vars[target_role_index] = new_role_var;

        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = state.state.core_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        state.state.core_sets[target_role_index] = new_set_var;
    }

    void simulate_skip(int label_index) {
        // Do not apply any translation and set skip to true
        // fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
        // fprintf(outputFile, "        skip = 1;");
        // fprintf(outputFile, "    }");
        variable new_skip = state.state.skip.createFrom();
        TExpr cond = solver->createGEqExpr(state.state.program_counter.get_solver_var(), solver->createBVConst(label_index, state.pc_size));
        TExpr new_val = solver->createCondExpr(cond, one, state.state.skip.get_solver_var());

        emit_assignment(new_skip, new_val);

        state.state.skip = new_skip;

    }

    TExpr generate_check_implication(int role_index, const variable& init_r_i_var) {
        //((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
//        TExpr init_r_i = zero;
//        for (auto &&atom : user->config()) {
//            if (atom->role_array_index == role_index) {
//                init_r_i = one;
//                break;
//            }
//        }

        TExpr init_r_i = init_r_i_var.get_solver_var();

        TVar role_var = state.state.role_vars[role_index].get_solver_var();
        TVar role_set = state.state.core_sets[role_index].get_solver_var();
        TVar set_false_r_i = state.state.core_value_false[role_index].get_solver_var();
        TVar set_true_r_i = state.state.core_value_true[role_index].get_solver_var();

        TExpr impl_prec =
            solver->createOrExpr(
                solver->createNotExpr(solver->createEqExpr(role_var, init_r_i)),
                solver->createOrExpr(
                    solver->createAndExpr(set_false_r_i, solver->createEqExpr(init_r_i, one)),
                    solver->createAndExpr(set_true_r_i, solver->createEqExpr(init_r_i, zero))
                ));

        TExpr cond = solver->createImplExpr(impl_prec,
                                            role_set);

        // fprintf(outputFile, "((core_%s != %d) => set_%s))", role, init_r_i, role);
        return cond;
    }

    void generate_check() {
        // fprintf(outputFile, "    /*--------------- ERROR CHECK ------------*/\n");
        // fprintf(outputFile, "    /*--------------- assume(\\phi) ------------*/\n");
        emit_comment("CHECK_BEGIN" + state.target_expr->to_string());

        std::vector<variable> origs = state.saved_state.top().role_vars;

        TExpr rule_assumption = generate_from_prec(state.target_expr);
        emit_assumption(rule_assumption);

        int user_id = 0;
        //          /\
        // assume( /  \          ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i))
        //        r_i \in \phi
        // fprintf(outputFile, "//          /\\\n");
        // fprintf(outputFile, "// assume( /  \\          ((core_r_i != init_r_i) \\/ ((set_false_r_i /\\ init_r_i = 1) \\/ (set_true_r_i /\\ init_r_i = 0)) => set_r_i)))";
        // fprintf(outputFile, "//        r_i \\in \\phi\n");
        TExpr impl_assumption = zero;
//        for (auto &&user : policy->unique_configurations()) {
            TExpr inner_and = one;
            for (int i = 0; i < policy->atom_count(); i++) {
                if (state.tracked_roles[i]) {
                    TExpr impl_r_ui = generate_check_implication(i, origs[i]);
                    inner_and = solver->createAndExpr(inner_and, impl_r_ui);
                }
            }
            impl_assumption = solver->createOrExpr(impl_assumption, inner_and);
//        }
        emit_assumption(impl_assumption);

        emit_comment("CHECK_END" + state.target_expr->to_string());

        // fprintf(outputFile, "    assert(0);\n");
    }

    void generate_update_state() {
        // IF NOT IN BASE CASE DO NOT GENERATE INITIALIZATION
        if (state.deep > 0) {
            return;
        }
        // fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
        for (int i = 0; i < policy->atom_count(); i++) {
            if (state.core_roles[i]) {
                variable new_core = state.state.role_vars[i].createFrom();
                // COULD BE REMOVED
                state.state.nondet_bool = state.state.nondet_bool.createFrom();

                TExpr new_val = solver->createCondExpr(state.state.core_sets[i].get_solver_var(),
                                                       state.state.role_vars[i].get_solver_var(),
                                                       state.state.nondet_bool.get_solver_var());
                emit_assignment(new_core, new_val);

                state.state.role_vars[i] = new_core;

                // UPDATE VALUE_TRUE
                variable new_value_true = state.state.core_value_true[i].createFrom();
                TExpr new_value_true_var = solver->createCondExpr(solver->createEqExpr(state.state.role_vars[i].get_solver_var(),
                                                                                       one),
                                                                  one,
                                                                  state.state.core_value_true[i].get_solver_var());
                emit_assignment(new_value_true, new_value_true_var);
                state.state.core_value_true[i] = new_value_true;

                // UPDATE VALUE_FALSE
                variable new_value_false = state.state.core_value_false[i].createFrom();
                TExpr new_value_false_var = solver->createCondExpr(solver->createEqExpr(state.state.role_vars[i].get_solver_var(),
                                                                                        zero),
                                                                   one,
                                                                   state.state.core_value_false[i].get_solver_var());
                emit_assignment(new_value_false, new_value_false_var);
                state.state.core_value_false[i] = new_value_false;


                // fprintf(outputFile, "    core_%s = set_%s ? core_%s : nondet_bool();\n", role, role, role);
            }
            else {
                variable nvar = state.state.role_vars[i].createFrom();
                state.state.role_vars[i] = nvar;
            }
        }

        state.state.program_counter = state.state.program_counter.createFrom();
        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");

    }

    void generate_round() {
        int label_idx = 0;
        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_update_state();


        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            if (state.tracked_roles[atom->role_array_index] && policy->per_role_can_assign_rule(atom).size() > 0) {
//                int exclude = target_rule->is_ca ? exclude_idx : -1;
                simulate_can_assigns_by_role(atom, label_idx++);
            }
        }

        // fprintf(outputFile, "\n\n");

        // fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
            if (state.tracked_roles[atom->role_array_index] && policy->per_role_can_revoke_rule(atom).size() > 0) {
//                int exclude = !excluded_is_ca ? exclude_idx : -1;
                simulate_can_revokes_by_role(atom, label_idx++);
            }
        }

        simulate_skip(label_idx);
        // fprintf(outputFile, "\n\n");
    }

    void generate_main() {
        // fprintf(outputFile, "int main(void) {\n\n");

        for (int i = 0; i < state.tracked_roles_size; ++i) {
            generate_round();
        }
        generate_check();
        // fprintf(outputFile, "    return 0;\n");
        // fprintf(outputFile, "}\n");
    }

    bool checkUnreachable() {
        generate_main();

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


    public:
    OverapproxTransformer(const std::shared_ptr<SMTFactory<TVar, TExpr>> _solver,
                          const std::shared_ptr<arbac_policy>& _policy,
                          const Expr _to_check,
                          const std::set<rulep> _to_check_source) :
        solver(_solver),
        policy(_policy),
        state(_solver.get(), _policy, Config::overapprox_depth),
        zero(solver->createFalse()), one(solver->createTrue()) {
//        solver->deep_clean();
        init_threads();
        state.push(_to_check, _to_check_source, one);
    }

    ~OverapproxTransformer() = default;

    bool apply() {
        bool ret = checkUnreachable();

        if (policy->per_role_can_assign_rule(policy->goal_role).size() < 1) {
            log->info("Target role is not assignable!");
            log->info("Target role is not reachable");
            return false;
        }
        if (ret) {
            log->info("Target role may be reachable");
        }
        else {
            log->info("Target role is not reachable");
        }

        return ret;
    }
};

    template <typename TVar, typename TExpr>
    bool overapprox(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                    const std::shared_ptr<arbac_policy>& policy,
                    const Expr& to_check,
                    const std::set<rulep>& to_check_source) {
        solver->deep_clean();
        if (is_constant_true(to_check)) {
            return false;
        }
        OverapproxTransformer<TVar, TExpr> transf(solver, policy, to_check, to_check_source);
        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
        bool res = transf.apply();
        // if (res || true)
        //     solver->printContext();
        return res;
    }


    template bool overapprox<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                             const std::shared_ptr<arbac_policy>& policy,
                                             const Expr& to_check,
                                             const std::set<rulep>& to_check_source);

    template bool overapprox<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                         const std::shared_ptr<arbac_policy>& policy,
                                         const Expr& to_check,
                                         const std::set<rulep>& to_check_source);

    template bool overapprox<BoolectorExpr, BoolectorExpr>(const std::shared_ptr<SMTFactory<BoolectorExpr, BoolectorExpr>>& solver,
                                                           const std::shared_ptr<arbac_policy>& policy,
                                                           const Expr& to_check,
                                                           const std::set<rulep>& to_check_source);

    template bool overapprox<msat_term, msat_term>(const std::shared_ptr<SMTFactory<msat_term, msat_term>>& solver,
                                                   const std::shared_ptr<arbac_policy>& policy,
                                                   const Expr& to_check,
                                                   const std::set<rulep>& to_check_source);

}
