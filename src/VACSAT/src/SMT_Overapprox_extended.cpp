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

    static int ext_porr = 0;

template <typename TVar, typename TExpr>
class ExtendedOverapproxTransformer {
    private:
    typedef generic_variable<TVar, TExpr> variable;

    static std::pair<int, int> get_pc_size_max_value(const std::shared_ptr<arbac_policy>& policy, const std::set<Atomp>& tracked_atoms) {
        int count = 1;

        for (auto &&atom : tracked_atoms) {
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
        return { bits, count - 1 };
    }

    struct overapprox_status;
    class variables {
        friend struct overapprox_status;
    private:
        variable guard;
    public:
        /*const*/ std::vector<variable> role_vars;
        /*const*/ std::vector<variable> role_changed;
        /*const*/ std::vector<variable> role_sets;

        variable program_counter;
        variable skip;
        variable update_guard;
        variable nondet_bool;

        variables() = default;

        variables(std::shared_ptr<arbac_policy> policy, SMTFactory<TVar, TExpr>* solver, const std::vector<bool>& tracked_roles) :
                role_vars (std::vector<variable>((unsigned long) policy->atom_count())),
                role_changed (std::vector<variable>((unsigned long) policy->atom_count())),
                role_sets (std::vector<variable>((unsigned long) policy->atom_count())) {
            program_counter = variable("pc", -1, 1, solver, BIT_VECTOR);

            nondet_bool = variable("nondet_bool", -1, 1, solver, BOOLEAN);
            // fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
            skip = variable("skip", 0, 1, solver, BOOLEAN);

            guard = variable("guard", 0, 1, solver, BOOLEAN);
            update_guard = variable("update_guard", 0, 1, solver, BOOLEAN);

            for (int i = 0; i < policy->atom_count(); i++) {
                if (tracked_roles[i]) {
                    role_vars[i] = variable(policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- CHECKS ---------*/\n");
                    role_sets[i] = variable(("set_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- VALUE changed ---------*/\n");
                    role_changed[i] = variable(("changed_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                } else {
                    log->info("Skipping atom: {}, since not tracked", *policy->atoms(i));
                }
            }
        }
    };

    struct overapprox_status {
        friend class variables;

//        std::vector<variable> actual_core_value_true;
//        std::vector<variable> actual_core_value_false;
//        std::vector<variable> actual_core_sets;
        SMTFactory<TVar, TExpr>* solver;
        const std::shared_ptr<arbac_policy>& policy;
        /*--- VALUES ---*/
        variables state;
//        std::set<rulep> target_rules;
        Expr target_expr;
        const std::vector<bool> tracked_roles;
//        const std::set<Atomp>& tracked_roles_set;
//        std::vector<bool> core_roles;
        const int tracked_roles_count;
//        int core_roles_count;
        const int pc_size;
        //// pc_max_value is the value from which we have to start skipping (inclusive)
        const int pc_max_value;
        int deep;

//         constraints on assertions
//        std::list<TExpr> constraints;

        /*--- SAVED ---*/
        std::stack<variables> saved_state;
//        std::stack<std::set<rulep>> saved_target_rules;
        std::stack<Expr> saved_target_expr;
//        std::stack<std::vector<bool>> saved_tracked_roles;
//        std::stack<std::vector<bool>> saved_core_roles;
//        std::stack<int> saved_tracked_roles_count;
//        std::stack<int> saved_core_roles_count;
        std::stack<int> saved_deep;

        void save_all() {
            // cloning and saving...
            variables old_state = state;
            saved_state.push(old_state);
//            std::set<rulep> old_target_rules = target_rules;
//            saved_target_rules.push(old_target_rules);
            Expr old_target_expr = target_expr;
            saved_target_expr.push(old_target_expr);
//            std::vector<bool> old_tracked_roles = tracked_roles;
//            saved_tracked_roles.push(old_tracked_roles);
//            std::vector<bool> old_core_roles = core_roles;
//            saved_core_roles.push(old_core_roles);
//            int old_tracked_roles_count = tracked_roles_count;
//            saved_tracked_roles_count.push(old_tracked_roles_count);
//            int old_core_roles_count = core_roles_count;
//            saved_core_roles_count.push(old_core_roles_count);
//            int old_pc_size = pc_size;
//            saved_pc_size.push(old_pc_size);
            int old_deep = deep;
            saved_deep.push(old_deep);
        }

        void restore_all_but_state() {
            // restoring and popping all but state...
//            target_rules = saved_target_rules.top();
//            saved_target_rules.pop();
            target_expr = saved_target_expr.top();
            saved_target_expr.pop();
//            tracked_roles = saved_tracked_roles.top();
//            saved_tracked_roles.pop();
//            core_roles = saved_core_roles.top();
//            saved_core_roles.pop();
//            tracked_roles_count = saved_tracked_roles_count.top();
//            saved_tracked_roles_count.pop();
//            core_roles_count = saved_core_roles_count.top();
//            saved_core_roles_count.pop();
//            pc_size = saved_pc_size.top();
//            saved_pc_size.pop();
            deep = saved_deep.top();
            saved_deep.pop();
        }

        /*void update_conditionally() {
            //FIXME: really not necessary?
            for (auto &&item : state.role_changed) {

            }
        }*/

        void restore_state() {
            variables old_state = saved_state.top();

            //RESTORE GUARDS
            TVar old_guard = old_state.guard.get_solver_var();
            TVar frame_guard = state.guard.get_solver_var();
            variable new_guard = state.guard.createFrom();
//            this->emit_assignment(new_guard, old_guard);
            solver->assertLater(solver->createEqExpr(new_guard.get_solver_var(), old_guard));
            state.guard = new_guard;

            //RESTORE PC
            TVar old_program_counter = old_state.program_counter.get_solver_var();
            variable new_program_counter = state.program_counter.createFrom();
//            this->emit_assignment(new_guard, old_guard);
            solver->assertLater(solver->createEqExpr(new_program_counter.get_solver_var(), old_program_counter));
            state.program_counter = new_program_counter;

            // RESTORING OLD STEP SET STATE
            for (int i = 0; i < tracked_roles.size(); ++i) {
                if (tracked_roles[i]) {
                    //TRACKED: RESTORE OLD VALUE
                    TVar old_set_state = old_state.role_sets[i].get_solver_var();
                    variable new_set_state = state.role_sets[i].createFrom();
                    this->emit_assignment(new_set_state, old_set_state);
                    state.role_sets[i] = new_set_state;
                } else {
                    //UNTRACKED: SET VARIABLE TO FALSE (NEXT USAGE WILL FIND UNSET!)
//                    state.core_sets[i] = state.core_sets[i].createFrom();
//                    this->emit_assignment(state.core_sets[i], solver->createFalse());
                }
            }

//            update_program_counter();
            //RESTORE OLD SKIP
            TVar old_skip = old_state.skip.get_solver_var();
            variable new_skip = state.skip.createFrom();
            this->emit_assignment(new_skip, old_skip);
            state.skip = new_skip;

            //UPDATING CHANGED MEMORY WITH ITE ON GUARD
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (tracked_roles[i]) {
                    variable new_changed = state.role_changed[i].createFrom();
                    variable old_changed = old_state.role_changed[i];
                    TExpr new_changed_value =
                            solver->createCondExpr(frame_guard,
                                                   solver->createOrExpr(old_changed.get_solver_var(),
                                                                        state.role_changed[i].get_solver_var()),
                                                   old_state.role_changed[i].get_solver_var());
                    emit_assignment(new_changed, new_changed_value);
                    state.role_changed[i] = new_changed;
                }
            }

            //MAKE CONSISTENT COPYING ALL VALUE WITH ITE ON GUARD
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (tracked_roles[i]) {
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
            }

            saved_state.pop();
        }

        //        void update_tracked_core_role_array_set_pc_size(const Expr &target_expr) {
////            tracked_roles_count = 0;
////            for (auto &&tracked_i : policy->atoms()) {
////                if (contains(target_expr->atoms(), tracked_i)) {
////                    tracked_roles_count++;
////                    tracked_roles[tracked_i->role_array_index] = true;
////                } else {
////                    tracked_roles[tracked_i->role_array_index] = false;
////                }
////            }
////
////            for (auto &&core_i : target_expr->atoms()) {
////                if (core_roles[core_i->role_array_index] == false) {
////                    core_roles_count++;
////                }
////                core_roles[core_i->role_array_index] = true;
////            }
//
//            // let f(r) = 0 if not assignable nor revokable, 2 if both assignable and revokable, 1 otherwise  \sum_{r \in core_roles}(f(r))
////        std::cout << "################################################################################################" << std::endl;
////        std::cout << "Working on: " << *target_rule << std::endl;
////        std::cout << "Expr:       " << *target_expr << std::endl;
////        std::cout << "Minimal:    " << get_pc_size(cores) << std::endl;
////        std::cout << "Overapprox: " << numBits((core_roles_count * 2) + 1) << std::endl;
////        std::cout << "################################################################################################" << std::endl;
//
//            pc_size = get_pc_size(policy, tracked_roles_set);
//
//        }

        void create_program_counter() {
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

        void clean_changed_memory() {
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (tracked_roles[i]) {
                    variable new_role_changed = state.role_changed[i].createFrom();
                    this->emit_assignment(new_role_changed, solver->createFalse());
                    state.role_changed[i] = new_role_changed;
                }
            }
        }

        void init_new_frame(const Expr& _target_expr/*, const std::set<rulep>& _target_rule*/) {
            deep = deep - 1;
//            target_rules.insert(_target_rule.begin(), _target_rule.end());
            target_expr = _target_expr;
//            update_tracked_core_role_array_set_pc_size(target_expr);
//            update_program_counter();
            clean_changed_memory();
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
                if (tracked_roles[i]) {
                    TExpr init_role_changed = solver->createEqExpr(state.role_changed[i].get_solver_var(),
                                                                   _false);
                    solver->assertLater(init_role_changed);

                    TExpr init_role_sets = solver->createEqExpr(state.role_sets[i].get_solver_var(),
                                                                _false);
                    solver->assertLater(init_role_sets);
                }
            }

            TExpr init_skip = solver->createEqExpr(state.skip.get_solver_var(), _false);
            solver->assertLater(init_skip);
            TExpr init_guard = solver->createEqExpr(state.guard.get_solver_var(), _true);
            solver->assertLater(init_guard);
            TExpr init_update_guard = solver->createEqExpr(state.update_guard.get_solver_var(), _true);
            solver->assertLater(init_update_guard);
            create_program_counter();
        }

    public:

        overapprox_status() = delete;

        overapprox_status(SMTFactory<TExpr, TVar>* _solver,
                          const std::shared_ptr<arbac_policy>& _policy,
                          int _deep,
                          std::tuple<const std::vector<bool>, // _tracked_roles,
                                     const int, // _tracked_roles_count,
                                     const int, //_pc_size
                                     const int /* _pc_max_value */> tracked_and_pc) :
                solver(_solver),
                policy(_policy),
                state(policy, solver, std::get<0>(tracked_and_pc)),
//                target_rules(std::set<rulep>()),
                target_expr(nullptr),
                tracked_roles(std::get<0>(tracked_and_pc)),
//                role_roles((ulong) policy->atom_count()),
                tracked_roles_count(std::get<1>(tracked_and_pc)),
//                role_roles_count(0),
                pc_size(std::get<2>(tracked_and_pc)),
                pc_max_value(std::get<3>(tracked_and_pc)),
                deep(_deep) {
//            for (int i = 0; i < policy->atom_count(); ++i) {
//                role_roles[i] = false;
//            }
            internal_init();
        }

        inline void emit_assignment(const variable& var, const TVar& value) {
            TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            TExpr guarded_ass = solver->createImplExpr(state.guard.get_solver_var(),
                                                       ass);
            solver->assertLater(guarded_ass);

        }

        inline void emit_assumption(const TExpr& value) {
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            TExpr guarded_ass = solver->createImplExpr(state.guard.get_solver_var(),
                                                      value);
            solver->assertLater(guarded_ass);
        }

        inline void emit_comment(const std::string& comment) {
            //Working automatically and only in Z3
            if (std::is_same<z3::expr, TExpr>::value) {
                solver->assertNow(solver->createBoolVar(comment));
                log->debug("Emitting comment: " + comment);
            }
        }

        inline variable create_get_nondet_bool_var() {
            state.nondet_bool = state.nondet_bool.createFrom();
            return state.nondet_bool;
        }

        void push(Expr _target_expr, /*std::set<rulep> _target_rule, */TExpr guard) {
            log->warn(++ext_porr);
//            log->warn("pushing");
//            log->warn("Pushing {}", *_target_expr);
            emit_comment("PUSH" + _target_expr->to_string());
            save_all();
            set_guard(guard);
            init_new_frame(_target_expr/*, _target_rule*/);
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
//    std::stringstream fmt;

//    void clean_fmt() {
//        fmt.str(std::string());
//    }
//
    overapprox_status state;

    const TExpr zero;
    const TExpr one;

//    std::vector<bool> tracked_roles;
//    int tracked_roles_count;
//    int pc_size;

    static std::tuple<std::vector<bool>, int, int, int> get_tracked_pc_size_pc_maxvalue(const std::shared_ptr<arbac_policy>& policy, const Expr& phi_t) {
        bool fixpoint = false;

        std::set<Atomp> to_track;

        to_track.insert(phi_t->atoms().begin(), phi_t->atoms().end());

        while (!fixpoint) {
            fixpoint = true;

            for (auto &&rule : policy->rules()) {
//                    print_collection(necessary_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": "_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": " << (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) << std::endl;
                if (contains(to_track, rule->target)) {
//                        print_collection(rule->admin->literals());
//                        print_collection(rule->prec->literals());
                    auto old_size = to_track.size();

                    //FIXME: absolutely remove the following if working with admin!
                    to_track.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
                    to_track.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                    if (old_size - to_track.size() != 0) {
                        fixpoint = false;
                    }
                }
            }
        }

        int tracked_roles_count = 0;
        std::vector<bool> tracked_roles((unsigned long) policy->atom_count());
        for (int i = 0; i < policy->atom_count(); ++i) {
            tracked_roles[i] = false;
        }
        for (auto &&atom : to_track) {
            tracked_roles[atom->role_array_index] = true;
            tracked_roles_count++;
        }

        std::pair<int, int> pc_size_max_value = get_pc_size_max_value(policy, to_track);
        return std::tuple<std::vector<bool>, int, int, int>(tracked_roles,
                                                            tracked_roles_count,
                                                            pc_size_max_value.first,
                                                            pc_size_max_value.second);
    }


//
//    //int *roles_ca_counts = NULL;
//    //int *roles_cr_counts = NULL;
//
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
                if (state.tracked_roles[atom->role_array_index]) {
                    bool has = contains(conf->config(), atom);
                    conf_expr = solver->createAndExpr(conf_expr,
                                                      solver->createEqExpr(
                                                              state.state.role_vars[atom->role_array_index].get_solver_var(),
                                                              has ? one : zero));
                }
            }
            init = solver->createOrExpr(init, conf_expr);
        }
        solver->assertLater(init);
    }

    TExpr generate_PC_prec(int pc) {
        // fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
        return solver->createEqExpr(state.state.program_counter.get_solver_var(),
                                    solver->createBVConst(pc, state.pc_size)) ;
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
        TExpr skip_condition = solver->createNotExpr(state.state.skip.get_solver_var());
        Expr ca_expr;
        if (policy->per_role_can_assign_rule(target_role).size() < 1) {
            ca_expr = createConstantFalse();
        } else {
            policy->per_role_can_assign_rule(target_role);
            auto ite = policy->per_role_can_assign_rule(target_role).begin();
            ca_expr = (*ite)->prec;
            for (++ite; ite != policy->per_role_can_assign_rule(target_role).end(); ++ite) {
                rulep rule = *ite;
//                if (contains(state.target_rules, rule)) {
//                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
//                    continue;
//                }
                // print_ca_comment(outputFile, ca_idx);
                ca_expr = createOrExpr(ca_expr, rule->prec);
                // fprintf(outputFile, "        ||\n");
            }
        }

//        if (state.deep > 0) {
////            log->warn("pushing rule {} with depth {}", *ca_expr, state.deep);
//            state.push(ca_expr/*, state.target_rules*/, if_prelude);
//            generate_main();
//            state.pop();
//        }
        TExpr ca_guards = generate_CA_cond(ca_expr);

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(state.state.role_sets[target_role->role_array_index].get_solver_var());
        // this should prevent dummy set for the last time not changing the value
        TExpr was_false = solver->createNotExpr(solver->createEqExpr(state.state.role_vars[target_role->role_array_index].get_solver_var(),
                                                                     one));
        TExpr cond = solver->createAndExpr(solver->createAndExpr(skip_condition, ca_guards),
                                           solver->createAndExpr(not_set, was_false));
        return cond;
    }

    TExpr get_revoke_cond_by_role(const atomp& target_role, int label_index) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        Expr cr_expr;

        TExpr skip_condition = solver->createNotExpr(state.state.skip.get_solver_var());

        if (policy->per_role_can_revoke_rule(target_role).size() < 1) {
            cr_expr = createConstantFalse();
        } else {
            auto ite = policy->per_role_can_revoke_rule(target_role).begin();
            cr_expr = (*ite)->prec;
            for (++ite; ite != policy->per_role_can_revoke_rule(target_role).end(); ++ite) {
                rulep rule = *ite;
//                if (contains(state.target_rules, rule)) {
//                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
//                    continue;
//                }
                cr_expr = createOrExpr(cr_expr, rule->prec);
            }
        }

//        if (state.deep > 0) {
////            log->warn("pushing rule {} with depth {}", *cr_expr, state.deep);
//            state.push(cr_expr, /*state.target_rules,*/ if_prelude);
//            generate_main();
//            state.pop();
//        }

        TExpr cr_guards = generate_CR_cond(cr_expr);


        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(state.state.role_sets[target_role->role_array_index].get_solver_var());
        // this should prevent dummy set for the last time not changing the value
        TExpr was_true = solver->createNotExpr(solver->createEqExpr(state.state.role_vars[target_role->role_array_index].get_solver_var(),
                                                                    zero));
        TExpr cond = solver->createAndExpr(solver->createAndExpr(skip_condition, cr_guards),
                                           solver->createAndExpr(not_set, was_true));
        return cond;
    }

    void simulate_can_assigns_by_role(const atomp& target_role, int label_index) {
        //This forces the transition to happen if pc = label
        TExpr pc_precondition = generate_PC_prec(label_index);

        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        TExpr ass_cond = get_assignment_cond_by_role(target_role, label_index);

        emit_assumption(solver->createImplExpr(pc_precondition, ass_cond));

        int target_role_index = target_role->role_array_index;

        TExpr new_role_val = solver->createCondExpr(pc_precondition, one, state.state.role_vars[target_role_index].get_solver_var());
        TExpr new_changed_val = solver->createCondExpr(pc_precondition, one, state.state.role_changed[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(pc_precondition, one, state.state.role_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            role_%s = 1;\n", role_array[target_role_index]);
        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        state.state.role_vars[target_role_index] = new_role_var;

        // fprintf(outputFile, "            changed_%s = 1;\n", role_array[target_role_index]);
        variable new_changed_var = state.state.role_changed[target_role_index].createFrom();
        emit_assignment(new_changed_var, new_changed_val);
        state.state.role_changed[target_role_index] = new_changed_var;


        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = state.state.role_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        state.state.role_sets[target_role_index] = new_set_var;
    }

    void simulate_can_revokes_by_role(const atomp& target_role, int label_index) {
        //This forces the transition to happen if pc = label
        TExpr pc_precondition = generate_PC_prec(label_index);

        TExpr revoke_cond = get_revoke_cond_by_role(target_role, label_index);

        emit_assumption(solver->createImplExpr(pc_precondition, revoke_cond));

        int target_role_index = target_role->role_array_index;

        TExpr new_role_val = solver->createCondExpr(pc_precondition, zero, state.state.role_vars[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(pc_precondition, one, state.state.role_sets[target_role_index].get_solver_var());

        // fprintf(outputFile, "            role_%s = 0;\n", role_array[target_role_index]);
        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        state.state.role_vars[target_role_index] = new_role_var;

        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = state.state.role_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        state.state.role_sets[target_role_index] = new_set_var;
    }

    void simulate_skip() {
        // Do not apply any translation and set skip to true
        // fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
        // fprintf(outputFile, "        skip = 1;");
        // fprintf(outputFile, "    }");
        variable new_skip = state.state.skip.createFrom();
        TExpr cond = solver->createGEqExpr(state.state.program_counter.get_solver_var(),
                                           solver->createBVConst(state.pc_max_value, state.pc_size));
        TExpr new_val = solver->createCondExpr(cond, one, state.state.skip.get_solver_var());

        emit_assignment(new_skip, new_val);

        state.state.skip = new_skip;

    }

    TExpr generate_check_implication(int role_index, const variable& init_r_i_var) {
        //(changeed_r_i ==> set_r_i)
        ////((role_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
//        TExpr init_r_i = zero;
//        for (auto &&atom : user->config()) {
//            if (atom->role_array_index == role_index) {
//                init_r_i = one;
//                break;
//            }
//        }

        TExpr init_r_i = init_r_i_var.get_solver_var();

        TVar role_var = state.state.role_vars[role_index].get_solver_var();
        TVar role_set = state.state.role_sets[role_index].get_solver_var();
        TVar role_changed = state.state.role_changed[role_index].get_solver_var();

//        TExpr impl_prec =
//            solver->createOrExpr(
//                solver->createNotExpr(solver->createEqExpr(role_var, init_r_i)),
//                solver->createOrExpr(
//                    solver->createAndExpr(set_false_r_i, solver->createEqExpr(init_r_i, one)),
//                    solver->createAndExpr(set_true_r_i, solver->createEqExpr(init_r_i, zero))
//                ));

        TExpr cond = solver->createImplExpr(role_changed,
                                            role_set);

        // fprintf(outputFile, "((role_%s != %d) => set_%s))", role, init_r_i, role);
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
        // assume( /  \          (changed_r_i ==> set_r_i)
        //        r_i \in Track
        // fprintf(outputFile, "//          /\\\n");
        // fprintf(outputFile, "// assume( /  \\          (changed_r_i ==> set_r_i)\n";
        // fprintf(outputFile, "//        r_i \\in Track\n");
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

    void generate_pc_update() {
        variable new_pc = state.state.program_counter.createFrom();
        // If I was skipping continue with old pc value
        TExpr continue_skipping = solver->createImplExpr(state.state.skip.get_solver_var(),
                                                         solver->createEqExpr(new_pc.get_solver_var(),
                                                                              state.state.program_counter.get_solver_var()));
        emit_assumption(continue_skipping);
        state.state.program_counter = new_pc;
    }

    void update_constrained_value(const atomp& atom) {
        /*
         * if (!set(r) && *) { //Do update iff exists at least a ca and a cr
         *      r = *
         *      changed = true
         * }
         * */

        emit_comment("updating role " + atom->name);

        if (policy->per_role_can_assign_rule(atom).empty() &&
            policy->per_role_can_revoke_rule(atom).empty()) {
            // Cannot be changed
            emit_comment("role " + atom->name + " cannot be changed");
            return;
        }

        variable role_var = state.state.role_vars[atom->role_array_index];
        variable role_set = state.state.role_sets[atom->role_array_index];
        variable new_role_var = state.state.role_vars[atom->role_array_index].createFrom();

        variable update_guard_var = state.state.update_guard.createFrom();
        state.state.update_guard = update_guard_var;
        variable do_update = state.create_get_nondet_bool_var();
        TExpr not_skipping = solver->createNotExpr(state.state.skip.get_solver_var());
        TExpr update_guard = solver->createAndExpr(not_skipping,
                                                   solver->createAndExpr(solver->createNotExpr(role_set.get_solver_var()),
                                                                         do_update.get_solver_var()));

        emit_assignment(update_guard_var, update_guard);


        TExpr updated_value = state.create_get_nondet_bool_var().get_solver_var();

        //Variable has really changed
        TExpr constraints = solver->createNotExpr(solver->createEqExpr(role_var.get_solver_var(),
                                                                       updated_value));

        // Updated value can be TRUE if |CA(r)| > 0
        // Take the negation: if |CA(r)| = 0 then updated value cannot be TRUE (this works only if it must be changed)
        if (policy->per_role_can_assign_rule(atom).empty()) {
            constraints = solver->createAndExpr(constraints,
                                                solver->createNotExpr(solver->createEqExpr(updated_value,
                                                                                           one)));
        }
        // Updated value can be FALSE if |CR(r)| > 0
        // Take the negation: if |CR(r)| = 0 then updated value cannot be FALSE (this works only if it must be changed)
        if (policy->per_role_can_revoke_rule(atom).empty()) {
            constraints = solver->createAndExpr(constraints,
                                                solver->createNotExpr(solver->createEqExpr(updated_value,
                                                                                           zero)));
        }

        //assert the constraint guarded by the fact the update must take place
        // TODO: consider using XOR
        emit_assumption(solver->createImplExpr(update_guard_var.get_solver_var(), constraints));

        // Perform update guarded by "update_guard"
        // on role_value
        TExpr new_val = solver->createCondExpr(update_guard_var.get_solver_var(),
                                               updated_value,
                                               role_var.get_solver_var());
        emit_assignment(new_role_var, new_val);
        state.state.role_vars[atom->role_array_index] = new_role_var;

        // on role_changed
        variable old_changed_var = state.state.role_changed[atom->role_array_index];
        variable new_changed_var = state.state.role_changed[atom->role_array_index].createFrom();
        TExpr new_changed = solver->createCondExpr(update_guard_var.get_solver_var(),
                                                   one,
                                                   old_changed_var.get_solver_var());
        emit_assignment(new_changed_var, new_changed);
        state.state.role_changed[atom->role_array_index] = new_changed_var;

        emit_comment("role " + atom->name + " updated");
    }

    void generate_update_state() {
        // IF NOT IN BASE CASE DO NOT GENERATE INITIALIZATION
        emit_comment("S updating at: " + std::to_string(state.deep) + " ");
        if (state.deep > 0) {
            state.push(createConstantTrue(), solver->createNotExpr(state.state.skip.get_solver_var()));
            generate_main();
            state.pop();
        } else {
            // fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
            for (int i = 0; i < policy->atom_count(); i++) {
                if (state.tracked_roles[i]) {
                    atomp atom = policy->atoms(i);
                    update_constrained_value(atom);
                    // fprintf(outputFile, "    role_%s = set_%s ? role_%s : nondet_bool();\n", role, role, role);
                }
            }
        }

        emit_comment("E updating at: " + std::to_string(state.deep) + " ");
        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");

    }

    void generate_round() {
        int label_idx = 0;
        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_pc_update();

        simulate_skip();

        //TODO: everything MUST be guarded by (!skip)

        generate_update_state();


        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            if (state.tracked_roles[atom->role_array_index] &&
                policy->per_role_can_assign_rule(atom).size() > 0) {
//                int exclude = target_rule->is_ca ? exclude_idx : -1;
                simulate_can_assigns_by_role(atom, label_idx++);
            }
        }

        // fprintf(outputFile, "\n\n");

        // fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
            if (state.tracked_roles[atom->role_array_index] &&
                policy->per_role_can_revoke_rule(atom).size() > 0) {
//                int exclude = !excluded_is_ca ? exclude_idx : -1;
                simulate_can_revokes_by_role(atom, label_idx++);
            }
        }

        assert(label_idx == state.pc_max_value);
        // fprintf(outputFile, "\n\n");
    }

    void generate_main() {
        // fprintf(outputFile, "int main(void) {\n\n");

        for (int i = 0; i < state.tracked_roles_count; ++i) {
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
    ExtendedOverapproxTransformer(const std::shared_ptr<SMTFactory<TVar, TExpr>> _solver,
                                  const std::shared_ptr<arbac_policy>& _policy,
                                  const Expr _to_check
                                  /*const std::set<rulep> _to_check_source*/) :
        solver(_solver),
        policy(_policy),
        // could be changed instead of using tuple with references that... can be changed from the outside!!!
        state(_solver.get(), _policy, Config::overapprox_depth, get_tracked_pc_size_pc_maxvalue(_policy, _to_check)),
        zero(solver->createFalse()),
        one(solver->createTrue()) {
//        solver->deep_clean();
        init_threads();
        state.push(_to_check, /*_to_check_source,*/ one);
    }

    ~ExtendedOverapproxTransformer() = default;

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
    bool extended_overapprox(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                             const std::shared_ptr<arbac_policy>& policy,
                             const Expr& to_check) {
        solver->deep_clean();
        if (is_constant_true(to_check)) {
            return false;
        }
        ExtendedOverapproxTransformer<TVar, TExpr> transf(solver, policy, to_check);
        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
        bool res = transf.apply();
        // if (res || true)
        //     solver->printContext();
        return res;
    }


    template bool extended_overapprox<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                                      const std::shared_ptr<arbac_policy>& policy,
                                                      const Expr& to_check);

    template bool extended_overapprox<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                                  const std::shared_ptr<arbac_policy>& policy,
                                                  const Expr& to_check);

    template bool extended_overapprox<BoolectorExpr, BoolectorExpr>(const std::shared_ptr<SMTFactory<BoolectorExpr, BoolectorExpr>>& solver,
                                                                    const std::shared_ptr<arbac_policy>& policy,
                                                                    const Expr& to_check);

    template bool extended_overapprox<msat_term, msat_term>(const std::shared_ptr<SMTFactory<msat_term, msat_term>>& solver,
                                                            const std::shared_ptr<arbac_policy>& policy,
                                                            const Expr& to_check);

}
