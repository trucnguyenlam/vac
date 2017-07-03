//#include "ARBACExact.h"
#include <time.h>
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <memory>

#include "SMT.h"
#include "SMT_Pruning.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "Logics.h"
#include "BMC_Struct.h"
#include "Policy.h"

#include <chrono>
#include <stack>

namespace SMT {

template <typename TVar, typename TExpr>
class OverapproxTransformer {
    private:
    typedef generic_variable<TVar, TExpr> variable;

    static int get_pc_size(std::shared_ptr<arbac_policy> policy, const std::set<Atomp>& atoms) const {
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
        return bits_count(count);
    }

    class variables {
    public:
        const std::vector<variable> role_vars;
        const std::vector<variable> core_value_true;
        const std::vector<variable> core_value_false;
        const std::vector<variable> core_sets;

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
//        std::vector<variable> actual_core_value_true;
//        std::vector<variable> actual_core_value_false;
//        std::vector<variable> actual_core_sets;
        SMTFactory<TVar, TExpr>* solver;
        std::shared_ptr<arbac_policy> policy;
        /*--- VALUES ---*/
        variables state;
        std::set<rulep> target_rules;
        Expr target_expr;
        std::vector<bool> core_roles;
        int core_roles_size;
        int pc_size;

        /*--- SAVED ---*/
        std::stack<variables> saved_state;
        std::stack<std::set<rulep>> saved_target_rules;
        std::stack<Expr> saved_target_expr;
        std::stack<std::vector<bool>> saved_core_roles;
        std::stack<int> saved_core_roles_size;
        std::stack<int> saved_pc_size;

        void save_all() {
            // cloning and saving...
            variables old_state = state;
            saved_state.push(old_state);
            std::set<rulep> old_target_rules = target_rules;
            saved_target_rules.push(old_target_rules);
            Expr old_target_expr = target_expr;
            saved_target_expr.push(old_target_expr);
            std::vector<bool> old_core_roles = core_roles;
            saved_core_roles.push(old_core_roles);
            int old_core_roles_size = core_roles_size;
            saved_core_roles_size.push(old_core_roles_size);
            int old_pc_size = pc_size;
            saved_pc_size.push(old_pc_size);
        }

        void restore_all_but_state() {
            // restoring and popping all but state...
            target_rules = saved_target_rules.top();
            saved_target_rules.pop();
            target_expr = saved_target_expr.top();
            saved_target_expr.pop();
            core_roles = saved_core_roles.top();
            saved_core_roles.pop();
            core_roles_size = saved_core_roles_size.top();
            saved_core_roles_size.pop();
            pc_size = saved_pc_size.top();
            saved_pc_size.pop();
        }

        void restore_state() {
            variables old_state = saved_state.top();
            // RESTORING OLD STEP SET STATE
            for (int i = 0; i < core_roles.size(); ++i) {
                bool c_status = core_roles[i];
                if (!c_status) {
                    //UNTRACKED: SET VARIABLE TO FALSE (NEXT USAGE WILL FIND UNSET!)
                    state.core_sets[i] = state.core_sets[i].createFrom();
                    TExpr set_false = solver->createEqExpr(state.core_sets[i].get_solver_var(), solver->createFalse());
                    solver->assertLater(set_false);
                } else {
                    //TRACKED: RESTORE OLD VALUE
                    TVar old_set_state = old_state.core_sets[i].get_solver_var();
                    variable new_set_state = state.core_sets[i].createFrom();
                    TExpr set = solver->createEqExpr(new_set_state.get_solver_var(), old_set_state);
                    solver->assertLater(set);
                    state.core_sets[i] = new_set_state;
                }
            }

            update_program_counter();
            //RESTORE OLD SKIP
            TVar old_skip = old_state.skip.get_solver_var();
            variable new_skip = state.skip.createFrom();
            TExpr skip_assign = solver->createEqExpr(new_skip.get_solver_var(), old_skip);
            solver->assertLater(skip_assign);
            state.skip = new_skip;

            saved_state.pop();
        }

        void update_core_role_array_set_pc_size(const Expr& target_expr) {
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
            state.program_counter = variable(state.program_counter.name, state.program_counter.idx + 1, pc_size, solver, BIT_VECTOR);
        }

        void init_new_frame(const Expr& _target_expr, const rulep& _target_rule) {
            target_rules.insert(_target_rule);
            target_expr = _target_expr;
            update_core_role_array_set_pc_size(target_expr);
            update_program_counter();

        }


    public:

        overapprox_status(SMTFactory<TExpr, TVar>* _solver, std::shared_ptr<arbac_policy> _policy) :
                solver(_solver),
                policy(_policy),
                state(policy, solver),
                target_rules(std::set<rulep>()),
                target_expr(nullptr),
                core_roles((ulong) policy->atom_count()),
                core_roles_size(-1),
                pc_size(-1) {
            for (int i = 0; i < policy->atom_count(); ++i) {
                core_roles[i] = false;
            }
        }

        void push(Expr _target_expr, rulep _target_rule) {
            save_all();
            init_new_frame(_target_expr, _target_rule);
        }

        void pop() {
            restore_all_but_state();
            restore_state();
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

    TExpr zero;
    TExpr one;



//
//    //int *roles_ca_counts = NULL;
//    //int *roles_cr_counts = NULL;
//
    inline void emit_assignment(const variable& variable, const TExpr& value) {
        TExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
        solver->assertLater(assign);
    }

    inline void emit_assumption(const TExpr& expr) {
        solver->assertLater(expr);
    }


//    void generate_header(char *inputFile, int rule_id, int is_ca) {
//        time_t mytime;
//        mytime = time(NULL);
//        fprintf(stdout, "/*\n");
//        fprintf(stdout, "*  generated by VAC pruning-R6 [ 0000 / 0000 ]\n");
//        fprintf(stdout, "*\n");
//        fprintf(stdout, "*  instance version    {}\n");
//        fprintf(stdout, "*\n");
//        fprintf(stdout, "*  %s\n", ctime(&mytime));
//        fprintf(stdout, "*\n");
//        fprintf(stdout, "*  params:\n");
//        fprintf(stdout, "*    %s, --rounds %d\n", inputFile, core_roles_size + 1);
//        fprintf(stdout, "* MERGE_RULES\n");
//        fprintf(stdout, "*\n");
//        fprintf(stdout, "*  users: %d\n", (int)policy->users().size());
//        fprintf(stdout, "*  roles: %d\n", policy->atom_count());
////        fprintf(stdout, "*  adminroles: %d\n", admin_role_array_index_size);
//        fprintf(stdout, "*  CA: %lu\n", policy->can_assign_rules().size());
//        fprintf(stdout, "*  CR: %lu\n", policy->can_revoke_rules().size());
//        fprintf(stdout, "*  CR: %lu\n", policy->can_revoke_rules().size());
//        fprintf(stdout, "*  CR: %lu\n", policy->can_revoke_rules().size());
//        fprintf(stdout, "*\n");
//        fprintf(stdout, "*  rule: %s, id: %d:\n", target_rule->get_type().c_str(), target_rule->original_idx);
//        fprintf(stdout, "*  Expr: %s", target_expr->to_string().c_str());
//        target_rule->print();
//        fprintf(stdout, "*/\n");
//        fprintf(stdout, "\n\n");
//
//        // fprintf(stdout, "#define IF(PC,COND,APPL) if (");
//        // fprintf(stdout, "(__cs_pc0 == PC) && (COND) ) { APPL; }\n");
//
//        fprintf(stdout, "\n");
//
//        return;
//    }


    void set_globals() {
        emit_assignment(state.state.skip, zero);

        for (int i = 0; i < policy->atom_count(); i++) {
            // fprintf(outputFile, "/*---------- SET CHECKS = 1 ---------*/\n");
            emit_assignment(state.state.core_sets[i], zero);
            emit_assignment(state.state.core_value_true[i], zero);
            emit_assignment(state.state.core_value_false[i], zero);
        }
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
        TExpr ca_guards = solver->createFalse();

        for (auto &&rule :policy->per_role_can_assign_rule(target_role)) {
            if (contains(state.target_rules, rule)) {
                // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                continue;
            }
            // print_ca_comment(outputFile, ca_idx);
            ca_guards = solver->createOrExpr(ca_guards, generate_CA_cond(rule->prec));
            // fprintf(outputFile, "        ||\n");
        }

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
        TExpr cr_guards = solver->createFalse();

        for (auto &&rule :policy->per_role_can_revoke_rule(target_role)) {
            if (contains(state.target_rules, rule)) {
                // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                continue;
            }
            cr_guards = solver->createOrExpr(cr_guards, generate_CR_cond(rule->prec));
        }

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

//    void simulate_skip(int label_index) {
//        // Do not apply any translation and set skip to true
//        // fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
//        // fprintf(outputFile, "        skip = 1;");
//        // fprintf(outputFile, "    }");
//        variable new_skip = skip.createFrom();
//        TExpr cond = solver->createGEqExpr(program_counter.get_solver_var(), solver->createBVConst(label_index, pc_size));
//        TExpr new_val = solver->createCondExpr(cond, one, skip.get_solver_var());
//
//        emit_assignment(new_skip, new_val);
//
//        skip = new_skip;
//
//    }
//
//    TExpr generate_check_implication(int role_index, const userp& user) {
//        //((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
//        TExpr init_r_i = zero;
//        for (auto &&atom : user->config()) {
//            if (atom->role_array_index == role_index) {
//                init_r_i = one;
//                break;
//            }
//        }
//
//        TVar role_var = role_vars[role_index].get_solver_var();
//        TVar role_set = core_sets[role_index].get_solver_var();
//        TVar set_false_r_i = core_value_false[role_index].get_solver_var();
//        TVar set_true_r_i = core_value_true[role_index].get_solver_var();
//
//        TExpr impl_prec =
//            solver->createOrExpr(
//                solver->createNotExpr(solver->createEqExpr(role_var, init_r_i)),
//                solver->createOrExpr(
//                    solver->createAndExpr(set_false_r_i, solver->createEqExpr(init_r_i, one)),
//                    solver->createAndExpr(set_true_r_i, solver->createEqExpr(init_r_i, zero))
//                ));
//
//        TExpr cond = solver->createImplExpr(impl_prec,
//                                            role_set);
//
//        // fprintf(outputFile, "((core_%s != %d) => set_%s))", role, init_r_i, role);
//        return cond;
//    }
//
//    void generate_check() {
//        // fprintf(outputFile, "    /*--------------- ERROR CHECK ------------*/\n");
//        // fprintf(outputFile, "    /*--------------- assume(\\phi) ------------*/\n");
//
//        TExpr rule_assumption = generate_from_prec(target_expr);
//        emit_assumption(rule_assumption);
//
//        int user_id = 0;
//        //         \  /          /\
//        // assume(  \/        ( /  \          ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i)))
//        //        u_i \in U    r_i \in \phi
//        // fprintf(outputFile, "//         \\  /          /\\\n");
//        // fprintf(outputFile, "// assume(  \\/        ( /  \\          ((core_r_i != init_r_i) \\/ ((set_false_r_i /\\ init_r_i = 1) \\/ (set_true_r_i /\\ init_r_i = 0)) => set_r_i)))\n");
//        // fprintf(outputFile, "//        u_i \\in U    r_i \\in \\phi\n");
//        TExpr impl_assumption = zero;
//        for (auto &&user : policy->unique_configurations()) {
//            TExpr inner_and = one;
//            for (int i = 0; i < policy->atom_count(); i++) {
//                if (core_roles[i]) {
//                    TExpr impl_r_ui = generate_check_implication(i, user);
//                    inner_and = solver->createAndExpr(inner_and, impl_r_ui);
//                }
//            }
//            impl_assumption = solver->createOrExpr(impl_assumption, inner_and);
//        }
//        emit_assumption(impl_assumption);
//        // fprintf(outputFile, "    assert(0);\n");
//    }
//
//    void generate_update_state() {
//        // fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
//        for (int i = 0; i < policy->atom_count(); i++) {
//            if (core_roles[i]) {
//                variable new_core = role_vars[i].createFrom();
//                // COULD BE REMOVED
//                nondet_bool = nondet_bool.createFrom();
//
//                TExpr new_val = solver->createCondExpr(core_sets[i].get_solver_var(), role_vars[i].get_solver_var(), nondet_bool.get_solver_var());
//                emit_assignment(new_core, new_val);
//
//                role_vars[i] = new_core;
//
//                // UPDATE VALUE_TRUE
//                variable new_value_true = core_value_true[i].createFrom();
//                TExpr new_value_true_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), one), one, core_value_true[i].get_solver_var());
//                emit_assignment(new_value_true, new_value_true_var);
//                core_value_true[i] = new_value_true;
//
//                // UPDATE VALUE_FALSE
//                variable new_value_false = core_value_false[i].createFrom();
//                TExpr new_value_false_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), zero), one, core_value_false[i].get_solver_var());
//                emit_assignment(new_value_false, new_value_false_var);
//                core_value_false[i] = new_value_false;
//
//
//                // fprintf(outputFile, "    core_%s = set_%s ? core_%s : nondet_bool();\n", role, role, role);
//            }
//            else {
//                variable nvar = role_vars[i].createFrom();
//                role_vars[i] = nvar;
//            }
//        }
//
//        program_counter = program_counter.createFrom();
//        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");
//
//    }
//
//    void generate_round() {
//        int label_idx = 0;
//        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
//        generate_update_state();
//
//
//        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
//        for (auto &&atom :policy->atoms()) {
//            if (core_roles[atom->role_array_index] && policy->per_role_can_assign_rule(atom).size() > 0) {
////                int exclude = target_rule->is_ca ? exclude_idx : -1;
//                simulate_can_assigns_by_role(atom, label_idx++);
//            }
//        }
//
//        // fprintf(outputFile, "\n\n");
//
//        // fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
//        for (auto &&atom :policy->atoms()) {
//            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
//            if (core_roles[atom->role_array_index] && policy->per_role_can_revoke_rule(atom).size() > 0) {
////                int exclude = !excluded_is_ca ? exclude_idx : -1;
//                simulate_can_revokes_by_role(atom, label_idx++);
//            }
//        }
//
//        simulate_skip(label_idx);
//        // fprintf(outputFile, "\n\n");
//    }
//
//    void generate_main() {
//        // fprintf(outputFile, "int main(void) {\n\n");
//
//        for (int i = 0; i < core_roles_size; ++i) {
//            generate_round();
//        }
//        generate_check();
//        // fprintf(outputFile, "    return 0;\n");
//        // fprintf(outputFile, "}\n");
//    }
//
//    bool checkUnreachable() {
//        set_globals();
//        generate_main();
//
//        SMTResult res = solver->solve();
//
////        std::cout << *target_rule << std::endl;
////
////        solver->printContext("z3.lisp");
//
//        return res == UNSAT;
//    }
//
//
//    public:
//    R6Transformer(const std::shared_ptr<SMTFactory<TVar, TExpr>> _solver,
//                  const std::shared_ptr<arbac_policy>& _policy,
//                  const Expr _to_check,
//                  const std::shared_ptr<rule> _to_check_source) :
//        solver(_solver),
//        policy(_policy),
//        target_rule(_to_check_source),
//        target_expr(_to_check),
//        zero(solver->createFalse()), one(solver->createTrue()),
//        pc_size(get_pc_size(target_expr->atoms())) {
//        solver->deep_clean();
//        allocate_core_role_array_set_pc_size();
//        generate_variables();
//    }
//
//    ~R6Transformer() {
////        deallocate_precomputated_values();
//        free_core_role_array();
//        free_globals();
//    }
//
//    bool apply_r6() {
//        return checkUnreachable();
//    }
};

    template <typename TVar, typename TExpr>
    bool overapprox(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const Expr& to_check,
                  const std::shared_ptr<rule>& to_check_source) {
//        if (is_constant_true(to_check)) {
//            return false;
//        }
//        R6Transformer<TVar, TExpr> transf(solver, policy, to_check, to_check_source);
//        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
//        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
//        bool res = transf.apply_r6();
//        // if (res || true)
//        //     solver->printContext();
//        return res;
    }


    template bool overapprox<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                             const std::shared_ptr<arbac_policy>& policy,
                                             const Expr& to_check,
                                             const std::shared_ptr<rule>& to_check_source);
    template bool overapprox<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                         const std::shared_ptr<arbac_policy>& policy,
                                         const Expr& to_check,
                                         const std::shared_ptr<rule>& to_check_source);

}
