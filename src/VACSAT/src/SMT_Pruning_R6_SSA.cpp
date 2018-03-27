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
#include "SMT_BMC_Struct.h"
#include "Policy.h"
#include "SMTSolvers/boolector.h"

#include <chrono>
#include <mathsat.h>

namespace SMT {

class R6Transformer {
    private:

    typedef generic_variable variable;

    std::shared_ptr<SMTFactory> solver;
    std::stringstream fmt;

    void clean_fmt() {
        fmt.str(std::string());
    }

    /*--- SMT VARIABLE INDEXES ---*/
    /*--- VALUES ARE  ---*/
    std::vector<variable> role_vars;
//    SMTExpr* solver_role_vars;
    std::vector<variable> core_value_true;
    std::vector<variable> core_value_false;
    std::vector<variable> core_sets;
    variable program_counter;
    variable skip;
    variable nondet_bool;

    std::shared_ptr<arbac_policy> policy;
    std::list<rulep> excluded_rules;
    Expr target_expr;
    std::set<Expr> free;
    userp target_user;

    SMTExpr zero;
    SMTExpr one;

    bool *core_roles = nullptr;
    int core_roles_size = 0;
    int pc_size;

    //int *roles_ca_counts = NULL;
    //int *roles_cr_counts = NULL;

    inline void emit_assignment(const variable& variable, const SMTExpr& value) {
        SMTExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
        solver->assertLater(assign);
    }

    inline void emit_assumption(const SMTExpr& expr) {
        solver->assertLater(expr);
    }

//    template <typename TCmp = std::less<atomp>>
    int get_pc_size(const std::set<Atomp>& atoms) const {
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

    void allocate_core_role_array_set_pc_size() {
//        auto cores = ;
        core_roles = new bool[policy->atom_count()];
        for (int i = 0; i < policy->atom_count(); i++) {
            core_roles[i] = false;
        }

        for (auto &&core : target_expr->atoms()) {
            core_roles[core->role_array_index] = true;
            core_roles_size++;
        }

        // let f(r) = 0 if not assignable nor revokable, 2 if both assignable and revokable, 1 otherwise  \sum_{r \in core_roles}(f(r))
//        std::cout << "################################################################################################" << std::endl;
//        std::cout << "Working on: " << *target_rule << std::endl;
//        std::cout << "Expr:       " << *target_expr << std::endl;
//        std::cout << "Minimal:    " << get_pc_size(cores) << std::endl;
//        std::cout << "Overapprox: " << numBits((core_roles_size * 2) + 1) << std::endl;
//        std::cout << "################################################################################################" << std::endl;

        pc_size = get_pc_size(target_expr->atoms());

    }

    void free_core_role_array() {
        delete[] core_roles;
    }

    int numBits(int pc) const {
        int i = 1, bit = 0;

        if (pc < 2) return 1;

        while (pc >= i) {
            i = i * 2;
            bit++;
        }

        return (bit);
    }

    void generate_variables() {

        // fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n\n");
        SMTFactory* _solver_ptr = solver.get();

        role_vars = std::vector<variable>((unsigned long) policy->atom_count());
        core_sets = std::vector<variable>((unsigned long) policy->atom_count());
        core_value_true = std::vector<variable>((unsigned long) policy->atom_count());
        core_value_false = std::vector<variable>((unsigned long) policy->atom_count());
        // ext_vars = new std::shared_ptr<variable>[role_array_size];
        program_counter = variable("pc", -1, pc_size, _solver_ptr, BIT_VECTOR);

        nondet_bool = variable("nondet_bool", -1, 1, _solver_ptr, BOOLEAN);
        // fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
        skip = variable("skip", 0, 1, _solver_ptr, BOOLEAN);

        for (int i = 0; i < policy->atom_count(); i++) {
            if (core_roles[i]) {
                // fprintf(outputFile, "/*---------- CORE ROLES ---------*/\n");
                fmt << "core_" << policy->atoms()[i]->name;
                role_vars[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr, BOOLEAN);
                clean_fmt();
                // fprintf(outputFile, "/*---------- SET CHECKS ---------*/\n");
                fmt << "set_" << policy->atoms()[i]->name;
                core_sets[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr, BOOLEAN);
                clean_fmt();
                // fprintf(outputFile, "/*---------- VALUE TRUE CHECKS ---------*/\n");
                fmt << "value_true_" << policy->atoms()[i]->name;
                core_value_true[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr, BOOLEAN);
                clean_fmt();
                // fprintf(outputFile, "/*---------- VALUE FALSE CHECKS ---------*/\n");
                fmt << "value_false_" << policy->atoms()[i]->name;
                core_value_false[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr, BOOLEAN);
                clean_fmt();
            }
            else {
                // fprintf(outputFile, "/*---------- EXTERNAL ROLES ---------*/\n");
                fmt << "ext_" << policy->atoms()[i]->name;
                role_vars[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr, BOOLEAN);
                clean_fmt();
                core_sets[i] = variable::dummy();
                core_value_true[i] = variable::dummy();
                core_value_false[i] = variable::dummy();
            }
        }
    }

    void set_globals() {
        emit_assignment(skip, zero);

        for (int i = 0; i < policy->atom_count(); i++) {
            if (core_roles[i]) {
                // fprintf(outputFile, "/*---------- SET CHECKS = 1 ---------*/\n");
                emit_assignment(core_sets[i], zero);
                emit_assignment(core_value_true[i], zero);
                emit_assignment(core_value_false[i], zero);
            }
        }
    }

    SMTExpr generate_if_SKIP_PC(int pc) {
        // fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
        return solver->createAndExpr(solver->createNotExpr(skip.get_solver_var()),
                                     solver->createEqExpr(program_counter.get_solver_var(),
                                                          solver->createBVConst(pc, pc_size)));
    }

    SMTExpr generate_from_prec(const Expr &precond) {
//        SMSMTExpr* array = get_t_array(precond->literals());

//        if (log) {
//            target_rule->print();
//            for (int i = 0; i < policy->atom_count(); ++i) {
//                std::cout << role_vars[i] << "; ";
//            }
//            std::cout << std::endl << std::endl;
//        }

        SMTExpr res = generateSMTFunction(solver, precond, role_vars, "");

//        delete[] array;
//        std::cout << "\t" << res << std::endl;
//        for (auto ite = map.begin(); ite != map.end(); ++ite) {
//            std::cout << ite->first << ": " << ite->second << std::endl;
//        }
        return res;
    }

    SMTExpr generate_CA_cond(const Expr& ca_precond) {
        return generate_from_prec(ca_precond);
    }

    SMTExpr generate_CR_cond(const Expr& cr_precond) {
        return generate_from_prec(cr_precond);
    }

    SMTExpr get_assignment_cond_by_role(const atomp& target_role, int label_index) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        SMTExpr if_prelude = generate_if_SKIP_PC(label_index);
        SMTExpr ca_guards = solver->createFalse();

        for (auto &&rule :policy->per_role_can_assign_rule(target_role)) {
//            if (excluded_rules != nullptr && (rule->is_ca == target_rule->is_ca) && (rule == target_rule)) {
            if (contains(excluded_rules.begin(), excluded_rules.end(), rule)) {
                // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                continue;
            }
            // print_ca_comment(outputFile, ca_idx);
            ca_guards = solver->createOrExpr(ca_guards, generate_CA_cond(rule->prec));
            // fprintf(outputFile, "        ||\n");
        }

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        SMTExpr not_set = solver->createNotExpr(core_sets[target_role->role_array_index].get_solver_var());
        SMTExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, ca_guards), not_set);
        return cond;
    }

    SMTExpr get_revoke_cond_by_role(const atomp& target_role, int label_index) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        SMTExpr if_prelude = generate_if_SKIP_PC(label_index);
        SMTExpr cr_guards = solver->createFalse();

        for (auto &&rule :policy->per_role_can_revoke_rule(target_role)) {
//            if (target_rule != nullptr && (rule->is_ca == target_rule->is_ca) && (rule == target_rule)) {
            if (contains(excluded_rules.begin(), excluded_rules.end(), rule)) {
                // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
                continue;
            }
            cr_guards = solver->createOrExpr(cr_guards, generate_CR_cond(rule->prec));
        }

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        SMTExpr not_set = solver->createNotExpr(core_sets[target_role->role_array_index].get_solver_var());
        SMTExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, cr_guards), not_set);
        return cond;
    }

    void simulate_can_assigns_by_role(const atomp& target_role, int label_index) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        SMTExpr cond = get_assignment_cond_by_role(target_role, label_index);

        int target_role_index = target_role->role_array_index;

        SMTExpr new_role_val = solver->createCondExpr(cond, one, role_vars[target_role_index].get_solver_var());
        SMTExpr new_set_val = solver->createCondExpr(cond, one, core_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            core_%s = 1;\n", role_array[target_role_index]);
        variable new_role_var = role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        role_vars[target_role_index] = new_role_var;


        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = core_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        core_sets[target_role_index] = new_set_var;
    }

    void simulate_can_revokes_by_role(const atomp& target_role, int label_index) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        SMTExpr cond = get_revoke_cond_by_role(target_role, label_index);

        int target_role_index = target_role->role_array_index;

        SMTExpr new_role_val = solver->createCondExpr(cond, zero, role_vars[target_role_index].get_solver_var());
        SMTExpr new_set_val = solver->createCondExpr(cond, one, core_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            core_%s = 0;\n", role_array[target_role_index]);
        variable new_role_var = role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        role_vars[target_role_index] = new_role_var;

        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = core_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        core_sets[target_role_index] = new_set_var;
    }

    void simulate_skip(int label_index) {
        // Do not apply any translation and set skip to true
        // fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
        // fprintf(outputFile, "        skip = 1;");
        // fprintf(outputFile, "    }");
        variable new_skip = skip.createFrom();
        SMTExpr cond = solver->createGEqExpr(program_counter.get_solver_var(), solver->createBVConst(label_index, pc_size));
        SMTExpr new_val = solver->createCondExpr(cond, one, skip.get_solver_var());

        emit_assignment(new_skip, new_val);

        skip = new_skip;

    }

    SMTExpr generate_check_implication(int role_index, const userp& user) {
        //((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
        SMTExpr init_r_i = zero;
        for (auto &&atom : user->config()) {
            if (atom->role_array_index == role_index) {
                init_r_i = one;
                break;
            }
        }

        SMTExpr role_var = role_vars[role_index].get_solver_var();
        SMTExpr role_set = core_sets[role_index].get_solver_var();
        SMTExpr set_false_r_i = core_value_false[role_index].get_solver_var();
        SMTExpr set_true_r_i = core_value_true[role_index].get_solver_var();

        SMTExpr impl_prec =
            solver->createOrExpr(
                solver->createNotExpr(solver->createEqExpr(role_var, init_r_i)),
                solver->createOrExpr(
                    solver->createAndExpr(set_false_r_i, solver->createEqExpr(init_r_i, one)),
                    solver->createAndExpr(set_true_r_i, solver->createEqExpr(init_r_i, zero))
                ));

        SMTExpr cond = solver->createImplExpr(impl_prec,
                                            role_set);

        // fprintf(outputFile, "((core_%s != %d) => set_%s))", role, init_r_i, role);
        return cond;
    }

    void generate_check() {
        // fprintf(outputFile, "    /*--------------- ERROR CHECK ------------*/\n");
        // fprintf(outputFile, "    /*--------------- assume(\\phi) ------------*/\n");
        //FIXME: this if could be removed since if not tampone the free set is empty
        if (!Config::use_tampone) {
            SMTExpr rule_assumption = generate_from_prec(target_expr);
            emit_assumption(rule_assumption);
        } else {
            std::vector<variable> free_var_vect((ulong) policy->atom_count());
            for (auto &&atom : policy->atoms()) {
                free_var_vect[atom->role_array_index] = variable("adm_" + atom->name, 0, 1, solver.get(), BOOLEAN);
            }
            SMTExpr rule_assumption = generateSMTFunction2(solver, target_expr, free, role_vars, free_var_vect, "", "free");
            emit_assumption(rule_assumption);
        }

        int user_id = 0;
        //         \  /          /\
        // assume(  \/        ( /  \          ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i)))
        //        u_i \in U    r_i \in \phi
        // fprintf(outputFile, "//         \\  /          /\\\n");
        // fprintf(outputFile, "// assume(  \\/        ( /  \\          ((core_r_i != init_r_i) \\/ ((set_false_r_i /\\ init_r_i = 1) \\/ (set_true_r_i /\\ init_r_i = 0)) => set_r_i)))\n");
        // fprintf(outputFile, "//        u_i \\in U    r_i \\in \\phi\n");
        SMTExpr impl_assumption = zero;
        std::set<userp, std::function<bool(const userp&, const userp&)>> users;
        if (target_user == nullptr) {
            users = policy->unique_configurations();
        } else {
            users.insert(target_user);
        }
        for (auto &&user : users) {
            SMTExpr inner_and = one;
            for (int i = 0; i < policy->atom_count(); i++) {
                if (core_roles[i]) {
                    SMTExpr impl_r_ui = generate_check_implication(i, user);
                    inner_and = solver->createAndExpr(inner_and, impl_r_ui);
                }
            }
            impl_assumption = solver->createOrExpr(impl_assumption, inner_and);
        }
        emit_assumption(impl_assumption);
        // fprintf(outputFile, "    assert(0);\n");
    }

    void generate_update_state() {
        // fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
        for (int i = 0; i < policy->atom_count(); i++) {
            if (core_roles[i]) {
                variable new_core = role_vars[i].createFrom();
                // COULD BE REMOVED
                nondet_bool = nondet_bool.createFrom();

                SMTExpr new_val = solver->createCondExpr(core_sets[i].get_solver_var(), role_vars[i].get_solver_var(), nondet_bool.get_solver_var());
                emit_assignment(new_core, new_val);

                role_vars[i] = new_core;

                // UPDATE VALUE_TRUE
                variable new_value_true = core_value_true[i].createFrom();
                SMTExpr new_value_true_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), one), one, core_value_true[i].get_solver_var());
                emit_assignment(new_value_true, new_value_true_var);
                core_value_true[i] = new_value_true;

                // UPDATE VALUE_FALSE
                variable new_value_false = core_value_false[i].createFrom();
                SMTExpr new_value_false_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), zero), one, core_value_false[i].get_solver_var());
                emit_assignment(new_value_false, new_value_false_var);
                core_value_false[i] = new_value_false;


                // fprintf(outputFile, "    core_%s = set_%s ? core_%s : nondet_bool();\n", role, role, role);
            }
            else {
                variable nvar = role_vars[i].createFrom();
                role_vars[i] = nvar;
            }
        }

        program_counter = program_counter.createFrom();
        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");

    }

    void generate_round() {
        int label_idx = 0;
        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_update_state();


        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            if (core_roles[atom->role_array_index] && policy->per_role_can_assign_rule(atom).size() > 0) {
//                int exclude = target_rule->is_ca ? exclude_idx : -1;
                simulate_can_assigns_by_role(atom, label_idx++);
            }
        }

        // fprintf(outputFile, "\n\n");

        // fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
        for (auto &&atom :policy->atoms()) {
            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
            if (core_roles[atom->role_array_index] && policy->per_role_can_revoke_rule(atom).size() > 0) {
//                int exclude = !excluded_is_ca ? exclude_idx : -1;
                simulate_can_revokes_by_role(atom, label_idx++);
            }
        }

        simulate_skip(label_idx);
        // fprintf(outputFile, "\n\n");
    }

    void generate_main() {
        // fprintf(outputFile, "int main(void) {\n\n");

        for (int i = 0; i < core_roles_size; ++i) {
            generate_round();
        }
        generate_check();
        // fprintf(outputFile, "    return 0;\n");
        // fprintf(outputFile, "}\n");
    }

    bool checkUnreachable() {
        set_globals();
        generate_main();


//        if (Config::dump_smt_formula != "") {
//            solver->printContext(Config::dump_smt_formula);
//            log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
//        }
        SMTResult res = solver->solve();

//        std::cout << *target_rule << std::endl;
//
//        solver->printContext("z3.lisp");

        return res == SMTResult::UNSAT;
    }


    public:
    R6Transformer(const std::shared_ptr<SMTFactory>& _solver,
                  const std::shared_ptr<arbac_policy>& _policy,
                  const Expr& _to_check,
                  const std::set<Expr>& _free,
                  const std::list<rulep>& _excluded_rules,
                  const userp& _target_user) :
        solver(_solver),
        policy(_policy),
        excluded_rules(_excluded_rules),
        target_expr(_to_check),
        target_user(_target_user),
        pc_size(get_pc_size(target_expr->atoms())) {
        solver->deep_clean();
        free = _free,
        zero = solver->createFalse();
        one = solver->createTrue();
        allocate_core_role_array_set_pc_size();
        generate_variables();
    }

    ~R6Transformer() {
//        deallocate_precomputated_values();
        free_core_role_array();
    }

    bool apply_r6() {
        return checkUnreachable();
    }
};

    bool apply_r6(const std::shared_ptr<SMTFactory>& solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const Expr& to_check,
                  const std::set<Expr>& free,
                  const std::list<rulep>& excluded_rules,
                  const userp& tracked_user) {
        if (is_constant_true(to_check)) {
            return false;
        }
        R6Transformer transf(solver, policy, to_check, free, excluded_rules, tracked_user);
        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
        bool res = transf.apply_r6();
        // if (res || true)
        //     solver->printContext();
        return res;
    }

    bool apply_r6(const std::shared_ptr<SMTFactory>& solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const Expr& to_check,
                  const std::set<Expr>& free,
                  const rulep& to_check_source,
                  const userp& tracked_user) {
        std::list<rulep> excluded;
        excluded.push_back(to_check_source);
        return apply_r6(solver, policy, to_check, free, excluded, tracked_user);
    }

}
