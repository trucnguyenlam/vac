#include "ARBACExact.h"
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

#include <chrono>

namespace SMT {

template <typename TVar, typename TExpr>
class R6Transformer {
    private:
    
    std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
    std::stringstream fmt;

    void clean_fmt() {
        fmt.str(std::string());
    }

    // typedef 
    struct variable {
        std::shared_ptr<TVar> solver_varp;
        // std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
        SMTFactory<TVar, TExpr>* solver;
        int bv_size;
        std::string name;
        std::string full_name;
        int idx;

        variable() :
            solver_varp(nullptr), bv_size(-1), name(""), full_name(""), idx(-1), solver(nullptr) { }

        variable(const std::string _name, int _idx, int _bv_size, SMTFactory<TVar, TExpr>* _solver) : 
            bv_size(_bv_size), name(_name), full_name(_name + "_" + std::to_string(_idx)), idx(_idx), solver(_solver), solver_varp(nullptr) {
                // printf("CN: %s\n", full_name.c_str());
                solver_varp = std::make_shared<TVar>(solver->createVar2(full_name, bv_size));

                // TVar var_val = solver->createVar2(full_name, bv_size);
                // printf("%s: %d\n", name.c_str(), var_val);
                // int res = yices_pp_term(stdout, var_val, 160, 40, 0);
                // if (res < 0 || var_val == 0) {
                //     printf("wtf??\n");
                // }
                // printf("%s: %d\n", name.c_str(), *solver_varp);
                // res = yices_pp_term(stdout, *solver_varp, 160, 40, 0);
                // if (res < 0 || *solver_varp == 0) {
                //     printf("wtf??\n");
                // }

             }

        // ~variable() {
        //     delete[] solver_varp;
        // }

        // variable(std::string _name, int _idx, int _bv_size, TExpr value) : 
        //     bv_size(_bv_size), name(_name), idx(_idx),
        //     solver_var(solver->createVar2(_name + "_" + std::to_string(_idx)), _bv_size)  { }

        inline TVar get_solver_var() {
            if (solver_varp == nullptr)
                throw new std::runtime_error("Null variable");
            else {
                return *solver_varp;
            }
        }

        variable createFrom() {
            // printf("GF: %s\n", this->full_name.c_str());
            return variable(this->name, this->idx + 1, this->bv_size, this->solver);
        }

        static variable dummy() {
            variable res;
            res.name = std::string("dummy");
            res.idx = -1;
            res.bv_size = -1;
            return res;
        }

        // TExpr getAssignment() {
        //     if (solver_val == nullptr) {
        //         return solver->createTrue();
        //     }
        //     else {
        //         return solver->createEqExpr(solver_var, *solver_val);
        //     }
        // }

    }; 
    // variable;

    // variable dummy_var;

    /*--- SMT VARIABLE INDEXES ---*/
    /*--- VALUES ARE  ---*/
    variable* role_vars;
    variable* core_value_true;
    variable* core_value_false;
    variable* core_sets;
    variable program_counter;
    variable skip;
    variable nondet_bool;

    std::vector<Expr> ca_prec;
    std::vector<Expr> cr_prec;
    Expr target;

    TExpr zero;
    TExpr one;

    bool *core_roles = NULL;
    int core_roles_size = 0;
    int pc_size;

    int *roles_ca_counts = NULL;
    int *roles_cr_counts = NULL;
    int **per_role_ca_indexes = NULL;
    int **per_role_cr_indexes = NULL;

    void emit_assignment(variable& variable, TExpr value) {
        TExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
        solver->assertLater(assign);
    }

    void emit_assumption(TExpr expr) {
        solver->assertLater(expr);
    }

    void allocate_core_role_array(Expr t_expr) {
        auto cores = t_expr->literals();
        core_roles = new bool[role_array_size];
        for (int i = 0; i < role_array_size; i++) {
            core_roles[i] = false;
        }

        for (auto ite = cores.begin(); ite != cores.end(); ++ite) {
            core_roles[(*ite)->role_array_index] = true;
            core_roles_size++;
        }
        pc_size = numBits(core_roles_size + 1);
    }

    void free_core_role_array() {
        delete[] core_roles;
    }

    void precompute_merge() {

        float assignable_roles_count = 0;
        float removable_roles_count = 0;

        roles_ca_counts = new int[role_array_size];
        roles_cr_counts = new int[role_array_size];
        per_role_ca_indexes = new int*[role_array_size];
        per_role_cr_indexes = new int*[role_array_size];

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
                per_role_ca_indexes[i] = new int[roles_ca_counts[i]];

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
                per_role_cr_indexes[i] = new int[roles_cr_counts[i]];

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

    void deallocate_precomputated_values() {
        for (int i = 0; i < role_array_size; ++i) {
            if (per_role_ca_indexes[i] != NULL)
                delete[] per_role_ca_indexes[i];
            if (per_role_cr_indexes[i] != NULL)
                delete[] per_role_cr_indexes[i];
        }
        delete[] roles_ca_counts;
        delete[] roles_cr_counts;
        delete[] per_role_ca_indexes;
        delete[] per_role_cr_indexes;
    }

    int numBits(unsigned long pc) {
        int i = 1, bit = 0;

        if (pc < 2) return 1;

        while (pc >= i) {
            i = i * 2;
            bit++;
        }

        return (bit);
    }

    void generate_header(char *inputFile, int rule_id, int is_ca) {
        time_t mytime;
        mytime = time(NULL);
        fprintf(stdout, "/*\n");
        fprintf(stdout, "*  generated by VAC pruning-R6 [ 0000 / 0000 ]\n");
        fprintf(stdout, "*\n");
        fprintf(stdout, "*  instance version    {}\n");
        fprintf(stdout, "*\n");
        fprintf(stdout, "*  %s\n", ctime(&mytime));
        fprintf(stdout, "*\n");
        fprintf(stdout, "*  params:\n");
        fprintf(stdout, "*    %s, --rounds %d\n", inputFile, core_roles_size + 1);
        fprintf(stdout, "* MERGE_RULES\n");
        fprintf(stdout, "*\n");
        fprintf(stdout, "*  users: %d\n", user_array_size);
        fprintf(stdout, "*  roles: %d\n", role_array_size);
        fprintf(stdout, "*  adminroles: %d\n", admin_role_array_index_size);
        fprintf(stdout, "*  CA: %d\n", ca_array_size);
        fprintf(stdout, "*  CR: %d\n", cr_array_size);
        fprintf(stdout, "*\n");
        fprintf(stdout, "*  Rule: %s, id: %d:\n", is_ca ? "CA" : "CR", rule_id);
        if (is_ca) {
            print_ca_comment(stdout, rule_id);
        }
        else {
            print_cr_comment(stdout, rule_id);
        }
        fprintf(stdout, "*/\n");
        fprintf(stdout, "\n\n");

        // fprintf(stdout, "#define IF(PC,COND,APPL) if (");
        // fprintf(stdout, "(__cs_pc0 == PC) && (COND) ) { APPL; }\n");

        fprintf(stdout, "\n");

        return;
    }

    void generate_variables() {

        // fprintf(outputFile, "/*---------- INIT GLOBAL VARIABLES ---------*/\n\n");
        SMTFactory<TVar, TExpr>* _solver_ptr = solver.get();

        role_vars = new variable[role_array_size];
        core_sets = new variable[role_array_size];
        core_value_true = new variable[role_array_size];
        core_value_false = new variable[role_array_size];
        // ext_vars = new std::shared_ptr<variable>[role_array_size];
        program_counter = variable("pc", -1, pc_size, _solver_ptr);

        nondet_bool = variable("nondet_bool", -1, 1, _solver_ptr);
        // fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
        skip = variable("skip", 0, 1, _solver_ptr);

        for (int i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                // fprintf(outputFile, "/*---------- CORE ROLES ---------*/\n");
                fmt << "core_" << role_array[i];
                role_vars[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr);
                clean_fmt();
                // fprintf(outputFile, "/*---------- SET CHECKS ---------*/\n");
                fmt << "set_" << role_array[i];
                core_sets[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr);
                clean_fmt();
                // fprintf(outputFile, "/*---------- VALUE TRUE CHECKS ---------*/\n");
                fmt << "value_true_" << role_array[i];
                core_value_true[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr);
                clean_fmt();
                // fprintf(outputFile, "/*---------- VALUE FALSE CHECKS ---------*/\n");
                fmt << "value_false_" << role_array[i];
                core_value_false[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr);
                clean_fmt();
            }
            else {
                // fprintf(outputFile, "/*---------- EXTERNAL ROLES ---------*/\n");
                fmt << "ext_" << role_array[i];
                role_vars[i] = variable(fmt.str().c_str(), 0, 1, _solver_ptr);
                clean_fmt();
                core_sets[i] = variable::dummy();
                core_value_true[i] = variable::dummy();
                core_value_false[i] = variable::dummy();
            }
        }
    }

    void free_globals() {
        delete[] role_vars;
        delete[] core_sets;
        delete[] core_value_true;
        delete[] core_value_false;
    }

    void set_globals() {
        emit_assignment(skip, zero);

        for (int i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                // fprintf(outputFile, "/*---------- SET CHECKS = 1 ---------*/\n");
                emit_assignment(core_sets[i], zero);
                emit_assignment(core_value_true[i], zero);
                emit_assignment(core_value_false[i], zero);
            }
        }
    }

    TExpr generate_if_SKIP_PC(int pc) {
        // fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
        return solver->createAndExpr(solver->createNotExpr(skip.get_solver_var()),
                                     solver->createEqExpr(program_counter.get_solver_var(), 
                                                          solver->createBVConst(pc, pc_size)));
    }

    std::shared_ptr<TVar>* get_t_array(const std::set<Literalp>& literals) {
        std::shared_ptr<TVar>* array = new std::shared_ptr<TVar>[role_array_size];
        for (int i = 0; i < role_array_size; ++i) {
            array[i] = nullptr;
        }
        for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
            Literalp role_lit = *ite;
            std::shared_ptr<TVar> var = role_vars[role_lit->role_array_index].solver_varp;
            if (var == nullptr) {
                std::cerr << "Solver variable of role " << role_lit->name << " is null..." << std::endl;
                throw new std::runtime_error("Null variable");
            }
            array[role_lit->role_array_index] = var;
        }
        return array;
    };

    TExpr generate_from_prec(const Expr &precond) {
        std::shared_ptr<TVar>* array = get_t_array(precond->literals());

        TExpr res = generateSMTFunction(solver, precond, array, "");

        delete[] array;
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

    TExpr get_assignment_cond_by_role(int target_role_index, int label_index, int excluded_rule) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        TExpr if_prelude = generate_if_SKIP_PC(label_index);
        TExpr ca_guards = solver->createFalse();
        
        for (int i = 0; i < roles_ca_counts[target_role_index]; ++i) {
            int ca_idx = per_role_ca_indexes[target_role_index][i];
            if (ca_idx != excluded_rule) {
                // print_ca_comment(outputFile, ca_idx);
                ca_guards = solver->createOrExpr(ca_guards, generate_CA_cond(ca_prec[ca_idx]));
                // fprintf(outputFile, "        ||\n");
            }
        }

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(core_sets[target_role_index].get_solver_var());
        TExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, ca_guards), not_set);
        return cond;
    }

    TExpr get_revoke_cond_by_role(int target_role_index, int label_index, int excluded_rule) {
        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
        // fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
        TExpr if_prelude = generate_if_SKIP_PC(label_index);
        TExpr cr_guards = solver->createFalse();
        
        for (int i = 0; i < roles_cr_counts[target_role_index]; ++i) {
            int cr_idx = per_role_cr_indexes[target_role_index][i];
            if (cr_idx != excluded_rule) {
                // print_cr_comment(outputFile, ca_idx);
                cr_guards = solver->createOrExpr(cr_guards, generate_CR_cond(cr_prec[cr_idx]));
                // fprintf(outputFile, "        ||\n");
            }
        }

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        TExpr not_set = solver->createNotExpr(core_sets[target_role_index].get_solver_var());
        TExpr cond = solver->createAndExpr(solver->createAndExpr(if_prelude, cr_guards), not_set);
        return cond;
    }

    void simulate_can_assigns_by_role(int target_role_index, int label_index, int excluded_rule) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        TExpr cond = get_assignment_cond_by_role(target_role_index, label_index, excluded_rule);

        TExpr new_role_val = solver->createCondExpr(cond, one, role_vars[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(cond, one, core_sets[target_role_index].get_solver_var());


        // fprintf(outputFile, "            core_%s = 1;\n", role_array[target_role_index]);
        variable new_role_var = role_vars[target_role_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        role_vars[target_role_index] = new_role_var;


        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = core_sets[target_role_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        core_sets[target_role_index] = new_set_var;
    }

    void simulate_can_revokes_by_role(int target_role_index, int label_index, int excluded_rule) {
        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        TExpr cond = get_revoke_cond_by_role(target_role_index, label_index, excluded_rule);

        TExpr new_role_val = solver->createCondExpr(cond, zero, role_vars[target_role_index].get_solver_var());
        TExpr new_set_val = solver->createCondExpr(cond, one, core_sets[target_role_index].get_solver_var());


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
        TExpr cond = solver->createGEqExpr(program_counter.get_solver_var(), solver->createBVConst(label_index, pc_size));
        TExpr new_val = solver->createCondExpr(cond, one, skip.get_solver_var());

        emit_assignment(new_skip, new_val);

        skip = new_skip;
        
    }

    TExpr generate_check_implication(int role_index, int user_id) {
        //((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
        TExpr init_r_i = zero;
        for (int j = 0; j < user_config_array[user_id].array_size; j++) {
            if (user_config_array[user_id].array[j] == role_index) {
                init_r_i = one;
                break;
            }
        }    

        TVar role_var = role_vars[role_index].get_solver_var();
        TVar role_set = core_sets[role_index].get_solver_var();
        TVar set_false_r_i = core_value_false[role_index].get_solver_var();
        TVar set_true_r_i = core_value_true[role_index].get_solver_var();

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

        TExpr rule_assumption = generate_from_prec(target);
        emit_assumption(rule_assumption);

        int user_id = 0;
        //         \  /          /\
        // assume(  \/        ( /  \          ((core_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) => set_r_i)))
        //        u_i \in U    r_i \in \phi
        // fprintf(outputFile, "//         \\  /          /\\\n");
        // fprintf(outputFile, "// assume(  \\/        ( /  \\          ((core_r_i != init_r_i) \\/ ((set_false_r_i /\\ init_r_i = 1) \\/ (set_true_r_i /\\ init_r_i = 0)) => set_r_i)))\n");
        // fprintf(outputFile, "//        u_i \\in U    r_i \\in \\phi\n");
        TExpr impl_assumption = zero;
        for (int u = 0; u < user_array_size; u++) {
            TExpr inner_and = one;
            for (int i = 0; i < role_array_size; i++) {
                if (core_roles[i]) {
                    TExpr impl_r_ui = generate_check_implication(i, u);
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
        for (int i = 0; i < role_array_size; i++) {
            if (core_roles[i]) {
                variable new_core = role_vars[i].createFrom();
                // COULD BE REMOVED
                nondet_bool = nondet_bool.createFrom();

                TExpr new_val = solver->createCondExpr(core_sets[i].get_solver_var(), role_vars[i].get_solver_var(), nondet_bool.get_solver_var());
                emit_assignment(new_core, new_val);

                role_vars[i] = new_core;

                // UPDATE VALUE_TRUE
                variable new_value_true = core_value_true[i].createFrom();
                TExpr new_value_true_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), one), one, core_value_true[i].get_solver_var());
                emit_assignment(new_value_true, new_value_true_var);
                core_value_true[i] = new_value_true;

                // UPDATE VALUE_FALSE
                variable new_value_false = core_value_false[i].createFrom();
                TExpr new_value_false_var = solver->createCondExpr(solver->createEqExpr(role_vars[i].get_solver_var(), zero), one, core_value_false[i].get_solver_var());
                emit_assignment(new_value_false, new_value_false_var);
                core_value_false[i] = new_value_false;

                
                // fprintf(outputFile, "    core_%s = set_%s ? core_%s : nondet_bool();\n", role, role, role);
            }
            else {
                role_vars[i] = role_vars[i].createFrom();
            }
        }
        for (int i = 0; i < role_array_size; i++) {
            
        }

        program_counter = program_counter.createFrom();
        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");
        
    }

    void generate_round(int exclude_idx, bool excluded_is_ca) {
        int label_idx = 0;
        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_update_state();


        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (int i = 0; i < role_array_size; ++i) {
            if (core_roles[i] && roles_ca_counts[i] > 0) {
                int exclude = excluded_is_ca ? exclude_idx : -1;
                simulate_can_assigns_by_role(i, label_idx++, exclude);
            }
        }

        // fprintf(outputFile, "\n\n");

        // fprintf(outputFile, "    /*---------- CAN REVOKE SIMULATION ---------*/\n");
        for (int i = 0; i < role_array_size; ++i) {
            // printf("CR idx: %d, role: %s: count: %d\n", i, role_array[i], roles_cr_counts[i]);
            if (core_roles[i] && roles_cr_counts[i] > 0) {
                int exclude = !excluded_is_ca ? exclude_idx : -1;
                simulate_can_revokes_by_role(i, label_idx++, exclude);
            }
        }

        simulate_skip(label_idx);
        // fprintf(outputFile, "\n\n");
    }

    void
    generate_main(int exclude_idx, bool excluded_is_ca) {
        // fprintf(outputFile, "int main(void) {\n\n");
        
        for (int i = 0; i < core_roles_size; ++i) {
            generate_round(exclude_idx, excluded_is_ca);
        }
        generate_check();
        // fprintf(outputFile, "    return 0;\n");
        // fprintf(outputFile, "}\n");
    }

    bool checkUnreachable(int exclude_idx, bool excluded_is_ca) {
        set_globals();
        generate_main(exclude_idx, excluded_is_ca);

        SMTResult res = solver->solve();

        return res == UNSAT;
    }


    public:
    R6Transformer(std::shared_ptr<SMTFactory<TVar, TExpr>> _solver, std::vector<Expr>& _ca_exprs, std::vector<Expr>& _cr_exprs, Expr _to_check) :
        solver(_solver), pc_size(numBits(_to_check->literals().size())),
        ca_prec(_ca_exprs), cr_prec(_cr_exprs), target(_to_check),
        zero(solver->createFalse()), one(solver->createTrue()) {
        precompute_merge();
        allocate_core_role_array(_to_check);
        generate_variables();
    }

    ~R6Transformer() {
        deallocate_precomputated_values();
        free_core_role_array();
        free_globals();
    }

    bool apply_r6(int exclude_idx, bool excluded_is_ca) {
        return checkUnreachable(exclude_idx, excluded_is_ca);
    }
};

    template <typename TVar, typename TExpr>
    bool apply_r6(std::shared_ptr<SMTFactory<TVar, TExpr>> solver,
                  std::vector<Expr>& ca_exprs,
                  std::vector<Expr>& cr_exprs,
                  Expr to_check,
                  int exclude_idx, bool excluded_is_ca) {
        R6Transformer<TVar, TExpr> transf(solver, ca_exprs, cr_exprs, to_check);
        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
        bool res = transf.apply_r6(exclude_idx, excluded_is_ca);
        // if (res || true)
        //     solver->printContext();
        return res;
    }


    template bool apply_r6<term_t, term_t>(std::shared_ptr<SMTFactory<term_t, term_t>> solver,
                                           std::vector<Expr>& ca_exprs,
                                           std::vector<Expr>& cr_exprs,
                                           Expr to_check,
                                           int exclude_idx, bool excluded_is_ca);
    template bool apply_r6<expr, expr>(std::shared_ptr<SMTFactory<expr, expr>> solver,
                                       std::vector<Expr>& ca_exprs,
                                       std::vector<Expr>& cr_exprs,
                                       Expr to_check,
                                       int exclude_idx, bool excluded_is_ca);


//    bool apply_r6(int rule_index, bool is_ca) {
//        std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
//        R6Transformer<term_t, term_t> transf(solver, rule_index, is_ca);
//        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
//        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
//        bool res = transf.apply_r6(rule_index, is_ca);
//        // if (res || true)
//        //     solver->printContext();
//        return res;
//    }

}
