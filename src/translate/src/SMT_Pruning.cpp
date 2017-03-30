
#include <vector>
#include <set>
#include <memory>
#include <string>
#include <chrono>
#include <iostream>
#include <utility>

#include "ARBACExact.h"
#include "SMT_Pruning.h"
#include "SMT.h"
#include "Logics.h"
#include "SMTSolvers/yices.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    class Pruning {
        // struct formula {
        //     TExpr formula;
        //     std::set<int> variables;
        // };

        int set_contains(Expr expr, std::string name) {
            std::set<Literalp> literals = expr->literals();
            for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
                Literalp e = *ite;
                if (e->name == name) {
                    return true;
                }
            }
            return false;
        }

        void generateRoleVars() {
            for (int i = 0; i < role_array_size; i++) {
                std::string rname(role_array[i]);
                Literalp var = createLiteralp(rname, 1);
                role_vars.push_back(var);
            }
        }

        Expr getCRAdmFormula(int ruleId) {
            Expr ret = role_vars[cr_array[ruleId].admin_role_index];
            return ret;
        }

        Expr getCRPNFormula(int ruleId) {
            return createConstantExpr(true, 1);
        }

        Expr getCAAdmFormula(int ca_index) {
            Expr ret = role_vars[ca_array[ca_index].admin_role_index];
            return ret;
        }

        Expr getCAPNFormula(int ca_index) {
            Expr cond = createConstantExpr(true, 1);

            if (ca_array[ca_index].type == 0) {     // Has precondition
                // P
                if (ca_array[ca_index].positive_role_array_size > 0) {
                    int* ca_array_p = ca_array[ca_index].positive_role_array;
                    std::string rp_name = std::string(role_array[ca_array_p[0]]);
                    Expr ca_cond = role_vars[ca_array_p[0]];
                    for (int j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                        rp_name = std::string(role_array[ca_array_p[j]]);
                        ca_cond = createAndExpr(ca_cond, role_vars[ca_array_p[j]]);
                    }
                    cond = createAndExpr(cond, ca_cond);
                }
                // N
                if (ca_array[ca_index].negative_role_array_size > 0) {
                    int* ca_array_n = ca_array[ca_index].negative_role_array;
                    std::string rn_name = std::string(role_array[ca_array_n[0]]);
                    Expr cr_cond = createNotExpr(role_vars[ca_array_n[0]]);
                    for (int j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                        rn_name = std::string(role_array[ca_array_n[j]]);
                        cr_cond = createAndExpr(cr_cond, createNotExpr(role_vars[ca_array_n[j]]));
                    }
                    cond = createAndExpr(cond, cr_cond);
                }
            }

            return cond;
        }

        void generate_ca_cr_formulae() {
            int i;
            for (i = 0; i < ca_array_size; i++) {
                ca_adm_formulae.push_back(getCAAdmFormula(i));
                ca_pn_formulae.push_back(getCAPNFormula(i));
                // print_ca_comment(stdout, i);
                // printf("%s\n", getCAPNFormula(i)->print().c_str());
            }
            for (i = 0; i < cr_array_size; i++) {
                cr_adm_formulae.push_back(getCRAdmFormula(i));
                cr_pn_formulae.push_back(getCRPNFormula(i));
                // print_cr_comment(stdout, i);
                // printf("%s\n", getCRPNFormula(i)->print().c_str());
            }
        }

        int nonPositive(int roleId) {
            std::string role_name(role_array[roleId]);
            std::vector<Expr> to_check;
            auto ite = ca_adm_formulae.begin();
            for ( ; ite != ca_adm_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }            
            for (ite = ca_pn_formulae.begin(); ite != ca_pn_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }

            ite = cr_adm_formulae.begin();
            for ( ; ite != cr_adm_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }
            ite = cr_pn_formulae.begin();
            for ( ; ite != cr_pn_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                solver->clean();
                ite = to_check.begin();
                Expr cond = *ite;
                for ( ; ite != to_check.end(); ++ite) {
                    cond = createOrExpr(cond, *ite);
                }
                
                // if (std::string(role_array[roleId]) == "rd") {
                //     cond->setLiteralValue("rd", createConstantExpr(1, 1));
                // }
                
                std::map<std::string, TVar> map;
                TExpr fexpr = generateSMTFunction(solver, cond, map, "");
                
                TExpr lexpr = generateSMTFunction(solver, role_vars[roleId], map, "");

                // if (std::string(role_array[roleId]) == "rd") {
                //     yices_pp_term(stdout, fexpr, 160, 40, 0);
                //     yices_pp_term(stdout, lexpr, 160, 40, 0);
                // }

                solver->assertNow(lexpr);
                solver->assertNow(fexpr);
   
                // solver->loadToSolver();
                int res = false;
                switch (solver->solve()) {
                    case SAT: 
                        // fprintf(stdout, "System is SAT. Printing model...\n");
                        // solver->printModel();
                        return false;
                        break;
                    case UNSAT:
                        return true;
                        break;
                    case UNKNOWN:
                        return false;
                        break;
                }
                return res;
            }
        }

        int nonNegative(int roleId) {
            std::string role_name(role_array[roleId]);
            std::vector<Expr> to_check;
            auto ite = ca_adm_formulae.begin();
            for ( ; ite != ca_adm_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }
            ite = ca_pn_formulae.begin();
            for ( ; ite != ca_pn_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }
            ite = cr_adm_formulae.begin();
            for ( ; ite != cr_adm_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }

            ite = cr_pn_formulae.begin();
            for ( ; ite != cr_pn_formulae.end(); ++ite) {
                Expr e = *ite;
                if (set_contains(e, std::string(role_array[roleId]))) {
                    to_check.push_back(*ite);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                solver->clean();
                ite = to_check.begin();
                Expr cond = *ite;
                for ( ; ite != to_check.end(); ++ite) {
                    cond = createOrExpr(cond, *ite);
                }
                
                std::map<std::string, TVar> map;
                TExpr fexpr = generateSMTFunction(solver, cond, map, "");

                TExpr r_cond = generateSMTFunction(solver, createNotExpr(role_vars[roleId]), map, "");
                solver->assertNow(r_cond);
                solver->assertNow(fexpr);
                
                solver->loadToSolver();

                int res;
                switch (solver->solve()) {
                    case SAT: 
                        // fprintf(stdout, "System is SAT. Printing model...\n");
                        // solver->printModel();
                        res = false;
                        break;
                    case UNSAT:
                        res = true;
                        break;
                    case UNKNOWN:
                        res = false;
                        break;
                }
                return res;
            }
        }

        TExpr irr_pos(int roleId, std::vector<std::pair<Expr, Expr>> using_r, std::vector<std::pair<Expr, Expr>> assigning_r) {
            // ASSERT that ca uses role r
            std::map<std::string, TVar> c_map;
            std::map<std::string, TVar> adm_map;
            std::string role_name(role_array[roleId]);
            std::string c = "C";
            std::string adm = "adm";

            // \not C.r
            TExpr not_r_c = generateSMTFunction(solver, createNotExpr(role_vars[roleId]), c_map, c);

            std::vector<TExpr> lhs_exprs;
            for (auto u_ite = using_r.begin(); u_ite != using_r.end(); ++u_ite) {
                auto adm_pn = *u_ite;
                Expr rule_adm_expr = adm_pn.first;
                Expr rule_pn_expr = adm_pn.second;

                //generating \phi_r^{true}(C)
                rule_pn_expr->setLiteralValue(role_name, createConstantExpr(true, 1));
                TExpr phi_r_true_c = generateSMTFunction(solver, rule_pn_expr, c_map, c);
                
                //generating \not(\phi_r^{false}(C))
                // rule_pn_expr->setLiteralValue(role_name, createConstantExpr(false, 1));
                // TExpr phi_r_false_c = generateSMTFunction(solver, createNotExpr(rule_pn_expr), c_map, c);

                rule_pn_expr->resetValue();
                
                //generating \phi_a(admin)
                TExpr phi_a_adm = generateSMTFunction(solver, rule_adm_expr, adm_map, adm);

                // AND left side
                TExpr lhs = solver->createAndExpr(phi_r_true_c, phi_a_adm);

                lhs_exprs.push_back(lhs);
            }

            std::vector<TExpr> rhs_exprs;
            for (int i = 0; i < ca_array_size; i++) {
                //take only the rules assigning r. (\phi_a', \phi', r) \in CA
                if (ca_array[i].target_role_index != roleId) {
                    continue;
                }

                // \not \phi'(C)
                Expr phi1 = ca_pn_formulae[i];
                TExpr not_phi1_c = generateSMTFunction(solver, createNotExpr(phi1), c_map, c);

                // \not \phi_a'(adm)ca_adm_formulae
                Expr phi1_a = ca_adm_formulae[i];
                //setting ADMIN suffix on all literals
                TExpr not_phi1_a_adm = generateSMTFunction(solver, createNotExpr(phi1_a), adm_map, adm);

                rhs_exprs.push_back(solver->createOrExpr(not_phi1_c, not_phi1_a_adm));
            }

            // JOIN TOGETHER ALL LHS
            TExpr final_lhs = solver->createFalse();
            for (auto ite = lhs_exprs.begin(); ite != lhs_exprs.end(); ++ite) {
                final_lhs = solver->createOrExpr(final_lhs, *ite);
            }
            
            // JOIN TOGETHER ALL RHS
            TExpr final_rhs = solver->createTrue();
            for (auto ite = rhs_exprs.begin(); ite != rhs_exprs.end(); ++ite) {
                final_rhs = solver->createAndExpr(final_rhs, *ite);
            }

            // creating implication
            // TExpr res = solver->createImplExpr(impl_lhs, impl_rhs);
            TExpr res = solver->createAndExpr(not_r_c, solver->createAndExpr(final_lhs, final_rhs));
            return res;
        }

        // int deb = false;           
        // if (role_name == "rb") { deb = true; }
        // else                   { deb = false; }

        int irrelevantPositive(int roleId) {
            std::string role_name(role_array[roleId]);
            std::vector<std::pair<Expr, Expr>> using_r;
            std::vector<std::pair<Expr, Expr>> assigning_r;
            std::vector<std::pair<Expr, Expr>> removing_r;
            for (int i = 0; i < ca_array_size; i++) {
                Expr ca_adm = ca_adm_formulae[i];
                Expr ca_pn = ca_pn_formulae[i];
                if (ca_pn->containsLiteral(role_name)) {
                    using_r.push_back(std::make_pair(ca_adm, ca_pn));
                }
                if (ca_array[i].target_role_index == roleId) {
                    assigning_r.push_back(std::make_pair(ca_adm, ca_pn));
                }

            }
            for (int i = 0; i < cr_array_size; i++) {
                Expr cr_adm = cr_adm_formulae[i];
                Expr cr_pn = cr_pn_formulae[i];
                if (cr_pn->containsLiteral(role_name)) {
                    using_r.push_back(std::make_pair(cr_adm, cr_pn));
                }
                if (cr_array[i].target_role_index == roleId) {
                    assigning_r.push_back(std::make_pair(cr_adm, cr_pn));
                }
            }

            if (using_r.size() == 0) {
                printf("Role %s is never used. Remove it\n", role_array[roleId]);
                return true;
            }
            else {
                TExpr cond = irr_pos(roleId, using_r, assigning_r);
                solver->assertNow(cond);
                SMTResult smt_res = solver->solve();
                int res = 0;
                switch (smt_res) {
                    case SAT:
                        res = false;
                        break;
                    case UNSAT:
                        res = true;
                        break;
                    case UNKNOWN:
                        res = false;
                        break;
                }
                solver->clean();
                return res;
            }

        }


        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

        std::vector<int> nonPositiveRoles;
        std::vector<int> nonNegativeRoles;

        std::vector<Literalp> role_vars;

        std::vector<Expr> ca_adm_formulae;
        std::vector<Expr> ca_pn_formulae;
        std::vector<Expr> cr_adm_formulae;
        std::vector<Expr> cr_pn_formulae;

        public:

        void printNonPos() {
            for (int i = 0; i < role_array_size; i++) {
                int res = nonPositive(i);
                if (res) {
                    fprintf(stdout, "Role %s is nonPositive\n", role_array[i]);
                    nonPositiveRoles.push_back(i);
                }
                else {
                    // fprintf(stdout, "Role %s is Positive\n", role_array[i]);
                }
            }
            
        }

        void printNonNeg() {
            for (int i = 0; i < role_array_size; i++) {
                int res = nonNegative(i);
                if (res) {
                    fprintf(stdout, "Role %s is nonNegative\n", role_array[i]);
                    nonNegativeRoles.push_back(i);
                }
                else {
                    // fprintf(stdout, "Role %s is Negative\n", role_array[i]);
                }
            }
        }

        void PrintIrrelevantPos() {
            for (auto i = nonNegativeRoles.begin(); i < nonNegativeRoles.end(); ++i) {
                // // solver->push();
                // int res = irrelevantPositive(i);
                // if (res) {
                //     fprintf(stdout, "Role %s is irrelevantPositive\n", role_array[i]);
                //     // nonNegativeRoles.push_back(i);
                // }
                // else {
                //     // fprintf(stdout, "Role %s is Negative\n", role_array[i]);
                // }
                // // solver->pop();
                int can_remove = irrelevantPositive(*i);

                if (can_remove) {
                    printf("Role %s can be removed...\n", role_array[*i]);
                }
                else {
                    printf("Role %s cannot be removed...\n", role_array[*i]);
                }
            }
        }

        Pruning(std::shared_ptr<SMTFactory<TVar, TExpr>> _solver) : solver(_solver) {
            generateRoleVars();
            generate_ca_cr_formulae();
        }
    };

    // void test_yices() {
    //     context_t* context = yices_new_context(NULL);

    //     term_t type = yices_bool_type();

    //     term_t var1 = yices_new_uninterpreted_term(type);
    //     yices_set_term_name(var1, "x");
    //     term_t var2 = yices_new_uninterpreted_term(type);
    //     yices_set_term_name(var2, "x");
    //     yices_assert_formula(context, var1);
    //     yices_assert_formula(context, yices_not(var2));
        
    //     if (yices_check_context(context, NULL) == STATUS_SAT) {
    //         printf("SAT\n");
    //         model_t* model = yices_get_model(context, false);
    //         yices_pp_model(stdout, model, 120, 40, 0);
    //     }
    //     else {
    //         printf("UNSAT\n");
    //     }

    //     return;
    // }

    void prune(char* inputFile, FILE* output) {

        read_ARBAC(inputFile);
        // Preprocess the ARBAC Policies
        preprocess(0);
        build_config_array();

        std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
        Pruning<term_t, term_t> core(solver);

        auto start = std::chrono::high_resolution_clock::now();

        core.printNonPos();

        auto end = std::chrono::high_resolution_clock::now();
        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        std::cout << "------------ printNonPos " << milliseconds.count() << " ms ------------\n";


        start = std::chrono::high_resolution_clock::now();
        core.printNonNeg();

        end = std::chrono::high_resolution_clock::now();
        milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        std::cout << "------------ printNonNeg " << milliseconds.count() << " ms ------------\n";

        core.PrintIrrelevantPos();

        free_data();
        free_precise_temp_data();

    }
}
