
#include <vector>
#include <set>
#include <memory>
#include <string>
#include <chrono>
#include <iostream>
#include <utility>
#include <algorithm>

#include "ARBACExact.h"
#include "SMT_Pruning.h"
#include "SMT.h"
#include "Logics.h"
#include "Policy.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    class Pruning {

        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

        std::vector<int> nonPositiveRoles;
        std::vector<int> nonNegativeRoles;

        std::shared_ptr<arbac_policy> policy;

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

//        void generateRoleVars() {
//            for (int i = 0; i < role_array_size; i++) {
//                std::string rname(role_array[i]);
//                Literalp var = createLiteralp(rname, i, 1);
//                role_vars.push_back(var);
//            }
//        }

//        Expr getCRAdmFormula(int ruleId) {
//            Expr ret = role_vars[cr_array[ruleId].admin_role_index];
//            return ret;
//        }
//
//        Expr getCRPNFormula(int ruleId) {
//            return createConstantExpr(true, 1);
//        }
//
//        Expr getCAAdmFormula(int ca_index) {
//            Expr ret = role_vars[ca_array[ca_index].admin_role_index];
//            return ret;
//        }
//
//        Expr getCAPNFormula(int ca_index) {
//            Expr cond = createConstantExpr(true, 1);
//
//            if (ca_array[ca_index].type == 0) {     // Has precondition
//                // P
//                if (ca_array[ca_index].positive_role_array_size > 0) {
//                    int* ca_array_p = ca_array[ca_index].positive_role_array;
//                    std::string rp_name = std::string(role_array[ca_array_p[0]]);
//                    Expr ca_cond = role_vars[ca_array_p[0]];
//                    for (int j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
//                        rp_name = std::string(role_array[ca_array_p[j]]);
//                        ca_cond = createAndExpr(ca_cond, role_vars[ca_array_p[j]]);
//                    }
//                    cond = createAndExpr(cond, ca_cond);
//                }
//                // N
//                if (ca_array[ca_index].negative_role_array_size > 0) {
//                    int* ca_array_n = ca_array[ca_index].negative_role_array;
//                    std::string rn_name = std::string(role_array[ca_array_n[0]]);
//                    Expr cr_cond = createNotExpr(role_vars[ca_array_n[0]]);
//                    for (int j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
//                        rn_name = std::string(role_array[ca_array_n[j]]);
//                        cr_cond = createAndExpr(cr_cond, createNotExpr(role_vars[ca_array_n[j]]));
//                    }
//                    cond = createAndExpr(cond, cr_cond);
//                }
//            }
//
//            return cond;
//        }

//        void generate_ca_cr_formulae() {
//            int i;
//            for (i = 0; i < ca_array_size; i++) {
//                ca_adm_formulae.push_back(getCAAdmFormula(i));
//                ca_pn_formulae.push_back(getCAPNFormula(i));
//                // print_ca_comment(stdout, i);
//                // printf("%s\n", getCAPNFormula(i)->to_string().c_str());
//            }
//            for (i = 0; i < cr_array_size; i++) {
//                cr_adm_formulae.push_back(getCRAdmFormula(i));
//                cr_pn_formulae.push_back(getCRPNFormula(i));
//                // print_cr_comment(stdout, i);
//                // printf("%s\n", getCRPNFormula(i)->to_string().c_str());
//            }
//        }

        int nonPositiveNegative(int roleId, bool check_positive) {
            Literalp role = policy->atoms[roleId];
            std::vector<Expr> to_check;

            for (auto ite = policy->can_assign_rules.begin(); ite != policy->can_assign_rules.end(); ++ite) {
                std::shared_ptr<rule> rule = (*ite);
                if (rule->admin->literals().count(role) > 0) {
//                    std::cout << "Role: " << role->fullName() << " is administrative thus NOT non-positive" << std::endl;
                    return false;
                    to_check.push_back(rule->admin);
                }
                if (rule->prec->literals().count(role) > 0) {
                    to_check.push_back(rule->prec);
                }
            }

            for (auto ite = policy->can_revoke_rules.begin(); ite != policy->can_revoke_rules.end(); ++ite) {
                std::shared_ptr<rule> rule = *ite;
                if (rule->admin->literals().count(role)) {
//                    std::cout << "Role: " << role->fullName() << " is administrative thus NOT non-positive" << std::endl;
                    return false;
                    to_check.push_back(rule->admin);
                }
                if (rule->prec->literals().count(role)) {
                    to_check.push_back(rule->prec);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                solver->clean();

                bool exists = false;

                for (auto ite = to_check.begin(); ite != to_check.end(); ++ite) {
                    //TODO: eventually create a big dinsjunction on all formulae

                    std::map<std::string, TVar> tmap;
                    Expr expr = *ite;
                    // phi_a^TRUE
                    role->setValue(createConstantTrue());
                    TExpr phi_a_true = generateSMTFunction(solver, expr, tmap, "C");

                    // phi_a^FALSE
                    role->setValue(createConstantFalse());
                    TExpr phi_a_false = generateSMTFunction(solver, expr, tmap, "C");

                    role->resetValue();

                    TExpr final = solver->createTrue();
                    if (check_positive) {
                        // (phi_a^TRUE /\ \not phi_a^FALSE)
                        final = solver->createAndExpr(phi_a_true, solver->createNotExpr(phi_a_false));
                    }
                    else {
                        // (phi_a^FALSE /\ \not phi_a^TRUE)
                        final = solver->createAndExpr(phi_a_false, solver->createNotExpr(phi_a_true));
                    }

                    solver->assertNow(final);
//                    solver->assertNow(phi_a_true);
//                    solver->assertNow(solver->createNotExpr(phi_a_false));

                    SMTResult res = solver->solve();

                    if (res == SAT) {
                        exists = true;
                        break;
                    }
                }

//                std::cout << "Role: " << role->name << (exists ? " is NOT " : " IS ") << "non-positive." << std::endl;

                return !exists;
            }
        }

        TExpr irr_pos_cond(int roleId, std::vector<std::pair<Expr, Expr>> using_r, std::vector<std::pair<Expr, Expr>> assigning_r) {
            //FIXME: refactored. Fix here
            throw new std::runtime_error("FIXME: refactored. Fix here");
//            // ASSERT that ca uses role r
//            std::map<std::string, TVar> c_map;
//            std::map<std::string, TVar> adm_map;
//            std::string role_name(role_array[roleId]);
//            std::string c = "C";
//            std::string adm = "adm";
//
//            // \not C.r
//            TExpr not_r_c = generateSMTFunction(solver, createNotExpr(role_vars[roleId]), c_map, c);
//
//            std::vector<TExpr> lhs_exprs;
//            for (auto u_ite = using_r.begin(); u_ite != using_r.end(); ++u_ite) {
//                auto adm_pn = *u_ite;
//                Expr rule_adm_expr = adm_pn.first;
//                Expr rule_pn_expr = adm_pn.second;
//
//                //generating \phi_r^{true}(C)
//                rule_pn_expr->setLiteralValue(role_name, createConstantExpr(true, 1));
//                TExpr phi_r_true_c = generateSMTFunction(solver, rule_pn_expr, c_map, c);
//
//                // generating \not(\phi_r^{false}(C))
//                rule_pn_expr->setLiteralValue(role_name, createConstantExpr(false, 1));
//                TExpr phi_r_false_c = generateSMTFunction(solver, createNotExpr(rule_pn_expr), c_map, c);
//
//                rule_pn_expr->resetValue();
//
//                //generating \phi_a(admin)
//                TExpr phi_a_adm = generateSMTFunction(solver, rule_adm_expr, adm_map, adm);
//
//                // AND left side
//                TExpr lhs = solver->createAndExpr(solver->createAndExpr(phi_r_true_c, phi_r_false_c), phi_a_adm);
//
//                lhs_exprs.push_back(lhs);
//            }
//
//            std::vector<TExpr> rhs_exprs;
//            for (auto ass_ite = assigning_r.begin(); ass_ite != assigning_r.end(); ++ass_ite) {
//                //For all rule (\phi_a', \phi', r) \in CA
//
//                // \not \phi'(C)
//                Expr phi1 = (*ass_ite).second;
//                TExpr not_phi1_c = generateSMTFunction(solver, createNotExpr(phi1), c_map, c);
//
//                // \phi_a'(adm)
//                Expr phi1_a = (*ass_ite).first;
//                //setting ADMIN suffix on all literals
//                TExpr not_phi1_a_adm = generateSMTFunction(solver, phi1_a, adm_map, adm);
//
//                // \phi_a'(C)
//                //setting C suffix on all literals
//                TExpr not_phi1_a_c = generateSMTFunction(solver, phi1_a, c_map, c);
//
//                // \not (\phi_a'(adm) \/ \phi_a'(C))
//                TExpr lhs = solver->createNotExpr(solver->createOrExpr(not_phi1_a_adm, not_phi1_a_c));
//
//                rhs_exprs.push_back(solver->createOrExpr(not_phi1_c, lhs));
//            }
//
//            // JOIN TOGETHER ALL LHS
//            TExpr final_lhs = solver->createFalse();
//            for (auto ite = lhs_exprs.begin(); ite != lhs_exprs.end(); ++ite) {
//                final_lhs = solver->createOrExpr(final_lhs, *ite);
//            }
//
//            // JOIN TOGETHER ALL RHS
//            TExpr final_rhs = solver->createTrue();
//            for (auto ite = rhs_exprs.begin(); ite != rhs_exprs.end(); ++ite) {
//                final_rhs = solver->createAndExpr(final_rhs, *ite);
//            }
//
//            // creating implication
//            // TExpr res = solver->createImplExpr(impl_lhs, impl_rhs);
//            TExpr res = solver->createAndExpr(not_r_c, solver->createAndExpr(final_lhs, final_rhs));
//            return res;
        }

        TExpr irr_neg_cond(int roleId, std::vector<std::pair<Expr, Expr>> using_r, std::vector<std::pair<Expr, Expr>> removing_r) {
            //FIXME: refactored. Fix here
            throw new std::runtime_error("FIXME: refactored. Fix here");
//            // ASSERT that ca uses role r
//            std::map<std::string, TVar> c_map;
//            std::map<std::string, TVar> adm_map;
//            std::string role_name(role_array[roleId]);
//            std::string c = "C";
//            std::string adm = "adm";
//
//            // C.r
//            TExpr r_c = generateSMTFunction(solver, role_vars[roleId], c_map, c);
//
//            std::vector<TExpr> lhs_exprs;
//            for (auto u_ite = using_r.begin(); u_ite != using_r.end(); ++u_ite) {
//                auto adm_pn = *u_ite;
//                Expr rule_adm_expr = adm_pn.first;
//                Expr rule_pn_expr = adm_pn.second;
//
//                //generating \phi_r^{false}(C)
//                rule_pn_expr->setLiteralValue(role_name, createConstantExpr(false, 1));
//                TExpr phi_r_false_c = generateSMTFunction(solver, rule_pn_expr, c_map, c);
//
//                // generating \not(\phi_r^{true}(C))
//                rule_pn_expr->setLiteralValue(role_name, createConstantExpr(true, 1));
//                TExpr phi_r_true_c = generateSMTFunction(solver, createNotExpr(rule_pn_expr), c_map, c);
//
//                rule_pn_expr->resetValue();
//
//                //generating \phi_a(admin)
//                TExpr phi_a_adm = generateSMTFunction(solver, rule_adm_expr, adm_map, adm);
//
//                // AND left side
//                TExpr lhs = solver->createAndExpr(solver->createAndExpr(phi_r_false_c, phi_r_true_c), phi_a_adm);
//
//                lhs_exprs.push_back(lhs);
//            }
//
//            std::vector<TExpr> rhs_exprs;
//            for (auto rev_ite = removing_r.begin(); rev_ite != removing_r.end(); ++rev_ite) {
//                //For all rules revoking r. (\phi_a', \phi', r) \in CR
//
//                // \not \phi'(C)
//                Expr phi1 = rev_ite->second;
//                TExpr not_phi1_c = generateSMTFunction(solver, createNotExpr(phi1), c_map, c);
//
//                // \not \phi_a'(adm)ca_adm_formulae
//                Expr phi1_a = rev_ite->first;
//                //setting ADMIN suffix on all literals
//                TExpr not_phi1_a_adm = generateSMTFunction(solver, createNotExpr(phi1_a), adm_map, adm);
//
//                rhs_exprs.push_back(solver->createOrExpr(not_phi1_c, not_phi1_a_adm));
//            }
//
//            // JOIN TOGETHER ALL LHS
//            TExpr final_lhs = solver->createFalse();
//            for (auto ite = lhs_exprs.begin(); ite != lhs_exprs.end(); ++ite) {
//                final_lhs = solver->createOrExpr(final_lhs, *ite);
//            }
//
//            // JOIN TOGETHER ALL RHS
//            TExpr final_rhs = solver->createTrue();
//            for (auto ite = rhs_exprs.begin(); ite != rhs_exprs.end(); ++ite) {
//                final_rhs = solver->createAndExpr(final_rhs, *ite);
//            }
//
//            // creating implication
//            // TExpr res = solver->createImplExpr(impl_lhs, impl_rhs);
//            TExpr res = solver->createAndExpr(r_c, solver->createAndExpr(final_lhs, final_rhs));
//            return res;
        }

        TExpr irr_mix_cond(int roleId, std::vector<std::pair<Expr, Expr>> using_r, 
                            std::vector<std::pair<Expr, Expr>> assigning_r, 
                            std::vector<std::pair<Expr, Expr>> removing_r) {
            //FIXME: refactored. Fix here
            throw new std::runtime_error("FIXME: refactored. Fix here");
//            TExpr pos_cond = irr_pos_cond(roleId, using_r, assigning_r);
//            TExpr neg_cond = irr_neg_cond(roleId, using_r, removing_r);
//            return solver->createOrExpr(pos_cond, neg_cond);

        }

        // int deb = false;           
        // if (role_name == "rb") { deb = true; }
        // else                   { deb = false; }

        int irrelevantPositive(int roleId) {
            //FIXME: refactored. Fix here
            throw new std::runtime_error("FIXME: refactored. Fix here");
//            for (int i = 0; i < 100; i++) {
//                printf("ROTTO PER RUOLI AMMINISTRATIVI!! ");
//            }
//            std::string role_name(role_array[roleId]);
//            std::vector<std::pair<Expr, Expr>> using_r;
//            std::vector<std::pair<Expr, Expr>> assigning_r;
//            std::vector<std::pair<Expr, Expr>> removing_r;
//            for (int i = 0; i < ca_array_size; i++) {
//                Expr ca_adm = ca_adm_formulae[i];
//                Expr ca_pn = ca_pn_formulae[i];
//                // if (ca_pn->containsLiteral(role_name) || ca_adm->containsLiteral(role_name)) {
//                using_r.push_back(std::make_pair(ca_adm, ca_pn));
//                // }
//                if (ca_array[i].target_role_index == roleId) {
//                    assigning_r.push_back(std::make_pair(ca_adm, ca_pn));
//                }
//
//            }
//            for (int i = 0; i < cr_array_size; i++) {
//                Expr cr_adm = cr_adm_formulae[i];
//                Expr cr_pn = cr_pn_formulae[i];
//                // if (cr_pn->containsLiteral(role_name) || cr_adm->containsLiteral(role_name)) {
//                using_r.push_back(std::make_pair(cr_adm, cr_pn));
//                // }
//                if (cr_array[i].target_role_index == roleId) {
//                    removing_r.push_back(std::make_pair(cr_adm, cr_pn));
//                }
//            }
//
//            if (using_r.size() == 0) {
//                printf("Role %s is never used. Remove it\n", role_array[roleId]);
//                return true;
//            }
//            else {
//                TExpr cond = solver->createTrue();
//                if (std::find(nonPositiveRoles.begin(), nonPositiveRoles.end(), roleId) != nonPositiveRoles.end()) {
//                    printf("Role %s is nonPositive\n", role_array[roleId]);
//                    cond = solver->createAndExpr(cond, irr_neg_cond(roleId, using_r, removing_r));
//                }
//                else {
//                    if (std::find(nonNegativeRoles.begin(), nonNegativeRoles.end(), roleId) != nonNegativeRoles.end()) {
//                        printf("Role %s is nonNegative\n", role_array[roleId]);
//                        cond = solver->createAndExpr(cond, irr_pos_cond(roleId, using_r, assigning_r));
//                    }
//                    else {
//                        printf("Role %s is mixed\n", role_array[roleId]);
//                        cond = cond = solver->createAndExpr(cond, irr_mix_cond(roleId, using_r, assigning_r, removing_r));
//                    }
//                }
//                solver->assertNow(cond);
//                SMTResult smt_res = solver->solve();
//                int res = 0;
//                switch (smt_res) {
//                    case SAT:
//                        res = false;
//                        break;
//                    case UNSAT:
//                        res = true;
//                        break;
//                    case UNKNOWN:
//                        res = false;
//                        break;
//                }
//                solver->clean();
//                return res;
//            }

        }

        int implied(std::shared_ptr<rule> ca1, std::shared_ptr<rule> ca2) {
            std::map<std::string, TVar> c_map;
            std::map<std::string, TVar> adm_map;
            std::string c_suff("C");
            std::string adm_suff("admin");

            TExpr phi1_adm = generateSMTFunction(solver, ca1->admin, adm_map, adm_suff);
            TExpr phi1_pn = generateSMTFunction(solver, ca1->prec, c_map, c_suff);
            TExpr phi2_adm = generateSMTFunction(solver, ca2->admin, adm_map, adm_suff);
            TExpr phi2_pn = generateSMTFunction(solver, ca2->prec, c_map, c_suff);

            // \phi'_a(adm) /\ \phi'(C)
            TExpr lhs = solver->createAndExpr(phi2_adm, phi2_pn);

            // (\not\phi_a(adm)) \/ (\not\phi(c))
            // \not (\phi_a(adm) /\ \phi(C))
            TExpr rhs = solver->createNotExpr(solver->createAndExpr(phi1_adm, phi1_pn));

            // (\phi_a(adm) /\ \phi(C)) /\ ((\not\phi'_a(adm)) \/ (\not\phi'(c)))
            TExpr final_cond = solver->createAndExpr(lhs, rhs);

            solver->assertNow(final_cond);
            SMTResult res = solver->solve();
            solver->clean();
            return res == UNSAT;
        }

        public:

        void printNonPos() {
            for (int i = 0; i < policy->atom_count(); i++) {
                int res = nonPositiveNegative(i, true);
                if (res) {
                    fprintf(stdout, "Role %s is nonPositive\n", role_array[i]);
                    nonPositiveRoles.push_back(i);
                }
                else {
                     fprintf(stdout, "Role %s is administrative or NOT nonPositive\n", role_array[i]);
                }
            }
            
        }

        void printNonNeg() {
            for (int i = 0; i < role_array_size; i++) {
                int res = nonPositiveNegative(i, false);
                if (res) {
                    fprintf(stdout, "Role %s is nonNegative\n", role_array[i]);
                    nonNegativeRoles.push_back(i);
                }
                else {
                     fprintf(stdout, "Role %s is administrative or NOT nonNegative\n", role_array[i]);
                }
            }
        }

        void PrintIrrelevantPos() {
            //FIXME: refactored. Fix here
            throw new std::runtime_error("FIXME: refactored. Fix here");
//            // for (auto i = nonNegativeRoles.begin(); i < nonNegativeRoles.end(); ++i) {
//            for (int i = 0; i < role_array_size; ++i) {
//                // // solver->push();
//                // int res = irrelevantPositive(i);
//                // if (res) {
//                //     fprintf(stdout, "Role %s is irrelevantPositive\n", role_array[i]);
//                //     // nonNegativeRoles.push_back(i);
//                // }
//                // else {
//                //     // fprintf(stdout, "Role %s is Negative\n", role_array[i]);
//                // }
//                // // solver->pop();
//                int can_remove = irrelevantPositive(i);
//
//                if (can_remove) {
//                    printf("Role %s can be removed...\n", role_array[i]);
//                }
//                else {
//                    printf("Role %s cannot be removed...\n", role_array[i]);
//                }
//            }
        }

        void printImpliedPairs() {
            //FIXME: refactored. Fix here
//            throw new std::runtime_error("FIXME: refactored. Fix here");
            for (int i = 0; i < policy->can_assign_rules.size(); i++) {
                std::shared_ptr<rule> ca1 = policy->can_assign_rules[i];
                for (int j = 0; j < policy->can_assign_rules.size(); j++) {
                    std::shared_ptr<rule> ca2 = policy->can_assign_rules[j];
                    if (i != j &&
                            policy->can_assign_rules[i]->target->role_array_index ==
                                    policy->can_assign_rules[j]->target->role_array_index) {
                        printf("Implied: \n");
//                        print_ca_comment(stdout, i);
//                        std::cout << ca1 << std::endl;
//                        std::cout << ca2 << std::endl;
                        ca1->print();
                        ca2->print();
//                        print_ca_comment(stdout, j);
//                        std::pair<Expr, Expr> ca1_exprs = std::make_pair(ca_adm_formulae[i], ca_pn_formulae[i]);
//                        std::pair<Expr, Expr> ca2_exprs = std::make_pair(ca_adm_formulae[j], ca_pn_formulae[j]);
                        int are_implied = implied(ca1, ca2);
                        printf("%s!\n", are_implied ? "TRUE" : "FALSE");
                        if (are_implied) {
                        }
                    }
                }
            }
        }

        void test() {
            TVar v = solver->createBoolVar("polok");
            TExpr e1 = v;

            solver->assertNow(e1);
            std::string r1 = solver->solve() == SAT ? "SAT" : "UNSAT";

            std::cout << r1 << std::endl;
            solver->printModel();

            solver->clean();

            TExpr e2 = solver->createNotExpr(v);
            solver->assertNow(e2);
            std::string r2 = solver->solve() == SAT ? "SAT" : "UNSAT";

            std::cout << r2 << std::endl;
            solver->printModel();

        }

        void apply_rule_6() {

            bool fixpoint = false;
            int fix_ite = 1;

            auto start = std::chrono::high_resolution_clock::now();
            while (!fixpoint) {
                fixpoint = true;
                std::vector<std::shared_ptr<rule>> to_remove;

                fprintf(stdout, "Iteration %d:\n", fix_ite++);
                fprintf(stdout, "Total: %ld rules\n", policy->can_assign_rules.size());

//                for (int j = 0; j < policy->can_assign_rules.size(); ++j) {
//                    std::cout << *policy->can_assign_rules[j] << std::endl;
//                }

                for (int i = 0; i < policy->can_assign_rules.size(); i++) {
                    std::shared_ptr<rule> rule = policy->can_assign_rules[i];
                    solver->clean();
                    bool rem_pn = apply_r6<TVar, TExpr>(this->solver, this->policy, rule, false);
                    solver->clean();
                    bool rem_adm = rem_pn ? false : apply_r6<TVar, TExpr>(this->solver, this->policy, rule, true);

                    //                std::cout << ca_adm_formulae[i]->to_string() << std::endl;

                    //                if (!rem_pn && rem_adm)
                    //                    solver->printContext();

                    //                if (i == ca_index) {
                    //                    solver->printContext();
                    //                }

                    if (rem_pn) {
                        //                    print_ca_comment(stdout, i);
                        //                    fprintf(stdout, "rule %d %s be removed since not fireable\n\n", i, res ? "CAN" : "CANNOT");
                        fprintf(stdout, "X");
                        fflush(stdout);
                        to_remove.push_back(policy->can_assign_rules[i]);
                    } else if (rem_adm) {
                        fprintf(stdout, "O");
                        fflush(stdout);
                        to_remove.push_back(policy->can_assign_rules[i]);
                    } else {
                        fprintf(stdout, "-");
                        fflush(stdout);
                    }
                }

                for (auto ite = to_remove.begin(); ite != to_remove.end(); ++ite) {
//                    std::cout << **ite << ", ";
                    policy->remove_can_assign(*ite);
                }

                fixpoint = to_remove.size() == 0;

                fprintf(stdout, "\nRemoved %lu rules\n", to_remove.size());
            }


            auto end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            std::cout << "------------ Rule6 executed in " << milliseconds.count() << " ms ------------\n";

        }

        Pruning(std::shared_ptr<SMTFactory<TVar, TExpr>> _solver) :
            solver(_solver),
            policy(new arbac_policy()) { }
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

        for (int i = 0; i < hierarchy_array_size; ++i) {
            std::cout << hierarchy_array[i].inferior_role_index << " < " << hierarchy_array[i].superior_role_index << std::endl;
        }

        std::shared_ptr<SMTFactory<z3::expr, z3::expr>> solver(new Z3Solver());
        Pruning<z3::expr, z3::expr> core(solver);
//        std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
//        Pruning<term_t, term_t> core(solver);

//        core.apply_rule_6();
        core.printNonPos();

//        return;
//
//        auto start = std::chrono::high_resolution_clock::now();
//
//        core.printNonPos();
//
//        auto end = std::chrono::high_resolution_clock::now();
//        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//        std::cout << "------------ printNonPos " << milliseconds.count() << " ms ------------\n";
//
//
//        start = std::chrono::high_resolution_clock::now();
//        core.printNonNeg();
//
//        end = std::chrono::high_resolution_clock::now();
//        milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//        std::cout << "------------ printNonNeg " << milliseconds.count() << " ms ------------\n";
//
//        // core.PrintIrrelevantPos();
//        core.printImpliedPairs();
//
//        free_data();
//        free_precise_temp_data();

    }
}
