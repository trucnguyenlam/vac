
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
#include "ExprToSmt.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    class Pruning {

        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

        std::vector<int> nonPositiveRoles;
        std::vector<int> nonNegativeRoles;

        std::shared_ptr<arbac_policy> policy;

        bool set_contains(Expr expr, std::string name) {
            std::set<Literalp> literals = expr->literals();
            for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
                Literalp e = *ite;
                if (e->name == name) {
                    return true;
                }
            }
            return false;
        }

        bool have_common_atoms(Expr e1, Expr e2) {
            std::list<Literalp> intersection;
            std::set_intersection(e1->literals().begin(), e1->literals().end(),
                                  e2->literals().begin(), e2->literals().end(),
                                  std::back_inserter(intersection));
            return intersection.size() > 0;

        }

        void printLookup(std::vector<std::shared_ptr<TVar>> lookup) {
            for (int i = 0; i < lookup.size(); ++i) {
                std::cout << i << ": ";
                if (lookup[i] != nullptr) {
                    solver->printExpr(*lookup[i]);
                }
                else
                    std::cout << "NULL" << std::endl;
            }
        }

        bool immaterial_not_interfere(Expr adm) {
            // Check if the administrative expression interfere (cause false) in other expressions
            // TODO: consider changing with set to reduce equals checks
            std::list<Expr> other_exprs;
            for (auto iterator = policy->rules().begin();
                 iterator != policy->rules().end(); ++iterator) {
                rulep r = *iterator;
                other_exprs.push_back(r->prec);
                if (adm != r->admin) {
                    other_exprs.push_back(r->admin);
                }
            }

            std::vector<std::shared_ptr<TVar>> adm_var_vec((unsigned long) policy->atom_count());
            TExpr solver_adm = generateSMTFunction2(solver, adm, adm_var_vec, std::string("adm"));

            for (auto ite = other_exprs.begin(); ite != other_exprs.end(); ++ite) {
                Expr expr = *ite;

                if (!have_common_atoms(adm, expr)) {
                    // can go forward since atoms are disjoint
                    continue;
                }

                solver->clean();

                std::vector<std::shared_ptr<TVar>> free_var_vec((unsigned long) policy->atom_count());
                TExpr solver_exp = generateSMTFunction2(solver, expr, free_var_vec, std::string("adm"));

                std::vector<std::shared_ptr<TVar>> updated_vec = update_tlookup(free_var_vec, adm_var_vec);
                TExpr not_solver_exp = solver->createNotExpr(generateSMTFunction2(solver, expr, updated_vec, std::string("adm")));

                solver->assertNow(solver_adm);
                solver->assertNow(solver_exp);
                solver->assertNow(not_solver_exp);

                bool res = solver->solve() == UNSAT;

                if (!res) {
                    std::cout << *adm << " administrative part interfere with " << *expr << std::endl;
                    return false;
                }
            }

            return true;
        }

        bool immaterial_k_plus_two(Expr adm) {
            //FIXME: implement this method: immaterial_k_plus_two...
            return false;
        }

        bool immaterial_adm(Expr adm) {
            bool exists_user = false;
            //exists a user that satisfies phi_adm
            for (auto &&user : policy->users()) {
                solver->clean();

                Expr adm_expr = adm;
                Expr user_expr = policy->user_to_expr(user->original_idx);

                std::map<std::string, TVar> map;

                TExpr solver_adm_expr = generateSMTFunction(solver, adm_expr, map, user->name);
                TExpr solver_user_expr = generateSMTFunction(solver, user_expr, map, user->name);

                solver->assertNow(solver_user_expr);
                solver->assertNow(solver_adm_expr);

                bool satisfies = solver->solve() == SAT;

                if (satisfies) {
                    exists_user = true;
                    std::cout << "User " << *user << " satisfies administrative formula "
                              << *adm << std::endl;
                    break;
                }
            }

            if (!exists_user) {
                return false;
            }
            else {
                return immaterial_k_plus_two(adm) || immaterial_not_interfere(adm);
            }
        }

        int nonPositiveNegative(int roleId, bool check_positive) {
            Literalp role = policy->atoms(roleId);
            std::vector<Expr> to_check;

            for (auto ite = policy->can_assign_rules().begin(); ite != policy->can_assign_rules().end(); ++ite) {
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

            for (auto ite = policy->can_revoke_rules().begin(); ite != policy->can_revoke_rules().end(); ++ite) {
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

        TExpr irr_mix_cond_one(Literalp role,
                               std::shared_ptr<rule> using_r,
                               std::vector<std::shared_ptr<rule>> assigning_r,
                               std::vector<std::shared_ptr<rule>> removing_r) {

            std::map<std::string, TVar> c_map;
            std::map<std::string, TVar> adm_map;

            // C_r
            TExpr not_c_r = generateSMTFunction(solver, role, c_map, "C");
            // not C_r
            TExpr c_r = solver->createNotExpr(generateSMTFunction(solver, role, c_map, "C"));

            // phi_r^TRUE(C)
            role->setValue(createConstantTrue());
            TExpr phi_r_true_c = generateSMTFunction(solver, using_r->prec, c_map, "C");

            // phi_r^FALSE(C)
            role->setValue(createConstantFalse());
            TExpr phi_r_false_c = generateSMTFunction(solver, using_r->prec, c_map, "C");

            role->resetValue();

            //phi_a_(adm)
            TExpr phi_a_adm = generateSMTFunction(solver, using_r->admin, adm_map, "ADM");

            // phi_r^TRUE(C) /\ not phi_r^FALSE(C) /\ phi_a_(adm)
            TExpr pos_lhs = solver->createAndExpr(solver->createAndExpr(phi_r_true_c,
                                                                        solver->createNotExpr(phi_r_false_c)),
                                                  phi_a_adm);

            // not phi_r^TRUE(C) /\ phi_r^FALSE(C) /\ phi_a_(adm)
            TExpr neg_lhs = solver->createAndExpr(solver->createAndExpr(solver->createNotExpr(phi_r_true_c),
                                                                        phi_r_false_c),
                                                  phi_a_adm);

            //FIXME: not working with Z3 since it is unifying the literals not in C;

            std::vector<TExpr> assign_and_rhs;

            for (auto ite = assigning_r.begin(); ite != assigning_r.end(); ++ite) {
                std::shared_ptr<rule> ca = *ite;
                std::map<std::string, TVar> c1_map = c_map;
                std::map<std::string, TVar> adm1_map = adm_map;

                //phi'(C)
                TExpr phi1_c = generateSMTFunction(solver, ca->prec, c1_map, "C");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction(solver, ca->admin, adm1_map, "ADM");

//                //phi'_a(C)
//                TExpr phi1_a_c = generateSMTFunction(solver, ca->admin, c1_map, "C");

                // not phi'(C) \/ not phi'_a(adm)
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_c),
                                                  solver->createNotExpr(phi1_a_adm));

                assign_and_rhs.push_back(disj);
            }

            TExpr assign_bigand = solver->joinExprsWithAnd(assign_and_rhs);


            std::vector<TExpr> revoke_and_rhs;

            for (auto ite = removing_r.begin(); ite != removing_r.end(); ++ite) {
                std::shared_ptr<rule> cr = *ite;
                std::map<std::string, TVar> c1_map = c_map;
                std::map<std::string, TVar> adm1_map = adm_map;

                //phi'(C)
                TExpr phi1_c = generateSMTFunction(solver, cr->prec, c1_map, "C");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction(solver, cr->admin, adm1_map, "ADM");

//                //phi'_a(C)
//                TExpr phi1_a_c = generateSMTFunction(solver, cr->admin, c1_map, "C");

                // not phi'(C) \/ not phi'_a(adm)
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_c),
                                                  solver->createNotExpr(phi1_a_adm));

                revoke_and_rhs.push_back(disj);
            }

            TExpr revoke_bigand = solver->joinExprsWithAnd(revoke_and_rhs);

            TExpr pos_ca = solver->createAndExpr(not_c_r,
                                                 solver->createAndExpr(pos_lhs,
                                                                       assign_bigand));

            TExpr neg_ca = solver->createAndExpr(c_r,
                                                 solver->createAndExpr(neg_lhs,
                                                                       revoke_bigand));

            TExpr res = solver->createOrExpr(pos_ca, neg_ca);

            return res;
        }

        bool irrelevantRole(Literalp role) {

            if (role == policy->goal_role) {
//                std::cout << "Role " << role->fullName() << " is TARGET" << std::endl;
                return false;
            }

            std::vector<std::shared_ptr<rule>> using_r;
            std::vector<std::shared_ptr<rule>> assigning_r;
            std::vector<std::shared_ptr<rule>> removing_r;
            for (auto ite = policy->can_assign_rules().begin(); ite != policy->can_assign_rules().end(); ++ite) {
                std::shared_ptr<rule> ca = *ite;
                if (ca->admin->literals().count(role) > 0) {
//                    std::cout << "Role " << role->fullName() << " is administrative in " << *ca << std::endl;
                    return false;
                }
                if (ca->prec->containsLiteral(role)) {
                    using_r.push_back(ca);
                }
                if (ca->target == role) {
                    assigning_r.push_back(ca);
                }
            }
            for (auto ite = policy->can_revoke_rules().begin(); ite != policy->can_revoke_rules().end(); ++ite) {
                std::shared_ptr<rule> cr = *ite;
                if (cr->admin->literals().count(role) > 0) {
//                    std::cout << "Role " << role->fullName() << " is administrative in " << *cr << std::endl;
                    return false;
                }
                if (cr->prec->containsLiteral(role)) {
                    using_r.push_back(cr);
                }
                if (cr->target == role) {
                    removing_r.push_back(cr);
                }
            }

            if (using_r.size() == 0) {
//                printf("Role %s is never used. Remove it\n", role->to_string().c_str());
                return true;
            }
            else {
                bool can_remove = true;
                for (auto iterator = using_r.begin(); iterator != using_r.end(); ++iterator) {
                    std::shared_ptr<rule> r_using_r = *iterator;
                    solver->clean();
                    TExpr cond = irr_mix_cond_one(role,
                                                  r_using_r,
                                                  assigning_r,
                                                  removing_r);
                    solver->assertNow(cond);

                    SMTResult res = solver->solve();

//                    solver->printContext();
//
//                    solver->printModel();

                    if (res == SAT) {
                        can_remove = false;
                        break;
                    }

                }
//                std::cout << "role: " << *role << (can_remove ? " Can" : " Cannot") << " be removed" << std::endl;

                return can_remove;
            }

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

        bool equivalent_exprs(Expr e1, Expr e2) {
//            if (e1->literals() != e2->literals()) {
//                return false;
//            }
//            else {

            solver->clean();

            std::vector<std::shared_ptr<TVar>> var_vec;
            TExpr se1 = generateSMTFunction(solver, e1, var_vec, "eq");
            TExpr se2 = generateSMTFunction(solver, e2, var_vec, "eq");

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

            if (res) {
                std::cout << "Expressions " << *e1 << std::endl;
                std::cout << "            " << *e2 << std::endl;
                std::cout << "            are equivalent!" << *e1 << std::endl;
            }

            return res;

//            }
        }

        void merge_rules() {
            std::map<Literalp, std::list<rulep>> assigning;
            std::map<Literalp, std::list<rulep>> revoking;

            for (auto &&ca : policy->can_assign_rules()) {
                assigning[ca->target].push_back(ca);
            }
            for (auto &&cr : policy->can_revoke_rules()) {
                assigning[cr->target].push_back(cr);
            }


            for (auto &&pair : assigning) {
                std::list<rulep> rules = pair.second;
                std::list<std::list<rulep>> to_merge;

                for (auto &&rule : rules) {

                }


            }
            //FIXME: continue here
            throw new std::runtime_error("Not implemented yet");

        }

        public:

        void PruneImmaterialRoles() {
            std::map<Expr, std::list<rulep>> admins;
            for (auto &&rule : policy->rules()) {
                admins[rule->admin].push_back(rule);
            }
            for (auto &&adm_pair : admins) {
                bool can_change = immaterial_adm(adm_pair.first);
                if (can_change) {
                    std::cout << "Administrative expression " << *adm_pair.first << " IS IMMATERIAL" << std::endl;
                    for (auto &&rule : adm_pair.second) {
                        rule->admin = createConstantTrue();
                    }
                }
            }
        }

        void PruneIrrelevantRoles() {
            std::vector<Literalp> irrelevant;

            auto start = std::chrono::high_resolution_clock::now();

            for (auto iterator = policy->atoms().begin(); iterator != policy->atoms().end(); ++iterator) {
                Literalp r = *iterator;
                bool can_remove = irrelevantRole(r);
                if (can_remove) {
                    std::cout << *r << " is irrelevant." << std::endl;
                    irrelevant.push_back(r);
                }
            }

            auto end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
            std::cout << "------------ Rule6 executed in " << milliseconds.count() << " ms ------------\n";

            // REMOVAL:
            for (auto &&i_role : irrelevant) {
                policy->reomove_atom(i_role);
            }
            return;
        }

        void printImpliedPairs() {
            //FIXME: refactored. Fix here
//            throw new std::runtime_error("FIXME: refactored. Fix here");
            for (int i = 0; i < policy->can_assign_rules().size(); i++) {
                std::shared_ptr<rule> ca1 = policy->can_assign_rules()[i];
                for (int j = 0; j < policy->can_assign_rules().size(); j++) {
                    std::shared_ptr<rule> ca2 = policy->can_assign_rules()[j];
                    if (i != j &&
                            policy->can_assign_rules()[i]->target->role_array_index ==
                                    policy->can_assign_rules()[j]->target->role_array_index) {
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
                fprintf(stdout, "Total: %ld rules\n", policy->can_assign_rules().size());

//                for (int j = 0; j < policy->can_assign_rules().size(); ++j) {
//                    std::cout << *policy->can_assign_rules()[j] << std::endl;
//                }

                for (int i = 0; i < policy->can_assign_rules().size(); i++) {
                    std::shared_ptr<rule> rule = policy->can_assign_rules()[i];
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
                        to_remove.push_back(policy->can_assign_rules()[i]);
                    } else if (rem_adm) {
                        fprintf(stdout, "O");
                        fflush(stdout);
                        to_remove.push_back(policy->can_assign_rules()[i]);
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
        core.PruneIrrelevantRoles();
        core.PruneImmaterialRoles();
        core.PruneIrrelevantRoles();

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
