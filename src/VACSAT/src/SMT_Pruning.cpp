
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

        enum AtomStatus {
            UNUSED,
            NON_POSITIVE,
            NON_NEGATIVE,
            BOTH_VALUED
        };

        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

        std::shared_ptr<arbac_policy> policy;

        bool set_contains(const Expr& expr, const std::string& name) {
            std::set<Literalp> literals = expr->literals();
            for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
                Literalp e = *ite;
                if (e->name == name) {
                    return true;
                }
            }
            return false;
        }

        bool have_common_atoms(const Expr& e1, const Expr& e2) {
            std::list<Literalp> intersection;
            std::set_intersection(e1->literals().begin(), e1->literals().end(),
                                  e2->literals().begin(), e2->literals().end(),
                                  std::back_inserter(intersection));
            return intersection.size() > 0;

        }

        void printLookup(const std::vector<std::shared_ptr<TVar>>& lookup) {
            for (int i = 0; i < lookup.size(); ++i) {
                std::cout << i << ": ";
                if (lookup[i] != nullptr) {
                    solver->printExpr(*lookup[i]);
                }
                else
                    std::cout << "NULL" << std::endl;
            }
        }

        /* PRELIMINARY SIMPLE PRUNING (REMOVING ATOMS NOT USED IN ANY CONDITION,
         *                             CAN_ASSIGN OF NON POSITIVE ATOMS,
         *                             CAN_REVOKE OF NON NEGATIVE ATOMS AND OF GOAL ATOM) */
        bool has_status(const atom& atom, const std::list<Expr>& using_a, AtomStatus wanted_status) {
            for (auto &&expr : using_a) {
                solver->clean();
                std::vector<std::shared_ptr<TVar>> var_vect((unsigned long)policy->atom_count());

                // Phi_r_true(C)
//                atom->setValue(createConstantTrue());
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createTrue());
                TExpr phi_a_true = generateSMTFunction2(solver, expr, var_vect, "C");

                // Phi_r_false(C)
//                atom->setValue(createConstantFalse());
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createFalse());
                TExpr phi_a_false = generateSMTFunction2(solver, expr, var_vect, "C");

//                atom->resetValue();

                TExpr to_check = solver->createTrue();

                if (wanted_status == UNUSED) {
                    std::cerr << "Cannot check the UNUSED status here..." << std::endl;
                    throw new std::runtime_error("Cannot check the UNUSED status here...");
                }
                else if (wanted_status == NON_POSITIVE) {
                    // Phi_r_true(C) /\ not Phi_r_false(C)
                    to_check = solver->createAndExpr(phi_a_true,
                                                     solver->createNotExpr(phi_a_false));
                }
                else if (wanted_status == NON_NEGATIVE) {
                    // Phi_r_false(C) /\ not Phi_r_true(C)
                    to_check = solver->createAndExpr(solver->createNotExpr(phi_a_true),
                                                     phi_a_false);
                }
                else if (wanted_status == BOTH_VALUED) {
                    std::cerr << "Cannot check the BOTH_VALUED status here..." << std::endl;
                    throw new std::runtime_error("Cannot check the BOTH_VALUED status here...");
                }

                solver->assertNow(to_check);
                bool expr_is_counterexample = solver->solve() == SAT;
                if (expr_is_counterexample) {
                    return false;
                }
            }
            return true;
        }

        AtomStatus get_atom_status(const atom& atom) {
            std::list<Expr> using_a;
            for (auto &&rule : policy->rules()) {
                if (contains(rule->admin->literals().begin(), rule->admin->literals().end(), atom)) {
                    using_a.push_back(rule->admin);
                }
                if (contains(rule->prec->literals().begin(), rule->prec->literals().end(), atom)) {
                    using_a.push_back(rule->prec);
                }
            }
            if (using_a.size() <= 0) {
                return UNUSED;
            }
            if (has_status(atom, using_a, NON_POSITIVE)) {
                return NON_POSITIVE;
            }
            if (has_status(atom, using_a, NON_NEGATIVE)) {
                return NON_NEGATIVE;
            }
            return BOTH_VALUED;

        }

        template <typename _Predicate>
        bool forall_user(_Predicate pred) {
            for (auto &&user :policy->users()) {
                if (!pred(user)) {
                    return false;
                }
            }
            return true;
        }

        bool easy_pruning_user() {
            std::list<atom> not_used_atoms;
            std::list<rulep> rules_to_remove;
            for (auto &&atom : policy->atoms()) {
                bool used = false;
                for (auto &&rule : policy->rules()) {
                    if (contains(rule->admin->literals().begin(), rule->admin->literals().end(), atom) ||
                        contains(rule->prec->literals().begin(), rule->prec->literals().end(), atom)) {
                        used = true;
                        break;
                    }
                }
                if (!used && atom != policy->goal_role) {
                    not_used_atoms.push_back(atom);
                    std::cout << "Atom: " << *atom << " is never used. Removing it!" << std::endl;
                }
                else if (atom == policy->goal_role){
                    for (auto &&cr : policy->can_revoke_rules()) {
                        if (cr->target == atom) {
                            rules_to_remove.push_back(cr);
                            std::cout << "\t" << *cr << std::endl;
                        }
                    }
                    std::cout << "Atom: " << *atom << " is the GOAL_ROLE. Removing can_revoke_rules targeting it!" << std::endl;
                }
                else {
                    AtomStatus status = get_atom_status(atom);
                    switch (status) {
                        case UNUSED:
                            // done before
                            break;
                        case NON_NEGATIVE: {
                            // IF ALL USER DOES HAVE IT REMOVE IT SINCE NO NEED OF CHANGE
                            if (forall_user([&](const userp& user) { return contains(user->config(), atom); })) {
                                std::cout << "Atom: " << *atom << " is NON_NEGATIVE and all users have it. Remove it!" << std::endl;
                                not_used_atoms.push_back(atom);
                                break;
                            }
                            std::cout << "Atom: " << *atom << " is NON_NEGATIVE. Removing can_revoke_rules targeting it!" << std::endl;
                            for (auto &&cr : policy->can_revoke_rules()) {
                                if (cr->target == atom) {
                                    rules_to_remove.push_back(cr);
                                    std::cout << "\t" << *cr << std::endl;
                                }
                            }
                            break;
                        }
                        case NON_POSITIVE: {
                            // IF ALL USER DOES NOT HAVE IT REMOVE IT SINCE NO NEED OF CHANGE
                            if (forall_user([&](const userp& user) { return !contains(user->config(), atom); })) {
                                std::cout << "Atom: " << *atom << " is NON_POSITIVE and no users have it. Remove it!" << std::endl;
                                not_used_atoms.push_back(atom);
                                break;
                            }
                            std::cout << "Atom: " << *atom << " is NON_POSITIVE. Removing can_assign_rules targeting it!" << std::endl;
                            for (auto &&ca : policy->can_assign_rules()) {
                                if (ca->target == atom) {
                                    rules_to_remove.push_back(ca);
                                    std::cout << "\t" << *ca << std::endl;
                                }
                            }
                            break;
                        }
                        default:
                            break;
                    }
                }
            }

            for (auto &&atom : not_used_atoms) {
                policy->remove_atom(atom);
            }

            for (auto &&rule : rules_to_remove) {
                policy->remove_rule(rule);
            }

            return (not_used_atoms.size() > 0) ||
                   (rules_to_remove.size() > 0);

        }

        bool false_condition(const rulep& rule) {
            // CHECK IF BOTH ADMIN CONDITION AND CONDITION ARE SATISFIABLE
            solver->clean();

            std::vector<std::shared_ptr<TVar>> adm_vect((unsigned int) policy->atom_count());
            TExpr solver_adm = generateSMTFunction2(solver, rule->admin, adm_vect, "adm");

            std::vector<std::shared_ptr<TVar>> prec_vect((unsigned int) policy->atom_count());
            TExpr solver_prec = generateSMTFunction2(solver, rule->prec, prec_vect, "prec");

            TExpr check = solver->createAndExpr(solver_adm, solver_prec);
            solver->assertNow(check);
            SMTResult res = solver->solve();

            return res != SAT;
        }

        bool true_condition(const Expr& expr) {
            // CHECK IF AN EXPRESSION IS ALWAYS TRUE
            solver->clean();

            std::vector<std::shared_ptr<TVar>> var_vect((unsigned int) policy->atom_count());
            TExpr solver_expr = generateSMTFunction2(solver, expr, var_vect, "C");

            TExpr check = solver->createNotExpr(solver_expr);
            solver->assertNow(check);
            SMTResult res = solver->solve();

            return res != SAT;
        }

        bool easy_pruning_rule_condition() {
            std::list<rulep> false_to_remove;
            bool has_changed = false;
            for (auto &&rule :policy->rules()) {
                if (false_condition(rule)) {
                    has_changed = true;
                    std::cout << "Rule " << *rule << " is never satisfiable. Remove it." << std::endl;
                    false_to_remove.push_back(rule);
                }
                else {
                    if (!is_constant_true(rule->admin) && true_condition(rule->admin)) {
                        has_changed = true;
                        std::cout << "Administrative condition of rule " << *rule << " is always TRUE..." << std::endl;
                        rule->admin = createConstantTrue();
                    }
                    if (!is_constant_true(rule->prec) && true_condition(rule->prec)) {
                        has_changed = true;
                        std::cout << "Condition of rule " << *rule << " is always TRUE..." << std::endl;
                        rule->prec = createConstantTrue();
                    }
                }
            }
            for (auto &&rule : false_to_remove) {
                policy->remove_rule(rule);
            }
            return has_changed;
        }

        bool easy_pruning() {
            bool easy_pruning_user = this->easy_pruning_user();
            bool easy_pruning_rule_condition = this->easy_pruning_rule_condition();

            return easy_pruning_user ||
                   easy_pruning_rule_condition;
        }

        /* IMMATERIAL ADMIN FUNCTIONS */
        bool immaterial_not_interfere(const Expr& adm) {
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
                    //FIXME: to decide if leave like this (could remove too fiew e.g. (true || !ra))
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

        bool immaterial_k_plus_two(const std::set<atom>& conf) {
            int i = 0;
            for (auto &&user : policy->users()) {
                if (user->config() == conf) {
                    i++;
                }
            }
            return i > policy->users_to_track();
        }

        template <typename TComp>
        bool immaterial_adm(const std::set<userp, TComp>& user_confs, const Expr& adm) {
            bool exists_user = false;
            userp satisfiant = nullptr;
            //exists a user that satisfies phi_adm
            for (auto &&user : user_confs) {
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
                    satisfiant = user;
                    std::cout << "User " << *user << " satisfies administrative formula "
                              << *adm << std::endl;
                    break;
                }
            }

            if (satisfiant == nullptr) {
                return false;
            }
            else {
                return immaterial_k_plus_two(satisfiant->config()) || immaterial_not_interfere(adm);
            }
        }

        bool prune_immaterial_roles() {
            std::map<Expr, std::list<rulep>> admins;
//            std::set<userp>

            auto user_comp = [&](const userp user1, const userp user2){ return user1->config() < user2->config(); };
            auto confs = std::set<userp, decltype(user_comp)>( user_comp );

            for (auto &&user : policy->users()) {
                confs.insert(user);
            }

            for (auto &&rule : policy->rules()) {
                admins[rule->admin].push_back(rule);
            }
            bool has_changed = false;
            for (auto &&adm_pair : admins) {
                bool has_admin = immaterial_adm(confs, adm_pair.first);
                if (has_admin) {
                    std::cout << "Administrative expression " << *adm_pair.first << " IS IMMATERIAL" << std::endl;
                    has_changed = true;
                    for (auto &&rule : adm_pair.second) {
                        rule->admin = createConstantTrue();
                    }
                }
            }
            return has_changed;
        }

        /* IRRELEVANT ROLES FUNCTIONS */
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

        bool prune_irrelevant_roles() {
            std::vector<Literalp> irrelevant;

            for (auto iterator = policy->atoms().begin(); iterator != policy->atoms().end(); ++iterator) {
                Literalp r = *iterator;
                bool can_remove = irrelevantRole(r);
                if (can_remove) {
                    std::cout << *r << " is irrelevant." << std::endl;
                    irrelevant.push_back(r);
                }
            }

            // REMOVAL:
            for (auto &&i_role : irrelevant) {
                policy->remove_atom(i_role);
            }
            return irrelevant.size() > 0;
        }

        /* IMPLIED RULE FUNCTIONS */
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

        bool prune_implied_pairs() {
            std::list<rulep> to_remove;
            for (auto &&ca1 : policy->can_assign_rules()) {
                //FIXME: cache ca1 expressions here
                for (auto &&ca2 : policy->can_assign_rules()) {
                    if (ca1 != ca2 &&
                        ca1->target->role_array_index == ca2->target->role_array_index) {

                        int are_implied = implied(ca1, ca2);
                        if (are_implied) {
                            std::cout << *ca1 << std::endl;
                            std::cout << *ca2 << std::endl;
                            to_remove.push_back(ca2);
                        }
                    }
                }
            }
            for (auto &&cr1 : policy->can_revoke_rules()) {
                for (auto &&cr2 : policy->can_revoke_rules()) {
                    if (cr1 != cr2 &&
                        cr1->target->role_array_index == cr2->target->role_array_index) {

                        int are_implied = implied(cr1, cr2);
                        if (are_implied) {
                            std::cout << *cr1 << std::endl;
                            std::cout << *cr2 << std::endl;
                            to_remove.push_back(cr2);
                        }
                    }
                }
            }
            for (auto &&rule : to_remove) {
                policy->remove_rule(rule);
            }
            return to_remove.size() > 0;
        }

        /* MERGE RULE FUNCTIONS */
        bool equivalent_exprs(const Expr& e1, const Expr& e2) {
//            if (e1->literals() != e2->literals()) {
//                return false;
//            }
//            else {

            solver->clean();

            std::vector<std::shared_ptr<TVar>> var_vec(policy->atom_count());
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

//            if (res) {
//                std::cout << "Expressions " << *e1 << std::endl;
//                std::cout << "            " << *e2 << std::endl;
//                std::cout << "            are equivalent!" << *e1 << std::endl;
//            }

            return res;

//            }
        }

        const std::list<std::list<rulep>> partition_equivalent(const atom& target, const std::list<rulep>& targetings) {
            auto ite = targetings.begin();
            std::list<std::list<rulep>> partitions;
            partitions.push_back(std::list<rulep>());
            partitions.begin()->push_back(*ite);
            ++ite;

            for ( ; ite != targetings.end(); ++ite) {
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

        rulep merge_rules(const std::list<rulep>& to_merge) {
            auto ite = to_merge.begin();
            rulep first = *ite;
            Expr final_prec = first->prec;
            ++ite;
            for ( ; ite != to_merge.end(); ++ite) {
                rulep ith = *ite;
                final_prec = createOrExpr(final_prec, ith->prec);
            }
            rulep ret(new rule(first->is_ca, first->admin, final_prec, first->target, -1));
            return ret;
        }

        bool merge_rules() {
            bool changed = false;

            std::map<Literalp, std::list<rulep>> assigning;
            std::map<Literalp, std::list<rulep>> revoking;
            std::list<rulep> new_to_add;
            std::list<rulep> old_to_remove;

            for (auto &&ca : policy->can_assign_rules()) {
                assigning[ca->target].push_back(ca);
            }
            for (auto &&cr : policy->can_revoke_rules()) {
                revoking[cr->target].push_back(cr);
            }


            for (auto &&pair : assigning) {
                std::list<rulep> rules = pair.second;
                std::list<std::list<rulep>> partitions = partition_equivalent(pair.first, rules);

                for (auto &&partition : partitions) {
                    if (partition.size() > 1) {
                        rulep new_rule = merge_rules(partition);
                        new_to_add.push_back(new_rule);
                        old_to_remove.insert(old_to_remove.begin(), partition.begin(), partition.end());
                        std::cout << "Merging rules:" << std::endl;
                        for (auto &&rule : partition) {
                            std::cout << "\t" << *rule << std::endl;
                        }
                        std::cout << "To:" << std::endl;
                        std::cout << "\t" << *new_rule << std::endl;
                    }
                }
            }

            for (auto &&pair : revoking) {
                std::list<rulep> rules = pair.second;
                std::list<std::list<rulep>> partitions = partition_equivalent(pair.first, rules);

                for (auto &&partition : partitions) {
                    if (partition.size() > 1) {
                        rulep new_rule = merge_rules(partition);
                        new_to_add.push_back(new_rule);
                        old_to_remove.insert(old_to_remove.begin(), partition.begin(), partition.end());
                        std::cout << "Merging rules:" << std::endl;
                        for (auto &&rule : partition) {
                            std::cout << "\t" << *rule << std::endl;
                        }
                        std::cout << "To:" << std::endl;
                        std::cout << "\t" << *new_rule << std::endl;
                    }
                }
            }

            for (auto &&old_rule : old_to_remove) {
                policy->remove_rule(old_rule);
            }

            for (auto &&to_add : new_to_add) {
                policy->add_rule(to_add);
            }
            return old_to_remove.size() > 0;
        }

        /* RULE 6 FUNCTIONS (NOT FIREABLE RULES) */
        bool prune_rule_6() {
            std::vector<std::shared_ptr<rule>> to_remove;

            for (auto &&rule : policy->rules()) {
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
                    std::cout << "X";
                    std::flush(std::cout);
                    to_remove.push_back(rule);
                } else if (rem_adm) {
                    std::cout << "O";
                    std::flush(std::cout);
                    to_remove.push_back(rule);
                } else {
                    std::cout << "-";
                    std::flush(std::cout);
                }
            }

            for (auto &&rule : to_remove) {
                policy->remove_rule(rule);
            }

            std::cout << std::endl << "Removed " << to_remove.size() << " rules" << std::endl;

            return to_remove.size() > 0;

//            auto start = std::chrono::high_resolution_clock::now();
            // CODE
//            auto end = std::chrono::high_resolution_clock::now();
//            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//            std::cout << "------------ Rule6 executed in " << milliseconds.count() << " ms ------------\n";

        }

        /* NOT USED ANYMORE */
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

        public:

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

        void apply() {
            bool fixpoint = false;
            int fixpoint_iteration = 1;

            while (!fixpoint) {
                std::cout << "Applying easy_pruning on " << policy->rules().size() << std::endl;
                bool easy_pruning_res = this->easy_pruning();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;
                std::cout << "Applying prune_immaterial_roles on " << policy->rules().size() << std::endl;
                bool prune_immaterial_roles_res = this->prune_immaterial_roles();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;
                std::cout << "Applying merge_rules on " << policy->rules().size() << std::endl;
                bool merge_rules_res = this->merge_rules();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;
                std::cout << "Applying prune_irrelevant_roles on " << policy->rules().size() << std::endl;
                bool prune_irrelevant_roles_res = this->prune_irrelevant_roles();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;
                std::cout << "Applying prune_implied_pairs on " << policy->rules().size() << std::endl;
                bool prune_implied_pairs_res = this->prune_implied_pairs();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;
                std::cout << "Applying prune_rule_6 on " << policy->rules().size() << std::endl;
                bool prune_rule_6_res = this->prune_rule_6();
                std::cout << " ==> " << policy->rules().size() << " rules..." << std::endl;

                fixpoint =
                        !(easy_pruning_res           ||
                          prune_immaterial_roles_res ||
                          merge_rules_res            ||
                          prune_irrelevant_roles_res ||
                          prune_implied_pairs_res    ||
                          prune_rule_6_res);

                std::cout << "Iteration: " << fixpoint_iteration++ << std::endl;
            }

            std::cout << *policy;

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
        core.apply();
//        std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
//        Pruning<term_t, term_t> core(solver);

//        core.apply_rule_6();

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
