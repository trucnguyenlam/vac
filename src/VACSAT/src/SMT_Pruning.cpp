
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

//        bool set_contains(const Expr& expr, const std::string& name) {
//            std::set<Literalp> literals = expr->literals();
//            for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
//                Literalp e = *ite;
//                if (e->name == name) {
//                    return true;
//                }
//            }
//            return false;
//        }

        bool have_common_atoms(const Expr& e1, const Expr& e2) {
            std::list<Literalw> intersection;
            //TODO: sure is it correct?
            std::set_intersection(e1->literals().begin(), e1->literals().end(),
                                  e2->literals().begin(), e2->literals().end(),
                                  std::back_inserter(intersection), std::owner_less<Literalw>());
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

        /* PRELIMINARY BACKWARD SLICING */
        bool backward_slicing() {
            bool fixpoint = false;
            std::set<rulep> to_save;
            std::set<Literalw, std::owner_less<Literalw>> necessary_atoms;
            necessary_atoms.insert(Literalw(policy->goal_role));
            while (!fixpoint) {
                fixpoint = true;
                for (auto &&rule : policy->rules()) {
//                    print_collection(necessary_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": "_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": " << (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) << std::endl;
                    if (!contains(to_save, rule) && contains_ptr(necessary_atoms, rule->target)) {
//                        print_collection(rule->admin->literals());
//                        print_collection(rule->prec->literals());

                        necessary_atoms.insert(rule->admin->literals().begin(), rule->admin->literals().end());
                        necessary_atoms.insert(rule->prec->literals().begin(), rule->prec->literals().end());
                        to_save.insert(rule);
                        fixpoint = false;
                    }
                }
            }

            std::list<rulep> to_remove;
            for (auto &&rule : policy->rules()) {
                if (!contains(to_save, rule)) {
                    to_remove.push_back(rule);
                    log->debug(rule->to_string());
                }
            }

            std::list<atom> atoms_to_remove;
            for (auto &&atom : policy->atoms()) {
                if (!contains_ptr(necessary_atoms, atom)) {
                    atoms_to_remove.push_back(atom);
                    log->debug(atom->to_string());
                }
            }

            policy->remove_rules(to_remove);
            policy->remove_atoms(atoms_to_remove);

            return to_remove.size() > 0;
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
                    throw std::runtime_error("Cannot check the UNUSED status here...");
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
                    throw std::runtime_error("Cannot check the BOTH_VALUED status here...");
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
                if (contains_ptr(rule->admin->literals(), atom)) {
                    using_a.push_back(rule->admin);
                }
                if (contains_ptr(rule->prec->literals(), atom)) {
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

        bool atom_has_status(const atom& atom, AtomStatus status) {
            std::list<Expr> using_a;
            for (auto &&rule : policy->rules()) {
                if (contains_ptr(rule->admin->literals(), atom)) {
                    using_a.push_back(rule->admin);
                }
                if (contains_ptr(rule->prec->literals(), atom)) {
                    using_a.push_back(rule->prec);
                }
            }
            if (using_a.size() <= 0) {
                throw std::runtime_error("UNUSED cannot be compared");
                return false;
            }
            return has_status(atom, using_a, status);
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

        bool easy_pruning_positive_negative() {
            std::list<atom> not_used_atoms;
            std::list<rulep> rules_to_remove;
            for (auto &&atom : policy->atoms()) {
                bool used = false;
                for (auto &&rule : policy->rules()) {
                    if (contains_ptr(rule->admin->literals(), atom) ||
                        contains_ptr(rule->prec->literals(), atom)) {
                        used = true;
                        break;
                    }
                }
                if (!used && atom != policy->goal_role) {
                    not_used_atoms.push_back(atom);
                    log->trace("Atom: {} is never used. Removing it!", atom->to_string());
                }
                else if (atom == policy->goal_role){
                    for (auto &&cr : policy->can_revoke_rules()) {
                        if (cr->target == atom) {
                            rules_to_remove.push_back(cr);
                            log->trace("\t{}", cr->to_string());
                        }
                    }
                    log->trace("Atom: {} is the GOAL_ROLE. Removing can_revoke_rules targeting it!", atom->to_string());
                }
                else {
                    if (policy->per_role_can_assign_rule(atom).size() == 0 &&
                            policy->per_role_can_revoke_rule(atom).size() == 0) {
//                        std::cout << "Atom: " << *atom << " is NEVER ASSIGNED/REVOKED. Do not compute status!" << std::endl;
                        continue;
                    }
                    if (policy->per_role_can_assign_rule(atom).size() > 0) {
                        //CAN ASSIGN IT. CHECK IF NEVER POSITIVE (REMOVE CA)
                        if (atom_has_status(atom, NON_POSITIVE)) {
                            if (forall_user([&](const userp& user) { return !contains(user->config(), atom); })) {
                                log->trace("Atom: {} is NON_POSITIVE and no users have it. Remove it!", atom->to_string());
                                not_used_atoms.push_back(atom);
                            }
                            else {
                                log->trace("Atom: {} is NON_POSITIVE. Removing can_assign_rules targeting it!", atom->to_string());

                                auto to_remove = policy->per_role_can_assign_rule(atom);
                                for (auto &&r : to_remove) {
                                    log->trace(r->to_string());
                                }
                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
                            }
                        }
                    }
                    if (policy->per_role_can_revoke_rule(atom).size() > 0) {
                        //CAN REVOKE IT. CHECK IF NEVER NEGATIVE (REMOVE CR)
                        if (atom_has_status(atom, NON_NEGATIVE)) {
                            if (forall_user([&](const userp& user) { return contains(user->config(), atom); })) {
                                log->trace("Atom: {} is NON_NEGATIVE and all users have it. Remove it!", atom->to_string());
                                not_used_atoms.push_back(atom);
                            }
                            else {
                                log->trace("Atom: {} is NON_NEGATIVE. Removing can_revoke_rules targeting it!", atom->to_string());

                                auto to_remove = policy->per_role_can_revoke_rule(atom);
                                for (auto &&r : to_remove) {
                                    log->trace(r->to_string());
                                }
                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
                            }
                        }
                    }
//                    else {
//                        AtomStatus status = get_atom_status(atom);
//                        switch (status) {
//                            case UNUSED:
//                                // done before
//                                break;
//                            case NON_NEGATIVE: {
//                                // IF ALL USER DOES HAVE IT REMOVE IT SINCE NO NEED OF CHANGE
//                                if (forall_user([&](const userp& user) { return contains(user->config(), atom); })) {
//                                    std::cout << "Atom: " << *atom << " is NON_NEGATIVE and all users have it. Remove it!" << std::endl;
//                                    not_used_atoms.push_back(atom);
//                                    break;
//                                }
//                                std::cout << "Atom: " << *atom << " is NON_NEGATIVE. Removing can_revoke_rules targeting it!" << std::endl;
//    //                            for (auto &&cr : policy->can_revoke_rules()) {
//    //                                if (cr->target == atom) {
//    //                                    rules_to_remove.push_back(cr);
//    //                                    std::cout << "\t" << *cr << std::endl;
//    //                                }
//    //                            }
//                                auto to_remove = policy->per_role_can_revoke_rule(atom);
//                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
//                                break;
//                            }
//                            case NON_POSITIVE: {
//                                // IF ALL USER DOES NOT HAVE IT REMOVE IT SINCE NO NEED OF CHANGE
//                                if (forall_user([&](const userp& user) { return !contains(user->config(), atom); })) {
//                                    std::cout << "Atom: " << *atom << " is NON_POSITIVE and no users have it. Remove it!" << std::endl;
//                                    not_used_atoms.push_back(atom);
//                                    break;
//                                }
//                                std::cout << "Atom: " << *atom << " is NON_POSITIVE. Removing can_assign_rules targeting it!" << std::endl;
//    //                            for (auto &&ca : policy->can_assign_rules()) {
//    //                                if (ca->target == atom) {
//    //                                    rules_to_remove.push_back(ca);
//    //                                    std::cout << "\t" << *ca << std::endl;
//    //                                }
//    //                            }
//                                auto to_remove = policy->per_role_can_assign_rule(atom);
//                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
//                                break;
//                            }
//                            default:
//                                break;
//                        }
                }
            }

            policy->remove_atoms(not_used_atoms);
            policy->remove_rules(rules_to_remove);

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
                    log->trace("Rule {} is never satisfiable. Remove it.", rule->to_string());
                    false_to_remove.push_back(rule);
                }
                else {
                    if (!is_constant_true(rule->admin) && true_condition(rule->admin)) {
                        has_changed = true;
                        log->trace("Administrative condition of rule {} is always TRUE...", rule->to_string());
                        rule->admin = createConstantTrue();
                    }
                    if (!is_constant_true(rule->prec) && true_condition(rule->prec)) {
                        has_changed = true;
                        log->trace("Condition of rule {} is always TRUE...", rule->to_string());
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
            bool easy_pruning_user = this->easy_pruning_positive_negative();
            bool easy_pruning_rule_condition = this->easy_pruning_rule_condition();

            return easy_pruning_user ||
                   easy_pruning_rule_condition;
        }

        /* IMMATERIAL ADMIN FUNCTIONS */
        bool immaterial_not_interfere(const Expr& adm) {
            // Check if the administrative expression interfere (cause false) in other expressions
            // TODO: consider changing with set to reduce equals checks
            std::list<Expr> other_exprs;
            for (auto &&r : policy->rules()) {
                other_exprs.push_back(r->prec);
                if (adm != r->admin) {
                    other_exprs.push_back(r->admin);
                }
            }

            std::vector<std::shared_ptr<TVar>> adm_var_vec((unsigned long) policy->atom_count());
            TExpr solver_adm = generateSMTFunction2(solver, adm, adm_var_vec, std::string("adm"));

            for (auto &&expr : other_exprs) {

                if (!have_common_atoms(adm, expr)) {
                    //FIXME: to decide if leave like this (could remove too fiew e.g. (true || !ra))
                    // can go forward since atoms are disjoint
                    continue;
                }

                solver->clean();

                std::vector<std::shared_ptr<TVar>> free_var_vec((unsigned long) policy->atom_count());
                TExpr solver_exp = generateSMTFunction2(solver, expr, free_var_vec, std::string("adm"));

                std::vector<std::shared_ptr<TVar>> updated_vec = update_tlookup(free_var_vec, adm_var_vec);
//                std::cout << "adm_var_vec" << std::endl;
//                printLookup(adm_var_vec);
//                std::cout << "free_var_vec" << std::endl;
//                printLookup(free_var_vec);
//                std::cout << "updated_vec" << std::endl;
//                printLookup(updated_vec);
                TExpr not_solver_exp = solver->createNotExpr(generateSMTFunction2(solver, expr, updated_vec, std::string("adm")));

                solver->assertNow(solver_adm);
                solver->assertNow(solver_exp);
                solver->assertNow(not_solver_exp);

                bool res = solver->solve() == UNSAT;

                if (!res) {
//                    solver->printModel();
                    log->trace("{} administrative part interfere with {}", adm->to_string(), expr->to_string());
                    return false;
                }
            }

            return true;
        }

        int admin_count() {
            //FIXME: use semantics equivalence and not structural one
            auto expr_comp = [&](const Expr e1, const Expr e2){
                int res = e1->equals(e2) ? 0 : (e1 < e2);
                return res; };
            auto admin_exprs = std::set<Expr, decltype(expr_comp)>( expr_comp );

            Expr true_expr = createConstantTrue();
            for (auto &&rule :policy->rules()) {
                if (!rule->admin->equals(true_expr)) {
                    admin_exprs.insert(rule->admin);
//                    std::cout << "ADM: " << *rule->admin << std::endl;
                }
            }

//            print_collection(admin_exprs, "set: ");

            return (int) admin_exprs.size();
        }

        bool immaterial_k_plus_two(const std::set<atom>& conf, int count) {
            int i = 0;
            for (auto &&user : policy->users()) {
                if (user->config() == conf) {
                    i++;
                }
            }

            return i > count;
//            return i > policy->users_to_track();
        }

        bool immaterial_admin_in_prec(const rulep& rule) {
            // This rule checks if adm is implied in prec. If so we can remove the admin part and replace with TRUE since the check is done on
            solver->clean();
            std::vector<std::shared_ptr<TVar>> var_vect((ulong) policy->atom_count());

            TExpr s_adm = generateSMTFunction2(solver, rule->admin, var_vect, "C");

            TExpr s_prec = generateSMTFunction2(solver, rule->prec, var_vect, "C");

            TExpr to_check = solver->createAndExpr(solver->createNotExpr(s_adm),
                                                   s_prec);

            solver->assertNow(to_check);

            SMTResult res = solver->solve();

            return res == UNSAT;
        }

        bool immaterial_adm(const Expr& adm) {
            bool exists_user = false;
            userp satisfiant = nullptr;
            //exists a user that satisfies phi_adm
            for (auto &&user : policy->unique_configurations()) {
                solver->clean();

                Expr adm_expr = adm;
                Expr user_expr = policy->user_to_expr(user->original_idx, adm->literals());

                std::vector<std::shared_ptr<TVar>> var_vect((int) policy->atom_count());

                TExpr solver_adm_expr = generateSMTFunction2(solver, adm_expr, var_vect, user->name);
                TExpr solver_user_expr = generateSMTFunction2(solver, user_expr, var_vect, user->name);

                solver->assertNow(solver_user_expr);
                solver->assertNow(solver_adm_expr);

                bool satisfies = solver->solve() == SAT;

                if (satisfies) {
                    satisfiant = user;
                    log->trace("User {} satisfies administrative formula {}", user->to_string(), adm->to_string());
                    break;
                }
            }

            if (satisfiant == nullptr) {
                return false;
            }
            else {
                int _admin_count = admin_count();
                return immaterial_k_plus_two(satisfiant->config(), _admin_count) || immaterial_not_interfere(adm);
            }
        }

        bool prune_immaterial_roles_opt() {
            std::map<Expr, std::list<rulep>> admins;
            bool has_changed = false;

            for (auto &&rule : policy->rules()) {
//                if (!is_constant_true(rule->admin) && immaterial_admin_in_prec(rule)) {
//                    std::cout << "Admin is already checked in the precondition: " << *rule << std::endl;
//                    rule->admin = createConstantTrue();
//                    has_changed = true;
//                    continue;
//                }
                admins[rule->admin].push_back(rule);
            }
//            std::cout << admins.size() << std::endl;
            for (auto &&adm_pair : admins) {
                if (is_constant_true(adm_pair.first)) {
                    // Do nothing if the administrative expression is the True constant
                    continue;
                }
                bool has_admin = immaterial_adm(adm_pair.first);
                if (has_admin) {
                    log->trace("Administrative expression {} IS IMMATERIAL", adm_pair.first->to_string());
                    has_changed = true;
                    for (auto &&rule : adm_pair.second) {
                        rule->admin = createConstantTrue();
                    }
                }
            }
            return has_changed;
        }

        bool prune_immaterial_roles() {
//            std::map<Expr, std::list<rulep>> admins;
            bool has_changed = false;

            for (auto &&rule : policy->rules()) {
                if (is_constant_true(rule->admin))
                    continue;
                if (!is_constant_true(rule->admin) && immaterial_admin_in_prec(rule)) {
                    log->trace("Admin is already checked in the precondition: {}", rule->to_string());
                    rule->admin = createConstantTrue();
                    has_changed = true;
                    continue;
                }
                bool has_admin = immaterial_adm(rule->admin);
                if (has_admin) {
                    log->trace("Administrative expression {} IS IMMATERIAL", rule->admin->to_string());
                    has_changed = true;
                    rule->admin = createConstantTrue();
                }
//                admins[rule->admin].push_back(rule);
            }
            return has_changed;
        }

        /* IRRELEVANT ROLES FUNCTIONS */
        TExpr irr_mix_cond_one(const Literalp& role,
                               const std::shared_ptr<rule>& using_r,
                               const std::list<std::shared_ptr<rule>>& assigning_r,
                               const std::list<std::shared_ptr<rule>>& removing_r) {
            //TODO: ADD IRRELEVANT FOR ADMIN HERE

            std::vector<std::shared_ptr<TVar>> c_vect(policy->atom_count());
            std::vector<std::shared_ptr<TVar>> adm_vect(policy->atom_count());

            // C_r
            TExpr not_c_r = generateSMTFunction2(solver, role, c_vect, "C");
            // not C_r
            TExpr c_r = solver->createNotExpr(generateSMTFunction2(solver, role, c_vect, "C"));

            // phi_r^TRUE(C)
            role->setValue(createConstantTrue());
            TExpr phi_r_true_c = generateSMTFunction2(solver, using_r->prec, c_vect, "C");

            // phi_r^FALSE(C)
            role->setValue(createConstantFalse());
            TExpr phi_r_false_c = generateSMTFunction2(solver, using_r->prec, c_vect, "C");

            role->resetValue();

            //phi_a_(adm)
            TExpr phi_a_adm = generateSMTFunction2(solver, using_r->admin, adm_vect, "ADM");

            // phi_r^TRUE(C) /\ not phi_r^FALSE(C) /\ phi_a_(adm)
            TExpr pos_lhs = solver->createAndExpr(solver->createAndExpr(phi_r_true_c,
                                                                        solver->createNotExpr(phi_r_false_c)),
                                                  phi_a_adm);

            // not phi_r^TRUE(C) /\ phi_r^FALSE(C) /\ phi_a_(adm)
            TExpr neg_lhs = solver->createAndExpr(solver->createAndExpr(solver->createNotExpr(phi_r_true_c),
                                                                        phi_r_false_c),
                                                  phi_a_adm);

            std::list<TExpr> assign_and_rhs;

            for (auto &&ca : assigning_r) {
                std::vector<std::shared_ptr<TVar>> c1_vect = c_vect;
                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                TExpr phi1_c = generateSMTFunction2(solver, ca->prec, c1_vect, "C");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction2(solver, ca->admin, adm1_vect, "ADM");

                //phi'_a(C)
                TExpr phi1_a_c = generateSMTFunction2(solver, ca->admin, c1_vect, "C");

                // not (phi'(C)) \/ not (phi'_a(adm) \/ phi'_a(C))
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_c),
                                                  solver->createNotExpr(solver->createOrExpr(phi1_a_adm,
                                                                                             phi1_a_c)));

                assign_and_rhs.push_back(disj);
            }

            TExpr assign_bigand = solver->joinExprsWithAnd(assign_and_rhs);


            std::list<TExpr> revoke_and_rhs;

            for (auto &&cr  : removing_r) {
                std::vector<std::shared_ptr<TVar>> c1_vect = c_vect;
                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                TExpr phi1_c = generateSMTFunction2(solver, cr->prec, c1_vect, "C");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction2(solver, cr->admin, adm1_vect, "ADM");

                //phi'_a(C)
                TExpr phi1_a_c = generateSMTFunction2(solver, cr->admin, c1_vect, "C");

                // not (phi'(C)) \/ not (phi'_a(adm) \/ phi'_a(C))
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_c),
                                                  solver->createNotExpr(solver->createOrExpr(phi1_a_adm,
                                                                                             phi1_a_c)));

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

        TExpr irr_mix_adm_one(const Literalp& role,
                               const std::shared_ptr<rule>& using_r,
                               const std::list<std::shared_ptr<rule>>& assigning_r,
                               const std::list<std::shared_ptr<rule>>& removing_r) {
            //TODO: ADD IRRELEVANT FOR ADMIN HERE

            std::vector<std::shared_ptr<TVar>> adm_vect(policy->atom_count());

            // Adm_r
            TExpr not_adm_r = generateSMTFunction2(solver, role, adm_vect, "Adm");
            // not Adm_r
            TExpr adm_r = solver->createNotExpr(generateSMTFunction2(solver, role, adm_vect, "Adm"));

            // phi_a_r^TRUE(Adm)
            role->setValue(createConstantTrue());
            TExpr phi_a_r_true_adm = generateSMTFunction2(solver, using_r->admin, adm_vect, "C");

            // phi_a_r^FALSE(Adm)
            role->setValue(createConstantFalse());
            TExpr phi_a_r_false_adm = generateSMTFunction2(solver, using_r->admin, adm_vect, "C");

            role->resetValue();

            // phi_a_r^TRUE(Adm) /\ not phi_a_r^FALSE(Adm)
            TExpr pos_lhs = solver->createAndExpr(phi_a_r_true_adm,
                                                  solver->createNotExpr(phi_a_r_false_adm));

            // not phi_a_r^TRUE(Adm) /\ phi_a_r^FALSE(Adm)
            TExpr neg_lhs = solver->createAndExpr(solver->createNotExpr(phi_a_r_true_adm),
                                                  phi_a_r_false_adm);

            std::list<TExpr> assign_and_rhs;

            for (auto &&ca : assigning_r) {
                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                TExpr phi1_adm = generateSMTFunction2(solver, ca->prec, adm1_vect, "ADM");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction2(solver, ca->admin, adm1_vect, "ADM");

                // not (phi'(adm)) \/ not phi'_a(adm))
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_adm),
                                                  solver->createNotExpr(phi1_a_adm));

                assign_and_rhs.push_back(disj);
            }

            TExpr assign_bigand = solver->joinExprsWithAnd(assign_and_rhs);


            std::list<TExpr> revoke_and_rhs;

            for (auto &&cr  : removing_r) {
                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(adm)
                TExpr phi1_adm = generateSMTFunction2(solver, cr->prec, adm1_vect, "C");

                //phi'_a(adm)
                TExpr phi1_a_adm = generateSMTFunction2(solver, cr->admin, adm1_vect, "ADM");

                // not (phi'(C)) \/ not phi'_a(adm))
                TExpr disj = solver->createOrExpr(solver->createNotExpr(phi1_adm),
                                                  solver->createNotExpr(phi1_a_adm));

                revoke_and_rhs.push_back(disj);
            }

            TExpr revoke_bigand = solver->joinExprsWithAnd(revoke_and_rhs);

            TExpr pos_ca = solver->createAndExpr(not_adm_r,
                                                 solver->createAndExpr(pos_lhs,
                                                                       assign_bigand));

            TExpr neg_ca = solver->createAndExpr(adm_r,
                                                 solver->createAndExpr(neg_lhs,
                                                                       revoke_bigand));

            TExpr res = solver->createOrExpr(pos_ca, neg_ca);

            return res;
        }

        bool irrelevantRole(const Literalp& role) {
            if (role == policy->goal_role) {
//                std::cout << "Role " << role->fullName() << " is TARGET" << std::endl;
                return false;
            }

            std::list<rulep> admin_using_r;
            std::list<rulep> using_r;
            std::list<rulep> assigning_r;
            std::list<rulep> removing_r;
            for (auto &&ca : policy->can_assign_rules()) {
                if (contains_ptr(ca->admin->literals(), role)) {
                    admin_using_r.push_back(ca);
                }
                if (contains_ptr(ca->prec->literals(), role)) {
                    using_r.push_back(ca);
                }
                if (ca->target == role) {
                    assigning_r.push_back(ca);
                }
            }
            for (auto &&cr : policy->can_revoke_rules()) {
                if (contains_ptr(cr->admin->literals(), role)) {
                    admin_using_r.push_back(cr);
                }
                if (contains_ptr(cr->prec->literals(), role)) {
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
                for (auto &&r_using_r : using_r) {
                    solver->clean();
                    TExpr cond = irr_mix_cond_one(role,
                                                  r_using_r,
                                                  assigning_r,
                                                  removing_r);
                    solver->assertNow(cond);

                    SMTResult res = solver->solve();

                    if (res == SAT) {
                        can_remove = false;
                        break;
                    }

                }

                for (auto &&adm_using_r : admin_using_r) {
                    solver->clean();
                    TExpr cond = irr_mix_adm_one(role,
                                                 adm_using_r,
                                                 assigning_r,
                                                 removing_r);
                    solver->assertNow(cond);

                    SMTResult res = solver->solve();

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
            std::list<Literalp> irrelevant;

            for (auto &&r : policy->atoms()) {
                bool can_remove = irrelevantRole(r);
                if (can_remove) {
                    log->trace("{} is irrelevant.", r->to_string());
                    irrelevant.push_back(r);
                }
            }

            // REMOVAL:
            policy->remove_atoms(irrelevant);
            return irrelevant.size() > 0;
        }

        /* IMPLIED RULE FUNCTIONS */
        int implied(const std::shared_ptr<rule>& ca1, const std::shared_ptr<rule>& ca2) {
            std::vector<std::shared_ptr<TVar>> c_vect((ulong) policy->atom_count());
            std::vector<std::shared_ptr<TVar>> adm_vect((ulong) policy->atom_count());
            std::string c_suff("C");
            std::string adm_suff("admin");

            solver->clean();

            TExpr phi1_adm = generateSMTFunction2(solver, ca1->admin, adm_vect, adm_suff);
            TExpr phi2_adm = generateSMTFunction2(solver, ca2->admin, adm_vect, adm_suff);


            // For performances improvement we test admin first and then the precondition
            // // \phi_a(adm) /\ \not \phi'_a(adm)
            TExpr adm_cond = solver->createAndExpr(phi2_adm,
                                                   solver->createNotExpr(phi1_adm));

            solver->assertNow(adm_cond);
            SMTResult adm_res = solver->solve();

            if (adm_res == SAT) {
                return false;
            }
//            std::cout << "Admin, impl: " << *ca1->admin << " ==> " << *ca2->admin << std::endl;

//            std::cout << *ca1 << std::endl;
//            std::cout << *ca2 << std::endl;
            solver->clean();

            TExpr phi1_pn = generateSMTFunction2(solver, ca1->prec, c_vect, c_suff);
            TExpr phi2_pn = generateSMTFunction2(solver, ca2->prec, c_vect, c_suff);
            // \phi(C) /\ \not \phi'(C)
            TExpr cond = solver->createAndExpr(phi2_pn,
                                               solver->createNotExpr(phi1_pn));

            solver->assertNow(cond);
            SMTResult cond_res = solver->solve();

//            std::cout << "Prec, impl: " << *ca1->prec << " ==> " << *ca2->prec << ": " << (cond_res == SAT ? "SAT" : "UNSAT") << std::endl;
//            solver->printExpr(cond);
            return cond_res != SAT;




//            // \phi'_a(adm) /\ \phi'(C)
//            TExpr lhs = solver->createAndExpr(phi2_adm, phi2_pn);
//
//            // (\not\phi_a(adm)) \/ (\not\phi(c))
//            // \not (\phi_a(adm) /\ \phi(C))
//            TExpr rhs = solver->createNotExpr(solver->createAndExpr(phi1_adm, phi1_pn));
//
//            // (\phi_a(adm) /\ \phi(C)) /\ ((\not\phi'_a(adm)) \/ (\not\phi'(c)))
//            TExpr final_cond = solver->createAndExpr(lhs, rhs);

//            solver->assertNow(final_cond);
//            SMTResult res = solver->solve();
//            solver->clean();
//            return res == UNSAT;
        }

        bool prune_implied_pairs() {
            std::list<rulep> to_remove;
            // Support array used to keep track of can assign rules marked for removal
            std::vector<bool> ca_removed_mark(policy->can_assign_rules().size());
            // Support array used to keep track of can revoke rules marked for removal
            std::vector<bool> cr_removed_mark(policy->can_revoke_rules().size());
            for (auto &&atom :policy->atoms()) {
                std::list<rulep> assigning_rules = policy->per_role_can_assign_rule(atom);
                for (auto &&ca1 : assigning_rules) {
                    // If ca1 is marked for removal skip it (it avoids the duplicate rule removal)
                    if (ca_removed_mark[ca1->original_idx]) {
                        continue;
                    }
                    for (auto &&ca2 : assigning_rules) {
                        // If ca2 is marked for removal skip it
                        if (!ca_removed_mark[ca2->original_idx] && ca1 != ca2) {
                            assert(ca1->target->role_array_index == ca2->target->role_array_index);

                            int are_implied = implied(ca1, ca2);
                            if (are_implied) {
                                log->trace("Implied: {} ==>", ca1->to_string());
                                log->trace("         {}", ca2->to_string());
                                to_remove.push_back(ca2);
                                ca_removed_mark[ca2->original_idx] = true;
//                                std::cout << "" << std::endl;
                            }
                        }
                    }
                }
                std::list<rulep> revoking_rules = policy->per_role_can_revoke_rule(atom);
                for (auto &&cr1 : revoking_rules) {
                    // If cr1 is marked for removal skip it (it avoids the duplicate rule removal)
                    if (cr_removed_mark[cr1->original_idx]) {
                        continue;
                    }
                    for (auto &&cr2 : revoking_rules) {
                        // If cr2 is marked for removal skip it
                        if (!cr_removed_mark[cr2->original_idx] && cr1 != cr2) {
                            assert(cr1->target->role_array_index == cr2->target->role_array_index);

                            int are_implied = implied(cr1, cr2);
                            if (are_implied) {
                                log->trace("Implied: {} ==>", cr1->to_string());
                                log->trace("         {}", cr2->to_string());
                                to_remove.push_back(cr2);
//                                std::cout << "" << std::endl;
                            }
                        }
                    }
                }
            }

//            std::list<rulep> to_remove;
//            for (auto &&ca1 : policy->can_assign_rules()) {
//                //FIXME: cache ca1 expressions here
//                for (auto &&ca2 : policy->can_assign_rules()) {
//                    if (ca1 != ca2 &&
//                        ca1->target->role_array_index == ca2->target->role_array_index) {
//
//                        int are_implied = implied(ca1, ca2);
//                        if (are_implied) {
//                            std::cout << *ca1 << std::endl;
//                            std::cout << *ca2 << std::endl;
//                            to_remove.push_back(ca2);
//                        }
//                    }
//                }
//            }
//            for (auto &&cr1 : policy->can_revoke_rules()) {
//                for (auto &&cr2 : policy->can_revoke_rules()) {
//                    if (cr1 != cr2 &&
//                        cr1->target->role_array_index == cr2->target->role_array_index) {
//
//                        int are_implied = implied(cr1, cr2);
//                        if (are_implied) {
//                            std::cout << *cr1 << std::endl;
//                            std::cout << *cr2 << std::endl;
//                            to_remove.push_back(cr2);
//                        }
//                    }
//                }
//            }
            policy->remove_rules(to_remove);
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
                        log->trace("Merging rules:");
                        for (auto &&rule : partition) {
                            log->trace("\t{}", rule->to_string());
                        }
                        log->trace("To:");
                        log->trace("\t{}", new_rule->to_string());
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
                        log->trace("Merging rules:");
                        for (auto &&rule : partition) {
                            log->trace("\t{}", rule->to_string());
                        }
                        log->trace("To:");
                        log->trace("\t{}", new_rule->to_string());
                    }
                }
            }

            policy->remove_rules(old_to_remove);

            for (auto &&to_add : new_to_add) {
                policy->add_rule(to_add);
            }
            return old_to_remove.size() > 0;
        }

        /* RULE 6 FUNCTIONS (NOT FIREABLE RULES) */
        bool prune_rule_6() {
            std::list<std::shared_ptr<rule>> to_remove;

            for (auto &&rule : policy->rules()) {
//                if (rule->target->name.compare(0, 7, "anyfour") == 0) {
//                    std::cout << *rule << std::endl;
//                }
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

            std::cout << std::endl;

            for (auto &&rule :to_remove) {
//                policy->remove_rule(rule);
                log->trace(rule->to_string());
            }

            policy->remove_rules(to_remove);

//            std::cout << std::endl << "Removed " << to_remove.size() << " rules" << std::endl;

            return to_remove.size() > 0;

//            auto start = std::chrono::high_resolution_clock::now();
            // CODE
//            auto end = std::chrono::high_resolution_clock::now();
//            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//            std::cout << "------------ Rule6 executed in " << milliseconds.count() << " ms ------------\n";

        }

        /* SIMPLIFY EXPRESSIONS */
        std::list<atom> get_irrelevant(const Expr& expr) {
            std::list<atom> to_remove;
            for (auto &&watom : expr->literals()) {
                auto atom = watom.lock();
                solver->clean();

                std::vector<std::shared_ptr<TExpr>> var_vect((ulong) policy->atom_count());

                //phi_a_true
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createTrue());
                TExpr phi_a_true = generateSMTFunction2(solver, expr, var_vect, "C");

                //phi_a_false
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createFalse());
                TExpr phi_a_false = generateSMTFunction2(solver, expr, var_vect, "C");

                // Phi_r_true(C) /\ not Phi_r_false(C)
                TExpr pos = solver->createAndExpr(phi_a_true,
                                                 solver->createNotExpr(phi_a_false));
                // Phi_r_false(C) /\ not Phi_r_true(C)
                TExpr neg = solver->createAndExpr(solver->createNotExpr(phi_a_true),
                                                 phi_a_false);

                TExpr to_check = solver->createOrExpr(pos, neg);

                solver->assertNow(to_check);
                SMTResult res = solver->solve();

                if (res == UNSAT) {
                    to_remove.push_back(atom);
                }
            }
            return to_remove;
        }

        bool simplify_expressions() {
            bool has_changed = false;
            std::list<rulep> to_remove;
            std::list<rulep> to_add;
            for (auto &&rule :policy->rules()) {
//                std::cout << *rule << std::endl;

                std::list<atom> admin_to_remove = get_irrelevant(rule->admin);
                std::list<atom> prec_to_remove = get_irrelevant(rule->prec);

                if (admin_to_remove.size() > 0 || prec_to_remove.size() > 0) {

                    Expr adm = rule->admin;
                    for (auto &&atom : admin_to_remove) {
                        has_changed = true;
                        log->trace("Removing atom {} from expression {} since is not used", atom->to_string(), adm->to_string());
                        adm = delete_atom(adm, atom);
                        log->trace("\t==>{}", adm->to_string());
                    }
                    Expr prec = rule->prec;
                    for (auto &&atom : prec_to_remove) {
                        has_changed = true;
                        log->trace("Removing atom {} from expression {} since is not used", atom->to_string(), adm->to_string());
                        prec = delete_atom(prec, atom);
                        log->trace("\t==>{}", prec->to_string());
                    }

                    to_remove.push_back(rule);
                    to_add.push_back(std::shared_ptr<SMT::rule>(new SMT::rule(rule->is_ca, adm, prec, rule->target, -1)));
                }
            }


            policy->remove_rules(to_remove);
            policy->add_rules(to_add);


            return has_changed;
        }

        /* USER REDUCTION */
        void reduce_users() {
            auto unique_conf = policy->unique_configurations();
            std::list<std::pair<std::set<atom>, std::list<userp>>> partitions;

            for (auto &&u_conf : unique_conf) {
                partitions.push_back(std::pair<std::set<atom>, std::list<userp>>(u_conf->config(), std::list<userp>()));
            }

            int user_k = admin_count() + 1;

            for (auto &&pair : partitions) {
                if (pair.second.size() < user_k) {
                    for (auto &&user : policy->users()) {
                        if (user->config() == pair.first) {
                            pair.second.push_back(user);

                            if (pair.second.size() >= user_k) {
                                break;
                            }
                        }
                    }
                }
            }

            std::vector<userp> new_users;

            for (auto &&pair : partitions) {
                for (auto &&user : pair.second) {
                    new_users.push_back(user);
                }
            }

            policy->set_users(new_users);

        }

        /* ROLES REDUCTION */
        bool reduce_roles() {
            std::set<Literalw, std::owner_less<Literalw>> new_atoms;
            new_atoms.insert(Literalw(policy->goal_role));
            for (auto &&rule : policy->rules()) {
                new_atoms.insert(rule->admin->literals().begin(), rule->admin->literals().end());
                new_atoms.insert(rule->prec->literals().begin(), rule->prec->literals().end());
                new_atoms.insert(Literalw(rule->target));
            }
            if (new_atoms.size() != policy->atoms().size()) {
                std::vector<atom> nform(new_atoms.begin(), new_atoms.end());
                policy->set_atoms(nform);
                return true;
            }
            return false;
        }

        /* NOT USED ANYMORE */
        int nonPositiveNegative(int roleId, bool check_positive) {
            Literalp role = policy->atoms(roleId);
            std::vector<Expr> to_check;

            for (auto &&rule : policy->can_assign_rules()) {
                if (rule->admin->literals().count(role) > 0) {
//                    std::cout << "Role: " << role->fullName() << " is administrative thus NOT non-positive" << std::endl;
                    return false;
                    to_check.push_back(rule->admin);
                }
                if (rule->prec->literals().count(role) > 0) {
                    to_check.push_back(rule->prec);
                }
            }

            for (auto &&rule : policy->can_revoke_rules()) {
                if (rule->admin->literals().count(role) > 0) {
//                    std::cout << "Role: " << role->fullName() << " is administrative thus NOT non-positive" << std::endl;
                    return false;
                    to_check.push_back(rule->admin);
                }
                if (rule->prec->literals().count(role) > 0) {
                    to_check.push_back(rule->prec);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                solver->clean();

                bool exists = false;

                for (auto &&expr : to_check) {
                    //TODO: eventually create a big dinsjunction on all formulae

                    std::map<std::string, TVar> tmap;
                    // phi_a^TRUE
                    role->setValue(createConstantTrue());
                    TExpr phi_a_true = generateSMTFunction2(solver, expr, tmap, "C");

                    // phi_a^FALSE
                    role->setValue(createConstantFalse());
                    TExpr phi_a_false = generateSMTFunction2(solver, expr, tmap, "C");

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
            throw std::runtime_error("FIXME: refactored. Fix here");
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
            throw std::runtime_error("FIXME: refactored. Fix here");
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
            throw std::runtime_error("FIXME: refactored. Fix here");
//            TExpr pos_cond = irr_pos_cond(roleId, using_r, assigning_r);
//            TExpr neg_cond = irr_neg_cond(roleId, using_r, removing_r);
//            return solver->createOrExpr(pos_cond, neg_cond);

        }

        public:

//        void test() {
//            TVar v = solver->createBoolVar("polok");
//            TExpr e1 = v;
//
//            solver->assertNow(e1);
//            std::string r1 = solver->solve() == SAT ? "SAT" : "UNSAT";
//
//            std::cout << r1 << std::endl;
//            solver->printModel();
//
//            solver->clean();
//
//            TExpr e2 = solver->createNotExpr(v);
//            solver->assertNow(e2);
//            std::string r2 = solver->solve() == SAT ? "SAT" : "UNSAT";
//
//            std::cout << r2 << std::endl;
//            solver->printModel();
//
//        }

        void apply() {
            bool fixpoint = false;
            int fixpoint_iteration = 1;

            auto global_start = std::chrono::high_resolution_clock::now();


            while (!fixpoint) {
                auto step_start = std::chrono::high_resolution_clock::now();
//                solver->deep_clean();

//                for (auto &&user :policy->unique_configurations()) {
//                    std::cout << "###  " << user->to_full_string() << std::endl;
//                }

                log->debug("Applying backward_slicing on {}", policy->rules().size());
                bool backward_slicing_res = this->backward_slicing();
                backward_slicing_res = reduce_roles() || backward_slicing_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                solver->deep_clean();

//                std::cout << *policy << std::endl;


                log->debug("Applying easy_pruning on {}", policy->rules().size());
                bool easy_pruning_res = this->easy_pruning();
                easy_pruning_res = reduce_roles() && easy_pruning_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                if (easy_pruning_res) {
                    // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                    backward_slicing();
                }
                solver->deep_clean();

                log->debug("Applying prune_immaterial_roles on {}", policy->rules().size());
                bool prune_immaterial_roles_res = this->prune_immaterial_roles_opt(); // this->prune_immaterial_roles();
                prune_immaterial_roles_res = reduce_roles() || prune_immaterial_roles_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                if (prune_immaterial_roles_res) {
                    // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                    backward_slicing();
                }
                solver->deep_clean();

                log->debug("Applying prune_irrelevant_roles on {}", policy->rules().size());
                bool prune_irrelevant_roles_res = this->prune_irrelevant_roles();
                prune_irrelevant_roles_res = reduce_roles() || prune_irrelevant_roles_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                if (prune_irrelevant_roles_res) {
                    // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                    backward_slicing();
                }
                solver->deep_clean();


                log->debug("Applying prune_implied_pairs on {}", policy->rules().size());
                bool prune_implied_pairs_res = this->prune_implied_pairs();
                prune_implied_pairs_res = reduce_roles() || prune_implied_pairs_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                if (prune_implied_pairs_res) {
                    // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                    backward_slicing();
                }
                solver->deep_clean();


                bool merge_rules_res = false;
                if (Config::merge) {
                    log->debug("Applying merge_rules on {}", policy->rules().size());
                    merge_rules_res = this->merge_rules();
                    merge_rules_res = reduce_roles() || merge_rules_res;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    if (merge_rules_res) {
                        // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                        backward_slicing();
                    }
                    solver->deep_clean();


                    bool simplify_expression_res = simplify_expressions();
                    merge_rules_res = merge_rules_res || simplify_expression_res;

                }

                log->debug("Applying prune_rule_6 on {}", policy->rules().size());
                bool prune_rule_6_res = this->prune_rule_6();
                prune_rule_6_res = reduce_roles() || prune_rule_6_res;
                log->debug(" ==> {} rules...", policy->rules().size());
                solver->deep_clean();


                fixpoint =
                        !(
                          backward_slicing_res       ||
                          easy_pruning_res           ||
                          prune_immaterial_roles_res ||
                          prune_irrelevant_roles_res ||
                          prune_implied_pairs_res    ||
                          merge_rules_res            ||
                          prune_rule_6_res
                          );

                log->debug("Iteration: {}", fixpoint_iteration++);
                auto step_end = std::chrono::high_resolution_clock::now();
                auto step_milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(step_end - step_start);
                log->debug(" done in {} ms.", step_milliseconds .count());
            }

            reduce_users();
            solver->deep_clean();

            std::cout << *policy;

            auto global_end = std::chrono::high_resolution_clock::now();
            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(global_end - global_start);
            log->debug("------------ Pruning done in {} ms. ------------", milliseconds.count());

        }

        Pruning(const std::shared_ptr<SMTFactory<TVar, TExpr>>& _solver,
                const std::shared_ptr<arbac_policy>& policy) :
            solver(_solver),
            policy(policy) { }
    };

    template <typename TVar, typename TExpr>
    void prune_policy(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                      const std::shared_ptr<arbac_policy>& policy) {

        Pruning<TVar, TExpr> core(solver, policy);

        core.apply();
    }

    template void prune_policy<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                               const std::shared_ptr<arbac_policy>& policy);
    template void prune_policy<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                           const std::shared_ptr<arbac_policy>& policy);
}
