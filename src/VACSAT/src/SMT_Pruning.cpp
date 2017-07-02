#include <vector>
#include <set>
#include <memory>
#include <string>
#include <chrono>
#include <iostream>
#include <utility>
#include <algorithm>

//#include "old_parser/ARBACExact.h"
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

        std::shared_ptr<arbac_policy> policy;

        bool with_tampone = false;

        /*bool set_contains(const Expr& expr, const std::string& name) {
            std::set<Literalp> literals = expr->literals();
            for (auto ite = literals.begin(); ite != literals.end(); ++ite) {
                Literalp e = *ite;
                if (e->name == name) {
                    return true;
                }
            }
            return false;
        }*/

        bool check_sat(const Expr& expr,
                       const std::set<Expr>& lookup2_exprs,
                       const std::string& suffix1,
                       const std::string& suffix2,
                       const rulep& rule) {
            std::vector<std::shared_ptr<TVar>> lookup1((ulong) policy->atom_count());
            std::vector<std::shared_ptr<TVar>> lookup2((ulong) policy->atom_count());
            if (!with_tampone) {
                solver->clean();
                TExpr solver_expr = generateSMTFunction2(solver, expr, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                solver->assertNow(solver_expr);
                return solver->solve() == SAT;
            } else {
                return !apply_r6<TVar, TExpr>(solver, policy, expr, lookup2_exprs, rule);
            }

            log->critical("Uh?");
            throw unexpected_error("Uh?");
        }

        bool have_common_atoms(const Expr& e1, const Expr& e2) {
            std::list<atomp> intersection;
            //TODO: sure is it correct?
            std::set_intersection(e1->atoms().begin(), e1->atoms().end(),
                                  e2->atoms().begin(), e2->atoms().end(),
                                  std::back_inserter(intersection), std::owner_less<Atomp>());
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
            std::set<Atomp> necessary_atoms;
            necessary_atoms.insert(policy->goal_role);
            while (!fixpoint) {
                fixpoint = true;
                for (auto &&rule : policy->rules()) {
//                    print_collection(necessary_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": "_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": " << (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) << std::endl;
                    if (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) {
//                        print_collection(rule->admin->literals());
//                        print_collection(rule->prec->literals());

                        necessary_atoms.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
                        necessary_atoms.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                        to_save.insert(rule);
                        fixpoint = false;
                    }
                }
            }

            std::list<rulep> to_remove;
            for (auto &&rule : policy->rules()) {
                if (!contains(to_save, rule)) {
                    to_remove.push_back(rule);
                    log->trace("{}", *rule);
                }
            }

            std::list<atomp> atoms_to_remove;
            for (auto &&atom : policy->atoms()) {
                if (!contains(necessary_atoms, atom)) {
                    atoms_to_remove.push_back(atom);
                    log->trace("{}", *atom);
                }
            }

            policy->remove_rules(to_remove);
            policy->remove_atoms(atoms_to_remove);

            return to_remove.size() > 0;
        }

        /* PRELIMINARY SIMPLE PRUNING (REMOVING ATOMS NOT USED IN ANY CONDITION,
         *                             CAN_ASSIGN OF NON POSITIVE ATOMS,
         *                             CAN_REVOKE OF NON NEGATIVE ATOMS AND OF GOAL ATOM) */
        bool atom_is_used_as(const atomp& atom, const std::list<Expr>& using_a, int wanted_value) {
            if (atom->bv_size != 1) {
                log->error("UNSUPPORTED: Atom {} has bitvector size greater than 1. UNSUPPORTED", *atom);
                throw std::runtime_error("UNSUPPORTED: Atom " + atom->fullName() + " has bitvector size greater than 1. UNSUPPORTED");
            }
            for (auto &&expr : using_a) {
                //FIXME: add support for tampone
                solver->clean();
                // (declare-const tracked_true_atom Bool)
                TVar wanted_var = solver->createBoolVar("tracked_true_" + atom->fullName());
                // (declare-const tracked_false_atom Bool)
                TVar unwanted_var = solver->createBoolVar("tracked_false_" + atom->fullName());
                //FUTURE: when values other than booleans will be supported change solver->createTrue() to (solver->createBVConst(value))
                TExpr solver_want_value = wanted_value ? solver->createTrue() : solver->createFalse();
                // tracked_true_atom == value
                TExpr wanted_eq = solver->createEqExpr(wanted_var, solver_want_value);
                // tracked_false_atom != value
                TExpr unwanted_eq = solver->createNotExpr(solver->createEqExpr(unwanted_var, solver_want_value));
                std::vector<std::shared_ptr<TVar>> var_vect((unsigned long) policy->atom_count());

                // Phi_r_wanted(C)

                var_vect[atom->role_array_index] = std::make_shared<TExpr>(wanted_var);
                TExpr phi_a_true = generateSMTFunction(solver, expr, var_vect, "C");

                // Phi_r_unwanted(C)
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(unwanted_var);
                TExpr phi_a_false = generateSMTFunction(solver, expr, var_vect, "C");


                // Phi_r_true(C) /\ not Phi_r_false(C)
                TExpr to_check = solver->createAndExpr(phi_a_true,
                                                       solver->createNotExpr(phi_a_false));

//                TExpr solver_final_expr = solver->createAndExpr(to_check,
//                                                                solver->createAndExpr(wanted_eq,
//                                                                                      unwanted_eq));

//                solver->assertNow(solver_final_expr);
                solver->assertNow(to_check);
                solver->assertNow(wanted_eq);
                solver->assertNow(unwanted_eq);
                bool expr_is_counterexample = solver->solve() == SAT;
                if (expr_is_counterexample) {
                    return true;
                }
            }
            return false;
        }

        /*AtomStatus get_atom_status(const atom& atom) {
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

        }*/

        bool atom_used_as_value(const atomp& atom, int value, std::vector<std::shared_ptr<atom_status>>& cache) {
            std::shared_ptr<atom_status>& cache_value = cache[atom->role_array_index];
            if (cache_value->get_status(value) != atom_status::UNKNOWN) {
                // ALREADY IN CACHE
                return cache_value->get_status(value) == atom_status::USED;
            }
            std::list<Expr> using_a;
            for (auto &&rule : policy->rules()) {
                if (contains(rule->admin->atoms(), atom)) {
                    using_a.push_back(rule->admin);
                }
                if (contains(rule->prec->atoms(), atom)) {
                    using_a.push_back(rule->prec);
                }
            }
            if (using_a.size() <= 0) {
                cache_value->set_unused();
                return cache_value->get_status(value);
            }
            auto result = atom_is_used_as(atom, using_a, value) ? atom_status::USED : atom_status::UNUSED;
            cache_value->set_value(value, result);
            return result == atom_status::USED;
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
            std::list<atomp> not_used_atoms;
            std::list<rulep> rules_to_remove;
            std::vector<std::shared_ptr<atom_status>> atom_statuses = atom_status::create(policy);
            for (auto &&atom : policy->atoms()) {
                bool used = false;
                for (auto &&rule : policy->rules()) {
                    if (contains(rule->admin->atoms(), atom) ||
                        contains(rule->prec->atoms(), atom)) {
                        used = true;
                        break;
                    }
                }
                if (!used && atom != policy->goal_role) {
                    not_used_atoms.push_back(atom);
                    log->trace("Atom: {} is never used. Removing it!", *atom);
                } else if (atom == policy->goal_role) {
                    for (auto &&cr : policy->can_revoke_rules()) {
                        if (cr->target == atom) {
                            rules_to_remove.push_back(cr);
                            log->trace("\t{}", *cr);
                        }
                    }
                    log->trace("Atom {} is the GOAL_ROLE. Removing can_revoke_rules targeting it!", *atom);
                } else {
//                    if (policy->per_role_can_assign_rule(atom).size() == 0 &&
//                            policy->per_role_can_revoke_rule(atom).size() == 0) {
////                        std::cout << "Atom: " << *atom << " is NEVER ASSIGNED/REVOKED. Do not compute status!" << std::endl;
//                        continue;
//                    }
                    if (forall_user([&](const userp &user) { return !contains(user->config(), atom); })) {
//                        log->trace("Atom {}: no user has it", *atom);
                        if (!atom_used_as_value(atom, true, atom_statuses)) {
                            log->trace("Atom {} is NEVER used POSITIVELY and no users have it. Remove it!", *atom);
                            not_used_atoms.push_back(atom);
                            continue;
                        }
                    }
                    if (forall_user([&](const userp &user) { return contains(user->config(), atom); })) {
//                        log->trace("Atom {}: all users have it", *atom);
                        if (!atom_used_as_value(atom, false, atom_statuses)) {
                            log->trace("Atom {} is NEVER used NEGATIVELY and all users have it. Remove it!", *atom);
                            not_used_atoms.push_back(atom);
                            continue;
                        }
                    }
                    if (policy->per_role_can_assign_rule(atom).size() > 0) {
                        //CAN ASSIGN IT. CHECK IF NEVER POSITIVE (REMOVE CA)
                        if (!atom_used_as_value(atom, true, atom_statuses)) {
                            log->trace("Atom {} is NEVER used POSITIVELY. Removing can_assign_rules targeting it!",
                                       *atom);

                            auto to_remove = policy->per_role_can_assign_rule(atom);
                            for (auto &&r : to_remove) {
                                log->trace("{}", *r);
                            }
                            rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
                        }
                    }
                    if (policy->per_role_can_revoke_rule(atom).size() > 0) {
                        //CAN REVOKE IT. CHECK IF NEVER NEGATIVE (REMOVE CR)
                        if (!atom_used_as_value(atom, false, atom_statuses)) {
                            log->trace("Atom {} is NEVER used NEGATIVELY. Removing can_revoke_rules targeting it!",
                                       *atom);

                            auto to_remove = policy->per_role_can_revoke_rule(atom);
                            for (auto &&r : to_remove) {
                                log->trace("{}", *r);
                            }
                            rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
                        }
                    }
                    /* else {
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
    //                            for (auto &&cr : policy->can_revoke_rules()) {
    //                                if (cr->target == atom) {
    //                                    rules_to_remove.push_back(cr);
    //                                    std::cout << "\t" << *cr << std::endl;
    //                                }
    //                            }
                                auto to_remove = policy->per_role_can_revoke_rule(atom);
                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
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
    //                            for (auto &&ca : policy->can_assign_rules()) {
    //                                if (ca->target == atom) {
    //                                    rules_to_remove.push_back(ca);
    //                                    std::cout << "\t" << *ca << std::endl;
    //                                }
    //                            }
                                auto to_remove = policy->per_role_can_assign_rule(atom);
                                rules_to_remove.insert(rules_to_remove.end(), to_remove.begin(), to_remove.end());
                                break;
                            }
                            default:
                                break;
                        }*/
                }
            }

            policy->remove_atoms(not_used_atoms);
            policy->remove_rules(rules_to_remove);

            return (not_used_atoms.size() > 0) ||
                   (rules_to_remove.size() > 0);

        }

        bool false_condition(const rulep& rule) {
            //FIXME: add support for tampone
            // CHECK IF BOTH ADMIN CONDITION AND CONDITION ARE SATISFIABLE
            solver->clean();

            std::vector<std::shared_ptr<TVar>> adm_vect((unsigned int) policy->atom_count());
            std::vector<std::shared_ptr<TVar>> prec_vect((unsigned int) policy->atom_count());

            Expr joined = createAndExpr(rule->admin, rule->prec);
            std::set<Expr> part2;
            part2.insert(rule->prec);

//            TExpr solver_adm = generateSMTFunction2(solver, rule->admin, adm_vect, "adm");
//            TExpr solver_prec = generateSMTFunction2(solver, rule->prec, prec_vect, "prec");
//            TExpr check = solver->createAndExpr(solver_adm, solver_prec);

            TExpr solver_joined = generateSMTFunction2(solver, joined, part2, adm_vect, prec_vect, "adm", "prec");

            solver->assertNow(solver_joined);
            SMTResult res = solver->solve();

            return res != SAT;
        }

        bool true_condition(const Expr& expr) {
            //FIXME: tampone
            // CHECK IF AN EXPRESSION IS ALWAYS TRUE
            solver->clean();

//            std::vector<std::shared_ptr<TVar>> var_vect((unsigned int) policy->atom_count());
//            TExpr solver_expr = generateSMTFunction(solver, expr, var_vect, "C");

//            TExpr check = solver->createNotExpr(solver_expr);
//            solver->assertNow(check);
//            SMTResult res = solver->solve();

            std::set<Expr> empty;
            bool sat = check_sat(expr, empty, "C", "", nullptr);
            return !sat;
        }

        bool easy_pruning_rule_condition() {
            std::list<rulep> false_to_remove;
            bool has_changed = false;
            for (auto &&rule :policy->rules()) {
                if (false_condition(rule)) {
                    has_changed = true;
                    log->trace("Rule {} is never satisfiable. Remove it.", *rule);
                    false_to_remove.push_back(rule);
                }
                else {
                    if (!is_constant_true(rule->admin) && true_condition(rule->admin)) {
                        has_changed = true;
                        log->trace("Administrative condition of rule {} is always TRUE...", *rule);
                        rule->admin = createConstantTrue();
                    }
                    if (!is_constant_true(rule->prec) && true_condition(rule->prec)) {
                        has_changed = true;
                        log->trace("Condition of rule {} is always TRUE...", *rule);
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
        //TODO: remove this one
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
            TExpr solver_adm = generateSMTFunction(solver, adm, adm_var_vec, std::string("adm"));

            for (auto &&expr : other_exprs) {

                if (!have_common_atoms(adm, expr)) {
                    //FIXME: to decide if leave like this (could remove too fiew e.g. (true || !ra))
                    // can go forward since atoms are disjoint
                    continue;
                }

                solver->clean();

                std::vector<std::shared_ptr<TVar>> free_var_vec((unsigned long) policy->atom_count());
                TExpr solver_exp = generateSMTFunction(solver, expr, free_var_vec, std::string("adm"));

                std::vector<std::shared_ptr<TVar>> updated_vec = update_tlookup(free_var_vec, adm_var_vec);

                TExpr not_solver_exp = solver->createNotExpr(generateSMTFunction(solver, expr, updated_vec, std::string("adm")));

                solver->assertNow(solver_adm);
                solver->assertNow(solver_exp);
                solver->assertNow(not_solver_exp);

                bool res = solver->solve() == UNSAT;

                if (!res) {
//                    solver->printModel();
                    log->trace("{} administrative part interfere with {}", *adm, *expr);
                    return false;
                }
            }

            return true;
        }

        bool satisfies_using_set(const Expr& adm, const userp& user, std::vector<std::shared_ptr<atom_status>>& _atom_status) {
            auto lits = adm->atoms();
            for (auto &&atom : adm->atoms()) {
                std::vector<std::shared_ptr<TExpr>> var_vect((ulong) policy->atom_count());
//                std::shared_ptr<atom_status>& status = _atom_status[lit->role_array_index];
                if (contains(user->config(), atom) && !atom_used_as_value(atom, false, _atom_status)) {
                    var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createTrue());
                } else if (!contains(user->config(), atom) && !atom_used_as_value(atom, true, _atom_status)) {
                    var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createFalse());
                }

                solver->clean();
                TExpr inner_expr = generateSMTFunction(solver, adm, var_vect, "C");
                TExpr solver_expr = solver->createNotExpr(inner_expr);
                solver->assertNow(solver_expr);

                SMTResult res = solver->solve();

                if (res == UNSAT) {
                    log->trace("User {} satisfies formula {} without interference", user->to_full_string(), *adm);
                    return true;
                }
            }
            return false;
        }

        bool immaterial_not_interfere_new(const Expr& adm, std::vector<std::shared_ptr<atom_status>>& _atom_status) {
            for (auto &&conf : policy->unique_configurations()) {
                bool sat = satisfies_using_set(adm, conf, _atom_status);
                if (sat)
                    return true;
            }
            return false;
        }

        bool immaterial_get_k_plus_two(const userp& target_user, const Expr& adm, int k) {
            if (target_user->infinite) {
                log->trace("User {} satisfies administrative formula {} and there are infinite copy of her!",
                           target_user->to_full_string(), *adm);
                log->trace("\tRequired were {} (k = {}). (Remove  k + 2)", k + 2, k);
                return true;
            }
            std::set<atomp> conf = target_user->config();
            int i = 0;
            for (auto &&_user : policy->users()) {
                if (_user->config() == conf) {
                    if (_user->infinite) {
                        log->trace("User {} satisfies administrative formula {} and there are infinite copy of her!",
                                   _user->to_full_string(), *adm);
                        log->trace("\tRequired were {} (k = {}). (Remove  k + 2)", k + 2, k);
                        return true;
                    }
                    i++;
                }
            }

            bool res = i >= (k + 2);

            if (res) {
//                log->warn(policy->to_string());
                log->trace("User {} satisfies administrative formula {} and there are {} copy of her!",
                            target_user->to_full_string(), *adm, i);
                log->trace("\tRequired were {} (k = {}). (Remove  k + 2)", k + 2, k);
            }

            return res;
//            return i > policy->users_to_track();
        }

        bool immaterial_admin_in_prec(const rulep& rule) {
            // This rule checks if adm is implied in prec. If so we can remove the admin part and replace with TRUE since the check is done on
            solver->clean();
            std::vector<std::shared_ptr<TVar>> var_vect((ulong) policy->atom_count());

            TExpr s_adm = generateSMTFunction(solver, rule->admin, var_vect, "C");

            TExpr s_prec = generateSMTFunction(solver, rule->prec, var_vect, "C");

            TExpr to_check = solver->createAndExpr(solver->createNotExpr(s_adm),
                                                   s_prec);

            solver->assertNow(to_check);

            SMTResult res = solver->solve();

            return res == UNSAT;
        }

        bool immaterial_adm_k_plus_two(const Expr& adm) {
            bool exists_user = false;
            //exists a user that satisfies phi_adm
            for (auto &&user : policy->unique_configurations()) {
                solver->clean();

                Expr adm_expr = adm;
                Expr user_expr = policy->user_to_expr(user->original_idx, adm->atoms());

                std::vector<std::shared_ptr<TVar>> var_vect((ulong) policy->atom_count());

                TExpr solver_adm_expr = generateSMTFunction(solver, adm_expr, var_vect, user->name);
                TExpr solver_user_expr = generateSMTFunction(solver, user_expr, var_vect, user->name);

                solver->assertNow(solver_user_expr);
                solver->assertNow(solver_adm_expr);

                bool satisfies = solver->solve() == SAT;

                if (satisfies) {
                    int _admin_count = policy->admin_count();
                    bool cover_it = immaterial_get_k_plus_two(user, adm, _admin_count);
                    if (cover_it) {
                        return true;
                    }
                }
            }

            return false;
        }

        bool prune_immaterial_roles_opt() {
            std::map<Expr, std::list<rulep>, deepCmpExprs> admins;
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

//            log->warn("dim: {}", admins.size());
//            for (auto ite = admins.begin(); ite != admins.end(); ++ite) {
//                log->warn("mah...: {}", *ite->first);
//                log->warn("mah...: {}", ite->second.size());
//            }
//            std::cout << admins.size() << std::endl;
            std::vector<std::shared_ptr<atom_status>> statuses = atom_status::create(policy);
            for (auto &&adm_pair : admins) {
                if (is_constant_true(adm_pair.first)) {
                    // Do nothing if the administrative expression is the True constant
                    continue;
                }
                bool has_admin = immaterial_adm_k_plus_two(adm_pair.first) || immaterial_not_interfere_new(adm_pair.first, statuses);
//                for (auto &&status : statuses) {
//                    log->warn("{}", *status);
//                }
                if (has_admin) {
                    log->trace("Administrative expression {} IS IMMATERIAL", *adm_pair.first);
                    has_changed = true;
                    for (auto &&rule : adm_pair.second) {
                        rule->admin = createConstantTrue();
                    }
                }
            }
            return has_changed;
        }

        /*bool prune_immaterial_roles() {
            //std::map<Expr, std::list<rulep>> admins;
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
               //admins[rule->admin].push_back(rule);
            }
            return has_changed;
        }*/

        /* IRRELEVANT ROLES FUNCTIONS */
        std::pair<Expr, std::set<Expr>> irr_mix_cond_one(const Atomp& role,
                               const std::shared_ptr<rule>& using_r,
                               const std::list<std::shared_ptr<rule>>& assigning_r,
                               const std::list<std::shared_ptr<rule>>& removing_r) {
            //TODO: ADD IRRELEVANT FOR ADMIN HERE

//            std::vector<std::shared_ptr<TVar>> c_vect(policy->atom_count());
//            std::vector<std::shared_ptr<TVar>> adm_vect(policy->atom_count());

            Literalp role_lit = createLiteralp(role);

            std::set<Expr> on_adm;

            // C_r
            Expr c_r = role_lit;
            // not C_r
            Expr not_c_r = createNotExpr(role_lit);

            // phi_r^TRUE(C)
//            role->setValue(createConstantTrue());
            Expr phi_r_true_c = clone_substitute(using_r->prec, role_lit, createConstantTrue());

            // phi_r^FALSE(C)
//            role->setValue(createConstantFalse());
            Expr phi_r_false_c = clone_substitute(using_r->prec, role_lit, createConstantFalse());


            //phi_a_(adm)
            Expr phi_a_adm = using_r->admin;
            on_adm.insert(phi_a_adm);

            // phi_r^TRUE(C) /\ not phi_r^FALSE(C) /\ phi_a_(adm)
            Expr pos_lhs = createAndExpr(createAndExpr(phi_r_true_c,
                                                       createNotExpr(phi_r_false_c)),
                                         phi_a_adm);

            // not phi_r^TRUE(C) /\ phi_r^FALSE(C) /\ phi_a_(adm)
            Expr neg_lhs = createAndExpr(createAndExpr(createNotExpr(phi_r_true_c),
                                                       phi_r_false_c),
                                         phi_a_adm);

            std::list<Expr> assign_and_rhs;

//            log->warn("role: {}", *role);
//            log->warn("pos_lhs: {}", *pos_lhs);
//            log->warn("neg_lhs: {}", *neg_lhs);

            for (auto &&ca : assigning_r) {
//                std::vector<std::shared_ptr<TVar>> c1_vect = c_vect;
//                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                Expr phi1_c = ca->prec;

                //phi'_a(adm)
                Expr phi1_a_adm = clone_but_lits(ca->admin);
                on_adm.insert(phi1_a_adm);

                //phi'_a(C)
                Expr phi1_a_c = ca->admin;

                // not (phi'(C)) \/ not (phi'_a(adm) \/ phi'_a(C))
                Expr disj = createOrExpr(createNotExpr(phi1_c),
                                         createNotExpr(createOrExpr(phi1_a_adm,
                                                                    phi1_a_c)));

                assign_and_rhs.push_back(disj);
//                log->warn("assign: {}", *ca);
//                log->warn("cond: {}", *disj);
            }

            Expr assign_bigand = joinBigAnd(assign_and_rhs);


            std::list<Expr> revoke_and_rhs;

            for (auto &&cr  : removing_r) {
//                std::vector<std::shared_ptr<TVar>> c1_vect = c_vect;
//                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                Expr phi1_c = cr->prec;

                //phi'_a(adm)
                Expr phi1_a_adm = cr->admin;
                on_adm.insert(phi1_a_adm);

                //phi'_a(C)
                Expr phi1_a_c = cr->admin;

                // not (phi'(C)) \/ not (phi'_a(adm) \/ phi'_a(C))
                Expr disj = createOrExpr(createNotExpr(phi1_c),
                                         createNotExpr(createOrExpr(phi1_a_adm,
                                                                    phi1_a_c)));

                revoke_and_rhs.push_back(disj);
            }

            Expr revoke_bigand = joinBigAnd(revoke_and_rhs);

            Expr pos_ca = createAndExpr(not_c_r,
                                        createAndExpr(pos_lhs,
                                                      assign_bigand));

            Expr neg_ca = createAndExpr(c_r,
                                        createAndExpr(neg_lhs,
                                                      revoke_bigand));

            Expr res = createOrExpr(pos_ca, neg_ca);

            return std::pair<Expr, std::set<Expr>>(res, on_adm);
        }

        Expr irr_mix_adm_one(const Atomp& role,
                             const std::shared_ptr<rule>& using_r,
                             const std::list<std::shared_ptr<rule>>& assigning_r,
                             const std::list<std::shared_ptr<rule>>& removing_r) {

//            std::vector<std::shared_ptr<TVar>> adm_vect(policy->atom_count());

            Literalp role_lit = createLiteralp(role);

            // Adm_r
            Expr adm_r = role_lit;
            // not Adm_r
            Expr not_adm_r = createNotExpr(role_lit);

            // phi_a_r^TRUE(Adm)
//            role->setValue(createConstantTrue());
            Expr phi_a_r_true_adm = clone_substitute(using_r->admin, role_lit, createConstantTrue());

            // phi_a_r^FALSE(Adm)
//            role->setValue(createConstantFalse());
            Expr phi_a_r_false_adm = clone_substitute(using_r->admin, role_lit, createConstantFalse());

//            role->resetValue();

            // phi_a_r^TRUE(Adm) /\ not phi_a_r^FALSE(Adm)
            Expr pos_lhs = createAndExpr(phi_a_r_true_adm,
                                         createNotExpr(phi_a_r_false_adm));

            // not phi_a_r^TRUE(Adm) /\ phi_a_r^FALSE(Adm)
            Expr neg_lhs = createAndExpr(createNotExpr(phi_a_r_true_adm),
                                         phi_a_r_false_adm);

            std::list<Expr> assign_and_rhs;

            for (auto &&ca : assigning_r) {
//                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(C)
                Expr phi1_adm = ca->prec;

                //phi'_a(adm)
                Expr phi1_a_adm = ca->admin;

                // not (phi'(adm)) \/ not phi'_a(adm))
                Expr disj = createOrExpr(createNotExpr(phi1_adm),
                                         createNotExpr(phi1_a_adm));

                assign_and_rhs.push_back(disj);
            }

            Expr assign_bigand = joinBigAnd(assign_and_rhs);


            std::list<Expr> revoke_and_rhs;

            for (auto &&cr  : removing_r) {
//                std::vector<std::shared_ptr<TVar>> adm1_vect = adm_vect;

                //phi'(adm)
                Expr phi1_adm = cr->prec;

                //phi'_a(adm)
                Expr phi1_a_adm = cr->admin;

                // not (phi'(C)) \/ not phi'_a(adm))
                Expr disj = createOrExpr(createNotExpr(phi1_adm),
                                         createNotExpr(phi1_a_adm));

                revoke_and_rhs.push_back(disj);
            }

            Expr revoke_bigand = joinBigAnd(revoke_and_rhs);

            Expr pos_ca = createAndExpr(not_adm_r,
                                        createAndExpr(pos_lhs,
                                                      assign_bigand));

            Expr neg_ca = createAndExpr(adm_r,
                                        createAndExpr(neg_lhs,
                                                      revoke_bigand));

            Expr res = createOrExpr(pos_ca, neg_ca);

            return res;
        }

        bool irrelevantRole(const Atomp& role) {
            if (role == policy->goal_role) {
//                std::cout << "Role " << role->fullName() << " is TARGET" << std::endl;
                return false;
            }

            std::list<rulep> admin_using_r;
            std::list<rulep> using_r;
            std::list<rulep> assigning_r;
            std::list<rulep> removing_r;
            for (auto &&ca : policy->can_assign_rules()) {
                if (contains(ca->admin->atoms(), role)) {
                    admin_using_r.push_back(ca);
                }
                if (contains(ca->prec->atoms(), role)) {
                    using_r.push_back(ca);
                }
                if (ca->target == role) {
                    assigning_r.push_back(ca);
                }
            }
            for (auto &&cr : policy->can_revoke_rules()) {
                if (contains(cr->admin->atoms(), role)) {
                    admin_using_r.push_back(cr);
                }
                if (contains(cr->prec->atoms(), role)) {
                    using_r.push_back(cr);
                }
                if (cr->target == role) {
                    removing_r.push_back(cr);
                }
            }

            if (using_r.size() == 0 && admin_using_r.size() == 0) {
//                printf("Role %s is never used. Remove it\n", role->to_string().c_str());
                return true;
            }
            else {
                bool can_remove = true;
                for (auto &&r_using_r : using_r) {
                    solver->clean();
                    auto cond_pair = irr_mix_cond_one(role,
                                                      r_using_r,
                                                      assigning_r,
                                                      removing_r);

                    std::vector<std::shared_ptr<TVar>> c_vect((ulong) policy->atom_count());
                    std::vector<std::shared_ptr<TVar>> adm_vect((ulong) policy->atom_count());
                    TExpr solver_cond = generateSMTFunction2(solver,
                                                             cond_pair.first,
                                                             cond_pair.second,
                                                             c_vect,
                                                             adm_vect,
                                                             "C", "Adm");

//                    log->warn("{}", *cond_pair.first);
//                    for (auto &&expr : cond_pair.second) {
//                        log->warn("on_adm: {}", *expr);
//                    }
//                    solver->printExpr(solver_cond);
                    solver->assertNow(solver_cond);

                    SMTResult res = solver->solve();

                    if (res == SAT) {
                        can_remove = false;
                        return false;
                        break;
                    }

                }

                for (auto &&adm_using_r : admin_using_r) {
                    solver->clean();
                    Expr cond = irr_mix_adm_one(role,
                                                 adm_using_r,
                                                 assigning_r,
                                                 removing_r);

                    std::vector<std::shared_ptr<TVar>> adm_vect((ulong) policy->atom_count());
                    TExpr solver_cond = generateSMTFunction(solver, cond, adm_vect, "Adm");
                    solver->assertNow(solver_cond);

                    SMTResult res = solver->solve();

                    if (res == SAT) {
                        can_remove = false;
                        return false;
                        break;
                    }

                }
//                std::cout << "role: " << *role << (can_remove ? " Can" : " Cannot") << " be removed" << std::endl;

                return true;
                return can_remove;
            }

        }

        bool prune_irrelevant_roles() {
            std::list<Atomp> irrelevant;

            for (auto &&r : policy->atoms()) {
                bool can_remove = irrelevantRole(r);
                if (can_remove) {
                    log->trace("{} is irrelevant.", *r);
                    irrelevant.push_back(r);
                }
            }

            // REMOVAL:
            policy->remove_atoms(irrelevant);
            return irrelevant.size() > 0;
        }

        /* IMPLIED RULE FUNCTIONS */
        int implied(const std::shared_ptr<rule>& ca1, const std::shared_ptr<rule>& ca2) {
            //FIXME: tampone
            std::vector<std::shared_ptr<TVar>> c_vect((ulong) policy->atom_count());
            std::vector<std::shared_ptr<TVar>> adm_vect((ulong) policy->atom_count());
            std::string c_suff("C");
            std::string adm_suff("admin");

            std::set<Expr> on_admin;

//            solver->clean();

            Expr phi1_adm = ca1->admin;
            Expr phi2_adm = ca2->admin;

            // For performances improvement we test admin first and then the precondition
            // // \phi_a(adm) /\ \not \phi'_a(adm)
            Expr adm_cond = createAndExpr(phi2_adm,
                                          createNotExpr(phi1_adm));
            on_admin.insert(adm_cond);

//            solver->assertNow(adm_cond);
//            SMTResult adm_res = solver->solve();
//
//            if (adm_res == SAT) {
//                return false;
//            }
//            std::cout << "Admin, impl: " << *ca1->admin << " ==> " << *ca2->admin << std::endl;

//            std::cout << *ca1 << std::endl;
//            std::cout << *ca2 << std::endl;
//            solver->clean();

            Expr phi1_pn = ca1->prec;
            Expr phi2_pn = ca2->prec;
            // \phi(C) /\ \not \phi'(C)
            Expr cond = createAndExpr(phi2_pn,
                                      createNotExpr(phi1_pn));

//            solver->assertNow(cond);
//            SMTResult cond_res = solver->solve();

//            std::cout << "Prec, impl: " << *ca1->prec << " ==> " << *ca2->prec << ": " << (cond_res == SAT ? "SAT" : "UNSAT") << std::endl;
//            solver->printExpr(cond);

            Expr final_cond = createOrExpr(adm_cond, cond);

            bool sat = check_sat(final_cond, on_admin, "C", "Adm", nullptr);


            return !sat;




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
                                log->trace("Implied: {} ==>", *ca1);
                                log->trace("         {}", *ca2);
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
                                log->trace("Implied: {} ==>", *cr1);
                                log->trace("         {}", *cr2);
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
            //FIXME: tampone

            solver->clean();

            std::vector<std::shared_ptr<TVar>> var_vec((ulong) policy->atom_count());
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

//            if (res) {
//                std::cout << "Expressions " << *e1 << std::endl;
//                std::cout << "            " << *e2 << std::endl;
//                std::cout << "            are equivalent!" << *e1 << std::endl;
//            }

            return res;

//            }
        }

        const std::list<std::list<rulep>> partition_equivalent(const atomp& target, const std::list<rulep>& targetings) {
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

            std::map<Atomp, std::list<rulep>> assigning;
            std::map<Atomp, std::list<rulep>> revoking;
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
                            log->trace("\t{}", *rule);
                        }
                        log->trace("To:");
                        log->trace("\t{}", *new_rule);
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
                            log->trace("\t{}", *rule);
                        }
                        log->trace("To:");
                        log->trace("\t{}", *new_rule);
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
        enum interactive_split_result {
            REMOVE,
            SIMPLIFIED,
            UNCHANGED
        };

        /*std::list<OrExprp> get_or_list(Expr& expr, const std::set<ulong64>& visited, int max_level) {
            std::list<std::pair<int, OrExprp>> ors = get_or_expressions(expr, 1);
            std::list<OrExprp> res;
            for (auto &&pair : ors) {
                if (max_level >= 0 &&
                    pair.first > max_level) {
                    continue;
                }
                OrExprp _or = pair.second;
                if (!contains(visited, _or->node_idx)) {
                    res.push_back(_or);
                }
            }
            return res;
        };

        interactive_split_result interactive_split(const Expr& expr, const rulep& rule, bool admin) {
            int max_depth = Config::rule_6_max_depth;
            bool changed = false;
            Expr orig = expr;
            if (apply_r6<TVar, TExpr>(this->solver, this->policy, orig, rule)) {
                return REMOVE;
            }

            Expr rolling = clone_but_lits(orig);

            std::set<ulong64> visited;

            std::list<OrExprp> ors = get_or_list(rolling, visited, max_depth);

            while (ors.size() > 0) {
                auto _or = *ors.begin();
                visited.insert(_or->node_idx);

//                log->trace("Expr: {}", *rolling);
//                log->trace("{}", *_or);

                Expr old_r = _or->rhs;
                _or->rhs = createConstantFalse();
//                log->trace("testing: {}", *_or);
                if (apply_r6<TVar, TExpr>(this->solver, this->policy, rolling, rule)) {
                    _or->lhs = createConstantFalse();
                    _or->rhs = old_r;
                    changed = true;
                } else {
                    _or->rhs = old_r;
                }

                Expr old_l = _or->lhs;
                _or->lhs = createConstantFalse();
//                log->trace("testing: {}", *_or);
                if (apply_r6<TVar, TExpr>(this->solver, this->policy, rolling, rule)) {
                    _or->rhs = createConstantFalse();
                    _or->lhs = old_l;
                    changed = true;
                } else {
                    _or->lhs = old_l;
                }

                ors = get_or_list(rolling, visited, max_depth);
            }
            if (changed) {
//                log->trace("Expression is changed!");
//                log->trace("{}", *simplifyExpr(rolling));
//                log->trace("{}", *simplifyExpr(orig));
                rolling = simplifyExpr(rolling);
                if (admin) {
                    rule->admin = rolling;
                } else {
                    rule->prec = rolling;
                }
            } else {
//                log->trace("Expression is not changed!");
            }
//            log->trace("done!");
            return changed ? SIMPLIFIED : UNCHANGED;
        }*/

        std::list<OrExprp> get_proper_or_list(Expr& expr, const std::set<ulong64>& visited, int max_level) {
            std::list<std::pair<int, OrExprp>> ors = get_proper_or_expressions_sorted(expr, max_level, 1);
            std::list<OrExprp> res;
            for (auto &&pair : ors) {
                if (max_level >= 0 &&
                    pair.first > max_level) {
                    continue;
                }
                OrExprp _or = pair.second;
                if (!contains(visited, _or->node_idx)) {
                    res.push_back(_or);
                }
            }
            return res;
        };


//        bool check_sat(const Expr &expr) const {
//            solver->clean();
//            std::vector<std::shared_ptr<TVar>> var_vect((ulong) policy->atom_count());
//            TExpr solver_expr = generateSMTFunction(solver, expr, var_vect, "C");
//            solver->assertNow(solver_expr);
//            return solver->solve() != SAT;
//        }

//        bool always_false(const Expr& expr, const rulep& rule) {
//            if (with_tampone) {
//                return apply_r6<TVar, TExpr>(solver, policy, expr, rule);
//            } else {
//                return check_sat(expr);
//            }
//        }

        bool try_simplify(const Expr& expr, OrExprp _or, bool left, const rulep& rule) {
            Expr final;
            Expr copy = clone_but_lits(expr);
            Expr removed;
            if (left) {
                removed = _or->lhs;
                _or->lhs = createConstantFalse();
            } else {
                removed = _or->rhs;
                _or->rhs = createConstantFalse();
            }
//            log->info("");
//            log->info("expr: {}", *expr);
//            log->info("copy: {}", *copy);

            final = createAndExpr(createNotExpr(expr),
                                  copy);
//            log->info("final: {}", *final);

//            bool res = apply_r6<TVar, TExpr>(this->solver, this->policy, final, rule);
            std::set<Expr> empty;
            bool res = !check_sat(final, empty, "", "", rule);

//            log->info("remove: {}", res);

            if (!res) {
                if (left) {
                    _or->lhs = removed;
                } else {
                    _or->rhs = removed;
                }
            }

            return res;
        }

        interactive_split_result apply_remove_simplify(Expr& expr, const rulep& rule, bool admin) {
            // IF RULE IS NEVER FIREABLE THAN REMOVE IT!
//            if (apply_r6<TVar, TExpr>(this->solver, this->policy, expr, rule)) {
            std::set<Expr> empty;
            if (!check_sat(expr, empty, "", "", rule)) {
                return REMOVE;
            }

            bool changed = false;
            std::set<ulong64> visited;
            Expr actual = clone_but_lits(expr);
            std::list<OrExprp> ors = get_proper_or_list(actual, visited, Config::rule_6_max_depth);
            while (ors.size() > 0) {
                OrExprp to_analyze = *ors.begin();
                visited.insert(to_analyze->node_idx);
                bool can_remove_left = try_simplify(actual, to_analyze, true, rule);
                bool can_remove_right = try_simplify(actual, to_analyze, false, rule);
                if (can_remove_left || can_remove_right) {
                    changed = true;
                }
                ors = get_proper_or_list(actual, visited, Config::rule_6_max_depth);
            }

            if (changed) {
                if (admin) {
                    rule->admin = actual;
                } else {
                    rule->prec = actual;
                }
            }

            return changed ? SIMPLIFIED : UNCHANGED;
        }

        bool simplyfy_remove_false() {
            std::list<std::shared_ptr<rule>> to_remove;
            bool changed = false;
            bool do_log = false;

            for (auto &&rule : policy->rules()) {
//                if (rule->target->name.compare(0, 7, "anyfour") == 0) {
//                    std::cout << *rule << std::endl;
//                }
                if (do_log) {
                    log->trace("{}", *rule);
                }

                solver->clean();
                interactive_split_result rem_pn = apply_remove_simplify(rule->prec, rule, false); // interactive_split(rule->prec, rule, false); //apply_r6<TVar, TExpr>(this->solver, this->policy, rule->prec, rule);
                if (do_log) {
                    log->trace("{}", *rule);
                }
                solver->clean();
                interactive_split_result rem_adm =
                        rem_pn == REMOVE ? UNCHANGED
                                         : apply_remove_simplify(rule->admin, rule, true); // interactive_split(rule->admin, rule, true);
                if (do_log) {
                    log->trace("{}", *rule);
                }
                            ; // apply_r6<TVar, TExpr>(this->solver, this->policy, rule->admin, rule);

                //                std::cout << ca_adm_formulae[i]->to_string() << std::endl;

                //                if (!rem_pn && rem_adm)
                //                    solver->printContext();

                //                if (i == ca_index) {
                //                    solver->printContext();
                //                }


                if (rem_pn == REMOVE) {
                    //                    print_ca_comment(stdout, i);
                    //                    fprintf(stdout, "rule %d %s be removed since not fireable\n\n", i, res ? "CAN" : "CANNOT");
                    to_remove.push_back(rule);
                    changed = true;
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "X";
                        std::flush(std::cout);
                    }
                } else if (rem_adm == REMOVE) {
                    to_remove.push_back(rule);
                    changed = true;
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "O";
                        std::flush(std::cout);
                    }
                } else if (rem_pn == SIMPLIFIED || rem_adm == SIMPLIFIED) {
                    changed = true;
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "+";
                        std::flush(std::cout);
                    }
                } else {
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "-";
                        std::flush(std::cout);
                    }
                }
            }

            if (can_write(spdlog::level::trace)) {
                std::cout << std::endl;
            }

            for (auto &&rule :to_remove) {
//                policy->remove_rule(rule);
                log->trace("{}", *rule);
            }

            policy->remove_rules(to_remove);

//            std::cout << std::endl << "Removed " << to_remove.size() << " rules" << std::endl;

            return changed;

//            auto start = std::chrono::high_resolution_clock::now();
            // CODE
//            auto end = std::chrono::high_resolution_clock::now();
//            auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
//            std::cout << "------------ Rule6 executed in " << milliseconds.count() << " ms ------------\n";

        }

        /* SIMPLIFY EXPRESSIONS */
        std::list<atomp> get_irrelevant_atoms_in_expr(const Expr& expr) {
            std::list<atomp> to_remove;
            for (auto &&atom : expr->atoms()) {
                solver->clean();

                std::vector<std::shared_ptr<TExpr>> var_vect((ulong) policy->atom_count());

                //phi_a_true
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createTrue());
                TExpr phi_a_true = generateSMTFunction(solver, expr, var_vect, "C");

                //phi_a_false
                var_vect[atom->role_array_index] = std::make_shared<TExpr>(solver->createFalse());
                TExpr phi_a_false = generateSMTFunction(solver, expr, var_vect, "C");

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

                std::list<atomp> admin_to_remove = get_irrelevant_atoms_in_expr(rule->admin);
                std::list<atomp> prec_to_remove = get_irrelevant_atoms_in_expr(rule->prec);

                if (admin_to_remove.size() > 0 || prec_to_remove.size() > 0) {

                    Expr adm = rule->admin;
                    for (auto &&atom : admin_to_remove) {
                        has_changed = true;
                        log->trace("Removing atom {} from expression {} since is not used", *atom, *adm);
                        adm = delete_atom(adm, atom);
                        log->trace("\t==>{}", *adm);
                    }
                    Expr prec = rule->prec;
                    for (auto &&atom : prec_to_remove) {
                        has_changed = true;
                        log->trace("Removing atom {} from expression {} since is not used", *atom, *adm);
                        prec = delete_atom(prec, atom);
                        log->trace("\t==>{}", *prec);
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
            std::list<std::pair<std::set<atomp>, std::list<userp>>> partitions;

            for (auto &&u_conf : unique_conf) {
                partitions.push_back(std::pair<std::set<atomp>, std::list<userp>>(u_conf->config(), std::list<userp>()));
            }

            int user_k = policy->admin_count() + 1;

            for (auto &&pair : partitions) {
                if (pair.second.size() < user_k) {
                    for (auto &&user : policy->users()) {
                        if (user->config() == pair.first) {
                            if (user->infinite) {
                                int i = 1;
                                while (pair.second.size() < user_k) {
                                    pair.second.push_back(user->extract_copy(i++));
                                }
                                break;
                            }
                            pair.second.push_back(user);

                            if (pair.second.size() == user_k) {
                                break;
                            }
                            if (pair.second.size() > user_k) {
                                log->critical("User size cannot be greater than k + 1 and is {}; k + 1 = {}", pair.second.size(), user_k);
                                throw unexpected_error("User size cannot be greater than k + 1.");
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
            std::set<Atomp> new_atoms;
            new_atoms.insert(policy->goal_role);
            for (auto &&rule : policy->rules()) {
                new_atoms.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
                new_atoms.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                new_atoms.insert(rule->target);
            }
            if (new_atoms.size() != policy->atoms().size()) {
                std::vector<atomp> nform(new_atoms.begin(), new_atoms.end());
                policy->set_atoms(nform);
                return true;
            }
            return false;
        }

        /* SIMPLIFY OR ATTEMPT 1 */
        std::pair<int, std::list<atomp>> weight_union(const Expr& e1, const Expr& e2) {
            //COUNTING REDUNDANT LITERALS
            Expr joined = createOrExpr(e1, e2);
            auto lits = get_irrelevant_atoms_in_expr(joined);
            return std::pair<int, std::list<atomp>>((int) lits.size(), lits);
        }

        std::pair<int, Expr> smart_join(std::list<Expr> exprs) {
            int atoms_removed = false;
            while (exprs.size() > 1) {
                auto ite = exprs.begin();
                Expr first = *ite;
                auto best_match = ++ite;
                std::pair<int, std::list<atomp>> best_match_weight = weight_union(first, *best_match);
//                log->trace("First candidate! Redundant {}", best_match_weight.first);
//                for (auto &&lit : best_match_weight.second) {
//                    log->trace("{}", *lit);
//                }
//                log->trace("\t{}", **ite);
                for (++ite; ite != exprs.end(); ++ite) {
                    auto pair = weight_union(first, *ite);
                    if (pair.first > best_match_weight.first) {
//                        log->trace("Found a better candidate! Redundant {}", pair.first);
//                        for (auto &&lit : pair.second) {
//                            log->trace("{}", *lit);
//                        }
//                        log->trace("\t{}", **ite);
                        best_match_weight = pair;
                        best_match = ite;
                    }
                }
                Expr joined = createOrExpr(first, *best_match);
                if (log->level() == spdlog::level::trace && best_match_weight.first > 0) {
                    auto lite = best_match_weight.second.begin();
                    std::stringstream fmt;
                    fmt << "{" << **lite;
                    for (++lite; lite != best_match_weight.second.end(); ++lite) {
                        fmt << ", " << **lite;
                    }
                    fmt << "}";
                    log->trace("SAVED {} atoms: {} merging", best_match_weight.first, fmt.str());
                    log->trace("\t{}", *first);
                    log->trace("\t{}", **best_match);
                }
                for (auto &&red_lit : best_match_weight.second) {
                    atoms_removed++;
                    joined = delete_atom(joined, red_lit);
                }
                exprs.erase(exprs.begin());
                exprs.erase(best_match);
                exprs.push_back(joined);
            }
            return std::pair<int, Expr>(atoms_removed, *exprs.begin());
        }

        bool simplify_or_expressions() {
            bool changed = false;
            for (auto &&rule :policy->rules()) {
                std::list<Expr> sep = get_toplevel_or(rule->prec);
                log->warn("Rule {}:", *rule);
                for (auto &&item : sep) {
                    log->warn("\t{}", *item);
                }
                std::pair<int, Expr> new_cond = smart_join(sep);
                if (new_cond.first) {
                    changed = new_cond.first > 0;
//                    log->warn("now done: {}", *new_cond.second);
                    rule->prec = new_cond.second;
                }
            }
            return changed;
        }

        /* INFINITY BMC FUNCTIONS */
        void compute_all_atom_statuses(std::vector<std::shared_ptr<atom_status>>& cache) {
            for (auto &&atom : policy->atoms()) {
//                log->trace("Processing atom {}", *atom);
                atom_used_as_value(atom, 0, cache);
                atom_used_as_value(atom, 1, cache);
            }
        }

        bool query_infini_admin(int steps,
                                int rounds,
                                int wanted_threads_count) {
            std::vector<std::shared_ptr<atom_status>> statuses = atom_status::create(policy);
            compute_all_atom_statuses(statuses);

            std::list<rulep> to_remove_admin;

            std::map<Expr, std::list<rulep>, deepCmpExprs> per_admin_rules;
            for (auto &&rule : policy->rules()) {
                if (!is_constant_true(rule->admin)) {
                    per_admin_rules[rule->admin].push_back(rule);
                }
            }

            for (auto &&pair : per_admin_rules) {
                bool res = apply_infini_admin(solver, policy, pair.first, statuses, steps, rounds, wanted_threads_count);
//                log->trace("Administrative expression {} is {} with BMC.",*pair.first, res ? "REACHABLE" : "NOT REACHABLE");
                if (res) {
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "*";
                        std::flush(std::cout);
                    }
//                    log->trace("Removing in:");
                    for (auto &&rule : pair.second) {
//                        log->trace("\t{}", *rule);
                        to_remove_admin.push_back(rule);
                    }
                }
                else {
                    if (can_write(spdlog::level::trace)) {
                        std::cout << "=";
                        std::flush(std::cout);
                    }
                }
            }

            if (can_write(spdlog::level::trace)) {
                std::cout << std::endl;
            }

            for (auto &&rule : to_remove_admin) {
                rule->admin = createConstantTrue();
            }

            return to_remove_admin.size() > 0;
        }

        public:

        /*void test() {
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

        }*/

        void apply() {
            int fixpoint_iteration = 1;
            bool infini_fixpoint = false;

//
//            log->info("{}", *policy);
//            this->simplyfy_remove_false();
//            log->info("{}", *policy);
//            exit(0);

//            log->debug("Applying simplyfy_remove_false on {}", policy->rules().size());
//            bool prune_rule_6_res = this->simplyfy_remove_false();
//
//            log->info("{}", *policy);
//
//            exit(0);

            auto global_start = std::chrono::high_resolution_clock::now();

            while (!infini_fixpoint) {
                bool fixpoint = false;
                auto step_start = std::chrono::high_resolution_clock::now();
                while (!fixpoint) {
                    std::string tampone = with_tampone ? "with tampone" : "without tampone";

                    log->debug("Applying backward_slicing on {}", policy->rules().size());
                    bool backward_slicing_res = this->backward_slicing();
                    backward_slicing_res = reduce_roles() || backward_slicing_res;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    solver->deep_clean();

                    log->debug("Applying simplyfy_remove_false {} on {}", tampone, policy->rules().size());
                    bool prune_rule_6_res = this->simplyfy_remove_false();
                    prune_rule_6_res = reduce_roles() || prune_rule_6_res;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    if (prune_rule_6_res) {
                        // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                        backward_slicing();
                    }
                    solver->deep_clean();


                    log->debug("Applying easy_pruning {} on {}", tampone, policy->rules().size());
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


                    log->debug("Applying prune_irrelevant_roles {} on {}", tampone, policy->rules().size());
                    bool prune_irrelevant_roles_res = this->prune_irrelevant_roles();
                    prune_irrelevant_roles_res = reduce_roles() || prune_irrelevant_roles_res;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    if (prune_irrelevant_roles_res) {
                        // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                        backward_slicing();
                    }
                    solver->deep_clean();


                    bool merge_rules_res = false;
                    if (!Config::do_not_merge) {
                        log->debug("Applying merge_rules {} on {}", tampone, policy->rules().size());
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


                    log->debug("Applying prune_implied_pairs {} on {}", tampone, policy->rules().size());
                    bool prune_implied_pairs_res = this->prune_implied_pairs();
                    prune_implied_pairs_res = reduce_roles() || prune_implied_pairs_res;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    if (prune_implied_pairs_res) {
                        // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
                        backward_slicing();
                    }
                    solver->deep_clean();

//                    bool simplify_toplevel_or_res = false;
//                    if (Config::simplify_toplevel_or) {
//
//                        log->debug("Applying simplify_or_expressions on {}", policy->rules().size());
//                        simplify_toplevel_or_res = simplify_or_expressions();
//                        log->debug(" ==> {} rules...", policy->rules().size());
//                        if (merge_rules_res) {
//                            // IF SOMETHING CHANGED REPEAT THE BACKWARD SLICING SINCE IT IS FAST AND CAN REDUCE THE POLICY
//                            backward_slicing();
//                        }
//                        solver->deep_clean();
//
//
//                        bool simplify_expression_res = simplify_expressions();
//                        simplify_toplevel_or_res = simplify_toplevel_or_res || simplify_expression_res;
//                    }


                    fixpoint = with_tampone &&
                            !(
                                    backward_slicing_res ||
                                    easy_pruning_res ||
                                    prune_immaterial_roles_res ||
                                    prune_irrelevant_roles_res ||
                                    prune_implied_pairs_res ||
                                    merge_rules_res ||
                                    prune_rule_6_res
                            );
                    this->with_tampone = true;
                }

                if (!Config::no_infinity_bmc) {
                    log->debug("Applying infinity BMC on {}", policy->rules().size());
                    infini_fixpoint = !query_infini_admin(Config::infinity_bmc_rounds_count,
                                                          Config::infinity_bmc_steps_count, -1);
                    infini_fixpoint = reduce_roles() || infini_fixpoint;
                    log->debug(" ==> {} rules...", policy->rules().size());
                    solver->deep_clean();
                } else {
                    log->debug("Not applying infinity BMC");
                }

                log->debug("Iteration: {}", fixpoint_iteration++);
                auto step_end = std::chrono::high_resolution_clock::now();
                auto step_milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(
                        step_end - step_start);
                log->debug(" done in {} ms.", step_milliseconds.count());
            }

            reduce_users();
            solver->deep_clean();

            log->debug("{}", *policy);

//            apply_infini_admin(solver, policy, *policy->rules().begin(), createConstantTrue(), 10, 10, 10);
//
//            log->debug("{}", *policy);

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

//        bool res = apply_infini_admin(solver, policy, createAndExpr(policy->can_assign_rules()[0]->admin, policy->can_assign_rules()[1]->admin), 10, 10, -1);
//        log->debug("{}", res);

        Pruning<TVar, TExpr> core(solver, policy);

        core.apply();
    }

    template void prune_policy<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                               const std::shared_ptr<arbac_policy>& policy);
    template void prune_policy<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                           const std::shared_ptr<arbac_policy>& policy);
}
