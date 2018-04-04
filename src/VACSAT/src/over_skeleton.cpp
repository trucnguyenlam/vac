//
// Created by esteffin on 12/5/17.
//

#include "over_structures.h"
#include "prelude.h"
#include "SMT_BMC_Struct.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/Z3.h"
#include "SMTSolvers/mathsat.h"
#include "SMTSolvers/boolector.h"

namespace SMT {

    class simple_role_choicer : public role_choicer {

        const std::shared_ptr<arbac_policy> &policy;

    public:
        explicit simple_role_choicer(const std::shared_ptr<arbac_policy> &_policy) :
                policy(_policy) { }

        Choice classify(atomp r) const override {
//            if (r->name == "r1" || r->name == "r2") {
//                return REQUIRED;
//            }
            return Choice::FREE;
        }

        int get_required_count() const override {
            int count = 0;
            for (auto &&atom :policy->atoms()) {
                if (classify(atom) == Choice::REQUIRED) {
                    count++;
                }
            }
            return count;
        }

    };

    class learning_overapprox {
    private:
        typedef generic_variable variable;

        typedef proof_node node;
        typedef proof_node _node;
        typedef std::shared_ptr<proof_node> tree;
        typedef std::weak_ptr<proof_node> w_tree;

//        atomp fake_atom = nullptr;


        class SMT_proof_checker : public proof_checker {
        private:

            class b_solver_state {
            private:

                void init(SMTFactory* solver, const tree &node) {
                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string var_name = "var_" + node_id + "_" + atom->name;
                        vars[atom->role_array_index] = variable(var_name, 0, 1, solver, BOOLEAN);
                    }

                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string updated_in_subrun_name = "updated_in_subrun_" + node_id + "_" + atom->name;
                        updated_in_subrun[atom->role_array_index] = variable(updated_in_subrun_name, 0, 1, solver,
                                                                             BOOLEAN);
                    }

//                for (auto &&atom : node->node_infos.all_atoms) {
//                    std::string blocked_name = "blocked_" + node_id + "_" + atom->name;
//                    blocked[atom->role_array_index] = variable(blocked_name, 0, 1, solver, BOOLEAN);
//                }

                    int i = 0;
                    for (auto &&rules_c : node->node_infos.rules_c) {
                        std::string apply_rule_name = "apply_rule_" + std::to_string(i) + "_" + node_id;
                        apply_rule[i] = variable(apply_rule_name, -1, 1, solver, BOOLEAN);
                        i++;
                    }

                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string blocked_by_children_name = "blocked_by_children_" + node_id + "_" + atom->name;
                        blocked_by_children[atom->role_array_index] = variable(blocked_by_children_name, 0, 1, solver,
                                                                               BOOLEAN);
                    }
                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string unchecked_priority_name = "unchecked_priority_" + node_id + "_" + atom->name;
                        unchecked_priority[atom->role_array_index] = variable(unchecked_priority_name, 0, 1, solver, BOOLEAN);
                    }
                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string priority_name = "priority_" + node_id + "_" + atom->name;
                        priority[atom->role_array_index] = variable(priority_name, 0, 1, solver, BOOLEAN);
                    }
                    for (auto &&atom : node->node_infos.all_atoms) {
                        std::string second_priority_name = "second_priority_" + node_id + "_" + atom->name;
                        second_priority[atom->role_array_index] = variable(second_priority_name, 0, 1, solver, BOOLEAN);
                    }
//                for (auto &&atom : node->node_infos.all_atoms) {
//                    std::string priority_not_blocked_name = "priority_not_blocked_" + node_id + "_" + atom->name;
//                    priority_not_blocked[atom->role_array_index] = variable(priority_not_blocked_name, 0, 1, solver,
//                                                                            BOOLEAN);
//                }

                    //TODO: can be decreased only to actual atom count, but everything should be updated accordingly
                    var_id = variable("var_id_" + node_id, 0, bits_count(node->node_infos.policy_atoms_count), solver,
                                      BIT_VECTOR);
                    rule_id = variable("rule_id_" + node_id, 0, bits_count((uint) node->node_infos.rules_c.size()), solver,
                                       BIT_VECTOR);
                    skip = variable("skip_" + node_id, 0, 1, solver, BOOLEAN);
                    guard = variable("guard_" + node_id, 0, 1, solver, BOOLEAN);
                    refineable = variable("refineable_" + node_id, 0, 1, solver, BOOLEAN);
                    increase_budget = variable("increase_budget_" + node_id, 0, 1, solver, BOOLEAN);

                    //EXPLORATION STRATEGY SUPPORT VALUES
                    es_all_atoms_set = variable("all_atoms_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_skip_impl_all_atoms_set = variable("skip_impl_all_atoms_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_all_primary_priority_set = variable("all_primary_priority_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_only_primary_priority_set = variable("only_primary_priority_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_all_secondary_priority_set = variable("all_secondary_priority_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_only_both_priority_set = variable("only_both_priority_set_" + node_id, 0, 1, solver, BOOLEAN);
                    es_primary_priority_check = variable("primary_priority_check_" + node_id, 0, 1, solver, BOOLEAN);
                    es_both_priority_check = variable("both_priority_check_" + node_id, 0, 1, solver, BOOLEAN);
                }

            public:
                std::string &node_id;
                std::vector<variable> vars;
                std::vector<variable> updated_in_subrun;
//            std::vector<variable> blocked;
                std::vector<variable> apply_rule;
                std::vector<variable> blocked_by_children;
                std::vector<variable> unchecked_priority;
                std::vector<variable> priority;
                std::vector<variable> second_priority;
//            std::vector<variable> priority_not_blocked;
                variable var_id;
                variable rule_id;
                variable skip;
                variable guard;
                variable refineable;
                variable increase_budget;

                //Exploration_strategy tmp variables
                variable es_skip_impl_all_atoms_set;
                variable es_all_atoms_set;
                variable es_all_primary_priority_set;
                variable es_only_primary_priority_set;
                variable es_all_secondary_priority_set;
                variable es_only_both_priority_set;
                variable es_primary_priority_check;
                variable es_both_priority_check;

                b_solver_state() = delete;

                b_solver_state(const tree &node,
//                           const std::shared_ptr<arbac_policy>& policy,
                               SMTFactory* solver) :
                        node_id(node->uid),
                        vars(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
                        updated_in_subrun(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
//                    blocked(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
                        apply_rule(std::vector<variable>((uint) node->node_infos.rules_c.size())),
                        blocked_by_children(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
                        unchecked_priority(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
                        priority(std::vector<variable>((uint) node->node_infos.policy_atoms_count)),
                        second_priority(std::vector<variable>((uint) node->node_infos.policy_atoms_count)) {
                    init(solver, node);
//                set_guards();
                }
            };

            std::map<tree, std::unique_ptr<b_solver_state>> solver_state;
            std::map<tree, pruning_triggers> p_triggers;
//            const std::shared_ptr<arbac_policy> policy;
            std::shared_ptr<SMTFactory> solver;
//            const std::set<userp, std::function<bool(const userp &, const userp &)>> initial_confs;

            std::list<SMTExpr> assertions;

            variable tmp_bool;
            SMTExpr zero;
            SMTExpr one;

            bool annotate_proof = false;
            bool merge_rule_in_trans = false;

            // ASSERTIONS RELATED FUNCTIONS
            inline void strict_emit_assignment(const variable &var, const SMTExpr &value) {
                SMTExpr ass = solver->createEqExpr(var.get_solver_var(), value);
                solver->assertLater(ass);
            }

            inline void emit_assignment(const tree &node, const variable &var, const SMTExpr &value) {
                SMTExpr ass = solver->createEqExpr(var.get_solver_var(), value);
                //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
                SMTExpr guarded_ass = solver->createImplExpr(solver_state[node]->guard.get_solver_var(),
                                                           ass);
                solver->assertLater(guarded_ass);

            }

            inline void emit_assumption(const tree &node, const SMTExpr &value) {
                //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
                SMTExpr guarded_ass = solver->createImplExpr(solver_state[node]->guard.get_solver_var(),
                                                           value);
                solver->assertLater(guarded_ass);
            }

            inline void emit_comment(const std::string &comment) {
                //Working automatically and only in Z3
                if (solver->solver_name == Solver::Z3) {
                    solver->assertNow(solver->createBoolVar(comment));
//                    log->debug("Emitting comment: " + comment);
                }
            }

            // STATE AND MASKS RELATED FUNCTIONS
            void set_empty_node_state(const tree &node) {
                assert(solver_state[node] == nullptr);
                b_solver_state node_state = b_solver_state(node, solver.get());
                solver_state[node] = std::make_unique<b_solver_state>(node_state);
            }

            void set_zero(const tree &node, std::vector<variable> &vars) {
                for (auto &&atom : node->node_infos.all_atoms) {

//                    log->warn("{}", var.full_name);
//                    emit_assignment(node, vars[atom->role_array_index], zero);
                    strict_emit_assignment(vars[atom->role_array_index], zero);
//                        strict_emit_assignment(vars[atom->role_array_index], zero);
                }
            }

            void copy_mask(const tree &node, std::vector<variable> &source, std::vector<variable> &dest) {
                if (source.size() != dest.size()) {
                    throw unexpected("Cannot copy from container of different sizes");
                }
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    variable s = source[i];
                    variable d = dest[i];
                    SMTExpr source_val = s.get_solver_var();
                    emit_assignment(node, d, source_val);
                }
            }

            /**
             * This function copies the values from source to dest if the condition holds,
             * Otherwise it takes the value from dest
             * **/
            void cond_save_mask(const tree &node,
                                std::vector<variable> &source,
                                std::vector<variable> &dest,
                                SMTExpr condition) {
                if (source.size() != dest.size()) {
                    throw unexpected("Cannot sync two container of different sizes");
                }
                //TODO: check if atoms_a is enough
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    variable s = source[i];
                    variable old_d = dest[i];
                    variable new_d = old_d.createFrom();

                    SMTExpr value = solver->createCondExpr(condition,
                                                         s.get_solver_var(),
                                                         old_d.get_solver_var());
                    emit_assignment(node, new_d, value);
                    dest[i] = new_d;
                }
            }

            /**
             * This function set variables in dest to the OR of source1 and source2 if the condition holds,
             * Otherwise it takes the value from dest
             * **/
            void cond_save_ored_mask(const tree &node,
                                     std::vector<variable> &source1,
                                     std::vector<variable> &source2,
                                     std::vector<variable> &dest,
                                     SMTExpr condition) {
                if (source1.size() != source2.size() || source1.size() != dest.size()) {
                    throw unexpected("Cannot sync two container of different sizes");
                }
                //TODO: check if atoms_a is enough
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    variable s1 = source1[i];
                    variable s2 = source2[i];
                    variable old_d = dest[i];
                    variable new_d = old_d.createFrom();

                    SMTExpr value = solver->createCondExpr(condition,
                                                         solver->createOrExpr(s1.get_solver_var(), s2.get_solver_var()),
                                                         old_d.get_solver_var());
                    emit_assignment(node, new_d, value);
                    dest[i] = new_d;
                }
            }

            // NONDET ASSIGNMENT RELATED FUNCTIONS
            SMTExpr get_variable_invariant_from_node(const tree &node, const Atomp &var) {
                variable var_value = solver_state[node]->vars[var->role_array_index];

                SMTExpr value_valid = solver->createFalse();
                for (auto &&value : node->leaf_infos->nondet_restriction[var]) {
                    SMTExpr assigned_value = value ? one : zero;
                    value_valid = solver->createOrExpr(value_valid,
                                                       solver->createEqExpr(var_value.get_solver_var(),
                                                                            assigned_value));
                }
                return value_valid;
            }

            variable update_var_a(const tree &node, const Atomp &var) {
                if (!node->is_leaf()) {
                    throw unexpected("var update must be located to leaves only");
                }
                //IF THE ATOM IS UPDATEABLE
                if (!node->leaf_infos->nondet_restriction[var].empty()) {
                    //GUARD FOR NONDET UPDATE
                    emit_comment("Nondet_update_role_" + var->name);
                    tmp_bool = tmp_bool.createFrom();
                    SMTExpr update_guard =
                            solver->createAndExpr(solver->createNotExpr(
                                    solver_state[node]->blocked_by_children[var->role_array_index].get_solver_var()),
                                                  tmp_bool.get_solver_var());
                    emit_assignment(node, tmp_bool, update_guard);


                    //VAR VALUE UPDATE
                    variable old_var_val = solver_state[node]->vars[var->role_array_index];
                    variable new_var_val = old_var_val.createFrom();
                    SMTExpr guarded_val = solver->createCondExpr(tmp_bool.get_solver_var(),
                                                               new_var_val.get_solver_var(),
                                                               old_var_val.get_solver_var());
                    emit_assignment(node, new_var_val, guarded_val);
                    solver_state[node]->vars[var->role_array_index] = new_var_val;

                    //NEW VAR VALUE ASSUMPTIONS
                    SMTExpr value_was_changed = solver->createNotExpr(solver->createEqExpr(old_var_val.get_solver_var(),
                                                                                         new_var_val.get_solver_var()));
                    SMTExpr value_invariant = get_variable_invariant_from_node(node, var);
                    SMTExpr assumption_body = solver->createImplExpr(tmp_bool.get_solver_var(),
                                                                   solver->createAndExpr(value_was_changed,
                                                                                         value_invariant));
                    emit_assumption(node, assumption_body);

                    //SAVE THE FACT THAT THE VARIABLE HAS BEEN CHANGED
                    variable old_updated_in_subrun = solver_state[node]->updated_in_subrun[var->role_array_index];
                    variable new_updated_in_subrun = old_updated_in_subrun.createFrom();
                    SMTExpr new_updated_value = solver->createCondExpr(tmp_bool.get_solver_var(),
                                                                     one,
                                                                     old_updated_in_subrun.get_solver_var());
                    emit_assignment(node, new_updated_in_subrun, new_updated_value);
                    solver_state[node]->updated_in_subrun[var->role_array_index] = new_updated_in_subrun;
                } else {
                    //IF THE ATOM IS STATICALLY NOT UPDATEABLE
                    emit_comment("Role_" + var->name + "_is_not_updateable");
                    tmp_bool = tmp_bool.createFrom();
                    emit_assignment(node, tmp_bool, zero);
                }
                //RETURN TO CREATE THE REFINEABLE CHECK
                return tmp_bool;
            }

            void save_refineable_condition(const tree &node, std::list<variable> &update_guards) {
                if (!node->is_leaf()) {
//                    log->warn("setting to false refinement of internal node {}", node->uid);
                    strict_emit_assignment(solver_state[node]->refineable, zero);
                } else {
//                    log->warn("setting to false refinement of internal node {}", node->uid);
                    SMTExpr not_skipping = solver->createNotExpr(solver_state[node]->skip.get_solver_var());
                    SMTExpr at_least_one_updated = solver->createFalse();
                    for (auto &&update_guard : update_guards) {
                        at_least_one_updated = solver->createOrExpr(at_least_one_updated,
                                                                    update_guard.get_solver_var());
                    }

                    //!SKIP && \/_{var} nondet_guard_var
                    SMTExpr refineable = solver->createAndExpr(not_skipping,
                                                             at_least_one_updated);

                    if (p_triggers[node].check_gap) {
                        // Force the nondeterministic assignment of the node
                        emit_comment("Forcing nondet assignment");
                        strict_emit_assignment(solver_state[node]->refineable, one);
                    }

                    strict_emit_assignment(solver_state[node]->refineable, refineable);
                }
            }

            void update_unblocked_vars_a(const tree &node) {
                if (node->leaf_infos->gap != maybe_bool::NO &&
                    p_triggers[node].overapprox != maybe_bool::NO) {
                    emit_comment("Begin_nondet_assignment");
                    std::list<variable> update_guards;
                    for (auto &&var :node->node_infos.atoms_a) {
                        variable update_guard = update_var_a(node, var);
                        update_guards.push_back(update_guard);
                    }

                    save_refineable_condition(node, update_guards);
                    emit_comment("End_nondet_assignment");
                } else {
                    emit_comment("Nondet_assignment_suppressed");
                    strict_emit_assignment(solver_state[node]->refineable, zero);
                }
            }

            // TRANS RELATED FUNCTIONS
            std::vector<rulep> merge_by_target(const tree &node) {
                std::vector<rulep> result;
                std::map<std::pair<atomp, bool>, std::list<rulep>> rules_by_atom_kind;
                for (auto &&r_c : node->node_infos.rules_c) {
                    std::pair<atomp, bool> pair = std::make_pair(r_c->target, r_c->is_ca);
                    rules_by_atom_kind[pair].push_back(r_c);
                }

                for (auto &&key_value : rules_by_atom_kind) {
                    const std::pair<atomp, bool>& atom_is_ca = key_value.first;
                    Expr cond = createConstantFalse();
                    for (auto &&rule : key_value.second) {
                        cond = createOrExpr(cond, rule->prec);
                    }
                    rulep merged(new rule(atom_is_ca.second,
                                          createConstantTrue(),
                                          cond,
                                          atom_is_ca.first,
                                          -1));
                    result.push_back(merged);
                }

                return std::move(result);
            };

            SMTExpr get_rule_assumptions_c(const tree &node, std::pair<rulep, int> rule_id, SMTExpr &rule_is_selected) {
                rulep rule = rule_id.first;
                SMTExpr rule_precondition = generateSMTFunction(solver,
                                                              rule->prec,
                                                              solver_state[node]->vars,
                                                              "");
                SMTExpr target_not_blocked =
                        solver->createNotExpr(
                                solver_state[node]->blocked_by_children[rule->target->role_array_index].get_solver_var());
                SMTExpr rule_target_value = rule->is_ca ? one : zero;
                SMTExpr target_is_changed =
                        solver->createNotExpr(
                                solver->createEqExpr(
                                        solver_state[node]->vars[rule->target->role_array_index].get_solver_var(),
                                        rule_target_value));
                //IF THE RULE IS SELECTED THEN ALL THE PRECONDITIONS MUST HOLDS
                SMTExpr final_assumption =
                        solver->createImplExpr(rule_is_selected,
                                               solver->createAndExpr(rule_precondition,
                                                                     solver->createAndExpr(target_not_blocked,
                                                                                           target_is_changed)));
                return final_assumption;
            }

            /**
             * @fn set the corersponding blocked_by_children var
             * @param node
             * @param rule
             * @param is_rule_selected
             */
            void update_parent_blocked(const tree &node, rulep &rule, SMTExpr &is_rule_selected) {
                // UPDATE PARENT BLOCKED
                emit_comment("Blocked _parent node");
                if (node->is_root()) {
                    return;
                }
                const tree parent = node->parent().lock();
                int target_idx = rule->target->role_array_index;

                variable old_blocked = solver_state[parent]->blocked_by_children[target_idx];
                variable new_blocked = old_blocked.createFrom();
                // add node guard to avoid free value if node is skipping
                SMTExpr new_blocked_value =
                        solver->createCondExpr(
                                solver->createAndExpr(solver_state[node]->guard.get_solver_var(),
                                                      is_rule_selected),
                                one,
                                old_blocked.get_solver_var());
                strict_emit_assignment(new_blocked, new_blocked_value);
                solver_state[parent]->blocked_by_children[target_idx] = new_blocked;
            }

            void apply_rule_effect_c(const tree &node, std::pair<rulep, int> rule_id, SMTExpr &rule_is_selected) {
                rulep rule = rule_id.first;
                atomp target = rule->target;
                // UPDATE VAR VALUE
                variable old_var_var = solver_state[node]->vars[target->role_array_index];
                variable new_var_var = old_var_var.createFrom();
                SMTExpr rule_value = rule->is_ca ? one : zero;
                SMTExpr new_var_value = solver->createCondExpr(rule_is_selected,
                                                             rule_value,
                                                             old_var_var.get_solver_var());
                emit_assignment(node, new_var_var, new_var_value);
                solver_state[node]->vars[target->role_array_index] = new_var_var;

                // UPDATE UPDATED_IN_SUBRUN VALUE
                variable old_updated_in_subrun_var = solver_state[node]->updated_in_subrun[target->role_array_index];
                variable new_updated_in_subrun_var = old_updated_in_subrun_var.createFrom();
                SMTExpr new_updated_value = solver->createCondExpr(rule_is_selected,
                                                                 one,
                                                                 old_updated_in_subrun_var.get_solver_var());
                emit_assignment(node, new_updated_in_subrun_var, new_updated_value);
                solver_state[node]->updated_in_subrun[target->role_array_index] = new_updated_in_subrun_var;

                // UPDATE PARENT BLOCKED
                update_parent_blocked(node, rule, rule_is_selected);

                //SAVE VAR_ID
                variable &var_id_var = solver_state[node]->var_id;
                SMTExpr rule_var_id_value = solver->createBVConst(rule->target->role_array_index, var_id_var.bv_size);
                SMTExpr rule_selected_impl_var_id = solver->createImplExpr(rule_is_selected,
                                                                         solver->createEqExpr(
                                                                                 var_id_var.get_solver_var(),
                                                                                 rule_var_id_value));
                emit_assumption(node, rule_selected_impl_var_id);

                // SET PRIORITY OF THE NODE
                set_priority(node, rule, rule_is_selected);
            }

            void simulate_rule_c(const tree &node, std::pair<rulep, int> rule_id) {
                const rulep &rule = rule_id.first;
                const int r_id = rule_id.second;
                if (solver->solver_name == Solver::Z3) {
                    SMTExpr v = solver->createBVVar("Simulating_rule_" + rule->to_new_string(),
                                                 solver_state[node]->rule_id.bv_size);
                    SMTExpr value = solver->createBVConst(r_id, solver_state[node]->rule_id.bv_size);
                    solver->assertLater(solver->createEqExpr(v, value));
                }
                SMTExpr is_rule_selected_value =
                        solver->createEqExpr(solver_state[node]->rule_id.get_solver_var(),
                                             solver->createBVConst(r_id, solver_state[node]->rule_id.bv_size));

                // This ensures it is printed close to the usage in the model
                solver_state[node]->apply_rule[r_id] = solver_state[node]->apply_rule[r_id].createFrom();
                emit_assignment(node, solver_state[node]->apply_rule[r_id], is_rule_selected_value);


                SMTExpr is_rule_selected = solver_state[node]->apply_rule[r_id].get_solver_var();

                SMTExpr rule_assumptions = get_rule_assumptions_c(node, rule_id, is_rule_selected);

                emit_assumption(node, rule_assumptions);

                apply_rule_effect_c(node, rule_id, is_rule_selected);
            }

            void select_one_rule_c(const tree &node, std::vector<rulep>& rules_c) {
                //TO BE SURE TO APPLY AT LEAST ONE RULE WE HAVE TO ASSUME THAT RULE_ID <= RULE_COUNT
                SMTExpr assumption = solver->createLtExpr(solver_state[node]->rule_id.get_solver_var(),
                                                        solver->createBVConst((int) rules_c.size(),
                                                                              solver_state[node]->rule_id.bv_size));
                emit_assumption(node, assumption);
            }

            void transition_c(const tree &node) {
                emit_comment("Begin_transition_" + node->uid);
                std::vector<rulep> rules_c = merge_rule_in_trans ?
                                             std::move(merge_by_target(node)) :
                                             node->node_infos.rules_c;
                select_one_rule_c(node, rules_c);

                if (p_triggers[node].c_rule_check == nullptr) {
                    for (int r_id = 0; r_id < rules_c.size(); ++r_id) {
                        //execute all rules
                        std::pair<rulep, int> rule_id(rules_c[r_id], r_id);
                        simulate_rule_c(node, rule_id);
                    }
                } else {
                    if (merge_rule_in_trans) {
                        throw unexpected("Cannot merge rules if probing is enabled (triggers.c_rule_check)");
                    }
                    //execute only selected rule
                    rulep selected_rule = *p_triggers[node].c_rule_check;
                    int selected_id = (int) std::distance(rules_c.begin(),
                                                          std::find(rules_c.begin(), rules_c.end(), selected_rule));

                    assert(selected_id >= 0 && selected_id < rules_c.size());

                    // set the id to force role execution
                    emit_assignment(node,
                                    solver_state[node]->rule_id,
                                    solver->createBVConst(selected_id, solver_state[node]->rule_id.bv_size));
                    simulate_rule_c(node, std::make_pair(rules_c[selected_id], selected_id));

                }
                emit_comment("End_transition_" + node->uid);
            }

            // CHILDREN RELATED FUNCTIONS
            void set_skip(const tree &node) {
//                if (node->node_infos.rules_c.empty()) {
//                    // NODE MUST BE A SKIP SINCE NO TRANSITION CAN OCCUR
//                    strict_emit_assignment(node->solver_state->skip, one);
//                    strict_emit_assignment(node->solver_state->guard, zero);
//                    return;
//                }
                tmp_bool = tmp_bool.createFrom();
                SMTExpr skip_child_value = tmp_bool.get_solver_var();

                for (auto &&w_ancestor :node->ancestors()) {
                    const tree ancestor = w_ancestor.lock();
                    skip_child_value = solver->createOrExpr(skip_child_value,
                                                            solver_state[ancestor]->skip.get_solver_var());
                }

                if (p_triggers[node].no_skip) {
                    emit_comment("Do_not_skip_" + node->uid);
                    strict_emit_assignment(solver_state[node]->skip, zero);
                }

                strict_emit_assignment(solver_state[node]->skip, skip_child_value);
                strict_emit_assignment(solver_state[node]->guard,
                                       solver->createNotExpr(solver_state[node]->skip.get_solver_var()));
            }

            /* OLD update_node_var_blocked_after_child
            void update_node_var_blocked_after_child(tree &node, tree &child) {
                variable child_applied = child->solver_state->guard;
                for (auto &&atom : node->node_infos.atoms_a) {
                    int i = atom->role_array_index;
                    variable old_blocked_node_i = node->solver_state->blocked[i];
                    SMTExpr is_right_target = solver->createEqExpr(child->solver_state->var_id.get_solver_var(),
                                                                 solver->createBVConst(i,
                                                                                       child->solver_state->var_id.bv_size));

                    SMTExpr should_apply = solver->createAndExpr(child_applied.get_solver_var(),
                                                               is_right_target);

                    SMTExpr new_blocked_value_i = solver->createCondExpr(should_apply,
                                                                       one,
                                                                       old_blocked_node_i.get_solver_var());

                    variable new_blocked_node_i = old_blocked_node_i.createFrom();
                    emit_assignment(node, new_blocked_node_i, new_blocked_value_i);
                    node->solver_state->blocked[i] = new_blocked_node_i;
                }
            }*/

            void simulate_child(const tree &node, const tree &child) {
                set_empty_node_state(child);

                set_skip(child);
                copy_mask(child, solver_state[node]->vars, solver_state[child]->vars);
                copy_mask(child, solver_state[node]->blocked_by_children, solver_state[child]->blocked_by_children);


                subrun(child);

                cond_save_mask(node,
                               solver_state[child]->vars,
                               solver_state[node]->vars,
                               solver_state[child]->guard.get_solver_var());
                cond_save_ored_mask(node,
                                    solver_state[node]->updated_in_subrun,
                                    solver_state[child]->updated_in_subrun,
                                    solver_state[node]->updated_in_subrun,
                                    solver_state[child]->guard.get_solver_var());

//                update_node_var_blocked_after_child(node, child);
            }

            void simulate_children(const tree &node) {
                for (auto &&child :node->refinement_blocks()) {
                    if (node->node_infos.rules_c.empty() && !p_triggers[node].no_transition) {
                        emit_comment("Child_" + child->uid + "_not_generated_since_C_is_empty");
                        log->warn("Child_{}_not_generated_since_C_is_empty", child->uid);
                    }
                    emit_comment("Begin_child_" + child->uid + "_simulation");
                    simulate_child(node, child);
                    emit_comment("End_child_" + child->uid + "_simulation");
                }
            }

            // PRIORITY RELATED FUNCTIONS
            void set_priority(const tree &node, rulep& rule, SMTExpr rule_selected) {
                SMTExpr all_atoms_priority_set = one;
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    SMTExpr value = (contains(rule->prec->atoms(), atom)) ? one : zero;

                    SMTExpr priority_i_set = solver->createEqExpr(solver_state[node]->priority[i].get_solver_var(),
                                                                value);
                    all_atoms_priority_set = solver->createAndExpr(all_atoms_priority_set, priority_i_set);
                }
                SMTExpr if_rule_selected_priority_is_set = solver->createImplExpr(rule_selected, all_atoms_priority_set);
                emit_assumption(node, if_rule_selected_priority_is_set);
            }

            void set_unchecked_priority(const tree &node) {
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    SMTExpr atom_in_priority = solver_state[node]->priority[i].get_solver_var();
                    SMTExpr atom_blocked_by_children = solver_state[node]->blocked_by_children[i].get_solver_var();

                    // If leaf all priority is unchecked
                    SMTExpr atom_in_p_not_checked = node->is_leaf() ?
                                                  atom_in_priority :
                                                  solver->createAndExpr(atom_in_priority,
                                                                        solver->createNotExpr(atom_blocked_by_children));
                    variable& unchecked_atom = solver_state[node]->unchecked_priority[i];
                    emit_assignment(node, unchecked_atom, atom_in_p_not_checked);
                }
            }

            void set_second_priority(const tree &node) {
                if (node->is_leaf()) {
                    unexpected("Leaves do not have second priority");
                }
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    SMTExpr is_unchecked_in_children = zero;
                    // Exclude last child from snd priority
                    //TODO: put condition in last node not used for priority
//                    for (int j = 0; j < node->_refinement_blocks.size(); ++j) {
                    for (int j = 0; j < node->refinement_blocks().size() - 1; ++j) {
                        const tree& child = node->refinement_blocks()[j];
                        SMTExpr atom_is_unchecked_in_child = solver_state[child]->unchecked_priority[i].get_solver_var();
                        is_unchecked_in_children = solver->createOrExpr(is_unchecked_in_children, atom_is_unchecked_in_child);
                    }
                    emit_assignment(node, solver_state[node]->second_priority[i], is_unchecked_in_children);
                }
            }

            // MULTY PRIORITY EXPLORATION STRATEGY REVISITED
            SMTExpr rev_skipped_last_child(const tree& node) {
                if (node->is_leaf()) {
                    throw unexpected("Exploration strategy cannot be called on leaves");
                }
                tree last_child = node->refinement_blocks().back();
                return solver_state[last_child]->skip.get_solver_var();
            }

            void rev_es_set_all_done(const tree &node) {
                SMTExpr all_set = one;
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    variable updated_atom = solver_state[node]->updated_in_subrun[i];
                    variable blocked_atom = solver_state[node]->blocked_by_children[i];

                    SMTExpr if_upd_then_blocked = solver->createImplExpr(updated_atom.get_solver_var(),
                                                                       blocked_atom.get_solver_var());

                    all_set = solver->createAndExpr(all_set, if_upd_then_blocked);
                }
                emit_assignment(node, solver_state[node]->es_all_atoms_set, all_set);
            }

            /**
             *   skipped_last_child => es_all_atoms_set
             * @param node
             */
            void rev_es_set_if_skip_all_done(const tree &node) {
                SMTExpr skipped_last_child = rev_skipped_last_child(node);
                rev_es_set_all_done(node);

                SMTExpr if_skip_all_done = solver->createImplExpr(skipped_last_child,
                                                                solver_state[node]->es_all_atoms_set.get_solver_var());
                emit_assignment(node, solver_state[node]->es_skip_impl_all_atoms_set, if_skip_all_done);
            }

            /**
             * Computes the first part of the node's exploration strategy
             *   /\
             *  /  \  (updated_in_subrun[i] /\ priority[i]) ==> blocked_by_children[i]
             * /    \
             *   i
             * @param node: the node
             * @param primary_priority: specify if priority is primary or secondary
             */
            void rev_es_set_all_updated_priority_set(const tree &node, bool primary_priority) {
//                tree& last_node = node->_refinement_blocks.back();
                SMTExpr all_blocked = one;
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;
                    SMTExpr updated_and_priority = solver->createAndExpr(
                            solver_state[node]->updated_in_subrun[i].get_solver_var(),
                            primary_priority ?
                            solver_state[node]->priority[i].get_solver_var() :
                            solver_state[node]->second_priority[i].get_solver_var());

                    SMTExpr required_blocked = solver->createImplExpr(updated_and_priority,
                                                                    solver_state[node]->blocked_by_children[i].get_solver_var());

                    all_blocked = solver->createAndExpr(all_blocked,
                                                        required_blocked);
                }

                variable& es_all_priority_set =
                        primary_priority ?
                        solver_state[node]->es_all_primary_priority_set :
                        solver_state[node]->es_all_secondary_priority_set;
                emit_assignment(node, es_all_priority_set, all_blocked);
            }

            /**
             * Computes the second part of the node's exploration strategy
             *   /\
             *  /  \  (updated_in_subrun[i] /\ blocked_by_children[i] /\ (!blocked_in_last_child)) ==> priority_ored[i]
             * /    \
             *   i
             *  updated_in_subrun[i] /\ blocked_by_children[i] is used instead of blocked_by_children[i] to allow to use blocked
             *  (!blocked_in_last_child) allows to have a free action in the last child
             *  priority_ored = primary_priority ? primary : (primary \/ secondary)
             * @param node: the node
             * @param primary_priority: specify if priority is primary or primary and secondary
             */
            void rev_es_set_only_priority_blocked(const tree &node, bool primary_priority) {
                const tree& last_node = node->refinement_blocks().back();
                SMTExpr only_priority = one;
                for (auto &&atom : node->node_infos.all_atoms) {
                    int i = atom->role_array_index;

                    variable last_atom_set = solver_state[last_node]->var_id;
                    SMTExpr atom_in_last_op = solver->createEqExpr(solver->createBVConst(i, last_atom_set.bv_size),
                                                                 last_atom_set.get_solver_var());
                    if (p_triggers[node].no_sfogo) {
                        emit_comment("node" + node->uid + "is_marked_no_sfogo");
                        atom_in_last_op = zero;
                    }

                    SMTExpr atom_explicitely_set =
                            solver->createAndExpr(solver_state[node]->updated_in_subrun[i].get_solver_var(),
                                                  solver_state[node]->blocked_by_children[i].get_solver_var());

                    SMTExpr blocked_not_in_last = solver->createAndExpr(atom_explicitely_set,
                                                                      solver->createNotExpr(atom_in_last_op));


                    SMTExpr atom_in_required_priority =
                            primary_priority ?
                            solver_state[node]->priority[i].get_solver_var() :
                            solver->createOrExpr(solver_state[node]->priority[i].get_solver_var(),
                                                 solver_state[node]->second_priority[i].get_solver_var());

                    SMTExpr blocked_not_last_in_priorities =
                            solver->createImplExpr(blocked_not_in_last,
                                                   atom_in_required_priority);

                    only_priority = solver->createAndExpr(only_priority,
                                                          blocked_not_last_in_priorities);
                }

                variable& es_only_priority_set =
                        primary_priority ?
                        solver_state[node]->es_only_primary_priority_set :
                        solver_state[node]->es_only_both_priority_set;

                emit_assignment(node, es_only_priority_set, only_priority);
            }

            /**
             *
             *   (!all_priority_set) ==> (!skipped_last_child) /\ only_priority_set
             *
             * @param node: the node
             * @param primary_priority: specify if priority is primary or primary and secondary
             */
            void rev_es_set_all_priority_blocked(const tree &node, bool primary_priority) {
                const tree& last_node = node->refinement_blocks().back();

                rev_es_set_all_updated_priority_set(node, primary_priority);
                rev_es_set_only_priority_blocked(node, primary_priority);

                variable& es_all_priority_set =
                        primary_priority ?
                            solver_state[node]->es_all_primary_priority_set :
                            solver_state[node]->es_all_secondary_priority_set;

                variable& es_only_priority_set =
                        primary_priority ?
                            solver_state[node]->es_only_primary_priority_set :
                            solver_state[node]->es_only_both_priority_set;

                variable& es_priority_check =
                        primary_priority ?
                            solver_state[node]->es_primary_priority_check :
                            solver_state[node]->es_both_priority_check;

                SMTExpr skipped_last_child = rev_skipped_last_child(node);
                SMTExpr priority_check =
                        solver->createImplExpr(
                                solver->createNotExpr(es_all_priority_set.get_solver_var()),
                                solver->createAndExpr(
                                        solver->createNotExpr(skipped_last_child),
                                        es_only_priority_set.get_solver_var()));

                emit_assignment(node, es_priority_check, priority_check);
            }

            void rev_es_check(const tree &node) {
                if (p_triggers[node].no_priority || p_triggers[node].no_transition) {
                    emit_comment("Skipping_exploration_strategy_" + node->uid);
                    return;
                }
                set_second_priority(node);

                emit_comment("Begin_exploration_strategy_" + node->uid);

                rev_es_set_all_priority_blocked(node, true);
                emit_assumption(node, solver_state[node]->es_primary_priority_check.get_solver_var());
                rev_es_set_all_priority_blocked(node, false);
                emit_assumption(node, solver_state[node]->es_both_priority_check.get_solver_var());
                rev_es_set_if_skip_all_done(node);
                emit_assumption(node, solver_state[node]->es_skip_impl_all_atoms_set.get_solver_var());

                emit_comment("End_exploration_strategy_" + node->uid);
            }

            // SUBRUN FUNCTION
            void subrun(const tree &node) {
                emit_comment("Begin_subrun_" + node->uid);
                set_zero(node, solver_state[node]->updated_in_subrun);
                if (node->is_leaf()) {
                    emit_comment("Node_" + node->uid + "_is_leaf");
                    update_unblocked_vars_a(node);
                    if (p_triggers[node].no_transition) {
                        emit_comment("Transition_disabled_by_pruning");
                    } else {
                        transition_c(node);
                    }
                    set_unchecked_priority(node);
                } else {
                    emit_comment("Node_" + node->uid + "_is_internal");
                    simulate_children(node);
//                    exploration_strategy(node);
//                    multi_priority_exploration_strategy(node);

                    rev_es_check(node);
                    if (p_triggers[node].no_transition) {
                        emit_comment("Transition_disabled_by_pruning");
                    } else {
                        transition_c(node);
                    }
                    set_unchecked_priority(node);
                }
                emit_comment("End_subrun_" + node->uid);
            }

            // ROOT SUBRUN RELATED FUNCTIONS
            void do_not_skip_root(const tree &root) {
                variable &skip_root = solver_state[root]->skip;
                variable &root_guard = solver_state[root]->guard;

                strict_emit_assignment(skip_root, zero);
                strict_emit_assignment(root_guard, one);
            }

            void init_root_vars(const tree &root,
                                const std::set<userp, std::function<bool(const userp &,
                                                                         const userp &)>> &initial_confs) {
                SMTExpr init_expr = zero;
                for (auto &&conf : initial_confs) {
                    SMTExpr conf_expr = one;
                    for (auto &&atom : root->node_infos.all_atoms) {
                        SMTExpr init_value = contains(conf->config(), atom) ? one : zero;
                        variable root_var = solver_state[root]->vars[atom->role_array_index];
                        SMTExpr value_saved = solver->createEqExpr(root_var.get_solver_var(), init_value);
                        conf_expr = solver->createAndExpr(conf_expr, value_saved);
                    }
                    init_expr = solver->createOrExpr(init_expr,
                                                     conf_expr);
                }
                emit_assumption(root, init_expr);
            }

            void assert_invariant_pre_subrun(const tree &node) {
                assert(node->is_root());
                Expr &target_expr = node->node_infos.rules_c[0]->prec;

                SMTExpr invariant_expr = generateSMTFunction(solver,
                                                           target_expr,
                                                           solver_state[node]->vars,
                                                           "");
                assertions.push_back(invariant_expr);
            }

            void assert_invariant_post_subrun(const tree &node) {
                assert(node->is_root());
                atomp target_atom = node->node_infos.rules_c[0]->target;

                SMTExpr invariant_expr = generateSMTFunction(solver,
                                                             createEqExpr(createLiteralp(target_atom),
                                                                          createConstantTrue()),
                                                             solver_state[node]->vars,
                                                             "");
                assertions.push_back(invariant_expr);
            }

            void root_subrun(const tree &root,
                             const std::set<userp,
                                            std::function<bool(const userp &, const userp &)>> &initial_confs) {
                set_empty_node_state(root);
                do_not_skip_root(root);

                emit_comment("Variable_initialization");
                init_root_vars(root, initial_confs);

                assert_invariant_pre_subrun(root);
                set_zero(root, solver_state[root]->blocked_by_children);
                subrun(root);
                assert_invariant_post_subrun(root);
            }

            // SOLVER RELATED FUNCTIONS
            void add_assertions() {
                SMTExpr final_assertion = zero;
                for (auto &&assertion : assertions) {
                    final_assertion = solver->createOrExpr(final_assertion,
                                                           assertion);
                }
                solver->assertLater(final_assertion);
            }

            bool is_reachable(proofp &proof) {
                emit_comment("Root_subrun");
                root_subrun(proof->proof_tree, proof->initial_confs);
                emit_comment("Root_assertion");
                add_assertions();

                auto start = std::chrono::high_resolution_clock::now();

                solver->printContext(Config::dump_smt_formula);

                if (annotate_proof) {
                    if (Config::show_solver_statistics) {
                        solver->print_statistics();
                    }

                    if (solver->solver_name == Solver::Z3 && !Config::dump_smt_formula.empty()) {
                        solver->printContext(Config::dump_smt_formula);
                        log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
                    }
                }

                SMTResult res = solver->solve();

                if (annotate_proof) {
                    if (solver->solver_name == Solver::Z3 && !Config::dump_smt_formula.empty()) {
                        solver->printContext(Config::dump_smt_formula);
                        log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
//                        if (res == SMTResult::SAT) {
//                            solver->printModel();
//                        }
                    }

                    auto end = std::chrono::high_resolution_clock::now();
                    auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
                    log->debug("------------ SMT SOLVED IN {} ms ------------", milliseconds.count());
                }

                return res == SMTResult::SAT;
            }

            bool set_node_refinement_from_model(const tree &node) {
                if (node->node_infos.rules_c.empty() && !p_triggers[node].no_transition) {
                    // the node has not been expanded
                    if (node->is_leaf()) {
                        node->leaf_infos->gap = maybe_bool::NO;
                    }
                    return false;
                } else if (!node->is_leaf()) {
                    bool refineable_subtree = false;
                    for (auto &&child : node->refinement_blocks()) {
                        refineable_subtree = set_node_refinement_from_model(child) || refineable_subtree;
                    }
                    return refineable_subtree;
                } else {
                    bool is_node_refineable = node->leaf_infos->gap == maybe_bool::YES;
                    if (node->leaf_infos->gap == maybe_bool::UNKNOWN) {
                        is_node_refineable = solver->get_bool_value(solver_state[node]->refineable.get_solver_var());
                        node->leaf_infos->gap = is_node_refineable ? maybe_bool::YES : maybe_bool::UNKNOWN;
                    }
                    if (is_node_refineable) {
                        log->warn("Node {} is refineable", node->uid);
                    }

//                    bool increase_node_budget = solver->get_bool_value(node->solver_state->increase_budget.get_solver_var());
//                    node->infos->solverInfo->increase_budget = increase_node_budget ? b_solver_info::YES : b_solver_info::NO;
//                    if (node->infos->solverInfo->increase_budget == b_solver_info::YES) {
//                        log->warn("Node {} budget should be increased", node->uid);
//                    }
                    return is_node_refineable;
                }
            }

            bool anotate_refineable(tree &root) {
                return set_node_refinement_from_model(root);
            }

            void initialize() {
                tmp_bool = generic_variable("tmp_bool", 0, 1, solver.get(), BOOLEAN);
                zero = solver->createBoolConst(0);
                one = solver->createBoolConst(1);
            }

            void cleanup() {
                solver_state.clear();
                solver->deep_clean();
                assertions.clear();
                initialize();
            }

            // CONFIG RELATED FUNCTIONS
            bool get_merge_value(bool annotate, maybe_bool merge_rules) {
                if (!annotate && merge_rules == maybe_bool::YES) {
                    throw unexpected("Cannot merge rules in probing mode");
                }
                switch (merge_rules) {
                    case maybe_bool::UNKNOWN:
                        // If standard run then merge rules
                        return annotate;
                    case maybe_bool::YES:
                        return true;
                    case maybe_bool::NO:
                        return false;
                    default:
                        throw unexpected("uh?");
                }
            }

        public:

            SMT_proof_checker(//const std::shared_ptr<arbac_policy> _policy,
                              std::shared_ptr<SMTFactory> _solver,
//                              const std::set<userp, std::function<bool(const userp &,
//                                                                       const userp &)>> _initial_confs,
                              bool annotate,
                              maybe_bool merge_rules = maybe_bool::UNKNOWN) :
//                    policy(_policy),
                    solver(std::move(_solver)),
//                    initial_confs(std::move(_initial_confs)),
                    assertions(std::list<SMTExpr>()),
                    annotate_proof(annotate),
                    merge_rule_in_trans(get_merge_value(annotate, merge_rules)) { }


            over_analysis_result verify_proof(proofp proof) override {
                return verify_proof(proof, std::map<tree, pruning_triggers>());
            }

            over_analysis_result verify_proof(proofp proof,
                                              std::map<tree, pruning_triggers> triggers) override {
                over_analysis_result result;
                proof->dump_proof("asd.1", true, "pruning");
                p_triggers = std::move(triggers);
                solver->deep_clean();
                cleanup();
                bool over_reachable = is_reachable(proof);

                if (!over_reachable) {
                    result = over_analysis_result::SAFE;
                } else {
                    if (annotate_proof) {
                        bool is_refineable = anotate_refineable(proof->proof_tree);
                        result = is_refineable ? over_analysis_result::UNSAFE_INCOMPLETE : over_analysis_result::UNSAFE;
                    } else {
                        result = over_analysis_result::UNSAFE;
                    }
                }

                cleanup();

                return result;
            }
        };

        class tree_pruner {
        private:
            struct abstract_pruning_handle {
            public:
                proofp cloned_proof;
                tree target_node_l;
                tree fake_node_f;
                tree sfogo_node_s;
                tree testing_node_e;
                std::map<tree, pruning_triggers> p_triggers;
                abstract_pruning_handle(proofp _cloned_proof,
                                        tree _target_node_l,
                                        tree _fake_node_f,
                                        tree _sfogo_node_s,
                                        tree _testing_node_e,
                                        std::map<tree, pruning_triggers> _p_triggers) :
                    cloned_proof(std::move(_cloned_proof)),
                    target_node_l(std::move(_target_node_l)),
                    fake_node_f(std::move(_fake_node_f)),
                    sfogo_node_s(std::move(_sfogo_node_s)),
                    testing_node_e(std::move(_testing_node_e)),
                    p_triggers(std::move(_p_triggers)) { }
            };

            SMT_proof_checker pruner_checker;

            void remove_rule_a(tree& node, rulep& rule) {
                std::vector<rulep>& rules = node->node_infos.rules_a;
                rules.erase(std::remove(rules.begin(), rules.end(), rule), rules.end());

                std::function<void(tree)> fun = [&](tree _node) {
                    _node->node_infos.rules_a.erase(std::remove(_node->node_infos.rules_a.begin(),
                                                                _node->node_infos.rules_a.end(),
                                                                rule),
                                                    _node->node_infos.rules_a.end());
                    _node->node_infos.rules_c.erase(std::remove(_node->node_infos.rules_c.begin(),
                                                                _node->node_infos.rules_c.end(),
                                                                rule),
                                                    _node->node_infos.rules_c.end());
                };

                for (auto &&child : node->refinement_blocks()) {
                    child->tree_pre_order_iter(fun);
                }

                node->consolidate_tree();
            }

            // PARTITION FUNCTIONS
            std::pair<rulep, bool> get_reach_impl_test_rule(std::vector<rulep>& rules, rulep& target_rule) {
                Expr new_condition = createConstantFalse();
                int similar_count = 0;
                for (auto &&rule : rules) {
                    if (target_rule->target == rule->target &&
                        target_rule->is_ca == rule->is_ca &&
                        target_rule != rule) {
                        new_condition = createOrExpr(new_condition, rule->prec);
                        similar_count++;
                    }
                }
                new_condition = createAndExpr(target_rule->prec,
                                              createNotExpr(new_condition));
                rulep final_rule(new rule(target_rule->is_ca,
                                          createConstantTrue(),
                                          new_condition,
                                          target_rule->target,
                                          -target_rule->original_idx));

                return std::make_pair(final_rule, similar_count > 0);
            };


//            tree &_tree;

            // ABSTRACT PRUNING FUNCTIONS
            abstract_pruning_handle create_abstract_handle(proofp& proof, tree& node, int rule_6_subnodes) { //, rulep& tested_rule) {
//            tree root = node->clone();

                tree_path f_path = node->path;
                f_path.push_back(0);

                node_policy_infos f_policy_infos = node->node_infos.clone();
                std::list<std::weak_ptr<proof_node>> f_ancestors = node->ancestors();
                f_ancestors.push_back(node);

                tree abstract_f(new _node(f_path,
                                          "F",
                                          node->depth + 1,
                                          node_invariants(),
                                          f_policy_infos,
                                          nullptr,
                                          f_ancestors,
                                          node,
                                          std::vector<tree>()));


                tree_path s_path = node->path;
                s_path.push_back(1);

                node_policy_infos s_policy_infos = node->node_infos.clone();
                //Copy rules but r
                s_policy_infos.rules_c = node->node_infos.rules_a;
//                for (auto &&r : s_policy_infos.rules_a) {
//                    if (r != tested_rule) {
//                        s_policy_infos.rules_c.push_back(r);
//                    }
//                }
                std::list<std::weak_ptr<proof_node>> s_ancestors = f_ancestors;
                s_ancestors.push_back(abstract_f);

                tree s_sfogo(new _node(s_path,
                                       "S",
                                       node->depth + 1,
                                       node_invariants(),
                                       s_policy_infos,
                                       std::make_unique<leaves_infos>(leaves_infos()),
                                       s_ancestors,
                                       node,
                                       std::vector<tree>()));


                tree_path e_path = abstract_f->path;
                e_path.push_back(0);

                node_policy_infos e_policy_infos = node->node_infos.clone();
//                e_policy_infos.rules_c.clear();
                std::list<std::weak_ptr<proof_node>> e_ancestors = abstract_f->ancestors();
                e_ancestors.push_back(abstract_f);

                tree testing_e(new _node(e_path,
                                         "E",
                                         abstract_f->depth + 1,
                                         node_invariants(),
                                         e_policy_infos,
                                         std::make_unique<leaves_infos>(leaves_infos()),
                                         e_ancestors,
                                         abstract_f,
                                         std::vector<tree>()));

                node->add_child(abstract_f);
                node->add_child(s_sfogo);
                abstract_f->add_child(testing_e);

//                log->warn(testing_e->leaf_infos->JSON_stringify());

                node->consolidate_tree();
//                log->warn(testing_e->leaf_infos->JSON_stringify());

                std::map<tree, pruning_triggers> p_triggers;
                p_triggers[abstract_f].no_transition = true;
                p_triggers[abstract_f].no_priority = true;
                p_triggers[testing_e].no_skip = true;
                p_triggers[testing_e].no_sfogo = true;
                p_triggers[node].no_priority = true;

                return abstract_pruning_handle(proof,
                                               node,
                                               std::move(abstract_f),
                                               std::move(s_sfogo),
                                               std::move(testing_e),
                                               std::move(p_triggers));
            }

            abstract_pruning_handle create_abstract(proofp& proof, tree& tested, int rule_6_subnodes) { //, rulep& tested_rule) {
                //FIXME: REMOVE CLONE!
//                proofp cloned_proof = proof->clone();
//                tree& cloned = cloned_proof->proof_tree;

                tree probed_node = proof->proof_tree->get_by_path(tested->path);

                abstract_pruning_handle ret_handle = create_abstract_handle(proof, probed_node, rule_6_subnodes);

//                auto nodes = proof->proof_tree->get_all_nodes();
//                for (auto &&orig_node :nodes) {
//                    log->critical("{}", orig_node->uid);
//                }

                if (rule_6_subnodes > 0) {
                    ret_handle.testing_node_e->leaf_infos->gap = maybe_bool::YES;

                    //FIXME: remove this awfull...
                    ret_handle.testing_node_e->node_infos.rules_c = ret_handle.testing_node_e->node_infos.rules_a;
                    ret_handle.cloned_proof->proof_tree->refine_tree(-1, rule_6_subnodes);
                    ret_handle.testing_node_e->node_infos.rules_c.clear();
                }

                return ret_handle;
            }

            bool test_node_rule_a(abstract_pruning_handle& handle, rulep& rule) {
                std::vector<rulep> old_s_rules = handle.sfogo_node_s->node_infos.rules_c;

                handle.sfogo_node_s->node_infos.rules_c.erase(
                        std::remove(handle.sfogo_node_s->node_infos.rules_c.begin(),
                                    handle.sfogo_node_s->node_infos.rules_c.end(), rule),
                        handle.sfogo_node_s->node_infos.rules_c.end());

                std::vector<rulep> testing_c;
                testing_c.push_back(rule);

//                handle.testing_node->node_infos.rules_c.clear();
//                handle.testing_node->node_infos.rules_c.push_back(rule);
                handle.testing_node_e->node_infos.rules_c = testing_c;

//                handle.cloned_proof->dump_proof("asd.1", true, "before");

//                handle.p_triggers[handle.target_node_l].no_priority = true;
//                handle.p_triggers[handle.testing_node_e].no_skip = true;

//                handle.cloned_tree->dump_tree("tree.js", true, "handle.cloned_tree");

//                log->critical("Testing no_sfogo ");
//                handle.p_triggers[handle.testing_node_e].no_sfogo = true;
                //FIXME: REMOVE THIS AWFULL
                std::map<tree, pruning_triggers> triggers;
                for (auto &&pair : handle.p_triggers) {
                    triggers[pair.first] = std::move(pair.second.clone());
                }

                over_analysis_result usable = pruner_checker.verify_proof(handle.cloned_proof, std::move(triggers));

                handle.sfogo_node_s->node_infos.rules_c = old_s_rules;

                return usable != over_analysis_result::SAFE;
            }

            bool test_rule_a(abstract_pruning_handle& handle, std::vector<rulep>& pool, rulep& tested) {
                std::pair<rulep, bool> test_rule_pair = get_reach_impl_test_rule(pool, tested);
                tree& node = handle.testing_node_e;
                std::vector<rulep> old_c = node->node_infos.rules_c;

                bool is_usable = test_node_rule_a(handle, test_rule_pair.first);

                node->node_infos.rules_c = old_c;

                if (log->level() <= spdlog::level::info) {
                    if (test_rule_pair.second) {
                        std::cout << (!is_usable ? "J" : "-");
                    } else {
                        std::cout << (!is_usable ? "A" : "-");
                    }
                    std::flush(std::cout);
                }

                return is_usable;
            }

            bool reduce_node_a_rules(proofp& proof, tree &node, bool refine_node_e) {
                if (!node->is_leaf()) {
                    unexpected("Abstract pruning MUST be performed on leaves only");
                }

                std::vector<rulep> old_rules_a = node->node_infos.rules_a;
                std::list<rulep> removed_a;
                std::vector<rulep> actual_rules_a = node->node_infos.rules_a;

                int rule_6_subnodes = -1;
                if (refine_node_e) {
                    log->warn("Rule 6 refinement...");
                    for (auto &&rule_a :old_rules_a) {
                        rule_6_subnodes = std::max(rule_6_subnodes, (int) rule_a->prec->atoms().size());
                    }
//                    assert(rule_6_subnodes >= 0);
                }

                abstract_pruning_handle abstract_handle = create_abstract(proof, node, rule_6_subnodes);


                log->warn("Probing A of node {}{}:", node->uid, refine_node_e ? " with refinement" : "");
                for (auto &&rule_a :old_rules_a) {
                    bool is_usable = test_rule_a(abstract_handle, actual_rules_a, rule_a);

//                    abstract_handle.cloned_proof->dump_proof("asd.1.js", true, "before_remove");
                    if (!is_usable) {
                        actual_rules_a.erase(std::remove(actual_rules_a.begin(), actual_rules_a.end(), rule_a),
                                             actual_rules_a.end());
                        remove_rule_a(abstract_handle.target_node_l, rule_a);
                        removed_a.push_back(rule_a);
                    }
//                    abstract_handle.cloned_proof->dump_proof("asd.2.js", true, "after_remove");
                }

                if (log->level() <= spdlog::level::info) {
                    std::cout << std::endl;
                }

                // Clenaing up
                abstract_handle.target_node_l->remove_children();

                node->node_infos.rules_a = actual_rules_a;

                for (auto &&r_rule : removed_a) {
                    log->debug("{}", *r_rule);
                }

                return !removed_a.empty();
            }

            // RULE PROBING FUNCTIONS

            //            bool reduce_node_c_rules(tree& root, tree &node) {
//                std::vector<rulep> new_rules;
//                std::vector<rulep> old_rules = node->node_infos.rules_c;
//                bool old_skip = node->triggers.no_skip;
//                // warn -> trace
//                log->warn("Probing C of node {}:", node->uid);
//                //FORCING NODE TO BE EXECUTED
//                node->triggers.no_skip = true;
//                for (auto &&rule :old_rules) {
//                    std::vector<rulep> probed_rule;
//                    probed_rule.push_back(rule);
//                    node->node_infos.rules_c = probed_rule;
//                    over_analysis_result res = transformer.verify_proof(root, false);
//
//                    // info -> trace
//                    if (log->level() <= spdlog::level::info) {
//                        std::cout << (res == over_analysis_result::SAFE ? "X" : "-");
//                        std::flush(std::cout);
//                    }
//
//                    if (res != over_analysis_result::SAFE) {
//                        new_rules.push_back(rule);
//                    }
//                }
//                // info -> trace
//                if (log->level() <= spdlog::level::info) {
//                    std::cout << std::endl;
//                }
//                node->node_infos.rules_c = new_rules;
//                node->triggers.no_skip = old_skip;
//
//                return old_rules.size() != new_rules.size();
//            }

            // IMPLIED RULE SIMPLIFICATION FUNCTIONS
            //            std::map<std::pair<atomp, bool>, std::vector<rulep>> partition_rules(std::vector<rulep>& rules) {
//                std::map<std::pair<atomp, bool>, std::vector<rulep>> res;
//                for (auto &&rule : rules) {
//                    std::pair<atomp, bool> key(rule->target, rule->is_ca);
//                    res[key].push_back(rule);
//                }
//                return std::move(res);
//            };

            bool test_rule_c(proofp& proof, tree& node, std::vector<rulep>& pool, rulep& tested) {
                std::pair<rulep, bool> test_rule_pair = get_reach_impl_test_rule(pool, tested);
                std::vector<rulep> old_c = node->node_infos.rules_c;

                std::map<tree, pruning_triggers> p_triggers;

                p_triggers[node].no_skip = true;
                node->node_infos.rules_c.clear();
                node->node_infos.rules_c.push_back(test_rule_pair.first);

                over_analysis_result res = pruner_checker.verify_proof(proof);


                p_triggers[node].no_skip = false;
                node->node_infos.rules_c = old_c;

                bool useless = res == over_analysis_result::SAFE;

                if (log->level() <= spdlog::level::info) {
                    if (test_rule_pair.second) {
                        std::cout << (useless ? "I" : "-");
                    } else {
                        std::cout << (useless ? "X" : "-");
                    }
                    std::flush(std::cout);
                }

                return useless;
            }

            std::pair<bool, std::vector<rulep>> reduce_implied_c(proofp& proof, tree& node) {

                bool changed = false;

                std::vector<rulep> actual_rules = node->node_infos.rules_c;
                for (auto &&rule : node->node_infos.rules_c) {
                    bool to_remove = test_rule_c(proof, node, actual_rules, rule);

                    if (to_remove) {
                        changed = true;
                        actual_rules.erase(std::remove(actual_rules.begin(), actual_rules.end(), rule),
                                           actual_rules.end());
                    }
                }
                return std::pair<bool, std::vector<rulep>>(changed, actual_rules);
            }

            bool remove_node_implied_rules_c(proofp& root, tree& node) {
                log->warn("Probing implied C of node {}:", node->uid);
                std::vector<rulep> old_rules = node->node_infos.rules_c;
//                std::map<std::pair<atomp, bool>, std::vector<rulep>> partitions = partition_rules(node);

                std::pair<bool, std::vector<rulep>> red_p = reduce_implied_c(root, node);
                bool changed = red_p.first;
                std::vector<rulep> final_rules = red_p.second;


                if (log->level() <= spdlog::level::info) {
                    std::cout << std::endl;
                    std::flush(std::cout);
                }
                for (auto &&rule : old_rules) {
                    if (!contains(final_rules.begin(), final_rules.end(), rule)) {
                        log->debug("Rule {} will be removed", *rule);
                    }
                }
                node->node_infos.rules_c = final_rules;
                return changed;
            }

            // TREE EXPLORATION UTILITY FUNCTIONS
            std::list<tree> get_nodes_bfs_reversed(tree& root) {
                std::list<tree> internal_nodes;
                root->tree_bfs_iter([&](tree _node) { internal_nodes.push_back(_node); });
                internal_nodes.reverse();
                return std::move(internal_nodes);
            }

            // MAIN PRUNING FUNCTIONS

            //            void reduce_tree_c_rules(tree& root) {
//                std::list<tree> internal_nodes = get_nodes_bfs_reversed(root);
////                bool changed = true;
////                while (changed) {
////                    changed = false;
//                for (auto &&node : internal_nodes) {
//                    reduce_node_c_rules(root, node);
////                    bool modified = reduce_node_c_rules(node);
////                    changed = changed || modified;
//                }
////                }
//            }

            void remove_implied_rules_c(proofp &proof) {
                std::list<tree> internal_nodes = get_nodes_bfs_reversed(proof->proof_tree);
                for (auto &&node : internal_nodes) {
                    remove_node_implied_rules_c(proof, node);
                }
            }

            void reduce_tree_a_rules(proofp &proof, bool refine_e) {
                std::list<tree> internal_nodes = get_nodes_bfs_reversed(proof->proof_tree);
//                bool changed = true;
//                while (changed) {
//                    changed = false;
                for (auto &&node : internal_nodes) {
                    if (node->is_leaf()) {
                        reduce_node_a_rules(proof, node, refine_e);
                    }
//                    bool modified = reduce_node_c_rules(node);
//                    changed = changed || modified;
                }
//                }
            }

        public:
            explicit tree_pruner(const std::shared_ptr<SMTFactory>& _solver) : //, tree &root
                    pruner_checker(_solver,
                                   false,
                                   maybe_bool::NO) { }

            void prune_tree(proofp &_proof, bool apply_c_simplification, bool apply_a_simplification) {
                if (!apply_a_simplification && !apply_c_simplification) {
                    log->debug("Skipping pruning");
                    return;
                }
                if (apply_a_simplification) {
                    reduce_tree_a_rules(_proof, false);
                    reduce_tree_a_rules(_proof, true);
                }
                if (apply_c_simplification) {
//                    reduce_tree_c_rules(root);
                    remove_implied_rules_c(_proof);
                }
            }
        };

        int get_budget(proofp& proof) { // std::shared_ptr<simple_block_info<b_solver_info>>& info) {
            return proof->overapprox_strategy.blocks_count;
//            int max_budget = 0;
//            for (auto &&rule :info->rules) {
//                if (max_budget < rule->prec->atoms().size())
//                    max_budget = (int)rule->prec->atoms().size();
//            }
//            return max_budget + 1;
//            switch (overapprox_strategy.blocks_strategy) {
//                case OverapproxOptions::STRICT_BLOCK:
//                    return overapprox_strategy.blocks_count;
//                    break;
//                case OverapproxOptions::AT_MOST_BLOCK:
//                    return 1;
//                    break;
//                case OverapproxOptions::AT_LEAST_BLOCK:
//                    return overapprox_strategy.blocks_count;
//                    break;
//                default:
//                    throw unexpected_error("missing cases in switch on overapprox_strategy.blocks_strategy");
//            }
        }

//        void set_fake_tree(tree& root, std::& translator) {
//            tree_pruner pruner(translator);
//            pruner.prune_tree(root, false, true);
//
//            root->dump_tree("tree.js", true, "fake");
//
//            log->error("expanding root!");
//
//            root->leaf_infos->gap = maybe_bool::YES;
//            root->refine_tree(overapprox_strategy.depth, get_budget());
//            pruner.prune_tree(root, false, true);
//
//            root->dump_tree("tree.js", true, "fake");
//            log->error("expanding root_0!");
//
////            pruner.remove_implied_rules_c();
//            root->_refinement_blocks[0]->leaf_infos->gap = maybe_bool::YES;
//            root->refine_tree(overapprox_strategy.depth, get_budget());
//            pruner.prune_tree(root, false, true);
//
//            root->dump_tree("tree.js", true, "fake");
//            log->error("expanding root_1!");
//
//            root->_refinement_blocks[1]->leaf_infos->gap = maybe_bool::YES;
//            root->refine_tree(overapprox_strategy.depth, get_budget());
//            pruner.prune_tree(root, false, true);
//
//            root->dump_tree("tree.js", true, "fake");
//            log->error("expanding root_2!");
//
//            root->_refinement_blocks[2]->leaf_infos->gap = maybe_bool::YES;
//            root->refine_tree(overapprox_strategy.depth, get_budget());
//            pruner.prune_tree(root, false, true);
//
//            root->dump_tree("tree.js", true, "fake");
//            log->error("fake_tree created!");
//        }

        bool check_program(const std::shared_ptr<SMTFactory>& solver,
                           const std::vector<atomp>& orig_atoms,
                           const std::vector<rulep>& orig_rules,
                           const std::shared_ptr<arbac_policy>& policy,
                           const Expr& to_check) {
            SMT_proof_checker proof_translator(solver, true, maybe_bool::YES);


            proofp _proof(new proof_t(strategy,
                                      orig_atoms,
                                      orig_rules,
                                      policy,
                                      to_check));
//            set_fake_tree(proof_t, translator);
            bool completed = false;

            while (!completed) {
                log->warn("{}", _proof->tree_to_string());

//                log->debug("TESTING UNDERAPPROX PROOF");
//                block_nondet(proof_t);
//                over_analysis_result complete_result = translator.verify_proof(proof_t, true);
//                proof_t->clean_pruning_triggers();
//                assert(complete_result != over_analysis_result::UNSAFE_INCOMPLETE);
//                if (complete_result == over_analysis_result::UNSAFE) {
//                    proof_t->dump_tree("tree.js", true, "POST UNDERAPPROX");
//                    log->info("Target role may be reachable (but proof_t is not refineable)");
//                    return true;
//                }

                log->debug("TESTING OVERAPPROX PROOF");
                over_analysis_result result = proof_translator.verify_proof(_proof);
//                                              over_analysis_result::UNSAFE_INCOMPLETE;
                _proof->dump_proof("tree.js", true, "POST OVERAPPROX");

//                std::pair<std::string, std::string> strs = proof_t->tree_to_full_string();
//                log->debug("{}", strs.second);
                switch (result) {
                    case over_analysis_result::SAFE:
                        log->info("Target role is not reachable");
                        completed = true;
                        return false;
                        break;
                    case over_analysis_result::UNSAFE:
                        log->info("Target role may be reachable (but proof_t is not refineable)");
                        completed = true;
                        return true;
                        break;
                    case over_analysis_result::UNSAFE_INCOMPLETE:
                        log->info("Target role may be reachable...");
                        log->info("... PRUNING");
                        tree_pruner pruner(solver);
                        pruner.prune_tree(_proof, true, true);

                        log->info("... REFINING");

                        bool changed = _proof->proof_tree->refine_tree(_proof->overapprox_strategy.depth, get_budget(_proof));
                        //TODO: insert consolidate_tree in refine_tree
                        _proof->proof_tree->consolidate_tree();

                        _proof->proof_tree->dump_tree("tree.js", true, "POST PRUNING AND REFINEMENT");
                        if (solver->solver_name == Solver::Z3 && !Config::dump_smt_formula.empty()) {
                        }

//                        std::pair<std::string, std::string> strs = proof_t->tree_to_full_string();
//                        log->warn("{}", strs.first);
//                        log->debug("{}", strs.second);
                        if (!changed) {
                            log->info("Givin up refinement...");
                            completed = true;
                            return true;
                        }
                        break;
                }
            }
            throw unexpected("While loop should converge at some point!");
        }

        OverapproxOptions strategy;
    public:

        explicit learning_overapprox(OverapproxOptions _strategy) :
            strategy(_strategy) { }

        bool operator()(const std::shared_ptr<SMTFactory>& solver,
                        const std::vector<atomp>& orig_atoms,
                        const std::vector<rulep>& orig_rules,
                        const std::shared_ptr<arbac_policy>& policy,
                        const Expr& to_check) {
            return check_program(solver,
                                 orig_atoms,
                                 orig_rules,
                                 policy,
                                 to_check);
        }

    };

    bool overapprox_learning(const std::shared_ptr<SMTFactory>& solver,
                             const std::shared_ptr<arbac_policy>& policy,
                             const std::vector<atomp> atoms,
                             const std::vector<rulep> rules,
                             const Expr& to_check) {
        OverapproxOptions strategy = {
            .version = OverapproxOptions::LEARNING,
            .depth_strategy = OverapproxOptions::AT_MOST_DEPTH,
            .depth = Config::overapproxOptions.depth,
            .blocks_strategy = OverapproxOptions::AT_LEAST_BLOCK,
            .blocks_count = Config::overapproxOptions.blocks_count,
            .no_backward_slicing = Config::overapproxOptions.no_backward_slicing
        };
        learning_overapprox overapprox(strategy);
        return overapprox(solver, atoms, rules, policy, to_check);
    }


}
