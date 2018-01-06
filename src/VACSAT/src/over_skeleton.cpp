//
// Created by esteffin on 12/5/17.
//

#include "over_skeleton.h"
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
            return FREE;
        }

        int get_required_count() const override {
            int count = 0;
            for (auto &&atom :policy->atoms()) {
                if (classify(atom) == REQUIRED) {
                    count++;
                }
            }
            return count;
        }

    };

    template <typename TVar, typename TExpr>
    class learning_overapprox {
    private:
        typedef generic_variable<TVar, TExpr> variable;

        class b_solver_info;

        class b_solver_state;

        typedef gblock<simple_block_info<b_solver_info>, b_solver_state> node;
        typedef std::shared_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> tree;


        class b_solver_info {
        public:
            enum block_refineable {
                UNSET,
                YES,
                NO
            };
            block_refineable refineable = UNSET;
        };

        class b_solver_state {
        private:
//            const arbac_policy* policy;

            void init(SMTFactory<TVar, TExpr>* solver, const tree &node) {
                for (auto &&atom : node->infos->policy->atoms()) {
                    std::string var_name = "var_" + node_id + "_" + atom->name;
                    vars[atom->role_array_index] = variable(var_name, 0, 1, solver, BOOLEAN);
                }

                for (auto &&atom : node->infos->policy->atoms()) {
                    std::string updated_in_subrun_name = "updated_in_subrun_" + node_id + "_" + atom->name;
                    updated_in_subrun[atom->role_array_index] = variable(updated_in_subrun_name, 0, 1, solver,
                                                                         BOOLEAN);
                }

                for (auto &&atom : node->infos->policy->atoms()) {
                    std::string blocked_name = "blocked_" + node_id + "_" + atom->name;
                    blocked[atom->role_array_index] = variable(blocked_name, 0, 1, solver, BOOLEAN);
                }

                var_id = variable("var_id_" + node_id, 0, bits_count(node->infos->policy->atom_count()), solver,
                                  BIT_VECTOR);
                rule_id = variable("rule_id_" + node_id, 0, bits_count((uint) node->infos->rules.size()), solver,
                                   BIT_VECTOR);
                skip = variable("skip_" + node_id, 0, 1, solver, BOOLEAN);
                guard = variable("guard_" + node_id, 0, 1, solver, BOOLEAN);
                refineable = variable("refineable_" + node_id, 0, 1, solver, BOOLEAN);
            }

//            void set_guards(SMTFactory<TVar, TExpr>* solver) {
//                TExpr guard = solver->createTrue();
//
//                for (auto &&ancestor_g : ancestors_guards) {
//                    guard = solver->createAndExpr(guard, ancestor_g);
//                }
//
//
//            }

        public:
            std::string &node_id;
            std::vector<variable> vars;
            std::vector<variable> updated_in_subrun;
            std::vector<variable> blocked;
            variable var_id;
            variable rule_id;
            variable skip;
            variable guard;
            variable refineable;

            b_solver_state() = delete;

            b_solver_state(tree &node,
//                           const std::shared_ptr<arbac_policy>& policy,
                           SMTFactory<TVar, TExpr>* solver) :
                    node_id(node->uid),
                    vars(std::vector<variable>((uint) node->infos->policy->atom_count())),
                    updated_in_subrun(std::vector<variable>((uint) node->infos->policy->atom_count())),
                    blocked(std::vector<variable>((uint) node->infos->policy->atom_count())) {
                init(solver, node);
//                set_guards();
            }
        };

        enum over_analysis_result {
            SAFE,
            UNSAFE,
            UNSAFE_REFINEABLE
        };

        class tree_to_SMT {
        private:

            const std::shared_ptr<arbac_policy> policy;
            std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
            std::list<TExpr> assertions;

            variable tmp_bool;
            TExpr zero;
            TExpr one;
//        const bool use_admin;

//        restriction_info get_required(const std::shared_ptr<arbac_policy> &policy,
//                                            const std::vector<std::pair<Expr, Expr>> &target_exprs) {
//            restriction_info res;
//            for (auto &&expr : target_exprs) {
////                if (use_admin) {
////                    res.in_adm_target.insert(expr.second->atoms().begin(), expr.second->atoms().end());
////                }
//                for (auto &&atom : expr.first->atoms()) {
//                    if (_role_choicer.classify(atom) != role_choicer::EXCLUDED) {
//                        res.in_reg_target.insert(atom);
//                    }
//                }
//            }
//
//            for (auto &&rule : policy->rules()) {
//                if (contains(res.in_reg_target, rule->target)) {
//                    res.assigning_reg.insert(rule);
////                    if (use_admin) {
////                        res.in_precs.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
////                    }
//                    res.in_reg_precs.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
//                }
//            }
//
//            return res;
//        };
//
//        int get_layer_block_count(const std::shared_ptr<arbac_policy>& policy,
//                                  const layer_restriction_info& infos,
//                                  overapprox_strategy strategy) {
//            if (strategy.block_count > 0) {
//                return strategy.block_count;
//            } else {
//                int requireds = _role_choicer.get_required_count();
//                int dynamic = (int) infos.in_reg_target.size();
//
//                return requireds + dynamic;
//            }
//        };

            // ASSERTIONS RELATED FUNCTIONS
            inline void strict_emit_assignment(const variable &var, const TVar &value) {
                TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
                solver->assertLater(ass);
            }

            inline void emit_assignment(const tree& node, const variable &var, const TVar &value) {
                TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
                //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
                TExpr guarded_ass = solver->createImplExpr(node->solver_state->guard.get_solver_var(),
                                                           ass);
                solver->assertLater(guarded_ass);

            }

            inline void emit_assumption(const tree& node, const TExpr &value) {
                //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
                TExpr guarded_ass = solver->createImplExpr(node->solver_state->guard.get_solver_var(),
                                                           value);
                solver->assertLater(guarded_ass);
            }

            inline void emit_comment(const std::string &comment) {
                //Working automatically and only in Z3
                if (std::is_same<z3::expr, TExpr>::value) {
                    solver->assertNow(solver->createBoolVar(comment));
                    log->debug("Emitting comment: " + comment);
                }
            }

            // STATE AND MASKS RELATED FUNCTIONS
            void set_empty_node_state(tree &node) {
                assert(node->solver_state == nullptr);
                b_solver_state node_state = b_solver_state(node, solver.get());
                node->solver_state = std::make_shared<b_solver_state>(node_state);
            }

            void set_zero(std::vector<variable> &vars) {
                for (auto &&var : vars) {
//                    log->warn("{}", var.full_name);
                    strict_emit_assignment(var, zero);
                }
            }

            void copy_mask(tree &node, std::vector<variable> &source, std::vector<variable> &dest) {
                if (source.size() != dest.size()) {
                    throw unexpected_error("Cannot copy from container of different sizes");
                }
                for (int i = 0; i < source.size(); ++i) {
                    variable s = source[i];
                    variable d = dest[i];
                    TExpr source_val = s.get_solver_var();
                    emit_assignment(node, d, source_val);
                }
            }

            /*
             * This function copies the values from source to dest if the condition holds,
             * Otherwise it takes the value from dest
             * */
            void cond_save_mask(tree &node,
                                std::vector<variable> &source,
                                std::vector<variable> &dest,
                                TExpr condition) {
                if (source.size() != dest.size()) {
                    throw unexpected_error("Cannot sync two container of different sizes");
                }
                for (int i = 0; i < source.size(); ++i) {
                    variable s = source[i];
                    variable old_d = dest[i];
                    variable new_d = old_d.createFrom();

                    TExpr value = solver->createCondExpr(condition,
                                                         s.get_solver_var(),
                                                         old_d.get_solver_var());
                    emit_assignment(node, new_d, value);
                    dest[i] = new_d;
                }
            }

            /*
             * This function set variables in dest to the OR of source1 and source2 if the condition holds,
             * Otherwise it takes the value from dest
             * */
            void cond_save_ored_mask(tree &node,
                                     std::vector<variable> &source1,
                                     std::vector<variable> &source2,
                                     std::vector<variable> &dest,
                                     TExpr condition) {
                if (source1.size() != source2.size() || source1.size() != dest.size()) {
                    throw unexpected_error("Cannot sync two container of different sizes");
                }
                for (int i = 0; i < source1.size(); ++i) {
                    variable s1 = source1[i];
                    variable s2 = source2[i];
                    variable old_d = dest[i];
                    variable new_d = old_d.createFrom();

                    TExpr value = solver->createCondExpr(condition,
                                                         solver->createOrExpr(s1.get_solver_var(), s2.get_solver_var()),
                                                         old_d.get_solver_var());
                    emit_assignment(node, new_d, value);
                    dest[i] = new_d;
                }
            }

            // NONDET ASSIGNMENT RELATED FUNCTIONS
            TExpr get_variable_invariant_from_node(tree &node, const Atomp &var) {
                variable var_value = node->solver_state->vars[var->role_array_index];
                TExpr value_valid = solver->createFalse();
                for (auto &&rule :node->infos->rules) {
                    if (rule->target == var) {
                        TExpr assigned_value = rule->is_ca ? one : zero;
                        value_valid = solver->createOrExpr(value_valid,
                                                           solver->createEqExpr(var_value.get_solver_var(),
                                                                                assigned_value));
                    }
                }
                return value_valid;
            }

            variable update_var(tree &node, const Atomp &var) {
                //GUARD FOR NONDET UPDATE
                tmp_bool = tmp_bool.createFrom();
                TExpr update_guard =
                        solver->createAndExpr(solver->createNotExpr(
                                node->solver_state->blocked[var->role_array_index].get_solver_var()),
                                              tmp_bool.get_solver_var());
                emit_assignment(node, tmp_bool, update_guard);

                //VAR VALUE UPDATE
                variable old_var_val = node->solver_state->vars[var->role_array_index];
                variable new_var_val = old_var_val.createFrom();
                TExpr guarded_val = solver->createCondExpr(tmp_bool.get_solver_var(),
                                                           new_var_val.get_solver_var(),
                                                           old_var_val.get_solver_var());
                emit_assignment(node, new_var_val, guarded_val);
                node->solver_state->vars[var->role_array_index] = new_var_val;

                //NEW VAR VALUE ASSUMPTIONS
                TExpr value_was_changed = solver->createNotExpr(solver->createEqExpr(old_var_val.get_solver_var(),
                                                                                     new_var_val.get_solver_var()));
                TExpr value_invariant = get_variable_invariant_from_node(node, var);
                TExpr assumption_body = solver->createImplExpr(tmp_bool.get_solver_var(),
                                                               solver->createAndExpr(value_was_changed,
                                                                                     value_invariant));
                emit_assumption(node, assumption_body);

                //SAVE THE FACT THAT THE VARIABLE HAS BEEN CHANGED
                variable old_updated_in_subrun = node->solver_state->updated_in_subrun[var->role_array_index];
                variable new_updated_in_subrun = old_updated_in_subrun.createFrom();
                TExpr new_updated_value = solver->createCondExpr(tmp_bool.get_solver_var(),
                                                                 one,
                                                                 old_updated_in_subrun.get_solver_var());
                emit_assignment(node, new_updated_in_subrun, new_updated_value);
                node->solver_state->updated_in_subrun[var->role_array_index] = new_updated_in_subrun;

                //RETURN TO CREATE THE REFINEABLE CHECK
                return tmp_bool;
            }

            void save_refineable_condition(tree &node, std::list<variable> &update_guards) {
                TExpr not_skipping = solver->createNotExpr(node->solver_state->skip.get_solver_var());
                TExpr at_least_one_updated = solver->createFalse();
                for (auto &&update_guard : update_guards) {
                    at_least_one_updated = solver->createOrExpr(at_least_one_updated,
                                                                update_guard.get_solver_var());
                }

                //!SKIP && \/_{var} nondet_guard_var
                TExpr refineable = solver->createAndExpr(not_skipping,
                                                         at_least_one_updated);

                strict_emit_assignment(node->solver_state->refineable, refineable);
            }

            void update_unblocked_vars(tree &node) {
                emit_comment("Begin_nondet_assignment");
                std::list<variable> update_guards;
                for (auto &&var :policy->atoms()) {
                    variable update_guard = update_var(node, var);
                    update_guards.push_back(update_guard);
                }

                save_refineable_condition(node, update_guards);
                emit_comment("End_nondet_assignment");
            }

            // TRANS RELATED FUNCTIONS
            TExpr get_rule_assumptions(tree &node, int rule_id, TExpr &rule_is_selected) {
                rulep rule = node->infos->rules[rule_id];
                TExpr rule_precondition = generateSMTFunction(solver,
                                                              rule->prec,
                                                              node->solver_state->vars,
                                                              "");
                TExpr target_not_blocked =
                        solver->createNotExpr(
                                node->solver_state->blocked[rule->target->role_array_index].get_solver_var());
                TExpr rule_target_value = rule->is_ca ? one : zero;
                TExpr target_is_changed =
                        solver->createNotExpr(
                                solver->createEqExpr(
                                        node->solver_state->vars[rule->target->role_array_index].get_solver_var(),
                                        rule_target_value));
                //IF THE RULE IS SELECTED THEN ALL THE PRECONDITIONS MUST HOLDS
                TExpr final_assumption =
                        solver->createImplExpr(rule_is_selected,
                                               solver->createAndExpr(rule_precondition,
                                                                     solver->createAndExpr(target_not_blocked,
                                                                                           target_is_changed)));
                return final_assumption;
            }

            void apply_rule_effect(tree &node, int rule_id, TExpr &rule_is_selected) {
                rulep rule = node->infos->rules[rule_id];
                atomp target = rule->target;
                // UPDATE VAR VALUE
                variable old_var_var = node->solver_state->vars[target->role_array_index];
                variable new_var_var = old_var_var.createFrom();
                TExpr rule_value = rule->is_ca ? one : zero;
                TExpr new_var_value = solver->createCondExpr(rule_is_selected,
                                                             rule_value,
                                                             old_var_var.get_solver_var());
                emit_assignment(node, new_var_var, new_var_value);
                node->solver_state->vars[target->role_array_index] = new_var_var;

                // UPDATE UPDATED_IN_SUBRUN VALUE
                variable old_updated_in_subrun_var = node->solver_state->updated_in_subrun[target->role_array_index];
                variable new_updated_in_subrun_var = old_updated_in_subrun_var.createFrom();
                TExpr new_updated_value = solver->createCondExpr(rule_is_selected,
                                                                 one,
                                                                 old_updated_in_subrun_var.get_solver_var());
                emit_assignment(node, new_updated_in_subrun_var, new_updated_value);
                node->solver_state->updated_in_subrun[target->role_array_index] = new_updated_in_subrun_var;

                //SAVE VAR_ID
                variable old_var_id_var = node->solver_state->var_id;
                variable new_var_id_var = node->solver_state->var_id.createFrom();
                TExpr rule_var_id_value = solver->createBVConst(rule->target->role_array_index, old_var_id_var.bv_size);
                TExpr new_var_id_value = solver->createCondExpr(rule_is_selected,
                                                                rule_var_id_value,
                                                                old_var_id_var.get_solver_var());
                emit_assignment(node, new_var_id_var, new_var_id_value);
                node->solver_state->var_id = new_var_id_var;
            }

            void simulate_rule(tree &node, int rule_id) {
                TExpr rule_is_selected =
                        solver->createEqExpr(node->solver_state->rule_id.get_solver_var(),
                                             solver->createBVConst(rule_id, node->solver_state->rule_id.bv_size));

                TExpr rule_assumptions = get_rule_assumptions(node, rule_id, rule_is_selected);

                emit_assumption(node, rule_assumptions);

                apply_rule_effect(node, rule_id, rule_is_selected);
            }

            void apply_one_rule(tree &node) {
                //TO BE SURE TO APPLY AT LEAST ONE RULE WE HAVE TO ASSUME THAT RULE_ID <= RULE_COUNT
                TExpr assumption = solver->createLtExpr(node->solver_state->rule_id.get_solver_var(),
                                                        solver->createBVConst((int) node->infos->rules.size(),
                                                                              node->solver_state->rule_id.bv_size));
                emit_assumption(node, assumption);
            }

            void transition(tree &node) {
                emit_comment("Begin_transition_" + node->uid);
                apply_one_rule(node);
                for (int rule_id = 0; rule_id < node->infos->rules.size(); ++rule_id) {
                    simulate_rule(node, rule_id);
                }
                emit_comment("End_transition_" + node->uid);
            }

            // CHILDREN RELATED FUNCTIONS
            void set_skip(tree &node) {
                tmp_bool = tmp_bool.createFrom();
                TExpr skip_child_value = tmp_bool.get_solver_var();

                for (auto &&w_ancestor :node->ancestors) {
                    tree ancestor = w_ancestor.lock();
                    skip_child_value = solver->createOrExpr(skip_child_value,
                                                            ancestor->solver_state->skip.get_solver_var());
                }

                strict_emit_assignment(node->solver_state->skip, skip_child_value);
                strict_emit_assignment(node->solver_state->guard,
                                       solver->createNotExpr(node->solver_state->skip.get_solver_var()));
            }

            void update_var_blocked_by_child(tree &node, tree &child) {
                variable child_applied = child->solver_state->guard;
                for (int i = 0; i < node->solver_state->blocked.size(); ++i) {
                    variable old_blocked_node_i = node->solver_state->blocked[i];
                    TExpr is_right_target = solver->createEqExpr(child->solver_state->var_id.get_solver_var(),
                                                                 solver->createBVConst(i,
                                                                                       child->solver_state->var_id.bv_size));

                    TExpr should_apply = solver->createAndExpr(child_applied.get_solver_var(),
                                                               is_right_target);

                    TExpr new_blocked_value_i = solver->createCondExpr(should_apply,
                                                                       one,
                                                                       old_blocked_node_i.get_solver_var());

                    variable new_blocked_node_i = old_blocked_node_i.createFrom();
                    emit_assignment(node, new_blocked_node_i, new_blocked_value_i);
                    node->solver_state->blocked[i] = new_blocked_node_i;
                }
            }

            void simulate_child(tree &node, tree &child) {
                set_empty_node_state(child);

                copy_mask(child, node->solver_state->vars, child->solver_state->vars);
                copy_mask(child, node->solver_state->blocked, child->solver_state->blocked);

                set_skip(child);

                subrun(child);

                cond_save_mask(node, child->solver_state->vars,
                               node->solver_state->vars,
                               child->solver_state->guard.get_solver_var());
                cond_save_ored_mask(node,
                                    node->solver_state->updated_in_subrun,
                                    child->solver_state->updated_in_subrun,
                                    node->solver_state->updated_in_subrun,
                                    child->solver_state->guard.get_solver_var());

                update_var_blocked_by_child(node, child);
            }

            void simulate_children(tree &node) {
                for (auto &&child :node->refinement_blocks) {
                    emit_comment("Begin_child_" + child->uid + "_simulation");
                    simulate_child(node, child);
                    emit_comment("End_child_" + child->uid + "_simulation");
                }
            }

            // EXPLORATION_STRATEGY RELATED FUNCTIONS
            TExpr es_skipped_last_child(tree &node) {
                if (node->refinement_blocks.empty()) {
                    throw unexpected_error("exploration_strategy cannot be called on leaves");
                }
                std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> w_last_child = node->refinement_blocks.back();
                variable last_skip = w_last_child.lock()->solver_state->skip;

                TExpr skipped = last_skip.get_solver_var();

                TExpr all_set = one;

                for (int i = 0; i < node->solver_state->updated_in_subrun.size(); ++i) {
                    variable updated_in_subrun_node_i = node->solver_state->updated_in_subrun[i];
                    variable blocked_node_i = node->solver_state->blocked[i];

                    TExpr upd_impl_block_node_i = solver->createImplExpr(updated_in_subrun_node_i.get_solver_var(),
                                                                         blocked_node_i.get_solver_var());

                    all_set = solver->createAndExpr(all_set, upd_impl_block_node_i);
                }

                TExpr final_impl = solver->createAndExpr(skipped, all_set);

                return final_impl;
            }

            TExpr var_not_in_priority_and_set(tree &node, int idx) {
                variable rule_id_node = node->solver_state->rule_id;

                //THIS CREATES A BIG OR ON THE SET OF RULES OF (RULE_ID_NODE = R.ID)
                TExpr in_priority_node = zero;
                for (int i = 0; i < node->infos->rules.size(); ++i) {
                    rulep &rule = node->infos->rules[i];
                    if (contains(rule->prec->atoms(), policy->atoms(idx))) {
                        TExpr rule_cond = solver->createEqExpr(rule_id_node.get_solver_var(),
                                                               solver->createBVConst(i, rule_id_node.bv_size));
                        in_priority_node = solver->createOrExpr(in_priority_node,
                                                                rule_cond);
                    }
                }

                //THIS CREATES A BIG OR ON THE SET OF CHILDREN TARGETS (!SKIP_CHILD /\ (IDX = VAR_ID_CHILD))
                TExpr set_by_children = zero;
                for (std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> &&w_child :node->refinement_blocks) {
                    auto child = w_child.lock();
                    TExpr var_idx = solver->createBVConst(idx, node->solver_state->var_id.bv_size);
                    TExpr var_id_child = child->solver_state->var_id.get_solver_var();
                    TExpr not_skip_child = solver->createNotExpr(child->solver_state->skip.get_solver_var());
                    TExpr is_set_by_child = solver->createAndExpr(not_skip_child,
                                                                  solver->createEqExpr(var_idx, var_id_child));
//                                                                  solver->createAndExpr(var_idx, var_id_child));
                    set_by_children = solver->createOrExpr(set_by_children,
                                                           is_set_by_child);
                }

                TExpr not_in_priority = solver->createNotExpr(in_priority_node);

                TExpr not_in_priority_and_set_cond = solver->createAndExpr(not_in_priority, set_by_children);

                return not_in_priority_and_set_cond;
            }

            TExpr all_priority_set(tree &node) {
                variable rule_id_node = node->solver_state->rule_id;
                TExpr global_priority_set = one;
                // in_priority_i ==> updated_in_subrun_i ==> blocked_i
                for (int i = 0; i < node->solver_state->updated_in_subrun.size(); ++i) {
                    //IN_PRIORITY_i
                    TExpr in_priority_node = zero;
                    for (int j = 0; j < node->infos->rules.size(); ++j) {
                        rulep &rule = node->infos->rules[j];
                        if (contains(rule->prec->atoms(), policy->atoms(i))) {
                            TExpr rule_cond = solver->createEqExpr(rule_id_node.get_solver_var(),
                                                                   solver->createBVConst(j, rule_id_node.bv_size));
                            in_priority_node = solver->createOrExpr(in_priority_node,
                                                                    rule_cond);
                        }
                    }

                    variable updated_in_subrun_node_i = node->solver_state->updated_in_subrun[i];
                    variable blocked_node_i = node->solver_state->blocked[i];

                    TExpr priority_updated_must_be_set_i =
                            solver->createImplExpr(in_priority_node,
                                                   solver->createImplExpr(updated_in_subrun_node_i.get_solver_var(),
                                                                          blocked_node_i.get_solver_var()));

                    global_priority_set = solver->createAndExpr(global_priority_set,
                                                                priority_updated_must_be_set_i);
                }

                return global_priority_set;
            }

            TExpr if_not_in_p_set_then_p_is_set(tree &node) {
                TExpr exists_not_in_priority_set = zero;
                for (int i = 0; i < node->solver_state->blocked.size(); ++i) {
                    TExpr not_in_priority_and_set_i = var_not_in_priority_and_set(node, i);
//                    log->warn("Atom {} -------------------------------", *policy->atoms(i));
//                    solver->printExpr(not_in_priority_and_set_i);
                    exists_not_in_priority_set = solver->createOrExpr(exists_not_in_priority_set,
                                                                      not_in_priority_and_set_i);
                }

                TExpr priority_is_set = all_priority_set(node);

                TExpr if_not_in_p_set_then_p_is_set = solver->createImplExpr(exists_not_in_priority_set,
                                                                             priority_is_set);
                return if_not_in_p_set_then_p_is_set;
            }

            TExpr if_not_in_p_set_then_p_is_set_root(tree &node) {
                // HERE I STATICALLY KNOW THE PRIORITY
                const std::set<atomp>& priority = node->infos->invariant->atoms();
                TExpr exists_not_in_priority_set = zero;

                for (auto &&atom : policy->atoms()) {
                    if (!contains(priority, atom)) {
                        variable atom_updated_in_subrun = node->solver_state->updated_in_subrun[atom->role_array_index];
                        variable atom_blocked = node->solver_state->blocked[atom->role_array_index];
                        TExpr not_in_priority_and_set_i = solver->createAndExpr(atom_updated_in_subrun.get_solver_var(),
                                                                                atom_blocked.get_solver_var());
                        exists_not_in_priority_set = solver->createOrExpr(exists_not_in_priority_set,
                                                                          not_in_priority_and_set_i);
                    }
                }

//                TExpr priority_is_set = all_priority_set(node);
                TExpr priority_is_set = one;
                for (auto &&atom : priority) {
                    variable atom_updated_in_subrun = node->solver_state->updated_in_subrun[atom->role_array_index];
                    variable atom_blocked = node->solver_state->blocked[atom->role_array_index];
                    TExpr updated_atom_is_set = solver->createImplExpr(atom_updated_in_subrun.get_solver_var(),
                                                                       atom_blocked.get_solver_var());
                    priority_is_set = solver->createAndExpr(priority_is_set,
                                                            updated_atom_is_set);
                }

                TExpr if_not_in_p_set_then_p_is_set = solver->createImplExpr(exists_not_in_priority_set,
                                                                             priority_is_set);
                return if_not_in_p_set_then_p_is_set;
            }

            TExpr not_skipped_last_child(tree &node) {
                if (node->refinement_blocks.empty()) {
                    throw unexpected_error("exploration_strategy cannot be called on leaves");
                }
                std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> w_last_child = node->refinement_blocks.back();
                variable last_skip = w_last_child.lock()->solver_state->skip;
                TExpr budget_expired = solver->createNotExpr(last_skip.get_solver_var());

                TExpr if_not_in_p_set_then_p_is_set_val = zero;

                //FIXME: Consider removing this
                if(node->is_root()) {
                    if_not_in_p_set_then_p_is_set_val = if_not_in_p_set_then_p_is_set_root(node);
                } else {
                    if_not_in_p_set_then_p_is_set_val = if_not_in_p_set_then_p_is_set(node);
                }

                TExpr final_cond = solver->createAndExpr(budget_expired, if_not_in_p_set_then_p_is_set_val);

                return final_cond;
            }

            void exploration_strategy(tree &node) {
                TExpr if_skipped = es_skipped_last_child(node);
//                log->warn("If Skipped----------------------------------------------------------------");
//                solver->printExpr(if_skipped);

//                log->warn("NOT SKIPPED-----------------------------------------------------------------");
                TExpr if_budget = not_skipped_last_child(node);
//                solver->printExpr(if_budget);


                TExpr global_assumption = solver->createOrExpr(if_skipped, if_budget);


                emit_assumption(node, global_assumption);
            }

            // SUBRUN FUNCTION
            void subrun(tree &node) {
                emit_comment("Begin_subrun_" + node->uid);
                set_zero(node->solver_state->updated_in_subrun);
                if (node->is_leaf()) {//Is_leaf(n)
                    emit_comment("Node_" + node->uid + "is_leaf");
                    update_unblocked_vars(node);
                    if (!node->is_root()) {
                        transition(node);
                    }
//                    return;
                } else {
                    emit_comment("Node_" + node->uid + "_is_internal");
                    simulate_children(node);
                    emit_comment("Begin_exploration_strategy_" + node->uid);
                    exploration_strategy(node);
                    emit_comment("End_exploration_strategy_" + node->uid);
                    if (!node->is_root()) {
                        transition(node);
                    }
//                    return;
                }
                emit_comment("End_subrun_" + node->uid);
            }

            // ROOT SUBRUN RELATED FUNCTIONS
            void do_not_skip_root(tree &root) {
                variable skip_root = root->solver_state->skip;
                variable root_guard = root->solver_state->guard;

                strict_emit_assignment(skip_root, zero);
                strict_emit_assignment(root_guard, one);
            }

            void init_root_vars(tree &root,
                                const std::set<userp, std::function<bool(const userp &, const userp &)>> &initial_confs) {
                TExpr init_expr = zero;
                for (auto &&conf : initial_confs) {
                    TExpr conf_expr = one;
                    for (auto &&atom : policy->atoms()) {
                        TExpr init_value = contains(conf->config(), atom) ? one : zero;
                        variable root_var = root->solver_state->vars[atom->role_array_index];
                        TExpr value_saved = solver->createEqExpr(root_var.get_solver_var(), init_value);
                        conf_expr = solver->createAndExpr(conf_expr, value_saved);
                    }
                    init_expr = solver->createOrExpr(init_expr,
                                                     conf_expr);
                }
                emit_assumption(root, init_expr);
            }

            void assert_invariant(tree &node) {
                TExpr invariant_expr = generateSMTFunction(solver,
                                                           node->infos->invariant,
                                                           node->solver_state->vars,
                                                           "");
                assertions.push_back(invariant_expr);
            }

            void root_subrun(tree &root,
                             const std::set<userp, std::function<bool(const userp &, const userp &)>> &initial_confs) {
                set_empty_node_state(root);
                do_not_skip_root(root);

                emit_comment("Variable_initialization");
                init_root_vars(root, initial_confs);

                assert_invariant(root);
                set_zero(root->solver_state->blocked);
                subrun(root);
                assert_invariant(root);
            }

            void add_assertions() {
                TExpr final_assertion = zero;
                for (auto &&assertion : assertions) {
                    final_assertion = solver->createOrExpr(final_assertion,
                                                           assertion);
                }
                solver->assertLater(final_assertion);
            }

            bool is_reachable(tree &root,
                              const std::set<userp, std::function<bool(const userp &, const userp &)>> &initial_confs) {
                emit_comment("root_subrun");
                root_subrun(root, initial_confs);
                emit_comment("root_assertion");
                add_assertions();

                auto start = std::chrono::high_resolution_clock::now();

                if (Config::show_solver_statistics) {
                    solver->print_statistics();
                }

                if (!std::is_same<term_t, TExpr>::value && Config::dump_smt_formula != "") {
                    solver->printContext(Config::dump_smt_formula);
                    log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
                }

                SMTResult res = solver->solve();

                if (std::is_same<term_t, TExpr>::value && Config::dump_smt_formula != "") {
                    solver->printContext(Config::dump_smt_formula);
                    log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
                    if (res == SAT) {
                        solver->printModel();
                    }
                }

                auto end = std::chrono::high_resolution_clock::now();
                auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
                log->debug("------------ SMT SOLVED IN {} ms ------------", milliseconds.count());

                return res == SAT;
            }

            bool set_node_refinement_from_model(tree &node) {
                if (!node->is_leaf()) {
                    bool refineable_subtree = false;
                    for (auto &&child : node->refinement_blocks) {
                        refineable_subtree = set_node_refinement_from_model(child) || refineable_subtree;
                    }
                    return refineable_subtree;
                } else {
                    bool is_node_refineable = solver->get_bool_value(node->solver_state->refineable.get_solver_var());
                    node->infos->solverInfo->refineable = is_node_refineable ? b_solver_info::YES : b_solver_info::NO;
                    if (is_node_refineable) {
                        log->warn("Node {} is refineable", node->uid);
                    }
                    return is_node_refineable;
                }
            }

            bool anotate_refineable(tree &root) {
                return set_node_refinement_from_model(root);
            }

            void initialize() {
                tmp_bool = variable("tmp_bool", 0, 1, solver.get(), BOOLEAN);
                zero = solver->createBoolConst(0);
                one = solver->createBoolConst(1);
            }

        public:

            tree_to_SMT(const std::shared_ptr<arbac_policy> _policy,
                        std::shared_ptr<SMTFactory<TVar, TExpr>> _solver) :
                    policy(_policy),
                    solver(_solver),
                    assertions(std::list<TExpr>()) { }

            over_analysis_result translate_and_run(tree &root,
                                                   const std::set<userp, std::function<bool(const userp &, const userp &)>> &initial_confs) {
                solver->deep_clean();
                initialize();
                bool result = is_reachable(root, initial_confs);
                if (result) {
                    bool is_refineable = anotate_refineable(root);
                    if (!is_refineable) {
                        return UNSAFE;
                    } else {
                        return UNSAFE_REFINEABLE;
                    }
                } else {
                    return SAFE;
                }
            }

        };

        const OverapproxOptions overapprox_strategy;

        std::shared_ptr<b_solver_info> get_empty_solver_info() {
            b_solver_info ret_body;
            ret_body.refineable = b_solver_info::UNSET;
            return std::make_shared<b_solver_info>(ret_body);
        }

        int get_budget() {
            switch (overapprox_strategy.blocks_strategy) {
                case OverapproxOptions::STRICT_BLOCK:
                    return overapprox_strategy.blocks_count;
                    break;
                case OverapproxOptions::AT_MOST_BLOCK:
                    return 1;
                    break;
                case OverapproxOptions::AT_LEAST_BLOCK:
                    return overapprox_strategy.blocks_count;
                    break;
                default:
                    throw unexpected_error("missing cases in switch on overapprox_strategy.blocks_strategy");
            }
        }

        void tree_clean_solver_info_state(tree& node) {
            node->solver_state = nullptr;
            node->infos->solverInfo->refineable = b_solver_info::UNSET;
            for (auto &&child :node->refinement_blocks) {
                tree_clean_solver_info_state(child);
            }
        }

        bool refine_tree(std::shared_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>>& _node) {
            if (!_node->is_leaf()) {
                bool changed = false;
                for (auto &&child :_node->refinement_blocks) {
                    changed = refine_tree(child) || changed;
                }
                return changed;
            } else if (overapprox_strategy.depth_strategy == OverapproxOptions::AT_MOST_DEPTH &&
                    _node->depth >= overapprox_strategy.depth) {
                return false;
            } else {
                if (_node->infos->solverInfo->refineable == b_solver_info::YES) {
                    int i = 0;
                    tree_path first_path = _node->path;
                    first_path.push_back(i);
                    simple_block_info<b_solver_info> root_info(_node->infos->policy,
                                                               _node->infos->rules,
                                                               get_empty_solver_info(),
                                                               createConstantTrue());
                    std::list<std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>>> prec_ancestors = _node->ancestors;
                    prec_ancestors.push_back(_node);
                    node actual_child(first_path,
                                      _node->depth + 1,
                                      std::make_shared<simple_block_info<b_solver_info>>(root_info),
                                      prec_ancestors);
                    tree last_inserted_child = std::make_shared<node>(actual_child);
                    _node->refinement_blocks.push_back(last_inserted_child);

                    int budget = get_budget();
                    for (++i; i < budget; ++i) {
                        first_path = _node->path;
                        first_path.push_back(i);
                        simple_block_info<b_solver_info> act_info(_node->infos->policy,
                                                                  _node->infos->rules,
                                                                  get_empty_solver_info(),
                                                                  createConstantTrue());
                        prec_ancestors = last_inserted_child->ancestors;
                        prec_ancestors.push_back(last_inserted_child);
                        actual_child = node(first_path,
                                            _node->depth + 1,
                                            std::make_shared<simple_block_info<b_solver_info>>(act_info),
                                            prec_ancestors);
                        last_inserted_child = std::make_shared<node>(actual_child);
                        _node->refinement_blocks.push_back(last_inserted_child);
                    }
                    return true;
                } else {
                    return false;
                }
            }
        }

        tree create_tree_root(const std::shared_ptr<arbac_policy>& policy,
                              const Expr& to_check) {
            node root("root", 0);

            simple_block_info<b_solver_info> root_info(policy, policy->rules(), get_empty_solver_info(), to_check);

            root.infos = std::make_shared<simple_block_info<b_solver_info>>(root_info);

            tree ret = std::make_shared<node>(root);

            return ret;
        }

    public:

        explicit learning_overapprox(OverapproxOptions strategy):
                overapprox_strategy(strategy) { }

        bool operator()(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                        const std::shared_ptr<arbac_policy>& policy,
                        const Expr& to_check) {

            bool completed = false;

            tree proof = create_tree_root(policy, to_check);

            while (!completed) {
                tree_to_SMT translator(policy, solver);

                over_analysis_result result =
                        translator.translate_and_run(proof, policy->unique_configurations());

                switch (result) {
                    case SAFE:
                        log->info("Target role is not reachable");
                        completed = true;
                        return false;
                        break;
                    case UNSAFE:
                        log->info("Target role may be reachable (but proof is not refineable)");
                        completed = true;
                        return true;
                        break;
                    case UNSAFE_REFINEABLE:
                        log->info("Target role may be reachable... REFINING");
                        bool changed = refine_tree(proof);
                        tree_clean_solver_info_state(proof);
                        if (!changed) {
                            log->info("Givin up refinement...");
                            completed = true;
                            return true;
                        }
                        break;
                }
            }
            throw unexpected_error("While loop should converge at some point!");
        }

    };

    template <typename TVar, typename TExpr>
    bool overapprox_learning(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                            const std::shared_ptr<arbac_policy>& policy,
                            const Expr& to_check) {
        OverapproxOptions strategy = {
            .version = OverapproxOptions::LEARNING,
            .depth_strategy = OverapproxOptions::AT_MOST_DEPTH,
            .depth = Config::overapproxOptions.depth,
            .blocks_strategy = OverapproxOptions::AT_LEAST_BLOCK,
            .blocks_count = -1,
        };
        learning_overapprox<TVar, TExpr> overapprox(strategy);
        return overapprox(solver, policy, to_check);
    }

    template bool overapprox_learning<term_t, term_t>(const std::shared_ptr<SMTFactory<term_t, term_t>>& solver,
                                                     const std::shared_ptr<arbac_policy>& policy,
                                                     const Expr& to_check);

    template bool overapprox_learning<expr, expr>(const std::shared_ptr<SMTFactory<expr, expr>>& solver,
                                                 const std::shared_ptr<arbac_policy>& policy,
                                                 const Expr& to_check);

    template bool overapprox_learning<BoolectorExpr, BoolectorExpr>(const std::shared_ptr<SMTFactory<BoolectorExpr, BoolectorExpr>>& solver,
                                                                   const std::shared_ptr<arbac_policy>& policy,
                                                                   const Expr& to_check);

    template bool overapprox_learning<msat_term, msat_term>(const std::shared_ptr<SMTFactory<msat_term, msat_term>>& solver,
                                                           const std::shared_ptr<arbac_policy>& policy,
                                                           const Expr& to_check);


}