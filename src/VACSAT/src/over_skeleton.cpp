//
// Created by esteffin on 12/5/17.
//

#include "over_skeleton.h"
#include "prelude.h"
#include "SMT_BMC_Struct.h"
#include "SMTSolvers/Z3.h"

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
    class tree_to_SMT {
    private:

        typedef generic_variable<TVar, TExpr> variable;
        const std::shared_ptr<arbac_policy> policy;
        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;

        variable tmp_bool;
        TExpr zero;
        TExpr one;
//        const bool use_admin;

        class b_solver_info;
        class b_solver_state;

        typedef std::shared_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> tree;


        class b_solver_info {
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

            void init(SMTFactory<TVar, TExpr>* solver, const tree& node) {
                for (auto &&atom : node->infos->policy->atoms()) {
                    std::string var_name = "var_" + node_id;
                    vars[atom->role_array_index] = variable(var_name, 0, 1, solver, BOOLEAN);

                    std::string updated_in_subrun_name = "updated_in_subrun_" + node_id;
                    updated_in_subrun[atom->role_array_index] = variable(updated_in_subrun_name, 0, 1, solver, BOOLEAN);

                    std::string blocked_name = "blocked_" + node_id;
                    blocked[atom->role_array_index] = variable(blocked_name, 0, 1, solver, BOOLEAN);
                }

                var_id = variable("var_id_" + node_id, 0, bits_count(node->infos->policy->atom_count()), solver, BIT_VECTOR);
                rule_id = variable("rule_id_" + node_id, 0, bits_count((uint) node->infos->rules.size()), solver, BIT_VECTOR);
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
            std::string& node_id;
            std::vector<variable> vars;
            std::vector<variable> updated_in_subrun;
            std::vector<variable> blocked;
            variable var_id;
            variable rule_id;
            variable skip;
            variable guard;
            variable refineable;

            b_solver_state() = delete;

            b_solver_state(tree& node,
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

        inline void strict_emit_assignment(const variable& var, const TVar& value) {
            TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
            solver->assertLater(ass);
        }
        inline void emit_assignment(const tree node, const variable& var, const TVar& value) {
            TExpr ass = solver->createEqExpr(var.get_solver_var(), value);
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            TExpr guarded_ass = solver->createImplExpr(node->solver_state->guard.get_solver_var(),
                                                       ass);
            solver->assertLater(guarded_ass);

        }
        inline void emit_assumption(const tree node, const TExpr& value) {
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            TExpr guarded_ass = solver->createImplExpr(node->solver_state->guard.get_solver_var(),
                                                       value);
            solver->assertLater(guarded_ass);
        }
        inline void emit_comment(const std::string& comment) {
            //Working automatically and only in Z3
            if (std::is_same<z3::expr, TExpr>::value) {
                solver->assertNow(solver->createBoolVar(comment));
                log->debug("Emitting comment: " + comment);
            }
        }

        void set_empty_node_state(tree& node) {
            assert(node->solver_state == nullptr);
            b_solver_state node_state = b_solver_state(node, solver.get());
            node->solver_state = std::make_shared<b_solver_state>(node_state);
        }

        void set_zero(std::vector<variable>& vars) {
            for (auto &&var : vars) {
                strict_emit_assignment(var, zero);
            }
        }

        void copy_mask(tree& node, std::vector<variable>& source, std::vector<variable>& dest) {
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
        void cond_save_mask(tree& node,
                            std::vector<variable>& source,
                            std::vector<variable>& dest,
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
        void cond_save_ored_mask(tree& node,
                                 std::vector<variable>& source1,
                                 std::vector<variable>& source2,
                                 std::vector<variable>& dest,
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
        TExpr get_variable_invariant_from_node(tree& node, const Atomp &var) {
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

        variable update_var(tree& node, const Atomp &var) {
            //GUARD FOR NONDET UPDATE
            tmp_bool = tmp_bool.createFrom();
            TExpr update_guard =
                    solver->createAndExpr(solver->createNotExpr(node->solver_state->blocked[var->role_array_index].get_solver_var()),
                                          tmp_bool.get_solver_var());
            emit_assignment(node, tmp_bool, update_guard);

            //VAR VALUE UPDATE
            variable old_var_val = node->solver_state->vars[var->role_array_index];
            variable new_var_val = node->solver_state->vars[var->role_array_index].create_from();
            TExpr guarded_val = solver->createCondExpr(tmp_bool.get_solver_var(),
                                                       new_var_val.get_solver_var(),
                                                       old_var_val.get_solver_var());
            emit_assignment(node, new_var_val, guarded_val);
            node->solver_state->vars[var->role_array_index] = new_var_val;

            //NEW VAR VALUE ASSUMPTIONS
            TExpr value_was_changed = solver->createNotExpr(solver->createEqExpr(old_var_val.get_solver_var(),
                                                                                 new_var_val.get_solver_var()));
            TExpr value_invariant = get_variable_invariant_from_node(node, var);
            TExpr assumption_body = solver->createImplExpr(tmp_bool,
                                                           solver->createAndExpr(value_was_changed,
                                                                                 value_invariant));
            emit_assumption(node, assumption_body);

            //SAVE THE FACT THAT THE VARIABLE HAS BEEN CHANGED
            variable old_updated_in_subrun = node->solver_state->updated_in_subrun[var->role_array_index];
            variable new_updated_in_subrun = node->solver_state->updated_in_subrun[var->role_array_index].create_from();
            TExpr new_updated_value = solver->createCondExpr(tmp_bool,
                                                             new_updated_in_subrun.get_solver_var(),
                                                             old_updated_in_subrun.get_solver_var());
            emit_assignment(node, new_updated_in_subrun, new_updated_value);

            //RETURN TO CREATE THE REFINEABLE CHECK
            return tmp_bool;
        }

        void save_refineable_condition(tree& node, std::list<variable>& update_guards) {
            TExpr not_skipping = solver->createNotExpr(node->solver_state->skip.get_solver_var());
            TExpr at_least_one_updated = solver->createFalse();
            for (auto &&update_guard : update_guards) {
                at_least_one_updated = solver->createOrExpr(at_least_one_updated,
                                                            update_guard);
            }

            //!SKIP && \/_{var} nondet_guard_var
            TExpr refineable = solver->createAndExpr(not_skipping,
                                                     at_least_one_updated);

            strict_emit_assignment(node->solver_state->refineable, refineable);
        }

        void update_unblocked_vars(tree& node) {
            std::list<variable> update_guards;
            for (auto &&var :policy->atoms()) {
                variable update_guard = update_var(node, var);
                update_guards.push_back(update_guard);
            }

            save_refineable_condition(node, update_guards);
        }

        // TRANS RELATED FUNCTIONS
        TExpr get_rule_assumptions(tree &node, int rule_id, TExpr& rule_is_selected) {
            rulep rule = node->infos->rules[rule_id];
            TExpr rule_precondition = generateSMTFunction(solver,
                                                          rule->prec,
                                                          node->solver_state->vars,
                                                          "");
            TExpr target_not_blocked =
                    solver->createNotExpr(node->solver_state->blocked[rule->target->role_array_index].get_solver_var());
            TExpr rule_target_value = rule->is_ca ? one : zero;
            TExpr target_is_changed =
                    solver->createNotExpr(
                            solver->createEqExpr(node->solver_state->vars[rule->target->role_array_index].get_solver_var(),
                            rule_target_value));
            //IF THE RULE IS SELECTED THEN ALL THE PRECONDITIONS MUST HOLDS
            TExpr final_assumption =
                    solver->createImplExpr(rule_is_selected,
                                           solver->createAndExpr(rule_precondition,
                                                                 solver->createAndExpr(target_not_blocked,
                                                                                       target_is_changed)));
            return final_assumption;
        }

        void apply_rule_effect(tree &node, int rule_id, TExpr& rule_is_selected) {
            rulep rule = node->infos->rules[rule_id];
            atomp target = rule->target;
            // UPDATE VAR VALUE
            variable old_var_var = node->solver_state->vars[target->role_array_index];
            variable new_var_var = node->solver_state->vars[target->role_array_index].create_from();
            TExpr rule_value = rule->is_ca ? one : zero;
            TExpr new_var_value = solver->createCondExpr(rule_is_selected,
                                                         rule_value,
                                                         old_var_var.get_solver_var());
            emit_assignment(node, new_var_var, new_var_value);
            node->solver_state->vars[target->role_array_index] = new_var_var;

            // UPDATE UPDATED_IN_SUBRUN VALUE
            variable old_updated_in_subrun_var = node->solver_state->updated_in_subrun[target->role_array_index];
            variable new_updated_in_subrun_var = node->solver_state->updated_in_subrun[target->role_array_index].create_from();
            TExpr new_updated_value = solver->createCondExpr(rule_is_selected,
                                                             one,
                                                             old_updated_in_subrun_var.get_solver_var());
            emit_assignment(node, new_updated_in_subrun_var, new_updated_value);
            node->solver_state->vars[target->role_array_index] = new_updated_in_subrun_var;

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

        void simulate_rule(tree& node, int rule_id) {
            TExpr rule_is_selected =
                    solver->createEqExpr(node->solver_state->rule_id.get_solver_var(),
                                         solver->createBVConst(rule_id, node->solver_state->rule_id.bv_size));

            TExpr rule_assumptions = get_rule_assumptions(node, rule_id, rule_is_selected);

            apply_rule_effect(node, rule_id, rule_is_selected);
        }

        void apply_one_rule(tree& node) {
            //TO BE SURE TO APPLY AT LEAST ONE RULE WE HAVE TO ASSUME THAT RULE_ID <= RULE_COUNT
            TExpr assumption = solver->createLtExpr(node->solver_state->rule_id.get_solver_var(),
                                                    solver->createBVConst((int) node->infos->rules.size(),
                                                                          node->solver_state->rule_id.bv_size));
            emit_assumption(node, assumption);
        }

        void transition(tree& node) {
            apply_one_rule(node);
            for (int rule_id = 0; rule_id < node->infos->rules.size(); ++rule_id) {
                simulate_rule(node, rule_id);
            }
        }

        // CHILDREN RELATED FUNCTIONS
        void set_skip(tree& node) {
            tmp_bool = tmp_bool.createFrom();
            TExpr skip_child_value = tmp_bool;

            for (std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> &&w_ancestor :node->ancestors) {
                tree ancestor = w_ancestor.lock();
                skip_child_value = solver->createOrExpr(skip_child_value, ancestor->solver_state->skip.get_solver_var());
            }

            strict_emit_assignment(node->solver_state->skip, skip_child_value);
            strict_emit_assignment(node->solver_state->guard,
                                   solver->createNotExpr(node->solver_state->skip.get_solver_var()));
        }

        void update_var_blocked_by_child(tree& node, tree& child) {
            variable child_applied = child->solver_state->guard;
            for (int i = 0; i < node->solver_state->blocked.size(); ++i) {
                variable old_blocked_node_i = node->solver_state->blocked[i];
                TExpr is_right_target = solver->createEqExpr(child->solver_state->var_id.get_solver_var(),
                                                             solver->createBVConst(i, child->solver_state->var_id.bv_size));

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

        void simulate_child(tree& node, tree& child) {
            set_empty_node_state(child);

            copy_mask(child, node->solver_state->vars, child->solver_state->vars);
            copy_mask(child, node->solver_state->blocked, child->solver_state->blocked);

            set_skip(child);

            subrun(child);

            cond_save_mask(node, child->solver_state->vars, node->solver_state->vars, child->solver_state->guard);
            cond_save_ored_mask(node,
                                node->solver_state->updated_in_subrun,
                                child->solver_state->updated_in_subrun,
                                node->solver_state->updated_in_subrun,
                                child->solver_state->guard);

            update_var_blocked_by_child(node, child);
        }

        void simulate_children(tree& node) {
            for (auto &&child :node->refinement_blocks) {
                simulate_child(node, child);
            }
        }

        // EXPLORATION_STRATEGY RELATED FUNCTIONS
        TExpr es_skipped_last_child(tree& node) {
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

            TExpr final_impl = solver->createImplExpr(skipped, all_set);

            return final_impl;
        }

        TExpr var_not_in_priority_and_set(tree& node, int idx) {
            variable rule_id_node = node->solver_state->rule_id;

            //THIS CREATES A BIG OR ON THE SET OF RULES OF (RULE_ID_NODE = R.ID)
            TExpr in_priority_node = zero;
            for (int i = 0; i < node->infos->rules.size(); ++i) {
                rulep& rule = node->infos->rules[i];
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
                                                              solver->createAndExpr(var_idx, var_id_child));
                set_by_children = solver->createOrExpr(set_by_children,
                                                       is_set_by_child);
            }

            TExpr not_in_priority = solver->createNotExpr(in_priority_node);

            TExpr not_in_priority_and_set_cond = solver->createAndExpr(not_in_priority, set_by_children);

            return not_in_priority_and_set_cond;
        }

        TExpr all_priority_set(tree& node) {
            variable rule_id_node = node->solver_state->rule_id;
            TExpr global_priority_set = one;
            // in_priority_i ==> updated_in_subrun_i ==> blocked_i
            for (int i = 0; i < node->solver_state->updated_in_subrun.size(); ++i) {
                //IN_PRIORITY_i
                TExpr in_priority_node = zero;
                for (int j = 0; j < node->infos->rules.size(); ++j) {
                    rulep& rule = node->infos->rules[j];
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

        TExpr if_not_in_p_set_then_p_is_set(tree& node) {
            TExpr exists_not_in_priority_set = zero;
            for (int i = 0; i < node->solver_state->blocked.size(); ++i) {
                TExpr not_in_priority_and_set_i = var_not_in_priority_and_set(node, i);
                exists_not_in_priority_set = solver->createOrExpr(exists_not_in_priority_set, not_in_priority_and_set_i);
            }

            TExpr priority_is_set = all_priority_set(node);

            TExpr if_not_in_p_set_then_p_is_set = solver->createImplExpr(exists_not_in_priority_set, priority_is_set);
            return if_not_in_p_set_then_p_is_set;
        }

        TExpr not_skipped_last_child(tree& node) {
            if (node->refinement_blocks.empty()) {
                throw unexpected_error("exploration_strategy cannot be called on leaves");
            }
            std::weak_ptr<gblock<simple_block_info<b_solver_info>, b_solver_state>> w_last_child = node->refinement_blocks.back();
            variable last_skip = w_last_child.lock()->solver_state->skip;
            TExpr budget_expired = solver->createNotExpr(last_skip.get_solver_var());

            TExpr if_not_in_p_set_then_p_is_set_val = if_not_in_p_set_then_p_is_set(node);

            TExpr final_cond = solver->createImplExpr(budget_expired, if_not_in_p_set_then_p_is_set_val);

            return final_cond;
        }

        void exploration_strategy(tree& node) {
            TExpr if_skipped = es_skipped_last_child(node);

            TExpr if_budget = not_skipped_last_child(node);


            TExpr global_assimption = solver->createOrExpr(if_skipped, if_budget);

            emit_assumption(node, global_assimption);
        }

        void subrun(tree& node) {
            set_zero(node->solver_state->updated_in_subrun);
            if (node->is_leaf()) {//Is_leaf(n)
                update_unblocked_vars(node);
                TExpr var_id_value = transition(node);
                return;
            } else {
                simulate_children(node);
                exploration_strategy(node);
                transition(node);
            }
        }

        void root_subrun(tree& root) {
            set_empty_node_state(root);

//            skip_root = false
//            Init(var_root)
//                    assert(invariant(var_root))
//            Set0(var_blocked_root);
//            assume( [[subrun(root, skip_root)]] )
//                    assert(invariant(var_root))
        }


        void initialize() {
            tmp_bool = variable("tmp_bool", 0, 1, solver.get(), BOOLEAN);
            zero = solver->createBoolConst(0);
            one = solver->createBoolConst(1);
        }

    public:



    };

}