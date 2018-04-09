//#include "ARBACExact.h"
#include <ctime>
#include <vector>
#include <iostream>
#include <string>
#include <sstream>
#include <memory>

#include "SMT.h"
#include "SMT_Analysis_functions.h"
#include "Logics.h"
#include "SMT_BMC_Struct.h"
#include "Policy.h"

#include <chrono>
#include <stack>

namespace SMT {

class AdminOverapproxTransformer {
    private:

    enum LayerOrBlock {
        LAYER,
        BLOCK
    };

    enum AdminOrTarget {
        ADMIN,
        TARGET
    };

    std::string AoTToString(AdminOrTarget aot) {
        return aot == ADMIN ? "Admin" : "Target";
    }

    std::string LoBToString(LayerOrBlock lob) {
        return lob == LAYER ? "Layer" : "Block";
    }

    struct RoleChoicer {
        enum Choice {
            REQUIRED,
            FREE,
            EXCLUDED
        };

        const std::shared_ptr<arbac_policy>& policy;

        explicit RoleChoicer(const std::shared_ptr<arbac_policy>& _policy) :
                policy(_policy) { }

        Choice classify(atomp r, AdminOrTarget aot) const {
//            if (r->name == "r1" || r->name == "r2") {
//                return REQUIRED;
//            }

            return FREE;
        }

        int get_required_count(AdminOrTarget aot) const {
            int count = 0;
            for (auto &&atom :policy->atoms()) {
                if (classify(atom, aot) == REQUIRED) {
                    count++;
                }
            }
            return count;
        }

    };

    typedef generic_variable variable;

    static int get_bit_count_for_choices(int pc) {
        int i = 1, bit = 0;

        if (pc < 2 ) return 1;

        while (pc > i) {
            i = i * 2;
            bit++;
        }

        return (bit);
    }

    static std::pair<int, int> get_pc_size_max_value(const std::shared_ptr<arbac_policy>& policy,
                                                     const std::set<Atomp>& tracked_atoms) {
        int count = 1;

        for (auto &&atom : tracked_atoms) {
            for (auto &&rule : policy->rules()) {
                if (rule->target == atom) {
                    count++;
                }
            }
        }
        int bits = get_bit_count_for_choices(count);
        return { bits, count - 1 };
    }

    struct overapprox_status;
    class variables {
        friend struct overapprox_status;
    private:
        variable guard;
    public:
        /*const*/ std::vector<variable> layer_admin_role_tracked;

        /*const*/ std::vector<variable> layer_user_role_tracked;

        /*const*/ std::vector<variable> selected_admin_role_vars;
        /*const*/ std::vector<variable> selected_admin_role_changed;
        /*const*/ std::vector<variable> selected_admin_role_sets;
//        /*const*/ std::vector<variable> block_admin_role_tracked;

        /*const*/ std::vector<variable> selected_user_role_vars;
        /*const*/ std::vector<variable> selected_user_role_changed;
        /*const*/ std::vector<variable> selected_user_role_sets;
//        /*const*/ std::vector<variable> block_user_role_tracked;

        /*const*/ std::vector<std::vector<variable>> all_role_vars;
        /*const*/ std::vector<std::vector<variable>> all_role_changed;
        /*const*/ std::vector<std::vector<variable>> all_role_sets;
//        /*const*/ std::vector<std::vector<variable>> all_role_tracked;

        variable layer_admin_idx;
        variable layer_target_idx;
        variable block_admin_idx;
        variable block_target_idx;
        variable program_counter;
        variable skip;
        variable update_guard;
        variable nondet_bool;

        variables() = default;

        variables(std::shared_ptr<arbac_policy> policy,
                  SMTFactory* solver,
                  int users_count,
                  const std::vector<bool>& interesting_roles) :
//                layer_admin_role_vars(std::vector<variable>((unsigned long) policy->atom_count())),
//                layer_admin_role_changed(std::vector<variable>((unsigned long) policy->atom_count())),
//                layer_admin_role_sets(std::vector<variable>((unsigned long) policy->atom_count())),
                layer_admin_role_tracked(std::vector<variable>((unsigned long) policy->atom_count())),
//                layer_user_role_vars(std::vector<variable>((unsigned long) policy->atom_count())),
//                layer_user_role_changed(std::vector<variable>((unsigned long) policy->atom_count())),
//                layer_user_role_sets(std::vector<variable>((unsigned long) policy->atom_count())),
                layer_user_role_tracked(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_admin_role_vars(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_admin_role_changed(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_admin_role_sets(std::vector<variable>((unsigned long) policy->atom_count())),
//                selected_admin_role_tracked(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_user_role_vars(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_user_role_changed(std::vector<variable>((unsigned long) policy->atom_count())),
                selected_user_role_sets(std::vector<variable>((unsigned long) policy->atom_count())),
//                selected_user_role_tracked(std::vector<variable>((unsigned long) policy->atom_count())),
                all_role_vars(std::vector<std::vector<variable>>((unsigned long) users_count)),
                all_role_changed(std::vector<std::vector<variable>>((unsigned long) users_count)),
                all_role_sets(std::vector<std::vector<variable>>((unsigned long) users_count)) {
            /*,
                all_role_tracked(std::vector<std::vector<variable>>((unsigned long) users_count))*/

            layer_admin_idx = variable("layer_admin_idx", -1, bits_count(users_count), solver, BIT_VECTOR);
            layer_target_idx = variable("layer_target_idx", -1, bits_count(users_count), solver, BIT_VECTOR);
            block_admin_idx = variable("block_admin_idx", -1, bits_count(users_count), solver, BIT_VECTOR);
            block_target_idx = variable("block_target_idx", -1, bits_count(users_count), solver, BIT_VECTOR);

            program_counter = variable("pc", -1, 1, solver, BIT_VECTOR);

            nondet_bool = variable("nondet_bool", -1, 1, solver, BOOLEAN);
            // fprintf(outputFile, "\n/*---------- SKIP CHECKS ---------*/\n");
            skip = variable("skip", 0, 1, solver, BOOLEAN);

            guard = variable("guard", 0, 1, solver, BOOLEAN);
            update_guard = variable("update_guard", 0, 1, solver, BOOLEAN);

            for (int i = 0; i < policy->atom_count(); i++) {
                if (interesting_roles[i]) {
                    // fprintf(outputFile, "/*---------- layer admin ROLE value ---------*/\n");
//                    layer_admin_role_vars[i] = variable("layer_admin_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer admin ROLE set ---------*/\n");
//                    layer_admin_role_sets[i] = variable(("layer_admin_set_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer admin ROLE changed ---------*/\n");
//                    layer_admin_role_changed[i] = variable(("layer_admin_changed_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer admin ROLE tracked ---------*/\n");
                    layer_admin_role_tracked[i] = variable(("layer_admin_tracked_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);

                    // fprintf(outputFile, "/*---------- layer user ROLE value ---------*/\n");
//                    layer_user_role_vars[i] = variable("layer_target_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer user ROLE set ---------*/\n");
//                    layer_user_role_sets[i] = variable(("layer_target_set_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer user ROLE changed ---------*/\n");
//                    layer_user_role_changed[i] = variable(("layer_target_changed_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- layer user ROLE tracked ---------*/\n");
                    layer_user_role_tracked[i] = variable(("layer_target_tracked_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);

                    // fprintf(outputFile, "/*---------- block admin ROLE value ---------*/\n");
                    selected_admin_role_vars[i] = variable("selected_admin_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block admin ROLE set ---------*/\n");
                    selected_admin_role_sets[i] = variable(("selected_admin_set_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block admin ROLE changed ---------*/\n");
                    selected_admin_role_changed[i] = variable(("selected_admin_changed_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block admin ROLE tracked ---------*/\n");
//                    selected_admin_role_tracked[i] = variable(("block_admin_tracked_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);

                    // fprintf(outputFile, "/*---------- block user ROLE value ---------*/\n");
                    selected_user_role_vars[i] = variable("selected_target_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block user ROLE set ---------*/\n");
                    selected_user_role_sets[i] = variable(("selected_target_set_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block user ROLE changed ---------*/\n");
                    selected_user_role_changed[i] = variable(("selected_target_changed_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    // fprintf(outputFile, "/*---------- block user ROLE tracked ---------*/\n");
//                    selected_user_role_tracked[i] = variable(("block_target_tracked_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                } else {
                    log->trace("Skipping atom: {}, since not interesting", *policy->atoms(i));
                }
            }

            for (int j = 0; j < users_count; ++j) {
                all_role_vars[j] = std::vector<variable>((unsigned long) policy->atom_count());
                all_role_changed[j] = std::vector<variable>((unsigned long) policy->atom_count());
                all_role_sets[j] = std::vector<variable>((unsigned long) policy->atom_count());
//                all_role_tracked[j] = std::vector<variable>((unsigned long) policy->atom_count());
                for (int i = 0; i < policy->atom_count(); i++) {
                    if (interesting_roles[i]) {
                        // fprintf(outputFile, "/*---------- ROLE value ---------*/\n");
                        all_role_vars[j][i] = variable("u_" + std::to_string(j) + "_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                        // fprintf(outputFile, "/*---------- ROLE set ---------*/\n");
                        all_role_changed[j][i] = variable("u_" + std::to_string(j) + "_set_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                        // fprintf(outputFile, "/*---------- ROLE changed ---------*/\n");
                        all_role_sets[j][i] = variable("u_" + std::to_string(j) + "_changed_" + policy->atoms()[i]->name, 0, 1, solver, BOOLEAN);
                        // fprintf(outputFile, "/*---------- ROLE tracked ---------*/\n");
//                        all_role_tracked[j][i] = variable((std::to_string(j) + "_tracked_" + policy->atoms()[i]->name), 0, 1, solver, BOOLEAN);
                    } else { }
                }
            }
        }
    };

    struct overapprox_infos {
    public:
        const Expr to_check;
        const std::vector<bool> interesting_roles;
        const int interesting_roles_count;
        const int user_count;
        const int pc_size;
        const int pc_max_value;

        overapprox_infos(const Expr _to_check,
                         const std::vector<bool> _interesting_roles,
                         const int _interesting_roles_count,
                         const int _user_count,
                         const int _pc_size,
                         const int _pc_max_value) :
                to_check(_to_check),
                interesting_roles(_interesting_roles),
                interesting_roles_count(_interesting_roles_count),
                user_count(_user_count),
                pc_size(_pc_size),
                pc_max_value(_pc_max_value) { }
    };

    struct overapprox_status {
        friend class variables;

        SMTFactory* solver;
        const std::shared_ptr<arbac_policy>& policy;
        /*--- VALUES ---*/
        variables state;
        std::vector<std::pair<std::pair<Expr, Expr>, int>> target_exprs;
        variable parent_pc;
        int blocks_to_do;

        const overapprox_infos infos;

        const RoleChoicer choicer;

        //// pc_max_value is the value from which we have to start skipping (inclusive)
        int deep;

        /*--- SAVED ---*/
        std::stack<variables> saved_state;
        std::stack<std::vector<std::pair<std::pair<Expr, Expr>, int>>> saved_target_exprs;
        std::stack<variable> saved_parent_pc;
        std::stack<int> saved_blocks_to_do;

        std::stack<int> saved_deep;

        void save_all() {
            // cloning and saving...
            variables old_state = state;
            saved_state.push(old_state);

            std::vector<std::pair<std::pair<Expr, Expr>, int>> old_target_exprs = target_exprs;
            saved_target_exprs.push(old_target_exprs);

            variable old_parent_pc = parent_pc;
            saved_parent_pc.push(old_parent_pc);

            int old_blocks_to_do = blocks_to_do;
            saved_blocks_to_do.push(blocks_to_do);

            int old_deep = deep;
            saved_deep.push(old_deep);
        }

        void restore_all_but_state() {
            // restoring and popping all but state...
            target_exprs = saved_target_exprs.top();
            saved_target_exprs.pop();

            variable old_parent_pc = parent_pc;
            saved_parent_pc.push(old_parent_pc);

            blocks_to_do = saved_blocks_to_do.top();
            saved_blocks_to_do.pop();

            deep = saved_deep.top();
            saved_deep.pop();
        }

        /*void update_conditionally() {
            //FIXME: really not necessary?
            for (auto &&item : state.role_changed) {

            }
        }*/

        void restore_state() {
            variables old_state = saved_state.top();

            //RESTORE GUARDS
            SMTExpr old_guard = old_state.guard.get_solver_var();
            SMTExpr frame_guard = state.guard.get_solver_var();
//            this->emit_assignment(new_guard, old_guard);

            variable new_guard = state.guard.createFrom();
            solver->assertLater(solver->createEqExpr(new_guard.get_solver_var(), old_guard));
            state.guard = new_guard;

            //RESTORE PC
            SMTExpr old_program_counter = old_state.program_counter.get_solver_var();
            variable new_program_counter = state.program_counter.createFrom();
//            this->emit_assignment(new_guard, old_guard);
            solver->assertLater(solver->createEqExpr(new_program_counter.get_solver_var(), old_program_counter));
            state.program_counter = new_program_counter;

            {
                //RESTORIE LAYER/BLOCK ADM/USER IDX
                SMTExpr old_block_adm_idx = old_state.block_admin_idx.get_solver_var();
                variable new_block_adm_idx = state.block_admin_idx.createFrom();
//            this->emit_assignment(new_guard, old_guard);
                solver->assertLater(solver->createEqExpr(new_block_adm_idx.get_solver_var(), old_block_adm_idx));
                state.block_admin_idx = new_block_adm_idx;

                SMTExpr old_block_target_idx = old_state.block_target_idx.get_solver_var();
                variable new_block_target_idx = state.block_target_idx.createFrom();
//            this->emit_assignment(new_guard, old_guard);
                solver->assertLater(solver->createEqExpr(new_block_target_idx.get_solver_var(), old_block_target_idx));
                state.block_target_idx = new_block_target_idx;

                SMTExpr old_layer_admin_idx = old_state.layer_admin_idx.get_solver_var();
                variable new_layer_admin_idx = state.layer_admin_idx.createFrom();
//            this->emit_assignment(new_guard, old_guard);
                solver->assertLater(solver->createEqExpr(new_layer_admin_idx.get_solver_var(), old_layer_admin_idx));
                state.layer_admin_idx = new_layer_admin_idx;

                SMTExpr old_layer_target_idx = old_state.layer_target_idx.get_solver_var();
                variable new_layer_target_idx = state.layer_target_idx.createFrom();
//            this->emit_assignment(new_guard, old_guard);
                solver->assertLater(solver->createEqExpr(new_layer_target_idx.get_solver_var(), old_layer_target_idx));
                state.layer_target_idx = new_layer_target_idx;
            }


            // RESTORING USERS OLD STEP SET STATE
            for (int j = 0; j < infos.user_count; ++j) {
                emit_comment("B: Updating user " + std::to_string(j));
                for (int i = 0; i < policy->atom_count(); ++i) {
                    if (infos.interesting_roles[i]) {
                        // SET: RESTORE OLD VALUE
                        SMTExpr old_set_state = old_state.all_role_sets[j][i].get_solver_var();
                        variable new_set_state = state.all_role_sets[j][i].createFrom();
                        this->emit_assignment(new_set_state, old_set_state);
                        state.all_role_sets[j][i] = new_set_state;

                        // CHANGED: UPDATE MEMORY WITH ITE ON GUARD
                        variable new_changed = state.all_role_changed[j][i].createFrom();
                        variable old_changed = old_state.all_role_changed[j][i];
                        SMTExpr new_changed_value =
                                solver->createCondExpr(frame_guard,
                                                       solver->createOrExpr(old_changed.get_solver_var(),
                                                                            state.all_role_changed[j][i].get_solver_var()),
                                                       old_changed.get_solver_var());
                        emit_assignment(new_changed, new_changed_value);
                        state.all_role_changed[j][i] = new_changed;

                        // VALUE: UPDATE WITH ITE ON GUARD
                        variable sync_role_var = state.all_role_vars[j][i].createFrom();
                        SMTExpr cond_sync_role_var = solver->createCondExpr(frame_guard,
                                                                          state.all_role_vars[j][i].get_solver_var(),
                                                                          old_state.all_role_vars[j][i].get_solver_var());
                        emit_assignment(sync_role_var, cond_sync_role_var);
                        state.all_role_vars[j][i] = sync_role_var;
                    }
                }
                emit_comment("E: Updating user " + std::to_string(j));
            }

            // RESTORING OLD STEP TRACKED STATE
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (infos.interesting_roles[i]) {
                    //TRACKED: ADMIN RESTORE OLD VALUE
                    SMTExpr old_admin_tracked_state = old_state.layer_admin_role_tracked[i].get_solver_var();
                    variable new_admin_tracked_state = state.layer_admin_role_tracked[i].createFrom();
                    this->emit_assignment(new_admin_tracked_state, old_admin_tracked_state);
                    state.layer_admin_role_tracked[i] = new_admin_tracked_state;
                    //TRACKED: TARGET RESTORE OLD VALUE
                    SMTExpr old_user_tracked_state = old_state.layer_user_role_tracked[i].get_solver_var();
                    variable new_user_tracked_state = state.layer_user_role_tracked[i].createFrom();
                    this->emit_assignment(new_user_tracked_state, old_user_tracked_state);
                    state.layer_user_role_tracked[i] = new_user_tracked_state;
                } else {
                    //UNTRACKED: SET VARIABLE TO FALSE (NEXT USAGE WILL FIND UNSET!)
//                    state.core_sets[i] = state.core_sets[i].createFrom();
//                    this->emit_assignment(state.core_sets[i], solver->createFalse());
                }
            }

            //RESTORE OLD SKIP
            SMTExpr old_skip = old_state.skip.get_solver_var();
            variable new_skip = state.skip.createFrom();
            this->emit_assignment(new_skip, old_skip);
            state.skip = new_skip;

            saved_state.pop();
        }

        void create_program_counter() {
            if (infos.pc_size == 0) {
                log->critical("pc is zero in overapprox...");
//                state.program_counter = variable(state.program_counter.name,
//                                                 state.program_counter.idx + 1,
//                                                 pc_size + 1,
//                                                 solver,
//                                                 BIT_VECTOR);
                throw std::runtime_error("pc is zero in overapprox...");
            } else {
                state.program_counter = variable(state.program_counter.name,
                                                 state.program_counter.idx + 1,
                                                 infos.pc_size,
                                                 solver,
                                                 BIT_VECTOR);
            }
        }

        void clean_changed_memory() {
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (infos.interesting_roles[i]) {
                    //ADMIN
                    variable new_dmin_role_changed = state.selected_admin_role_changed[i].createFrom();
                    this->emit_assignment(new_dmin_role_changed, solver->createFalse());
                    state.selected_admin_role_changed[i] = new_dmin_role_changed;
                    //USER
                    variable new_user_role_changed = state.selected_user_role_changed[i].createFrom();
                    this->emit_assignment(new_user_role_changed, solver->createFalse());
                    state.selected_user_role_changed[i] = new_user_role_changed;
                }
            }
        }

        void create_new_clean_tracked_infos() {
            for (int i = 0; i < policy->atom_count(); ++i) {
                if (infos.interesting_roles[i]) {
                    //ADMIN
                    variable new_adm_role_tracked = state.layer_admin_role_tracked[i].createFrom();
                    state.layer_admin_role_tracked[i] = new_adm_role_tracked;
                    //USER
                    variable new_user_role_tracked = state.layer_user_role_tracked[i].createFrom();
                    state.layer_user_role_tracked[i] = new_user_role_tracked;
                }
            }
        }

        void copy_block_adm_user_idx_to_layer() {
            emit_comment("start layer admin multiplexing");
            variable nadm = state.layer_admin_idx.createFrom();
            state.layer_admin_idx = nadm;
            //VALID BECAUSE BLOCK_IDX IS NOT CLEANED
            emit_assignment(state.layer_admin_idx, state.block_admin_idx.get_solver_var());
            emit_comment("end layer admin multiplexing");

            emit_comment("start layer user multiplexing");
            variable nuser = state.layer_target_idx.createFrom();
            state.layer_target_idx = nuser;
            //VALID BECAUSE BLOCK_IDX IS NOT CLEANED
            emit_assignment(state.layer_target_idx, state.block_target_idx.get_solver_var());
            emit_comment("end layer user multiplexing");
        }

        int required_blocks(std::vector<std::pair<std::pair<Expr, Expr>, int>>& target_exprs) {
            int max_rules = 0;

            for (auto &&prec :target_exprs) {
                max_rules = std::max(max_rules, (int)(prec.first.first->atoms().size() + prec.first.second->atoms().size()));
            }

            int required = max_rules + choicer.get_required_count(ADMIN) + choicer.get_required_count(TARGET);

            return required;
        }

        int get_block_count(std::vector<std::pair<std::pair<Expr, Expr>, int>>& target_exprs) {
            int desired = Config::overapproxOptions.blocks_count;

            int required = required_blocks(target_exprs);

            log->trace("Desired: {}. Had {}", desired, required);

            if (desired <= -1) {
                return required;
            } else if (desired == 0) {
                throw std::runtime_error("Desired number of blocks cannot be 0");
            } else if (desired > required) {
                log->trace("required blocks {} is less than the desired {}", required, desired);
                log->trace("using {}", required);
                return required;
            } else {
                return desired;
            }
        }

        bool requires_nondet_block_layer() {
            return blocks_to_do < required_blocks(target_exprs);
        }

        void init_new_frame(const Expr& _target_expr, std::vector<std::pair<std::pair<Expr, Expr>, int>> _target_exprs) {
            deep = deep - 1;
//            target_rules.insert(_target_rule.begin(), _target_rule.end());
            target_exprs = _target_exprs;
            blocks_to_do = get_block_count(_target_exprs);
//            update_tracked_core_role_array_set_pc_size(target_expr);
//            update_program_counter();
            clean_changed_memory();
            copy_block_adm_user_idx_to_layer();
            create_new_clean_tracked_infos();
        }

        void set_guard(SMTExpr guard) {
            variable old_guard = state.guard;
            variable new_guard = old_guard.createFrom();
            SMTExpr new_val = solver->createAndExpr(old_guard.get_solver_var(), guard);
            solver->assertLater(solver->createEqExpr(new_guard.get_solver_var(), new_val));
            state.guard = new_guard;
        }

        void internal_init() {
            SMTExpr _false = solver->createFalse();
            SMTExpr _true = solver->createTrue();
            for (int j = 0; j < infos.user_count; ++j) {
                for (int i = 0; i < policy->atom_count(); ++i) {
                    if (infos.interesting_roles[i]) {
                        SMTExpr init_role_changed = solver->createEqExpr(state.all_role_changed[j][i].get_solver_var(),
                                                                       _false);
                        solver->assertLater(init_role_changed);

                        SMTExpr init_role_sets = solver->createEqExpr(state.all_role_sets[j][i].get_solver_var(),
                                                                    _false);
                        solver->assertLater(init_role_sets);
                    }
                }
            }

            for (int i = 0; i < policy->atom_count(); ++i) {
                if (infos.interesting_roles[i]) {
                    SMTExpr init_adm_role_tracked = solver->createEqExpr(state.layer_admin_role_tracked[i].get_solver_var(),
                                                                       _false);
                    solver->assertLater(init_adm_role_tracked);
                    SMTExpr init_user_role_tracked = solver->createEqExpr(state.layer_user_role_tracked[i].get_solver_var(),
                                                                        _false);
                    solver->assertLater(init_user_role_tracked);
                }
            }

            SMTExpr init_skip = solver->createEqExpr(state.skip.get_solver_var(), _false);
            solver->assertLater(init_skip);
            SMTExpr init_guard = solver->createEqExpr(state.guard.get_solver_var(), _true);
            solver->assertLater(init_guard);
            SMTExpr init_update_guard = solver->createEqExpr(state.update_guard.get_solver_var(), _true);
            solver->assertLater(init_update_guard);
            create_program_counter();
        }

    public:

        overapprox_status() = delete;

        overapprox_status(SMTFactory* _solver,
                          const std::shared_ptr<arbac_policy>& _policy,
                          int _deep,
                          const overapprox_infos infos) :
                solver(_solver),
                policy(_policy),
                state(policy, solver, infos.user_count, infos.interesting_roles),
//                target_rules(std::set<rulep>()),
                target_exprs(std::vector<std::pair<std::pair<Expr, Expr>, int>>()),
                blocks_to_do(-1),
                infos(infos),
                choicer(_policy),
                deep(_deep) {
            internal_init();
        }

        inline void emit_assignment(const variable& var, const SMTExpr& value) {
            SMTExpr ass = solver->createEqExpr(var.get_solver_var(), value);
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            SMTExpr guarded_ass = solver->createImplExpr(state.guard.get_solver_var(),
                                                       ass);
            solver->assertLater(guarded_ass);

        }

        inline void emit_assumption(const SMTExpr& value) {
            //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
            SMTExpr guarded_ass = solver->createImplExpr(state.guard.get_solver_var(),
                                                      value);
            solver->assertLater(guarded_ass);
        }

        inline void emit_comment(const std::string& comment) {
            //Working automatically and only in Z3
            if (solver->solver_name == Solver::Z3) {
                solver->assertNow(solver->createBoolVar(comment));
                log->debug("Emitting comment: " + comment);
            }
        }

        inline variable& create_get_nondet_bool_var() {
            state.nondet_bool = state.nondet_bool.createFrom();
            return state.nondet_bool;
        }

        void push(Expr _target_expr,
                /*std::set<rulep> _target_rule, */
                  SMTExpr guard,
                  variable _parent_pc,
                  std::vector<std::pair<std::pair<Expr, Expr>, int>> preconditions) {
//            log->trace(++ext_porr);
//            log->warn("pushing");
//            log->warn("Pushing {}", *_target_expr);
            emit_comment("PUSH" + _target_expr->to_string() + " " + std::to_string(blocks_to_do) + " rounds");
            save_all();
            parent_pc = _parent_pc;
            set_guard(guard);
            init_new_frame(_target_expr, preconditions);
//            log->critical("pushed target {} depth: {} rounds: {}", *_target_expr, deep, rounds_to_do);
        }

        void pop() {
//            log->warn("Popping {}", *target_expr);
//            Expr tgt = target_expr;
            restore_all_but_state();
            restore_state();
            emit_comment("POP");
        }

    };


    std::shared_ptr<SMTFactory> solver;
    std::shared_ptr<arbac_policy> policy;

    overapprox_status state;

    const SMTExpr zero;
    const SMTExpr one;

    static bool is_optional(int atom_idx) {
        return false;
    }

    static overapprox_infos get_interesting_pc_size_pc_maxvalue(const std::shared_ptr<arbac_policy> &policy,
                                                                const Expr &to_check,
                                                                const int user_count) {
        bool fixpoint = false;

        std::set<Atomp> interesting;

        interesting.insert(to_check->atoms().begin(), to_check->atoms().end());

        while (!fixpoint) {
            fixpoint = true;

            for (auto &&rule : policy->rules()) {
//                    print_collection(necessary_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": "_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": " << (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) << std::endl;
                if (contains(interesting, rule->target)) {
//                        print_collection(rule->admin->literals());
//                        print_collection(rule->prec->literals());
                    auto old_size = interesting.size();

                    //FIXME: absolutely restore the following if working with admin!
                    interesting.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
                    interesting.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                    if (old_size - interesting.size() != 0) {
                        fixpoint = false;
                    }
                }
            }
        }

        int interesting_roles_count = 0;
        std::vector<bool> interesting_roles((unsigned long) policy->atom_count());
        for (int i = 0; i < policy->atom_count(); ++i) {
            interesting_roles[i] = false;
        }
        for (auto &&atom : interesting) {
            interesting_roles[atom->role_array_index] = true;
            interesting_roles_count++;
        }

//        int required_rounds = 0;
//
//        for (auto &&atom : policy->atoms()) {
//             if (tracked_roles[atom->role_array_index]) {
//                if (policy->per_role_can_assign_rule(atom).empty() &&
//                    policy->per_role_can_revoke_rule(atom).empty()) {
//                    continue;
//                } else {
//                    required_rounds++;
//                }
//            }
//        }

        std::pair<int, int> pc_size_max_value = get_pc_size_max_value(policy, interesting);
        return overapprox_infos(to_check,
                                interesting_roles,
                                interesting_roles_count,
                                user_count,
                                pc_size_max_value.first,
                                pc_size_max_value.second);
    }

    inline void emit_assignment(const variable& var, const SMTExpr& value) {
//        SMTExpr assign = solver->createEqExpr(variable.get_solver_var(), value);
        state.emit_assignment(var, value);
    }

    inline void emit_assumption(const SMTExpr& expr) {
        state.emit_assumption(expr);
    }

    inline void emit_comment(std::string comment) {
        state.emit_comment(comment);
    }

    void det_init_atoms() {
        SMTExpr init = solver->createFalse();
        for (int i = 0; i < state.infos.user_count; ++i) {
            userp conf = policy->users(i);
            for (auto &&atom :policy->atoms()) {
                if (state.infos.interesting_roles[atom->role_array_index]) {
                    bool has = contains(conf->config(), atom);
                    emit_assignment(state.state.all_role_vars[i][atom->role_array_index],
                                    has ? one : zero);
                }
            }
        }
    }

    struct nondet_init_variables {
        std::vector<variable> thread_assigneds;
        variable nondet_int;
        variable guard;

        nondet_init_variables(overapprox_infos infos, SMTFactory* solver) :
            thread_assigneds(std::vector<variable>((uint) infos.user_count)),
            nondet_int(variable("nondet_int", -1, get_bit_count_for_choices(infos.user_count), solver, BIT_VECTOR)),
            guard(variable("nondet_ass_guard", 0, 1, solver, BOOLEAN)) {
            for (int i = 0; i < thread_assigneds.size(); ++i) {
                thread_assigneds[i] = variable("thread_" + std::to_string(i) + "_assigned", 0, 1, solver, BOOLEAN);
            }
        }
    };

    void thread_assignment_if(int thread_id, int user_id, nondet_init_variables& vars) {
        emit_comment("B User " + policy->users(user_id)->name + " to thread " + std::to_string(thread_id));

        SMTExpr con_e = solver->createBVConst(thread_id, vars.nondet_int.bv_size);
        SMTExpr eq_e = solver->createEqExpr(vars.nondet_int.get_solver_var(), con_e);
        SMTExpr not_e = solver->createNotExpr(vars.thread_assigneds[thread_id].get_solver_var());
        SMTExpr if_guard = solver->createAndExpr(eq_e,
                                               not_e);
        variable n_guard = vars.guard.createFrom();
        emit_assignment(n_guard, if_guard);
        vars.guard = n_guard;

        SMTExpr ass_val = solver->createCondExpr(vars.guard.get_solver_var(), one, vars.thread_assigneds[thread_id].get_solver_var());

        variable assigned = vars.thread_assigneds[thread_id].createFrom();
        emit_assignment(assigned, ass_val);
        vars.thread_assigneds[thread_id] = assigned;

        for (auto&& atom :policy->atoms()) {
            if (state.infos.interesting_roles[atom->role_array_index]) {
                variable old_var = state.state.all_role_vars[thread_id][atom->role_array_index];
                variable new_var = old_var.createFrom();

                SMTExpr act_val = contains(policy->users(user_id)->config(), atom) ?
                                one :
                                zero;

                SMTExpr new_val = solver->createCondExpr(vars.guard.get_solver_var(),
                                                       act_val,
                                                       old_var.get_solver_var());
                emit_assignment(new_var, new_val);
                state.state.all_role_vars[thread_id][atom->role_array_index] = new_var;
            }
        }
        emit_comment("E User " + policy->users(user_id)->name + " to thread " + std::to_string(thread_id));
    }

    void assign_thread_to_user(int user_id, nondet_init_variables& vars) {

        variable nndint = vars.nondet_int.createFrom();
        vars.nondet_int = nndint;

        for (int i = 0; i < state.infos.user_count; i++) {
            thread_assignment_if(i, user_id, vars);
        }
    }

    void nondet_init_atoms() {
        nondet_init_variables vars(state.infos, solver.get());
        for (int i = 0; i < policy->user_count(); i++) {
            assign_thread_to_user(i, vars);
        }

        SMTExpr assume_body = vars.thread_assigneds[0].get_solver_var();
        for (int i = 1; i < vars.thread_assigneds.size(); i++) {
            assume_body = solver->createAndExpr(vars.thread_assigneds[i].get_solver_var(), assume_body);
        }
        emit_assumption(assume_body);
    }

    SMTExpr generate_PC_prec(int pc) {
        // fprintf(outputFile, "    if (!skip && (__cs_pc == %d) &&\n", pc);
        return solver->createEqExpr(state.state.program_counter.get_solver_var(),
                                    solver->createBVConst(pc,
                                                          state.infos.pc_size));
    }

    SMTExpr generate_from_prec(const std::pair<Expr, Expr>& preconds) {
        SMTExpr adm_res = generateSMTFunction(solver, preconds.first, state.state.selected_admin_role_vars, "");

        SMTExpr prec_res = generateSMTFunction(solver, preconds.second, state.state.selected_user_role_vars, "");

        return solver->createAndExpr(adm_res, prec_res);
    }

            //    SMTExpr get_assignment_cond(const atomp& target_role, int label_index) {
//        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
//        // fprintf(outputFile, "    /* --- ASSIGNMENT RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
//        SMTExpr skip_condition = solver->createNotExpr(state.state.skip.get_solver_var());
//        Expr ca_expr;
//        if (policy->per_role_can_assign_rule(target_role).size() < 1) {
//            ca_expr = createConstantFalse();
//        } else {
//            policy->per_role_can_assign_rule(target_role);
//            auto ite = policy->per_role_can_assign_rule(target_role).begin();
//            ca_expr = (*ite)->prec;
//            for (++ite; ite != policy->per_role_can_assign_rule(target_role).end(); ++ite) {
//                rulep rule = *ite;
////                if (contains(state.target_rules, rule)) {
////                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
////                    continue;
////                }
//                // print_ca_comment(outputFile, ca_idx);
//                ca_expr = createOrExpr(ca_expr, rule->prec);
//                // fprintf(outputFile, "        ||\n");
//            }
//        }
//
////        if (state.deep > 0) {
//////            log->warn("pushing rule {} with depth {}", *ca_expr, state.deep);
////            state.push(ca_expr/*, state.target_rules*/, if_prelude);
////            generate_main();
////            state.pop();
////        }
//        SMTExpr ca_guards = generate_CA_cond(ca_expr);
//
//        // This user is not in this target role yet
//        // fprintf(outputFile, "        /* Role not SET yet */\n");
//        SMTExpr not_set = solver->createNotExpr(state.state.role_sets[target_role->role_array_index].get_solver_var());
//        // this should prevent dummy set for the last time not changing the value
//        SMTExpr was_false = solver->createNotExpr(solver->createEqExpr(state.state.role_vars[target_role->role_array_index].get_solver_var(),
//                                                                     one));
//        SMTExpr cond = solver->createAndExpr(solver->createAndExpr(skip_condition, ca_guards),
//                                           solver->createAndExpr(not_set, was_false));
//        return cond;
//    }
//
//    SMTExpr get_revoke_cond(const atomp& target_role, int label_index) {
//        // Precondition: exists always at least one CA that assign the role i.e.: roles_ca_counts[target_role_index] > 1
//        // fprintf(outputFile, "    /* --- REVOKE RULES FOR ROLE %s --- */\n", role_array[target_role_index]);
//        Expr cr_expr;
//
//        SMTExpr skip_condition = solver->createNotExpr(state.state.skip.get_solver_var());
//
//        if (policy->per_role_can_revoke_rule(target_role).size() < 1) {
//            cr_expr = createConstantFalse();
//        } else {
//            auto ite = policy->per_role_can_revoke_rule(target_role).begin();
//            cr_expr = (*ite)->prec;
//            for (++ite; ite != policy->per_role_can_revoke_rule(target_role).end(); ++ite) {
//                rulep rule = *ite;
////                if (contains(state.target_rules, rule)) {
////                    // EXCLUDE THE TARGET RULE FROM ASSIGNMENT
////                    continue;
////                }
//                cr_expr = createOrExpr(cr_expr, rule->prec);
//            }
//        }
//
////        if (state.deep > 0) {
//////            log->warn("pushing rule {} with depth {}", *cr_expr, state.deep);
////            state.push(cr_expr, /*state.target_rules,*/ if_prelude);
////            generate_main();
////            state.pop();
////        }
//
//        SMTExpr cr_guards = generate_CR_cond(cr_expr);
//
//
//        // This user is not in this target role yet
//        // fprintf(outputFile, "        /* Role not SET yet */\n");
//        SMTExpr not_set = solver->createNotExpr(state.state.role_sets[target_role->role_array_index].get_solver_var());
//        // this should prevent dummy set for the last time not changing the value
//        SMTExpr was_true = solver->createNotExpr(solver->createEqExpr(state.state.role_vars[target_role->role_array_index].get_solver_var(),
//                                                                    zero));
//        SMTExpr cond = solver->createAndExpr(solver->createAndExpr(skip_condition, cr_guards),
//                                           solver->createAndExpr(not_set, was_true));
//        return cond;
//    }
//
//    void simulate_can_assigns(const rulep& rule, int label_index) {
//        //This forces the transition to happen if pc = label
//        SMTExpr pc_precondition = generate_PC_prec(label_index);
//
//        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
//        SMTExpr ass_cond = get_assignment_cond(target_role, label_index);
//
//        emit_assumption(solver->createImplExpr(pc_precondition, ass_cond));
//
//        int target_role_index = target_role->role_array_index;
//
//        SMTExpr new_role_val = solver->createCondExpr(pc_precondition, one, state.state.role_vars[target_role_index].get_solver_var());
//        SMTExpr new_changed_val = solver->createCondExpr(pc_precondition, one, state.state.role_changed[target_role_index].get_solver_var());
//        SMTExpr new_set_val = solver->createCondExpr(pc_precondition, one, state.state.role_sets[target_role_index].get_solver_var());
//
//
//        // fprintf(outputFile, "            role_%s = 1;\n", role_array[target_role_index]);
//        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
//        emit_assignment(new_role_var, new_role_val);
//        state.state.role_vars[target_role_index] = new_role_var;
//
//        // fprintf(outputFile, "            changed_%s = 1;\n", role_array[target_role_index]);
//        variable new_changed_var = state.state.role_changed[target_role_index].createFrom();
//        emit_assignment(new_changed_var, new_changed_val);
//        state.state.role_changed[target_role_index] = new_changed_var;
//
//
//        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
//        variable new_set_var = state.state.role_sets[target_role_index].createFrom();
//        emit_assignment(new_set_var, new_set_val);
//        state.state.role_sets[target_role_index] = new_set_var;
//    }
//
//    void simulate_can_revokes(const atomp& target_role, int label_index) {
//        //This forces the transition to happen if pc = label
//        SMTExpr pc_precondition = generate_PC_prec(label_index);
//
//        SMTExpr revoke_cond = get_revoke_cond(target_role, label_index);
//
//        emit_assumption(solver->createImplExpr(pc_precondition, revoke_cond));
//
//        int target_role_index = target_role->role_array_index;
//
//        SMTExpr new_role_val = solver->createCondExpr(pc_precondition, zero, state.state.role_vars[target_role_index].get_solver_var());
//        SMTExpr new_set_val = solver->createCondExpr(pc_precondition, one, state.state.role_sets[target_role_index].get_solver_var());
//
//        // fprintf(outputFile, "            role_%s = 0;\n", role_array[target_role_index]);
//        variable new_role_var = state.state.role_vars[target_role_index].createFrom();
//        emit_assignment(new_role_var, new_role_val);
//        state.state.role_vars[target_role_index] = new_role_var;
//
//        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
//        variable new_set_var = state.state.role_sets[target_role_index].createFrom();
//        emit_assignment(new_set_var, new_set_val);
//        state.state.role_sets[target_role_index] = new_set_var;
//    }

    SMTExpr get_rule_cond(const rulep& rule) {
        // fprintf(outputFile, "    /* --- RULE %s --- */\n", rule);
        const Atomp& target_role = rule->target;
        SMTExpr skip_condition = solver->createNotExpr(state.state.skip.get_solver_var());
        std::pair<Expr, Expr> precs(rule->admin, rule->prec);

        SMTExpr assigned_val = rule->is_ca ? one : zero;

//        if (state.deep > 0) {
////            log->warn("pushing rule {} with depth {}", *ca_expr, state.deep);
//            state.push(ca_expr/*, state.target_rules*/, if_prelude);
//            generate_layer();
//            state.pop();
//        }

        SMTExpr ca_guards = generate_from_prec(precs);

        // This user is not in this target role yet
        // fprintf(outputFile, "        /* Role not SET yet */\n");
        SMTExpr not_set = solver->createNotExpr(state.state.selected_user_role_sets[target_role->role_array_index].get_solver_var());
        //This role is tracked in this round
        SMTExpr target_is_layer_adm = solver->createEqExpr(state.state.layer_admin_idx.get_solver_var(),
                                                         state.state.block_target_idx.get_solver_var());
        SMTExpr tracked =
                solver->createCondExpr(target_is_layer_adm,
                                       state.state.layer_admin_role_tracked[target_role->role_array_index].get_solver_var(),
                                       state.state.layer_user_role_tracked[target_role->role_array_index].get_solver_var());

        // this should prevent dummy set for the last time not changing the value
        SMTExpr has_changed = solver->createNotExpr(
                solver->createEqExpr(state.state.selected_user_role_vars[target_role->role_array_index].get_solver_var(),
                                     assigned_val));
        SMTExpr cond = solver->createAndExpr(solver->createAndExpr(solver->createAndExpr(skip_condition,
                                                                                       tracked),
                                                                 ca_guards),
                                           solver->createAndExpr(not_set,
                                                                 has_changed));
        return cond;

    }

    void simulate_rule(const rulep& rule, int rule_index) {
        //This forces the transition to happen if pc = label
        SMTExpr pc_precondition = generate_PC_prec(rule_index);

        //fprintf(outputFile, "tThread_%d_%d:\n", thread_id, label_index);
        SMTExpr ass_cond = get_rule_cond(rule);

        SMTExpr ass_value = rule->is_ca ? one : zero;

        emit_assumption(solver->createImplExpr(pc_precondition, ass_cond));

        int target_index = rule->target->role_array_index;

        SMTExpr new_role_val = solver->createCondExpr(pc_precondition,
                                                    ass_value,
                                                    state.state.selected_user_role_vars[target_index].get_solver_var());
        SMTExpr new_changed_val = solver->createCondExpr(pc_precondition,
                                                       one,
                                                       state.state.selected_user_role_changed[target_index].get_solver_var());
        SMTExpr new_set_val = solver->createCondExpr(pc_precondition,
                                                   one,
                                                   state.state.selected_user_role_sets[target_index].get_solver_var());
//        SMTExpr new_tracked_val = solver->createCondExpr(pc_precondition,
//                                                       one,
//                                                       state.state.role_tracked[target_index].get_solver_var());


        // fprintf(outputFile, "            role_%s = ass_value;\n", role_array[target_role_index]);
        variable new_role_var = state.state.selected_user_role_vars[target_index].createFrom();
        emit_assignment(new_role_var, new_role_val);
        state.state.selected_user_role_vars[target_index] = new_role_var;

        // fprintf(outputFile, "            changed_%s = 1;\n", role_array[target_role_index]);
        variable new_changed_var = state.state.selected_user_role_changed[target_index].createFrom();
        emit_assignment(new_changed_var, new_changed_val);
        state.state.selected_user_role_changed[target_index] = new_changed_var;


        // fprintf(outputFile, "            set_%s = 1;\n", role_array[target_role_index]);
        variable new_set_var = state.state.selected_user_role_sets[target_index].createFrom();
        emit_assignment(new_set_var, new_set_val);
        state.state.selected_user_role_sets[target_index] = new_set_var;


//        // fprintf(outputFile, "            tracked_%s = 1;\n", role_array[target_role_index]);
//        variable new_tracked_var = state.state.role_tracked[target_index].createFrom();
//        emit_assignment(new_tracked_var, new_tracked_val);
//        state.state.role_tracked[target_index] = new_tracked_var;
    }

    void simulate_skip() {
        // Do not apply any translation and set skip to true
        // fprintf(outputFile, "    if (__cs_pc >= %d) {", label_idx);
        // fprintf(outputFile, "        skip = 1;");
        // fprintf(outputFile, "    }");
        variable new_skip = state.state.skip.createFrom();
        SMTExpr cond = solver->createGEqExpr(state.state.program_counter.get_solver_var(),
                                           solver->createBVConst(state.infos.pc_max_value,
                                                                 state.infos.pc_size));
        SMTExpr new_val = solver->createCondExpr(cond, one, state.state.skip.get_solver_var());

        emit_assignment(new_skip, new_val);

        state.state.skip = new_skip;

    }

    void copy_from_user(AdminOrTarget aot, LayerOrBlock lob) {
        emit_comment("B: Copying user to " + AoTToString(aot) + " of " + LoBToString(lob));
        for (auto &&item :policy->atoms()) {
            if (state.infos.interesting_roles[item->role_array_index]) {
                variable n_r_val;
                variable n_r_set;
                variable n_r_changed;
                variable u_idx;

                if (aot == ADMIN) {
                    u_idx = (lob == BLOCK) ? state.state.block_admin_idx : state.state.layer_admin_idx;
                    n_r_val = state.state.selected_admin_role_vars[item->role_array_index].createFrom();
                    state.state.selected_admin_role_vars[item->role_array_index] = n_r_val;

                    n_r_set = state.state.selected_admin_role_sets[item->role_array_index].createFrom();
                    state.state.selected_admin_role_sets[item->role_array_index] = n_r_set;

                    n_r_changed = state.state.selected_admin_role_changed[item->role_array_index].createFrom();
                    state.state.selected_admin_role_changed[item->role_array_index] = n_r_changed;
                } else {
                    u_idx = (lob == BLOCK) ? state.state.block_target_idx : state.state.layer_target_idx;
                    n_r_val = state.state.selected_user_role_vars[item->role_array_index].createFrom();
                    state.state.selected_user_role_vars[item->role_array_index] = n_r_val;

                    n_r_set = state.state.selected_user_role_sets[item->role_array_index].createFrom();
                    state.state.selected_user_role_sets[item->role_array_index] = n_r_set;

                    n_r_changed = state.state.selected_user_role_changed[item->role_array_index].createFrom();
                    state.state.selected_user_role_changed[item->role_array_index] = n_r_changed;
                }

                SMTExpr new_value = solver->createFalse();
                SMTExpr new_set = solver->createFalse();
                SMTExpr new_changed = solver->createFalse();
                for (int i = 0; i < state.infos.user_count; ++i) {
                    SMTExpr is_selected = solver->createEqExpr(u_idx.get_solver_var(),
                                                             solver->createBVConst(i, u_idx.bv_size));

                    //VALUE
                    SMTExpr copy_value = solver->createEqExpr(n_r_val.get_solver_var(),
                                                            state.state.all_role_vars[i][item->role_array_index].get_solver_var());
                    new_value = solver->createOrExpr(new_value,
                                                     solver->createAndExpr(is_selected,
                                                                           copy_value));

                    //SET
                    SMTExpr copy_set = solver->createEqExpr(n_r_set.get_solver_var(),
                                                          state.state.all_role_sets[i][item->role_array_index].get_solver_var());
                    new_set = solver->createOrExpr(new_set,
                                                   solver->createAndExpr(is_selected,
                                                                         copy_set));

                    //CHANGED
                    SMTExpr copy_changed = solver->createEqExpr(n_r_changed.get_solver_var(),
                                                            state.state.all_role_changed[i][item->role_array_index].get_solver_var());
                    new_changed = solver->createOrExpr(new_changed,
                                                       solver->createAndExpr(is_selected,
                                                                             copy_changed));
                }
                //NOT AS ASSIGNMENT OTHERWISE IS TOO LONG WITH TONS OF ITE
                emit_assumption(new_value);
                emit_assumption(new_set);
                emit_assumption(new_changed);
            }
        }
        emit_comment("E: Copying user to " + AoTToString(aot) + " of " + LoBToString(lob));
    }

    void init_multiplexing() {
        emit_comment("start block admin multiplexing");
        variable nadm = state.state.block_admin_idx.createFrom();
        state.state.block_admin_idx = nadm;
        SMTExpr adm_existance = solver->createLtExpr(nadm.get_solver_var(),
                                                   solver->createBVConst(state.infos.user_count, nadm.bv_size));
        emit_assumption(adm_existance);
//        copy_from_user(ADMIN, lob);
        emit_comment("end block admin multiplexing");

        emit_comment("start block user multiplexing");
        variable nuser = state.state.block_target_idx.createFrom();
        state.state.block_target_idx = nuser;
        //Block target can only be layer_admin or layer_target
        SMTExpr target_existance =
                solver->createOrExpr(
                        solver->createEqExpr(nuser.get_solver_var(), state.state.layer_admin_idx.get_solver_var()),
                        solver->createEqExpr(nuser.get_solver_var(), state.state.layer_target_idx.get_solver_var()));
        emit_assumption(target_existance);
//        copy_from_user(TARGET, lob);
        emit_comment("end block user multiplexing");

//        after nondet assignment check that ((state.state.block_admin_idx == state.state.block_target_idx) ==> all variables are equals)
    }

    void check_if_equals(LayerOrBlock lob) {
        emit_comment("B: check eq in " + LoBToString(lob));
        variable admin_user_id = (lob == BLOCK) ? state.state.block_admin_idx : state.state.layer_admin_idx;
        variable target_user_id = (lob == BLOCK) ? state.state.block_target_idx : state.state.layer_target_idx;

        SMTExpr guard = solver->createEqExpr(admin_user_id.get_solver_var(), target_user_id.get_solver_var());

        for (auto &&atom :policy->atoms()) {
            if (state.infos.interesting_roles[atom->role_array_index]) {
                SMTExpr atom_eq = solver->createImplExpr(guard,
                                                       solver->createAndExpr(
                                                               state.state.selected_admin_role_vars[atom->role_array_index].get_solver_var(),
                                                               state.state.selected_user_role_vars[atom->role_array_index].get_solver_var()));
                emit_assumption(atom_eq);
            }
        }
        emit_comment("E: check eq in " + LoBToString(lob));
    }

    void save_copied_user(int user_idx, AdminOrTarget aot, LayerOrBlock lob) {
        emit_comment("B: Saving " + AoTToString(aot) + " to user " + std::to_string(user_idx) + " of " + LoBToString(lob));
        variable user_idx_var;
        if (lob == BLOCK) {
            user_idx_var = (aot == ADMIN) ? state.state.block_admin_idx : state.state.block_target_idx;
        } else {
            user_idx_var = (aot == ADMIN) ? state.state.layer_admin_idx : state.state.layer_target_idx;
        }
        SMTExpr guard = solver->createEqExpr(user_idx_var.get_solver_var(),
                                           solver->createBVConst(user_idx, user_idx_var.bv_size));
        std::vector<variable>& sources_vals = (aot == ADMIN) ?
                                              state.state.selected_admin_role_vars :
                                              state.state.selected_user_role_vars;
        std::vector<variable>& sources_sets = (aot == ADMIN) ?
                                              state.state.selected_admin_role_sets :
                                              state.state.selected_user_role_sets;
        std::vector<variable>& sources_changed = (aot == ADMIN) ?
                                                 state.state.selected_admin_role_changed :
                                                 state.state.selected_user_role_changed;
        for (auto &&atom :policy->atoms()) {
            if (state.infos.interesting_roles[atom->role_array_index]) {
                // save vars value
                variable nvar = state.state.all_role_vars[user_idx][atom->role_array_index].createFrom();
                SMTExpr new_val = solver->createCondExpr(guard,
                                                       sources_vals[atom->role_array_index].get_solver_var(),
                                                       state.state.all_role_vars[user_idx][atom->role_array_index].get_solver_var());
                state.state.all_role_vars[user_idx][atom->role_array_index] = nvar;
                emit_assignment(nvar, new_val);


                // save sets value
                variable nset = state.state.all_role_sets[user_idx][atom->role_array_index].createFrom();
                SMTExpr new_set = solver->createCondExpr(guard,
                                                       sources_sets[atom->role_array_index].get_solver_var(),
                                                       state.state.all_role_sets[user_idx][atom->role_array_index].get_solver_var());
                state.state.all_role_sets[user_idx][atom->role_array_index] = nset;
                emit_assignment(nset, new_set);


                // save changed value
                variable nchg = state.state.all_role_changed[user_idx][atom->role_array_index].createFrom();
                SMTExpr new_chg = solver->createCondExpr(guard,
                                                       sources_changed[atom->role_array_index].get_solver_var(),
                                                       state.state.all_role_changed[user_idx][atom->role_array_index].get_solver_var());
                state.state.all_role_changed[user_idx][atom->role_array_index] = nchg;
                emit_assignment(nchg, new_chg);
            }
        }
        emit_comment("E: Saving " + AoTToString(aot) + " to user " + std::to_string(user_idx) + " of " + LoBToString(lob));
    }

    void save_multiplexed_values(LayerOrBlock lob) {
        //FIXME: ADMIN COPY MUST ALWAYS BE BEFORE THE STANDARD ONE OTHERWISE IN CASE THE USER IS THE SAME CHANGES ARE OVERRIDDEN
        emit_comment("start layer admin de-multiplexing");
        for (int i = 0; i < state.infos.user_count; ++i) {
            save_copied_user(i, ADMIN, lob);
        }
        emit_comment("end layer admin de-multiplexing");

        emit_comment("start layer user de-multiplexing");
        for (int i = 0; i < state.infos.user_count; ++i) {
            save_copied_user(i, TARGET, lob);
        }
        emit_comment("end layer user de-multiplexing");
    }

    SMTExpr generate_guarded_target_assumption() {
        SMTExpr final_ass = zero;
        for (auto &&ttuple :state.target_exprs) {
            Expr adm_expr = ttuple.first.first;
            Expr user_expr = ttuple.first.second;
            int tidx = ttuple.second;

            SMTExpr stexpr = generate_from_prec(ttuple.first);

            SMTExpr parent_pc_texpr = solver->createEqExpr(state.parent_pc.get_solver_var(),
                                                         solver->createBVConst(tidx,
                                                                               state.infos.pc_size));

            SMTExpr ith_expr = solver->createAndExpr(parent_pc_texpr,
                                                   stexpr);
            final_ass = solver->createOrExpr(final_ass,
                                             ith_expr);
        }
        return final_ass;
    }


    SMTExpr generate_check_implication(int role_index, AdminOrTarget aot) {
        //((tracked_r_i /\ changed_r_i) ==> set_r_i)
        ////((role_r_i != init_r_i) \/ ((set_false_r_i /\ init_r_i = 1) \/ (set_true_r_i /\ init_r_i = 0)) ==> set_r_i))
//        SMTExpr init_r_i = zero;
//        for (auto &&atom : user->config()) {
//            if (atom->role_array_index == role_index) {
//                init_r_i = one;
//                break;
//            }
//        }

//        SMTExpr init_r_i = init_r_i_var.get_solver_var();

        std::vector<variable>& sets = (aot == ADMIN) ? state.state.selected_admin_role_sets: state.state.selected_user_role_sets;
        std::vector<variable>& changed = (aot == ADMIN) ? state.state.selected_admin_role_changed : state.state.selected_user_role_changed;
        std::vector<variable>& tracked = (aot == ADMIN) ? state.state.layer_admin_role_tracked : state.state.layer_user_role_tracked;


//        SMTExpr role_var = state.state.role_vars[role_index].get_solver_var();
        SMTExpr role_set = sets[role_index].get_solver_var();
        SMTExpr role_tracked = tracked[role_index].get_solver_var();
        SMTExpr role_changed = changed[role_index].get_solver_var();

//        SMTExpr impl_prec =
//            solver->createOrExpr(
//                solver->createNotExpr(solver->createEqExpr(role_var, init_r_i)),
//                solver->createOrExpr(
//                    solver->createAndExpr(set_false_r_i, solver->createEqExpr(init_r_i, one)),
//                    solver->createAndExpr(set_true_r_i, solver->createEqExpr(init_r_i, zero))
//                ));

        SMTExpr cond = solver->createImplExpr(solver->createAndExpr(role_tracked,
                                                                  role_changed),
                                            role_set);

        // fprintf(outputFile, "((role_%s != %d) => set_%s))", role, init_r_i, role);
        return cond;
    }

    void generate_check() {
        // fprintf(outputFile, "    /*--------------- ERROR CHECK ------------*/\n");
        // fprintf(outputFile, "    /*--------------- assume(\\phi) ------------*/\n");
        emit_comment("CHECK_BEGIN"); // + state.target_exprs->to_string());

        //TODO: not put since checked later. VERIFY (expecially with top_level)
//        generate_guarded_target_assumption();

//        std::vector<variable> origs = state.saved_state.top().role_vars;

//        SMTExpr rule_assumption = generate_from_prec(state.target_expr);
//        emit_assumption(rule_assumption);

        int user_id = 0;
        //                    /\
        // assume( skip ==>  /  \          ((tracked_r_i /\ changed_r_i) ==> set_r_i)
        //                  r_i \in R
        // fprintf(outputFile, "//                    /\\\n");
        // fprintf(outputFile, "// assume( skip ==>  /  \\          ((tracked_r_i /\ changed_r_i) ==> set_r_i)\n";
        // fprintf(outputFile, "//                  r_i \\in Track\n");
//        for (auto &&user : policy->unique_configurations()) {
        SMTExpr inner_and = one;
        for (int i = 0; i < policy->atom_count(); i++) {
            if (state.infos.interesting_roles[i]) {
                SMTExpr impl_r_ui = generate_check_implication(i, ADMIN);
                inner_and = solver->createAndExpr(inner_and, impl_r_ui);
            }
        }
        for (int i = 0; i < policy->atom_count(); i++) {
            if (state.infos.interesting_roles[i]) {
                SMTExpr impl_r_ui = generate_check_implication(i, TARGET);
                inner_and = solver->createAndExpr(inner_and, impl_r_ui);
            }
        }
        SMTExpr target_impl = solver->createImplExpr(state.state.skip.get_solver_var(), inner_and);
//        SMTExpr target_impl = inner_and;
//        }
        emit_assumption(target_impl);

        emit_comment("CHECK_END"); // + state.target_expr->to_string());

        // fprintf(outputFile, "    assert(0);\n");
    }

    void generate_pc_update() {
        variable new_pc = state.state.program_counter.createFrom();
        // If I was skipping continue with old pc value
        SMTExpr continue_skipping = solver->createImplExpr(state.state.skip.get_solver_var(),
                                                         solver->createEqExpr(new_pc.get_solver_var(),
                                                                              state.state.program_counter.get_solver_var()));
        emit_assumption(continue_skipping);
        state.state.program_counter = new_pc;
    }

    void update_constrained_value(const atomp& atom, bool tracked_only, AdminOrTarget aot) {
        /*
         * if (!set(r) && *) { //Do update iff exists at least a ca and a cr
         *      r = *
         *      changed = true
         * }
         * */

        emit_comment("updating role " + atom->name);

        std::vector<variable>& vars = (aot == ADMIN) ? state.state.selected_admin_role_vars : state.state.selected_user_role_vars;
        std::vector<variable>& sets = (aot == ADMIN) ? state.state.selected_admin_role_sets : state.state.selected_user_role_sets;
        std::vector<variable>& changed = (aot == ADMIN) ? state.state.selected_admin_role_changed : state.state.selected_user_role_changed;

        if (policy->per_role_can_assign_rule(atom).empty() &&
            policy->per_role_can_revoke_rule(atom).empty()) {
            // Cannot be changed
            emit_comment("role " + atom->name + " cannot be changed");
            return;
        }

        variable role_var = vars[atom->role_array_index];
        variable role_set = sets[atom->role_array_index];
        variable new_role_var = vars[atom->role_array_index].createFrom();

        variable update_guard_var = state.state.update_guard.createFrom();
        state.state.update_guard = update_guard_var;
        variable do_update = state.create_get_nondet_bool_var();
        SMTExpr not_skipping = solver->createNotExpr(state.state.skip.get_solver_var());
        SMTExpr update_guard = solver->createAndExpr(not_skipping,
                                                   solver->createAndExpr(solver->createNotExpr(role_set.get_solver_var()),
                                                                         do_update.get_solver_var()));

        if (tracked_only) {
            variable role_tracked = (aot == ADMIN) ?
                                    state.state.layer_admin_role_tracked[atom->role_array_index] :
                                    state.state.layer_user_role_tracked[atom->role_array_index];
            update_guard = solver->createAndExpr(update_guard, role_tracked.get_solver_var());
        }

        emit_assignment(update_guard_var, update_guard);


        SMTExpr updated_value = state.create_get_nondet_bool_var().get_solver_var();

        //Variable has really changed
        SMTExpr constraints = solver->createNotExpr(solver->createEqExpr(role_var.get_solver_var(),
                                                                       updated_value));

        // Updated value can be TRUE if |CA(r)| > 0
        // Take the negation: if |CA(r)| = 0 then updated value cannot be TRUE (this works only if it must be changed)
        if (policy->per_role_can_assign_rule(atom).empty()) {
            constraints = solver->createAndExpr(constraints,
                                                solver->createNotExpr(solver->createEqExpr(updated_value,
                                                                                           one)));
        }
        // Updated value can be FALSE if |CR(r)| > 0
        // Take the negation: if |CR(r)| = 0 then updated value cannot be FALSE (this works only if it must be changed)
        if (policy->per_role_can_revoke_rule(atom).empty()) {
            constraints = solver->createAndExpr(constraints,
                                                solver->createNotExpr(solver->createEqExpr(updated_value,
                                                                                           zero)));
        }

        //assert the constraint guarded by the fact the update must take place
        //NOTICE: Do NOT put XOR, IMPLICATION or OR are OK, but NO XOR for the god sake! Otherwise the aserted statement MUST be false!
        emit_assumption(solver->createImplExpr(update_guard_var.get_solver_var(),
                                               constraints));

        // Perform update guarded by "update_guard"
        // on role_value
        SMTExpr new_val = solver->createCondExpr(update_guard_var.get_solver_var(),
                                               updated_value,
                                               role_var.get_solver_var());
        emit_assignment(new_role_var, new_val);
        vars[atom->role_array_index] = new_role_var;

        // on role_changed
        variable old_changed_var = changed[atom->role_array_index];
        variable new_changed_var = changed[atom->role_array_index].createFrom();
        SMTExpr new_changed = solver->createCondExpr(update_guard_var.get_solver_var(),
                                                   one,
                                                   old_changed_var.get_solver_var());
        emit_assignment(new_changed_var, new_changed);
        changed[atom->role_array_index] = new_changed_var;

        emit_comment("role " + atom->name + " updated");
    }

    std::vector<std::pair<rulep, int>> get_interesting_rule_pairs() {
        static std::vector<std::pair<rulep, int>> res;

        if (!res.empty()) {
            return res;
        }
//        interesting Pair broken on indexes... Fix with numbers 0-n, not rule_idx
        int c = 0;
        for (auto &&rule :policy->rules()) {
            if (state.infos.interesting_roles[rule->target->role_array_index]) {
                res.push_back(std::pair<rulep, int>(rule, c++));
            }
        }
        return res;
    }

    std::vector<std::pair<std::pair<Expr, Expr>, int>> get_interesting_precondition_pairs() {
        static std::vector<std::pair<std::pair<Expr, Expr>, int>> res;

        if (!res.empty()) {
            return res;
        }

        auto rule_pairs = get_interesting_rule_pairs();

        for (auto &&rule_pair :rule_pairs) {
            res.push_back(std::pair<std::pair<Expr, Expr>, int>(std::pair<Expr,Expr>(rule_pair.first->admin,
                                                                                     rule_pair.first->prec), rule_pair.second));
        }

        return res;
    }

    void generate_update_state() {
        // IF NOT IN BASE CASE DO NOT GENERATE INITIALIZATION
        emit_comment("S updating at: " + std::to_string(state.deep) + " ");
        if (state.deep > 0) {
            //FIXME: this is executed every time, but is constant. REMOVE FROM HERE!
            std::vector<std::pair<std::pair<Expr, Expr>, int>> prec_pairs = get_interesting_precondition_pairs();

//            log->critical("Pushing at step {} of depth {}", round_idx, state.deep);
            state.push(createConstantTrue(),
                       solver->createNotExpr(state.state.skip.get_solver_var()),
                       state.state.program_counter,
                       prec_pairs);
            generate_layer();
            state.pop();
            copy_from_user(ADMIN, BLOCK);
            copy_from_user(TARGET, BLOCK);
        } else {
            copy_from_user(ADMIN, BLOCK);
            copy_from_user(TARGET, BLOCK);
            //            log->critical("update {} of depth {}", round_idx, state.deep);
            // fprintf(outputFile, "    /*---------- UPDATE STATE ---------*/\n");
            for (int i = 0; i < policy->atom_count(); i++) {
                if (state.infos.interesting_roles[i]) {
                    atomp atom = policy->atoms(i);
                    update_constrained_value(atom, false, ADMIN);
                    // fprintf(outputFile, "    role_%s = set_%s ? role_%s : nondet_bool();\n", role, role, role);
                }
            }
            for (int i = 0; i < policy->atom_count(); i++) {
                if (state.infos.interesting_roles[i]) {
                    atomp atom = policy->atoms(i);
                    update_constrained_value(atom, false, TARGET);
                    // fprintf(outputFile, "    role_%s = set_%s ? role_%s : nondet_bool();\n", role, role, role);
                }
            }
            check_if_equals(BLOCK);
        }

        emit_comment("E updating at: " + std::to_string(state.deep) + " ");
        // fprintf(outputFile, "    __cs_pc = nondet_bv();\n");

    }

    void generate_block() {
        int label_idx = 0;
        // fprintf(outputFile, "    /*---------- UPDATE ---------*/\n");
        generate_pc_update();

        simulate_skip();

        init_multiplexing();

        //TODO: everything MUST be guarded by (!skip)

        generate_update_state();

        // fprintf(outputFile, "    /*---------- CAN ASSIGN SIMULATION ---------*/\n");
        for (auto &&rule_pair :get_interesting_rule_pairs()) {
//            int exclude = target_rule->is_ca ? exclude_idx : -1;
            label_idx++;
            simulate_rule(rule_pair.first, rule_pair.second);

        }

        // fprintf(outputFile, "\n\n");

        save_multiplexed_values(BLOCK);

        assert(label_idx == state.infos.pc_max_value);
        // fprintf(outputFile, "\n\n");
    }

    void set_atom_tracked_state(int atom_id, AdminOrTarget aot) {
        atomp atom = policy->atoms(atom_id);

        auto choice = state.choicer.classify(atom, aot);

        if (choice != RoleChoicer::FREE) {
            SMTExpr value = choice == RoleChoicer::REQUIRED ? one : zero;
            emit_assignment(state.state.layer_admin_role_tracked[atom_id], value);
            emit_assignment(state.state.layer_user_role_tracked[atom_id], value);
            return;
        } else {
            SMTExpr tracked_value = zero;
            for (auto &&target_pair :state.target_exprs) {
                std::pair<Expr, Expr> exprp = target_pair.first;
                Expr texpr = (aot == ADMIN) ? exprp.first : exprp.second;
                int tidx = target_pair.second;
                if (!contains(texpr->atoms(), atom)) {
                    continue;
                } else {
                    SMTExpr cond = solver->createEqExpr(state.parent_pc.get_solver_var(),
                                                      solver->createBVConst(tidx,
                                                                            state.infos.pc_size));
                    tracked_value = solver->createOrExpr(cond,
                                                         tracked_value);
                }
            }
            emit_assignment((aot == ADMIN) ? state.state.layer_admin_role_tracked[atom_id] : state.state.layer_user_role_tracked[atom_id],
                            tracked_value);
        }
    }

    void set_tracked_infos() {
        for (int i = 0; i < policy->atom_count(); ++i) {
            if (state.infos.interesting_roles[i]) {
                set_atom_tracked_state(i, ADMIN);
                set_atom_tracked_state(i, TARGET);
            }
        }
    }

    void generate_layer_block_nondet() {
        copy_from_user(ADMIN, LAYER);
        copy_from_user(TARGET, LAYER);
        for (int i = 0; i < policy->atom_count(); i++) {
                if (state.infos.interesting_roles[i]) {
                    atomp atom = policy->atoms(i);
                    update_constrained_value(atom, true, ADMIN);
                    update_constrained_value(atom, true, TARGET);
                    // fprintf(outputFile, "    role_%s = set_%s ? role_%s : nondet_bool();\n", role, role, role);
                }
            }
        check_if_equals(LAYER);
        save_multiplexed_values(LAYER);
    }

    void generate_layer() {
        // fprintf(outputFile, "int main(void) {\n\n");

        set_tracked_infos();


        //do only if block count is insufficient
        if (state.requires_nondet_block_layer()) {
            generate_layer_block_nondet();
        }

        for (int i = 0; i < state.blocks_to_do; ++i) {
            emit_comment("Round " + std::to_string(i) + " deep " + std::to_string(state.deep));
            generate_block();
        }

        copy_from_user(ADMIN, LAYER);
        copy_from_user(TARGET, LAYER);
        generate_check();
        // fprintf(outputFile, "    return 0;\n");
        // fprintf(outputFile, "}\n");
    }

    void simulate_first_pc_user_ids() {
        variable new_pc = state.state.program_counter.createFrom();
        emit_assignment(new_pc, solver->createBVConst(0, state.infos.pc_size));
        state.state.program_counter = new_pc;

        variable new_admin = state.state.layer_admin_idx.createFrom();
        state.state.layer_admin_idx = new_admin;
        SMTExpr adm_existance = solver->createLtExpr(new_admin.get_solver_var(),
                                                   solver->createBVConst(state.infos.user_count, new_admin.bv_size));
        emit_assumption(adm_existance);

        variable new_target = state.state.layer_target_idx.createFrom();
        state.state.layer_target_idx = new_target;
        SMTExpr target_existance = solver->createLtExpr(new_target.get_solver_var(),
                                                      solver->createBVConst(state.infos.user_count, new_target.bv_size));
        emit_assumption(target_existance);


    }

    void generate_program() {
        std::vector<std::pair<std::pair<Expr, Expr>, int>> conditions;
        conditions.push_back(std::pair<std::pair<Expr, Expr>, int>(std::pair<Expr, Expr>(createConstantTrue(),
                                                                                         state.infos.to_check),
                                                                   0));
        simulate_first_pc_user_ids();

        state.push(state.infos.to_check, one,
                   state.state.program_counter, conditions);

        generate_layer();

//        copy_from_user(ADMIN, LAYER);
        copy_from_user(TARGET, LAYER);

        SMTExpr target_cond = generate_from_prec(conditions[0].first);
        emit_assumption(target_cond);
    }

    bool check_satisfiable() {
        auto start = std::chrono::high_resolution_clock::now();

        if (Config::show_solver_statistics) {
            solver->print_statistics();
        }

        if (Config::dump_smt_formula != "") {
            solver->printContext(Config::dump_smt_formula);
            log->info("BMC SMT formula dumped at: {}", Config::dump_smt_formula);
        }

        SMTResult res = solver->solve();

        auto end = std::chrono::high_resolution_clock::now();
        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        log->debug("------------ SMT SOLVED IN {} ms ------------", milliseconds.count());

        switch (res) {
            case SMTResult::SAT:
                log->debug("SAT\n");
                return true;
                break;
            case SMTResult::UNSAT:
                log->debug("UNSAT\n");
                return false;
                break;
            case SMTResult::UNKNOWN:
                log->warn("The status is unknown\n");
                break;
            case SMTResult::ERROR:
                log->error("Error in check_context");
                throw std::runtime_error("BMC: Error in check_context");
                break;
        }
        return false;
    }

    bool checkUnreachable() {
        generate_program();

        log->debug("SMT formula generated. Solving it...");

        bool result = check_satisfiable();

        return result;
    }


    public:
    AdminOverapproxTransformer(const std::shared_ptr<SMTFactory> _solver,
                               const std::shared_ptr<arbac_policy>& _policy,
                               const int user_count,
                               const Expr _to_check
                                  /*const std::set<rulep> _to_check_source*/) :
        solver(_solver),
        policy(_policy),
        // could be changed instead of using tuple with references that... can be changed from the outside!!!
        state(_solver.get(),
              _policy,
              Config::overapproxOptions.depth,
              get_interesting_pc_size_pc_maxvalue(_policy, _to_check, user_count)),
        zero(solver->createFalse()),
        one(solver->createTrue()) {
//        solver->deep_clean();
        if (state.infos.user_count < policy->user_count()) {
            nondet_init_atoms();
        } else {
            det_init_atoms();
        }
//        det_init_atoms();
    }

    ~AdminOverapproxTransformer() = default;

    bool apply() {
        bool ret = checkUnreachable();

        if (policy->per_role_can_assign_rule(policy->goal_role).size() < 1) {
            log->info("Target role is not assignable!");
            log->info("Target role is not reachable");
            return false;
        }
        if (ret) {
            log->info("Target role may be reachable");
        }
        else {
            log->info("Target role is not reachable");
        }

        return ret;
    }
};

    bool overapprox_admin(const std::shared_ptr<SMTFactory>& solver,
                          const std::shared_ptr<arbac_policy>& policy,
                          const int user_count,
                          const Expr& to_check) {
        solver->deep_clean();
        if (is_constant_true(to_check)) {
            return false;
        }
        AdminOverapproxTransformer transf(solver, policy, user_count, to_check);
        // std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
        // R6Transformer<expr, expr> transf(solver, rule_index, is_ca);
        bool res = transf.apply();
        // if (res || true)
        //     solver->printContext();
        return res;
    }

}
