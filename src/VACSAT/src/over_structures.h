//
// Created by esteffin on 12/4/17.
//

#ifndef VACSAT_OVER_STRUCTURES_H
#define VACSAT_OVER_STRUCTURES_H

#include <vector>
#include <memory>
#include <fstream>
#include <queue>
#include "Policy.h"

namespace SMT {

    class role_choicer {
    public:
        enum class Choice {
            REQUIRED,
            FREE,
            EXCLUDED
        };
        virtual Choice classify(atomp r) const = 0;
        virtual int get_required_count() const = 0;
    };

    typedef std::list<int> tree_path;
    std::string tree_path_to_string(tree_path& path);

    class invariant {
    public:
        const atomp atom;
        const bool value;
        const Expr expr;

        inline bool operator == (const invariant& rhs) const {
            return this->atom->role_array_index == rhs.atom->role_array_index &&
                    this->value == rhs.value;
        }

        inline bool operator < (invariant const& rhs) const {
            if (this->atom->role_array_index == rhs.atom->role_array_index) {
                return this->value < rhs.value;
            }
            return this->atom->role_array_index < rhs.atom->role_array_index;
        }

        invariant clone();

        invariant(atomp _atom, bool _value);
    };

    class invariants {
        std::set<invariant> cnt;
        bool cnt_changed = true;
        std::map<atomp, std::set<bool>> cache;
    public:

        invariants clone();

        invariants();

        const std::map<atomp, std::set<bool>>& get_as_map();

        void add_invariant(invariant inv);

        const std::set<invariant>& get_as_set();

        Expr get_expr();
    };

    class node_invariants {
    public:
        invariants inv_pre_A;
        invariants inv_A_C;
        invariants inv_post_C;

        node_invariants clone();

        node_invariants();
    };

    class node_policy_infos {
    public:
        std::vector<rulep> rules_a;
        std::vector<rulep> rules_c;
        std::vector<atomp> all_atoms;
        std::vector<atomp> atoms_a;
        int policy_atoms_count;

        node_policy_infos clone();

        node_policy_infos(const node_policy_infos &n_i) = default;

        node_policy_infos(std::vector<rulep> _rules_a,
                          std::vector<rulep> _rules_c,
                          std::vector<atomp> _all_atoms,
                          std::vector<atomp> _atoms_a,
                          int _policy_atoms_count);

        std::string JSON_stringify(const std::string& prefix = "");
    };

    class pruning_triggers {
    public:
        std::unique_ptr<rulep> c_rule_check;
        std::unique_ptr<std::pair<atomp, bool>> pre_A_check;
        std::unique_ptr<std::pair<atomp, bool>> A_C_check;
        std::unique_ptr<std::pair<atomp, bool>> post_A_check;
        std::unique_ptr<std::pair<atomp, bool>> pre_A_blocked_check;
        std::unique_ptr<std::pair<atomp, bool>> post_A_blocked_check;
        bool no_transition; /// Disable transition
        bool no_skip;       /// Forbids the node to skip
        bool no_priority;   /// Disable node exploration strategy
        bool no_sfogo;      /// Do not count last node as sfogo

        //FOR LEAVES ONLY
        maybe_bool overapprox;    /// Forces/denies/leave free the overapproximation of the leaf
        bool check_gap;

        pruning_triggers clone();

        void clean();

        bool probing_enabled();

        std::string JSON_stringify(const std::string& prefix = "");

        pruning_triggers();
    };

    class leaves_infos {
    public:

        std::map<atomp, std::set<bool>> nondet_restriction;
        maybe_bool gap;

        leaves_infos clone();

        leaves_infos();

        std::string JSON_stringify(const std::string& prefix = "");
    };

    class proof_node : public std::enable_shared_from_this<proof_node> {//: public node<LayerInfo, BlockInfo> {
    private:

        std::shared_ptr<proof_node> memberwise_clone();

        void rebuild_weak_ptrs();

        void get_nodes(proof_node* node,
                       std::list<proof_node*>& list);

        void filter_nodes_tail(std::list<std::shared_ptr<proof_node>>& acc,
                               std::function<bool(std::shared_ptr<proof_node>&)> fn);

        void get_tree_nodes_tail(std::list<std::shared_ptr<proof_node>>& ret_list);

        void JSON_stringify_node(std::stringstream& fmt, const std::string& prefix = "");

        void update_leaves_infos();

        bool refine_tree_core(int max_depth, int child_count);

        std::list<std::weak_ptr<proof_node>> _ancestors;
        std::weak_ptr<proof_node> _parent;
        std::vector<std::shared_ptr<proof_node>> _refinement_blocks;

    public:

        tree_path path;
        std::string uid;
        const int depth;

        node_invariants invariants;
        node_policy_infos node_infos;
        std::unique_ptr<leaves_infos> leaf_infos;

//        pruning_triggers triggers;

        const std::list<std::weak_ptr<proof_node>>& ancestors() const {
            return _ancestors;
        }
        const std::weak_ptr<proof_node>& parent() const {
            return _parent;
        }
        const std::vector<std::shared_ptr<proof_node>>& refinement_blocks() const {
            return _refinement_blocks;
        }

        std::list<std::shared_ptr<proof_node>> get_all_nodes();

        std::list<std::shared_ptr<proof_node>> get_all_leaves();

        proof_node(tree_path _path,
                   int _depth,
                   const node_policy_infos& _node_infos,
                   std::unique_ptr<leaves_infos> leaf_infos,
                   std::list<std::weak_ptr<proof_node>> ancestors,
                   std::weak_ptr<proof_node> parent);

        proof_node(tree_path _path,
                   std::string _uid,
                   int _depth,
                   node_invariants _invariants,
                   const node_policy_infos _node_infos,
                   std::unique_ptr<leaves_infos> _leaf_infos,
                   std::list<std::weak_ptr<proof_node>> ancestors,
                   std::weak_ptr<proof_node> parent,
                   std::vector<std::shared_ptr<proof_node>> refinement_blocks);

        std::string tree_to_string();

        std::shared_ptr<proof_node> clone();

        bool is_leaf();

        bool is_root();

//        bool pruning_enabled();

        void tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node>)> fun);

        void tree_bfs_iter(std::function<void(std::shared_ptr<proof_node>)> fun);

        std::list<std::shared_ptr<proof_node>> get_tree_nodes();

//        void clean_pruning_triggers();

        std::string JSON_stringify();

        void dump_tree(const std::string& fname, bool javascript_compliant, const std::string heading_name = "");

        std::shared_ptr<proof_node> get_by_path(tree_path path);

        void consolidate_tree();

        bool refine_tree(int max_depth, int child_count);

        //FIXME: to be removed...
        inline void add_child(std::shared_ptr<proof_node> node) {
            this->_refinement_blocks.push_back(node);
        }

    };

    class proof_checker;

    class proof_t {
    private:

        std::vector<rulep> remove_duplicates_discard_admin(std::vector<rulep>& orig_rules) {
            std::vector<rulep> res;
            for (auto &&rule : orig_rules) {
                bool should_insert = true;
                for (auto &&selected : res) {
                    if ( selected->is_ca == rule->is_ca &&
                         selected->target == rule->target &&
                         selected->prec->equals(rule->prec)) {
                        should_insert = false;
                        break;
                    }
                }
                if (should_insert) {
                    res.push_back(rule);
                }
            }
            return std::move(res);
        }

        std::pair<std::vector<atomp>, std::vector<rulep>> slice_policy(const std::vector<atomp> &orig_atoms,
                                                                       const std::vector<rulep> &orig_rules,
                                                                       const Expr &target) {
            bool fixpoint = false;
            std::set<rulep> rules_to_save_set;
            std::set<atomp> necessary_atoms_set;
            necessary_atoms_set.insert(target->atoms().begin(), target->atoms().end());
            while (!fixpoint) {
                fixpoint = true;
                for (auto &&rule : orig_rules) {
//                    print_collection(necessary_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": "_atoms);
//                    print_collection(to_save);
//                    std::cout << *rule << ": " << (!contains(to_save, rule) && contains(necessary_atoms, rule->target)) << std::endl;
                    if (!contains(rules_to_save_set, rule) && contains(necessary_atoms_set, rule->target)) {
//                        print_collection(rule->admin->literals());
//                        print_collection(rule->prec->literals());

//                        necessary_atoms.insert(rule->admin->atoms().begin(), rule->admin->atoms().end());
                        necessary_atoms_set.insert(rule->prec->atoms().begin(), rule->prec->atoms().end());
                        rules_to_save_set.insert(rule);
                        fixpoint = false;
                    }
                }
            }

            std::vector<rulep> rules_to_save(rules_to_save_set.begin(), rules_to_save_set.end());
            std::vector<atomp> necessary_atoms(necessary_atoms_set.begin(), necessary_atoms_set.end());

            std::vector<rulep> rules_to_save_no_dups = remove_duplicates_discard_admin(rules_to_save);

            return std::pair<std::vector<atomp>, std::vector<rulep>>(std::move(necessary_atoms),
                                                                     std::move(rules_to_save_no_dups));
        }

        std::shared_ptr<proof_node> init_get_root(const std::vector<atomp>& orig_atoms,
                                                 const std::vector<rulep>& orig_rules,
                                                 const std::shared_ptr<arbac_policy>& policy,
                                                 const Expr& to_check) {
            std::vector<atomp> used_atoms;
            std::vector<rulep> used_rules;

            log->warn("Original atoms: {}", orig_atoms.size());
            log->warn("Original rules: {}", orig_rules.size());
            if (overapprox_strategy.no_backward_slicing) {
                used_atoms = orig_atoms;
                used_rules = orig_rules;
            } else {
                auto pair = slice_policy(orig_atoms, orig_rules, to_check);
                used_atoms = pair.first;
                used_rules = pair.second;

                log->warn("Applied slicing");

                log->warn("after slicing atoms: {}", used_atoms.size());
                log->warn("after slicing rules: {}", used_rules.size());
            }
            std::shared_ptr<proof_node> proof = create_tree_root(policy->atom_count(), used_atoms, used_rules, to_check);
            return std::move(proof);
        }

        atomp create_target_atom(const std::shared_ptr<arbac_policy> &policy) {
            if (target_atom == nullptr) {
                return createAtomp("__overapprox__target__", policy->atom_count(), 1);
            } else {
                return target_atom;
            }
//            if (fake_atom == nullptr) {
//                fake_atom = createAtomp("__overapprox__fake__", policy->atom_count() + 1, 1);
//            }
        };

        std::shared_ptr<proof_node> create_tree_root(const int policy_atom_count,
                                                     const std::vector<atomp> &atoms,
                                                     const std::vector<rulep> &rules,
                                                     const Expr &to_check) {

            rulep root_rule(new rule(true,
                                     createConstantTrue(),
                                     to_check,
                                     target_atom,
                                     -1));

            std::vector<rulep> root_rule_c;
            root_rule_c.push_back(std::move(root_rule));

            std::vector<atomp> all_atoms = atoms;
            all_atoms.push_back(target_atom);

            node_policy_infos root_info(rules,
                                        std::move(root_rule_c),
                                        std::move(all_atoms),
                                        atoms,
                                        policy_atom_count + 2);

            std::unique_ptr<leaves_infos> root_leaf_infos(new leaves_infos());

            std::shared_ptr<proof_node> root(new proof_node(std::list<int>(),
                                                            0,
                                                            root_info,
                                                            std::move(root_leaf_infos),
                                                            std::list<std::weak_ptr<proof_node>>(),
                                                            std::weak_ptr<proof_node>()));

            root->consolidate_tree();

            return root;
        }

        proof_t(const OverapproxOptions _overapprox_strategy,
                const atomp _target_atom,
                std::shared_ptr<proof_node> _proof_tree,
                const std::set<userp, std::function<bool(const userp &, const userp &)>> _initial_confs) :
                overapprox_strategy(_overapprox_strategy),
                target_atom(_target_atom),
                proof_tree(_proof_tree),
                initial_confs(_initial_confs) { }

    public:
        const OverapproxOptions overapprox_strategy;
        const atomp target_atom = nullptr;
        std::shared_ptr<proof_node> proof_tree;
        const std::set<userp, std::function<bool(const userp &, const userp &)>> initial_confs;

        proof_t(const OverapproxOptions strategy,
                const std::vector<atomp>& orig_atoms,
                const std::vector<rulep>& orig_rules,
                const std::shared_ptr<arbac_policy>& policy,
                const Expr& to_check) :
                overapprox_strategy(strategy),
                target_atom(create_target_atom(policy)),
                proof_tree(init_get_root(orig_atoms,
                                         orig_rules,
                                         policy,
                                         to_check)),
                initial_confs(policy->unique_configurations()) { }

        std::shared_ptr<proof_t> clone() {
            OverapproxOptions new_overapprox_strategy = this->overapprox_strategy;
            atomp new_target_atom = this->target_atom;
            std::shared_ptr<proof_node> new_proof_tree = this->proof_tree->clone();
            std::set<userp, std::function<bool(const userp &, const userp &)>> new_initial_confs = this->initial_confs;

            std::shared_ptr<proof_t> ret(new proof_t(std::move(new_overapprox_strategy),
                                                     std::move(new_target_atom),
                                                     std::move(new_proof_tree),
                                                     std::move(new_initial_confs)));

            return ret;
        }

        std::string tree_to_string() {
            return proof_tree->tree_to_string();
        }

        void dump_tree(const std::string& fname, bool javascript_compliant, const std::string heading_name = "") {
            proof_tree->dump_tree(fname, javascript_compliant, heading_name);
        }

    };

    typedef std::shared_ptr<proof_t> proofp;

    enum class over_analysis_result {
        SAFE,
        UNSAFE,
        UNSAFE_INCOMPLETE
    };

    class proof_checker {
        virtual over_analysis_result verify_proof(proofp proof) = 0;
        virtual over_analysis_result verify_proof(proofp proof,
                                                  std::map<std::shared_ptr<proof_node>, pruning_triggers>& triggers) = 0;
    };
}

#endif //VACSAT_OVER_STRUCTURES_H
