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

    template <typename SolverState>
    class proof_node : public std::enable_shared_from_this<proof_node<SolverState>> {//: public node<LayerInfo, BlockInfo> {
    private:

        std::shared_ptr<proof_node<SolverState>> memberwise_clone();

        void rebuild_weak_ptrs();

        void get_nodes(proof_node<SolverState>* node,
                       std::list<proof_node<SolverState>*>& list);

        void filter_nodes_tail(std::list<std::shared_ptr<proof_node<SolverState>>>& acc,
                               std::function<bool(std::shared_ptr<proof_node<SolverState>>&)> fn);

        void get_tree_nodes_tail(std::list<std::shared_ptr<proof_node<SolverState>>>& ret_list);

        void JSON_stringify_node(std::stringstream& fmt, const std::string& prefix = "");

        void update_leaves_infos();

        bool refine_tree_core(int max_depth, int child_count);

    public:

        tree_path path;
        std::string uid;
        const int depth;

        node_invariants invariants;
        node_policy_infos node_infos;
        std::unique_ptr<leaves_infos> leaf_infos;

        pruning_triggers triggers;

        std::shared_ptr<SolverState> solver_state;
        std::list<std::weak_ptr<proof_node<SolverState>>> ancestors;
        std::weak_ptr<proof_node<SolverState>> parent;
        std::vector<std::shared_ptr<proof_node<SolverState>>> refinement_blocks;

        std::list<std::shared_ptr<proof_node<SolverState>>> get_all_nodes();

        std::list<std::shared_ptr<proof_node<SolverState>>> get_all_leaves();

        proof_node(tree_path _path,
                   int _depth,
                   const node_policy_infos& _node_infos,
                   std::unique_ptr<leaves_infos> _leaves_infos,
                   std::list<std::weak_ptr<proof_node<SolverState>>> _ancestors,
                   std::weak_ptr<proof_node<SolverState>> _parent);

        proof_node(tree_path _path,
                   std::string _uid,
                   int _depth,
                   node_invariants _invariants,
                   const node_policy_infos _node_infos,
                   std::unique_ptr<leaves_infos> _leaf_infos,
                   pruning_triggers _pruning_triggers,
                   std::shared_ptr<SolverState> _solver_state,
                   std::list<std::weak_ptr<proof_node<SolverState>>> _ancestors,
                   std::weak_ptr<proof_node<SolverState>> _parent,
                   std::vector<std::shared_ptr<proof_node<SolverState>>> _refinement_blocks);

        std::string tree_to_string();

        std::shared_ptr<proof_node<SolverState>> clone();

        bool is_leaf();

        bool is_root();

        bool pruning_enabled();

        void tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node<SolverState>>)> fun);

        void tree_bfs_iter(std::function<void(std::shared_ptr<proof_node<SolverState>>)> fun);

        std::list<std::shared_ptr<proof_node<SolverState>>> get_tree_nodes();

        void clean_pruning_triggers();

        void clean_solver_info_state();

        std::string JSON_stringify();

        void dump_tree(const std::string& fname, bool javascript_compliant, const std::string heading_name = "");

        std::shared_ptr<proof_node<SolverState>> get_by_path(tree_path path);

        void consolidate_tree();

        bool refine_tree(int max_depth, int child_count);

    };
}

#include "over_structures.tpp"

#endif //VACSAT_OVER_STRUCTURES_H
