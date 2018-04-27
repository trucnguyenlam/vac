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
        std::shared_ptr<rulep> c_rule_check;
        std::shared_ptr<std::pair<atomp, bool>> pre_A_check;
        std::shared_ptr<std::pair<atomp, bool>> A_C_check;
        std::shared_ptr<std::pair<atomp, bool>> post_A_check;
        std::shared_ptr<std::pair<atomp, bool>> pre_A_blocked_check;
        std::shared_ptr<std::pair<atomp, bool>> post_A_blocked_check;
        bool no_transition; /// Disable transition
        bool no_skip;       /// Forbids the node to skip
        bool no_priority;   /// Disable node exploration strategy
        bool no_sfogo;      /// Do not count last node as sfogo

        //FOR LEAVES ONLY
        maybe_bool overapprox;    /// Forces/denies/leave free the overapproximation of the leaf
        bool check_gap;

        pruning_triggers clone();

        void clean();

        bool probing_enabled() const;

//        std::string JSON_stringify(const std::string& prefix = "");
        std::string JSON_stringify(const std::string& prefix = "", bool only_active = true) const;

        pruning_triggers();
    };

    class leaves_infos {
    public:

        std::map<atomp, std::set<bool>> nondet_restriction;
        bool no_gap;

        leaves_infos clone();

        leaves_infos();

        std::string JSON_stringify(const std::string& prefix = "");
    };

    class proof_node : public std::enable_shared_from_this<proof_node> {//: public node<LayerInfo, BlockInfo> {
    private:
        friend class proof_t;

        std::shared_ptr<proof_node> memberwise_clone();

        void rebuild_weak_ptrs();

//        void get_nodes(proof_node* node,
//                       std::list<proof_node*>& list);

        void filter_nodes_tail(std::list<std::shared_ptr<proof_node>>& acc,
                               std::function<bool(std::shared_ptr<proof_node>&)> fn);

        void get_tree_nodes_tail(std::list<std::shared_ptr<proof_node>>& ret_list);

        void JSON_stringify_node(std::stringstream& fmt, const std::string& prefix = "");

        void update_leaves_infos();

        /**
         * Function that expand a leaf of the tree if less than max_depth adding #child_count refinement children
         * @param max_depth: the max depth for the refinement (< 0) for unlimited
         * @param child_count: The number of child of the node
         * @return true if the node has been refined, false otherways
         **/
        bool refine_node(int max_depth, int child_count);

        std::list<std::weak_ptr<proof_node>> _ancestors;
        std::list<std::weak_ptr<proof_node>> _right_siblings;
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

        const inline std::list<std::weak_ptr<proof_node>>& ancestors() const {
            return _ancestors;
        }
        const inline std::weak_ptr<proof_node>& parent() const {
            return _parent;
        }
        const inline std::list<std::weak_ptr<proof_node>>& right_siblings() {
            if (this->is_root()) {
                return _right_siblings;
            }

            // Lazy initialize _right_siblings
            if (_right_siblings.empty()) {
                std::shared_ptr<proof_node> thisp = this->shared_from_this();
                std::shared_ptr<proof_node> parent = this->parent().lock();
                bool passed = false;
                for (auto &&sibling : parent->_refinement_blocks) {
                    if (passed) {
                        _right_siblings.push_back(sibling);
                    }
                    if (sibling == thisp) {
                        passed = true;
                    }
                }
            }

            return _right_siblings;
        }
        const inline std::vector<std::shared_ptr<proof_node>>& refinement_blocks() const {
            return _refinement_blocks;
        }
        bool is_leftmost_child() const;


        std::list<std::shared_ptr<proof_node>> get_all_nodes();

        std::list<std::shared_ptr<proof_node>> get_all_leaves();

        proof_node(tree_path _path,
                   int _depth,
                   const node_policy_infos& _node_infos,
                   std::unique_ptr<leaves_infos> _leaves_infos,
                   std::list<std::weak_ptr<proof_node>> ancestors,
                   std::weak_ptr<proof_node> parent);

        proof_node(tree_path _path,
                   std::string _uid,
                   int _depth,
                   node_invariants _invariants,
                   const node_policy_infos _node_infos,
                   std::unique_ptr<leaves_infos> _leaves_infos,
                   std::list<std::weak_ptr<proof_node>> ancestors,
                   std::weak_ptr<proof_node> parent,
                   std::vector<std::shared_ptr<proof_node>> refinement_blocks);

        std::string tree_to_string();

        std::shared_ptr<proof_node> clone();

        bool is_leaf() const;

        bool is_root() const;

//        bool pruning_enabled();

        void tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node>)> fun);

        void tree_bfs_iter(std::function<void(std::shared_ptr<proof_node>)> fun);

        std::list<std::shared_ptr<proof_node>> get_tree_nodes();

//        void clean_pruning_triggers();

        std::string JSON_stringify();

        const std::string dump_tree_str(bool javascript_compliant, const std::string heading_name = "");
        void dump_tree(const std::string& fname, bool javascript_compliant, const std::string heading_name = "");

        std::shared_ptr<proof_node> get_by_path(tree_path path);

        void consolidate_tree();

//        bool refine_tree(std::list<std::shared_ptr<proof_node>>& nodes, int max_depth, int child_count);

        //FIXME: to be removed...
        inline void add_child(std::shared_ptr<proof_node> node) {
            this->_refinement_blocks.push_back(node);
        }
        inline void remove_children() {
            this->_refinement_blocks.clear();
            this->leaf_infos = std::make_unique<leaves_infos>(leaves_infos());
            this->consolidate_tree();
        }

    };

    class proof_checker;

    class proof_t {
    private:
        std::shared_ptr<proof_node> init_get_root(const std::vector<atomp>& orig_atoms,
                                                 const std::vector<rulep>& orig_rules,
                                                 const std::shared_ptr<arbac_policy>& policy,
                                                 const Expr& to_check);

        std::shared_ptr<proof_node> create_tree_root(const int policy_atom_count,
                                                     const std::vector<atomp> &atoms,
                                                     const std::vector<rulep> &rules,
                                                     const Expr &to_check);

        proof_t(const OverapproxOptions _overapprox_strategy,
                const atomp _target_atom,
                std::shared_ptr<proof_node> _proof_tree,
                const std::set<userp, std::function<bool(const userp &, const userp &)>> _initial_confs);

    public:
        const OverapproxOptions overapprox_strategy;
        const atomp target_atom;
        std::shared_ptr<proof_node> proof_tree;
        const std::set<userp, std::function<bool(const userp &, const userp &)>> initial_confs;

        proof_t(const OverapproxOptions strategy,
                const std::vector<atomp>& orig_atoms,
                const std::vector<rulep>& orig_rules,
                const std::shared_ptr<arbac_policy>& policy,
                const Expr& to_check);

        std::shared_ptr<proof_t> clone();

        std::string tree_to_string();

        bool refine_proof(std::list<std::shared_ptr<proof_node>>& nodes, int max_depth, int child_count);

        const std::string dump_proof_str(bool javascript_compliant, const std::string heading_name = "");
        void dump_proof(const std::string& fname, bool javascript_compliant, const std::string heading_name = "");

    };

    typedef std::shared_ptr<proof_t> proofp;

    enum class over_analysis_result {
        SAFE,
        UNSAFE,
        UNSAFE_INCOMPLETE
    };

    class proof_checker {
        virtual std::pair<over_analysis_result, std::list<std::shared_ptr<proof_node>>>
                verify_proof_get_refinement(proofp proof) = 0;
        virtual over_analysis_result verify_proof(proofp proof) = 0;
        virtual over_analysis_result verify_proof(proofp proof,
                                                  std::map<std::shared_ptr<proof_node>, pruning_triggers> triggers) = 0;
    };
}

#endif //VACSAT_OVER_STRUCTURES_H
