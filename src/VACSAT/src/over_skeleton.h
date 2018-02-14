//
// Created by esteffin on 12/4/17.
//

#ifndef VACSAT_OVER_SKELETON_H
#define VACSAT_OVER_SKELETON_H

#include <vector>
#include <memory>
#include <fstream>
#include <queue>
#include "Policy.h"

namespace SMT {

    class role_choicer {
    public:
        enum Choice {
            REQUIRED,
            FREE,
            EXCLUDED
        };
        virtual Choice classify(atomp r) const = 0;
        virtual int get_required_count() const = 0;
    };

    typedef std::list<int> tree_path;
    std::string tree_path_to_string(tree_path& path) {
        std::string ret = "_root";
        for (auto &&p : path) {
            ret = ret + "_" + std::to_string(p);
        }
        return ret + "_";
    }

    class invariant {
    public:
        const atomp atom;
        const bool value;
        const Expr expr;

        inline bool operator == (const invariant& rhs) const {
            return this->atom->role_array_index == rhs.atom->role_array_index &&
                    this->value == rhs.value;
        }

        inline bool operator <(invariant const& rhs)const {
            if (this->atom->role_array_index == rhs.atom->role_array_index) {
                return this->value < rhs.value;
            }
            return this->atom->role_array_index < rhs.atom->role_array_index;
        }

        invariant clone() {
            invariant res(this->atom,
                          this->value);
            return res;
        }

        invariant(atomp _atom,
                  bool _value) :
                atom(_atom),
                value(_value),
                expr(createEqExpr(createLiteralp(atom),
                                  createConstantExpr(value, 1))) { }

    };

    class invariants {
        std::set<invariant> cnt;
        bool cnt_changed = true;
        std::map<atomp, std::set<bool>> cache;
    public:

        invariants clone() {
            std::set<invariant> _cnt = this->cnt;
            invariants res;
            res.cnt = _cnt;
            res.cnt_changed = true;
            return res;
        }

        invariants():
                cnt(std::set<invariant>()),
                cnt_changed(true),
                cache(std::map<atomp, std::set<bool>>()){ }

        const std::map<atomp, std::set<bool>>& get_as_map() {
            if (!cnt_changed) {
                return cache;
            }
            cnt_changed = false;
            for (auto &&inv : cnt) {
                cache[inv.atom].insert(inv.value);
            }
            return cache;
        };

        void add_invariant(invariant inv) {
            cnt.insert(std::move(inv));
            cache = std::map<atomp, std::set<bool>>();
            cnt_changed = true;
        }

        const std::set<invariant>& get_as_set() {
            return cnt;
        }

        Expr get_expr() {
            if (cnt.empty()) {
                return nullptr;
            }
            auto ite = cnt.begin();
            Expr res = ite->expr;
            for (++ite; ite != cnt.end(); ++ite) {
                res = createAndExpr(res, ite->expr);
            }
            return res;
        }
    };

    class node_invariants {
    public:
        invariants inv_pre_A;
        invariants inv_A_C;
        invariants inv_post_C;

        node_invariants clone() {
            node_invariants res;

            res.inv_pre_A = this->inv_pre_A.clone();
            res.inv_A_C = this->inv_A_C.clone();
            res.inv_post_C = this->inv_post_C.clone();

            return res;
        }

        node_invariants() :
                inv_pre_A(invariants()),
                inv_A_C(invariants()),
                inv_post_C(invariants()) { }
    };

    class node_policy_infos {
    public:
        std::vector<rulep> rules_a;
        std::vector<rulep> rules_c;
        std::vector<atomp> all_atoms;
        std::vector<atomp> atoms_a;
        int policy_atoms_count;

        node_policy_infos clone() {
            const std::vector<rulep> _rules_a = this->rules_a;
            const std::vector<rulep> _rules_c = this->rules_c;
            const std::vector<atomp> _all_atoms = this->all_atoms;
            const std::vector<atomp> _atoms_a = this->atoms_a;

            node_policy_infos res(_rules_a, _rules_c, _all_atoms, _atoms_a, this->policy_atoms_count);

            return res;
        }


        node_policy_infos(const node_policy_infos &n_i) :
                rules_a(n_i.rules_a),
                rules_c(n_i.rules_c),
                all_atoms(n_i.all_atoms),
                atoms_a(n_i.atoms_a),
                policy_atoms_count(n_i.policy_atoms_count) { }

        node_policy_infos(std::vector<rulep> _rules_a,
                          std::vector<rulep> _rules_c,
                          std::vector<atomp> _all_atoms,
                          std::vector<atomp> _atoms_a,
                          int _policy_atoms_count):
                rules_a(std::move(_rules_a)),
                rules_c(std::move(_rules_c)),
                all_atoms(std::move(_all_atoms)),
                atoms_a(std::move(_atoms_a)),
                policy_atoms_count(_policy_atoms_count) { }

        std::string JSON_stringify(const std::string& prefix = "") {
            std::stringstream fmt;
            std::string i_prefix = prefix;
            fmt << "{" << std::endl;
            i_prefix = prefix + "\t";

            fmt << i_prefix << "rules_a: [" << std::endl;
            for (auto &&rule_a : rules_a) {
                fmt << i_prefix << "\t\"" << *rule_a << "\"," << std::endl;
            }
            fmt << i_prefix << "]," << std::endl;

            fmt << i_prefix << "rules_c: [" << std::endl;
            for (auto &&rule_c : rules_c) {
                fmt << i_prefix << "\t\"" << *rule_c << "\"," << std::endl;
            }
            fmt << i_prefix << "]," << std::endl;

            fmt << i_prefix << "all_atoms: [" << std::endl;
            for (auto &&all_atom : all_atoms) {
                fmt << i_prefix << "\t\"" << *all_atom << "\"," << std::endl;
            }
            fmt << i_prefix << "]," << std::endl;

            fmt << i_prefix << "atoms_a: [" << std::endl;
            for (auto &&atom_a : atoms_a) {
                fmt << i_prefix << "\t\"" << *atom_a << "\"," << std::endl;
            }
            fmt << i_prefix << "]," << std::endl;

            fmt << i_prefix << "policy_atoms_count: " << policy_atoms_count << std::endl;

            fmt << prefix << "}";

            return fmt.str();
        }
    };

    class pruning_triggers {
    public:
        std::unique_ptr<std::pair<atomp, bool>> pre_A_check;
        std::unique_ptr<std::pair<atomp, bool>> A_C_check;
        std::unique_ptr<std::pair<atomp, bool>> post_A_check;
        std::unique_ptr<std::pair<atomp, bool>> pre_A_blocked_check;
        std::unique_ptr<std::pair<atomp, bool>> post_A_blocked_check;
        bool no_skip;
        bool no_priority;

        //FOR LEAVES ONLY
        bool overapprox;
        bool check_gap;

        pruning_triggers clone() {
            std::pair<atomp, bool> _pre_A_check_cnt = *this->pre_A_check;
            std::pair<atomp, bool> _A_C_check_cnt = *this->A_C_check;
            std::pair<atomp, bool> _post_A_check_cnt = *this->post_A_check;
            std::pair<atomp, bool> _pre_A_blocked_check_cnt = *this->pre_A_blocked_check;
            std::pair<atomp, bool> _post_A_blocked_check_cnt = *this->post_A_blocked_check;
            bool _no_skip = no_skip;
            bool _no_priority = no_priority;

            bool _overapprox = this->overapprox;
            bool _check_gap = this->check_gap;

            pruning_triggers res;

            std::unique_ptr<std::pair<atomp, bool>> _pre_A_check =
                    std::make_unique<std::pair<atomp, bool>>(_pre_A_check_cnt);
            std::unique_ptr<std::pair<atomp, bool>> _A_C_check =
                    std::make_unique<std::pair<atomp, bool>>(_A_C_check_cnt);
            std::unique_ptr<std::pair<atomp, bool>> _post_A_check =
                    std::make_unique<std::pair<atomp, bool>>(_post_A_check_cnt);
            std::unique_ptr<std::pair<atomp, bool>> _pre_A_blocked_check =
                    std::make_unique<std::pair<atomp, bool>>(_pre_A_blocked_check_cnt);
            std::unique_ptr<std::pair<atomp, bool>> _post_A_blocked_check =
                    std::make_unique<std::pair<atomp, bool>>(_post_A_blocked_check_cnt);

            res.pre_A_check = std::move(pre_A_check);
            res.A_C_check = std::move(A_C_check);
            res.post_A_check = std::move(post_A_check);
            res.pre_A_blocked_check = std::move(pre_A_blocked_check);
            res.post_A_blocked_check = std::move(post_A_blocked_check);
            res.no_skip = no_skip;
            res.no_priority = no_priority;

            res.overapprox = _overapprox;
            res.check_gap = _check_gap;

            return res;
        }

        void clean() {
            this->pre_A_check = nullptr;
            this->A_C_check = nullptr;
            this->post_A_check = nullptr;
            this->pre_A_blocked_check = nullptr;
            this->post_A_blocked_check = nullptr;
            this->no_skip = false;
            this->no_priority = false;
            this->overapprox = false;
            this->check_gap = false;
        }

        pruning_triggers() :
                pre_A_check(nullptr),
                A_C_check(nullptr),
                post_A_check(nullptr),
                pre_A_blocked_check(nullptr),
                post_A_blocked_check(nullptr),
                no_skip(false),
                no_priority(false),
                overapprox(false),
                check_gap(false) { }
    };

    class leaves_infos {
    public:
        enum class gap_info {
            UNKNOWN,
            YES,
            NO };

        static const std::string gap_to_string(const gap_info info) {
            switch (info) {
                case gap_info::UNKNOWN:
                    return "UNKNOWN";
                case gap_info::YES:
                    return "YES";
                case gap_info::NO:
                    return "NO";
            }
            return "uh?";
        }

        std::map<atomp, std::set<bool>> nondet_restriction;
        gap_info gap;

        leaves_infos clone() {
            std::map<atomp, std::set<bool>> _nondet_restriction = this->nondet_restriction;
            leaves_infos res;
            res.nondet_restriction = _nondet_restriction;
            res.gap = this->gap;
            return res;
        }

        leaves_infos():
                nondet_restriction(std::map<atomp, std::set<bool>>()),
                gap(gap_info::UNKNOWN) { }

        std::string JSON_stringify(const std::string& prefix = "") {
            std::stringstream fmt;
            fmt << "{" << std::endl;
            fmt << prefix << "\tgap: " << gap_to_string(gap) << "," << std::endl;
            fmt << prefix << "\tnondet_restriction: {" << std::endl; //"..." << std::endl;
            for (auto &&kv : nondet_restriction) {
                fmt << prefix << "\t" << *kv.first << ": { ";
                for (auto &&v : kv.second) {
                    fmt << bool_to_true_false(v) << ", ";
                }
                fmt << "}," << std::endl;
            }
            fmt << prefix << "}";
            return fmt.str();
        }
    };

    template <typename SolverState>
    class proof_node : public std::enable_shared_from_this<proof_node<SolverState>> {//: public node<LayerInfo, BlockInfo> {
    private:
        class tree_printer {
        private:
            std::string depth;

            void Push( char c ) {
                depth += ' ';
                depth += c;
                depth += ' ';
                depth += ' ';
            }

            void Pop( ) {
                depth = depth.substr(0, depth.size() - 4);
            }

            void tree_to_string (std::stringstream& stream, const proof_node<SolverState>* tree) {
                stream << "(" << tree->uid << ")" << std::endl;

                auto ite = tree->refinement_blocks.begin();

                while (ite != tree->refinement_blocks.end()) {
                    const std::shared_ptr<proof_node<SolverState>>& child = *ite;
                    ++ite;
                    stream << depth << " `--";
                    Push( ite != tree->refinement_blocks.end() ? '|' : ' ' );
                    tree_to_string( stream, child.get() );
                    Pop( );
                }
            }

        public:
            std::string operator()(const proof_node<SolverState>* tree) {
                std::stringstream str;
                tree_to_string(str, tree);
                return str.str();
            }

        };

        std::shared_ptr<proof_node<SolverState>> memberwise_clone() {
            if (this->solver_state != nullptr) {
                throw std::runtime_error("Solver state must be null when cloning");
            }

            tree_path c_path = this->path;
            std::string c_uid = this->uid;
            int c_depth = this->depth;
            bool c_is_leaf = this->is_leaf;

            node_invariants c_invariants = this->invariants.clone();
            node_policy_infos c_node_infos = this->node_infos.clone();
            std::unique_ptr<leaves_infos> c_leaf_infos = nullptr;
            if (this->leaf_infos != nullptr) {
                leaves_infos c_leaf_infos_cnt = *this->leaf_infos;
                c_leaf_infos = std::make_unique<leaves_infos>(c_leaf_infos_cnt);
            }

            pruning_triggers c_triggers = this->triggers.clone();

            // WEAK VALUES ARE REBBUILT AFTER
//            std::list<std::weak_ptr<proof_node<SolverState>>> c_ancestors;
//            std::weak_ptr<proof_node<SolverState>> c_parent;
            std::shared_ptr<proof_node<SolverState>> c_node(
                    new proof_node<SolverState>(c_path,
                                                c_uid,
                                                c_depth,
                                                c_is_leaf,
                                                c_invariants,
                                                c_node_infos,
                                                std::move(c_leaf_infos),
                                                c_triggers,
                                                nullptr,
                                                std::list<std::weak_ptr<proof_node<SolverState>>>(),
                                                std::weak_ptr<proof_node<SolverState>>(),
                                                std::vector<std::shared_ptr<proof_node<SolverState>>>()));

            for (std::shared_ptr<proof_node<SolverState>> &&child : this->refinement_blocks) {
                std::shared_ptr<proof_node<SolverState>> c_child = child->memberwise_clone();
//                c_child->parent = c_node;
                c_node->refinement_blocks.push_back(c_child);
            }


            return c_node;
        };

        void rebuild_weak_ptrs() {
            std::list<std::weak_ptr<proof_node<SolverState>>> last_ancestors = this->ancestors;
            std::shared_ptr<proof_node<SolverState>> this_shared(this->shared_from_this());
            last_ancestors.push_back(this_shared);
            for (std::shared_ptr<proof_node<SolverState>> &&child : this->refinement_blocks) {
                child->parent = this_shared;
                child->ancestors = last_ancestors;
                child->rebuild_weak_ptrs();
                last_ancestors.push_back(child);
            }
        }

        void get_nodes(proof_node<SolverState>* node,
                       std::list<proof_node<SolverState>*>& list) {
            list.push_back(node);
            for (auto &&child : node->refinement_blocks) {
                get_nodes(child.get(), list);
            }
        };

        void filter_nodes_tail(std::list<std::shared_ptr<proof_node<SolverState>>>& acc,
                               std::function<bool(std::shared_ptr<proof_node<SolverState>>&)> fn) {
            std::shared_ptr<proof_node<SolverState>> _this = this->shared_from_this();
            if (fn(_this)) {
                acc.push_back(_this);
            }
            for (auto &&child : refinement_blocks) {
                filter_nodes_tail(acc, fn);
            }
        }

        void get_tree_nodes_tail(std::list<std::shared_ptr<proof_node<SolverState>>>& ret_list) {
            ret_list.push_back(this->shared_from_this());
            for (auto &&child : refinement_blocks) {
                child->get_tree_nodes_tail(ret_list);
            }
        }

        void JSON_stringify_node(std::stringstream& fmt, const std::string& prefix = "") {
            fmt << prefix << "{" << std::endl;
            std::string i_prefix = prefix + "\t";
            std::string omissis = "\"...\"";
            fmt << i_prefix << "uid: " << uid << "," << std::endl;
            fmt << i_prefix << "path: " << tree_path_to_string(path) << "," << std::endl;
            fmt << i_prefix << "depth: " << std::to_string(depth) << "," << std::endl;
            fmt << i_prefix << "node_infos: " << node_infos.JSON_stringify(i_prefix) << "," << std::endl;
            fmt << i_prefix << "leaf_infos: " << (leaf_infos == nullptr ? "null" : leaf_infos->JSON_stringify(i_prefix)) << "," << std::endl;
            fmt << i_prefix << "invariants: " << omissis << "," << std::endl;
            fmt << i_prefix << "triggers: " << omissis << "," << std::endl;
            fmt << i_prefix << "solver_state: " << omissis << "," << std::endl;
            auto shared_parent = parent.lock();
            fmt << i_prefix << "parent: " << (shared_parent == nullptr ? "null" : shared_parent->uid) << "," << std::endl;
            fmt << i_prefix << "ancestors: [" << std::endl;
            for (auto &&w_ancestor : ancestors) {
                auto ancestor = w_ancestor.lock();
                fmt << i_prefix << "\t" << ancestor->uid << "," << std::endl;
            }
            fmt << i_prefix << "]," << std::endl;

            fmt << i_prefix << "refinement_blocks: [" << std::endl;
            for (auto &&child : refinement_blocks) {
                fmt << i_prefix << "\t" << child->uid << "," << std::endl;
            }
            fmt << i_prefix << "]" << std::endl;
            fmt << prefix << "}";
        }

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

        std::list<std::shared_ptr<proof_node<SolverState>>> get_all_nodes() {
            std::list<std::shared_ptr<proof_node<SolverState>>> res;
            filter_nodes_tail(res, [] (std::shared_ptr<proof_node<SolverState>>& node) { return true; });
            return std::move(res);
        }

        std::list<std::shared_ptr<proof_node<SolverState>>> get_all_leaves() {
            std::list<std::shared_ptr<proof_node<SolverState>>> res;
            filter_nodes_tail(res, [] (std::shared_ptr<proof_node<SolverState>>& node) { return node->is_leaf(); });
            return std::move(res);
        }

        proof_node(tree_path _path,
                   int _depth,
                   const node_policy_infos& _node_infos,
                   std::unique_ptr<leaves_infos> _leaves_infos,
                   std::list<std::weak_ptr<proof_node<SolverState>>> _ancestors,
                   std::weak_ptr<proof_node<SolverState>> _parent) :
                path(std::move(_path)),
                uid(tree_path_to_string(path)),
                depth(_depth),
                invariants(node_invariants()),
                node_infos(_node_infos),
                leaf_infos(std::move(_leaves_infos)),
                triggers(pruning_triggers()),
                solver_state(nullptr),
                ancestors(std::move(_ancestors)),
                parent(_parent),
                refinement_blocks(std::vector<std::shared_ptr<proof_node<SolverState>>>()) { }

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
                   std::vector<std::shared_ptr<proof_node<SolverState>>> _refinement_blocks):
                path(std::move(_path)),
                uid(std::move(_uid)),
                depth(_depth),
                invariants(std::move(_invariants)),
                node_infos(_node_infos),
                leaf_infos(std::move(_leaf_infos)),
                pruning_triggers(_pruning_triggers),
                solver_state(_solver_state),
                ancestors(_ancestors),
                parent(_parent),
                refinement_blocks(_refinement_blocks) { }

        std::string tree_to_string() {
            std::stringstream stream;
            tree_printer printer;
            stream << printer(this);
            return stream.str();
        }

        std::shared_ptr<proof_node<SolverState>> clone() {
            std::shared_ptr<proof_node<SolverState>> cloned = this->memberwise_clone();
            cloned->rebuild_weak_ptrs();
            return cloned;
        }

        std::pair<std::string, std::string> tree_to_full_string() {
            tree_printer printer;

//            std::list<proof_node<SolverState>*> nodes;
            std::stringstream stream;

//            get_nodes(this, nodes);
//            for (auto &&node : nodes) {
//                stream << node->uid << ":" << std::endl;
//                stream << "\tleaf: " << bool_to_true_false(node->is_leaf()) << std::endl;
//                stream << node->infos;
//            }

            return std::pair<std::string, std::string>(printer(this), stream.str());
        }

        bool is_leaf() {
            return refinement_blocks.empty();
        }

        bool is_root() {
            return depth == 0;
        }

        void tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node<SolverState>>)> fun) {
            fun(this->shared_from_this());
            for (auto &&child : this->refinement_blocks) {
                child->tree_pre_order_iter(fun);
            }
        }

        void tree_dfs_iter(std::function<void(std::shared_ptr<proof_node<SolverState>>)> fun) {
            std::queue<std::shared_ptr<proof_node<SolverState>>> queue;
            queue.push(this->shared_from_this());
            while (!queue.empty()) {
                std::shared_ptr<proof_node<SolverState>> node = queue.front();
                queue.pop();
                fun(node);
                for (auto &&child : refinement_blocks) {
                    queue.push(child);
                }
            }
        }

        std::list<std::shared_ptr<proof_node<SolverState>>> get_tree_nodes() {
            std::list<std::shared_ptr<proof_node<SolverState>>> ret;
            get_tree_nodes_tail(ret);
            return std::move(ret);
        }

        void clean_solver_info_state() {
            this->solver_state = nullptr;
//            node->node_infos->solverInfo->refineable = b_solver_info::UNSET;
            for (auto &&child :this->refinement_blocks) {
                child->clean_solver_info_state();
            }
        }

        std::string JSON_stringify() {
            std::stringstream fmt;
            fmt << "[" <<std::endl;
            this->tree_dfs_iter([&fmt](std::shared_ptr<proof_node<SolverState>> node) {
                node->JSON_stringify_node(fmt, "\t");
                fmt << "," << std::endl;
            });
            fmt << "]" <<std::endl;
            return fmt.str();
        }

        void dump_tree(const std::string& fname) {
            std::ofstream out(fname);
            std::string structure = this->tree_to_string();
            std::string details = this->JSON_stringify();
            out << "/*" << std::endl;
            out << structure;
            out << "*/" << std::endl << std::endl;
            out << details;
            out << std::endl << std::endl;
            out.close();
        }
    };

    template <typename BlockSolverInfo>
    class simple_block_info {
    public:
//        const std::shared_ptr<arbac_policy>& policy;
        //NEEDED TO KNOW ARRAYS DIMENSIONS
        const int policy_atom_count;
        const std::vector<atomp> atoms;
        const std::vector<rulep> rules;
        std::shared_ptr<BlockSolverInfo> solverInfo;
        const Expr invariant;

        friend std::ostream& operator<< (std::ostream& stream, const simple_block_info& self) {
            stream << "\tpolicy_atom_count: " << self.policy_atom_count << std::endl;
            stream << "\tatoms: " << std::endl;
            for (auto &&atom : self.atoms) {
                stream << "\t\t" << *atom << std::endl;
            }
            stream << "\trules: " << std::endl;
            for (auto &&rule : self.rules) {
                stream << "\t\t" << *rule << std::endl;
            }
//            stream << "\tsolverInfo: " << *self.solverInfo << std::endl;
            stream << "\tinvariant: " << *self.invariant << std::endl;

            return stream;
        }

        simple_block_info(//const std::shared_ptr<arbac_policy>& _policy,
                          const int _policy_atom_count,
                          const std::vector<atomp> _atoms,
                          const std::vector<rulep> _rules,
                          std::shared_ptr<BlockSolverInfo> _solverInfo,
                          Expr _invariant):
//                policy(_policy),
                policy_atom_count(_policy_atom_count),
                atoms(_atoms),
                rules(_rules),
                solverInfo(_solverInfo),
                invariant(_invariant) { }
    };

}

#endif //VACSAT_OVER_SKELETON_H
