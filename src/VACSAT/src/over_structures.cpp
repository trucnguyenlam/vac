//
// Created by esteffin on 3/14/18.
//

#include "over_structures.h"

namespace SMT {

    std::string tree_path_to_string(tree_path &path) {
        std::string ret = "_root";
        for (auto &&p : path) {
            ret = ret + "_" + std::to_string(p);
        }
        return ret + "_";
    }

    // INVARIANT FUNCTIONS
    invariant::invariant(atomp _atom,
                         bool _value) : atom(std::move(_atom)),
                                        value(_value),
                                        expr(createEqExpr(createLiteralp(atom),
                                                          createConstantExpr(value, 1))) { }

    invariant invariant::clone() {
        invariant res(this->atom,
                      this->value);
        return res;
    }

    // INVARIANTS FUNCTIONS
    invariants::invariants():
            cnt(std::set<invariant>()),
            cnt_changed(true),
            cache(std::map<atomp, std::set<bool>>()){ }

    invariants invariants::clone() {
        std::set<invariant> _cnt = this->cnt;
        invariants res;
        res.cnt = _cnt;
        res.cnt_changed = true;
        return res;
    }

    const std::map<atomp, std::set<bool>>& invariants::get_as_map() {
        if (!cnt_changed) {
            return cache;
        }
        cnt_changed = false;
        for (auto &&inv : cnt) {
            cache[inv.atom].insert(inv.value);
        }
        return cache;
    };

    void invariants::add_invariant(invariant inv) {
        cnt.insert(std::move(inv));
        cache = std::map<atomp, std::set<bool>>();
        cnt_changed = true;
    }

    const std::set<invariant>& invariants::get_as_set() {
        return cnt;
    }

    Expr invariants::get_expr() {
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

    // NODE_INVARIANT FUNCTIONS
    node_invariants::node_invariants() :
            inv_pre_A(invariants()),
            inv_A_C(invariants()),
            inv_post_C(invariants()) { }

    node_invariants node_invariants::clone() {
        node_invariants res;

        res.inv_pre_A = this->inv_pre_A.clone();
        res.inv_A_C = this->inv_A_C.clone();
        res.inv_post_C = this->inv_post_C.clone();

        return res;
    }

    // NODE_POLICY_INFOS FUNCTIONS
    /*node_policy_infos::node_policy_infos(const node_policy_infos &n_i) :
            rules_a(n_i.rules_a),
            rules_c(n_i.rules_c),
            all_atoms(n_i.all_atoms),
            atoms_a(n_i.atoms_a),
            policy_atoms_count(n_i.policy_atoms_count) { }*/

    node_policy_infos::node_policy_infos(std::vector<rulep> _rules_a,
                                         std::vector<rulep> _rules_c,
                                         std::vector<atomp> _all_atoms,
                                         std::vector<atomp> _atoms_a,
                                         int _policy_atoms_count):
            rules_a(std::move(_rules_a)),
            rules_c(std::move(_rules_c)),
            all_atoms(std::move(_all_atoms)),
            atoms_a(std::move(_atoms_a)),
            policy_atoms_count(_policy_atoms_count) { }

    node_policy_infos node_policy_infos::clone() {
        const std::vector<rulep> _rules_a = this->rules_a;
        const std::vector<rulep> _rules_c = this->rules_c;
        const std::vector<atomp> _all_atoms = this->all_atoms;
        const std::vector<atomp> _atoms_a = this->atoms_a;

        node_policy_infos res(_rules_a, _rules_c, _all_atoms, _atoms_a, this->policy_atoms_count);

        return res;
    }

    std::string node_policy_infos::JSON_stringify(const std::string& prefix) {
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

    // PRUNING_TRIGGERS FUNCTIONS
    pruning_triggers::pruning_triggers() :
            c_rule_check(nullptr),
            pre_A_check(nullptr),
            A_C_check(nullptr),
            post_A_check(nullptr),
            pre_A_blocked_check(nullptr),
            post_A_blocked_check(nullptr),
            no_transition(false),
            no_skip(false),
            no_priority(false),
            no_sfogo(false),
            overapprox(maybe_bool::UNKNOWN),
            check_gap(false) { }

    pruning_triggers pruning_triggers::clone() {
        bool _no_transition = no_transition;
        bool _no_skip = no_skip;
        bool _no_priority = no_priority;
        bool _no_sfogo = no_sfogo;

        maybe_bool _overapprox = this->overapprox;
        bool _check_gap = this->check_gap;

        pruning_triggers res;

        std::unique_ptr<rulep> _c_rule_check = nullptr;
        if (this->c_rule_check != nullptr) {
            rulep _c_rule_check_cnt = *this->c_rule_check;
            _c_rule_check = std::make_unique<rulep>(_c_rule_check_cnt);
        }
        std::unique_ptr<std::pair<atomp, bool>> _pre_A_check = nullptr;
        if (this->pre_A_check != nullptr) {
            std::pair<atomp, bool> _pre_A_check_cnt = *this->pre_A_check;
            _pre_A_check = std::make_unique<std::pair<atomp, bool>>(_pre_A_check_cnt);
        }
        std::unique_ptr<std::pair<atomp, bool>> _A_C_check = nullptr;
        if (this->A_C_check != nullptr) {
            std::pair<atomp, bool> _A_C_check_cnt = *this->A_C_check;
            _A_C_check = std::make_unique<std::pair<atomp, bool>>(_A_C_check_cnt);
        }
        std::unique_ptr<std::pair<atomp, bool>> _post_A_check = nullptr;
        if (this->post_A_check != nullptr) {
            std::pair<atomp, bool> _post_A_check_cnt = *this->post_A_check;
            _post_A_check = std::make_unique<std::pair<atomp, bool>>(_post_A_check_cnt);
        }
        std::unique_ptr<std::pair<atomp, bool>> _pre_A_blocked_check = nullptr;
        if (this->pre_A_blocked_check != nullptr) {
            std::pair<atomp, bool> _pre_A_blocked_check_cnt = *this->pre_A_blocked_check;
            _pre_A_blocked_check = std::make_unique<std::pair<atomp, bool>>(_pre_A_blocked_check_cnt);
        }
        std::unique_ptr<std::pair<atomp, bool>> _post_A_blocked_check = nullptr;
        if (this->post_A_blocked_check != nullptr) {
            std::pair<atomp, bool> _post_A_blocked_check_cnt = *this->post_A_blocked_check;
            _post_A_blocked_check = std::make_unique<std::pair<atomp, bool>>(_post_A_blocked_check_cnt);
        }

        res.c_rule_check = std::move(_c_rule_check);
        res.pre_A_check = std::move(_pre_A_check);
        res.A_C_check = std::move(_A_C_check);
        res.post_A_check = std::move(_post_A_check);
        res.pre_A_blocked_check = std::move(_pre_A_blocked_check);
        res.post_A_blocked_check = std::move(_post_A_blocked_check);
        res.no_transition = _no_transition;
        res.no_skip = _no_skip;
        res.no_priority = _no_priority;
        res.no_sfogo = _no_sfogo;

        res.overapprox = _overapprox;
        res.check_gap = _check_gap;

        return res;
    }

    void pruning_triggers::clean() {
        this->c_rule_check = nullptr;
        this->pre_A_check = nullptr;
        this->A_C_check = nullptr;
        this->post_A_check = nullptr;
        this->pre_A_blocked_check = nullptr;
        this->post_A_blocked_check = nullptr;
        this->no_transition = false;
        this->no_skip = false;
        this->no_priority = false;
        this->overapprox = maybe_bool::UNKNOWN;
        this->check_gap = false;
        this->no_sfogo = false;
    }

    bool pruning_triggers::probing_enabled() {
        return this->c_rule_check != nullptr ||
               this->pre_A_check != nullptr ||
               this->A_C_check != nullptr ||
               this->post_A_check != nullptr ||
               this->pre_A_blocked_check != nullptr ||
               this->post_A_blocked_check != nullptr ||
               this->no_transition ||
               this->no_skip ||
               this->no_priority ||
               this->overapprox != maybe_bool::UNKNOWN ||
               this->check_gap ||
               this->no_sfogo;
    }

    std::string pruning_triggers::JSON_stringify(const std::string& prefix) {
        if (!this->probing_enabled()) {
            return "false";
        }
        std::stringstream fmt;
        std::string i_prefix = prefix;
        fmt << "{" << std::endl;
        i_prefix = prefix + "\t";

        fmt << i_prefix << "c_rule_check: ";
        if (this->c_rule_check != nullptr) {
            fmt << (*c_rule_check)->to_string() << "," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "pre_A_check: ";
        if (this->pre_A_check != nullptr) {
            fmt << "{" << pre_A_check->first->name << ", " << pre_A_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "A_C_check: ";
        if (this->A_C_check != nullptr) {
            fmt << "{" << A_C_check->first->name << ", " << A_C_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "post_A_check: ";
        if (this->post_A_check != nullptr) {
            fmt << "{" << post_A_check->first->name << ", " << post_A_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "pre_A_blocked_check: ";
        if (this->pre_A_blocked_check != nullptr) {
            fmt << "{" << pre_A_blocked_check->first->name << ", " << pre_A_blocked_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "post_A_blocked_check: ";
        if (this->post_A_blocked_check != nullptr) {
            fmt << "{" << post_A_blocked_check->first->name << ", " << post_A_blocked_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "no_transition: " << bool_to_true_false(no_transition) << "," << std::endl;
        fmt << i_prefix << "no_skip: " << bool_to_true_false(no_skip) << "," << std::endl;
        fmt << i_prefix << "no_priority: " << bool_to_true_false(no_priority) << "," << std::endl;
        fmt << i_prefix << "no_sfogo: " << bool_to_true_false(no_sfogo) << "," << std::endl;
        fmt << i_prefix << "overapprox: " << maybe_bool_to_string(overapprox) << "," << std::endl;
        fmt << i_prefix << "check_gap: " << bool_to_true_false(check_gap) << "," << std::endl;

        fmt << prefix << "}";

        return fmt.str();
    }

    // LEAVES_INFOS FUNCTIONS
    leaves_infos::leaves_infos():
            nondet_restriction(std::map<atomp, std::set<bool>>()),
            gap(maybe_bool::UNKNOWN) { }

    leaves_infos leaves_infos::clone() {
        std::map<atomp, std::set<bool>> _nondet_restriction = this->nondet_restriction;
        leaves_infos res;
        res.nondet_restriction = _nondet_restriction;
        res.gap = this->gap;
        return res;
    }

    std::string leaves_infos::JSON_stringify(const std::string& prefix) {
        std::stringstream fmt;
        fmt << "{" << std::endl;
        fmt << prefix << "\tgap: " << maybe_bool_to_string(gap) << "," << std::endl;
        fmt << prefix << "\tnondet_restriction: {" << std::endl; //"..." << std::endl;
        std::string nprefix = prefix + "\t";
        for (auto &&kv : nondet_restriction) {
            fmt << nprefix << "\t" << *kv.first << ": { ";
            for (auto &&v : kv.second) {
                fmt << bool_to_true_false(v) << ", ";
            }
            fmt << "}," << std::endl;
        }
        fmt << nprefix << "}" << std::endl;
        fmt << prefix << "}";
        return fmt.str();
    }

    // TREE FUNCTIONS

    // TREE PRIVATE FUNCTIONS
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

        void tree_to_string (std::stringstream& stream, const proof_node* tree) {
            stream << "(" << tree->uid << ")" << std::endl;

            auto ite = tree->refinement_blocks.begin();

            while (ite != tree->refinement_blocks.end()) {
                const std::shared_ptr<proof_node>& child = *ite;
                ++ite;
                stream << depth << " `--";
                Push( ite != tree->refinement_blocks.end() ? '|' : ' ' );
                tree_to_string( stream, child.get() );
                Pop( );
            }
        }

    public:
        std::string operator()(const proof_node* tree) {
            std::stringstream str;
            tree_to_string(str, tree);
            return str.str();
        }

    };

    std::shared_ptr<proof_node> proof_node::memberwise_clone() {

        tree_path c_path = this->path;
        std::string c_uid = this->uid;
        int c_depth = this->depth;
        bool c_is_leaf = this->is_leaf();

        node_invariants c_invariants = this->invariants.clone();
        node_policy_infos c_node_infos = this->node_infos.clone();
        std::unique_ptr<leaves_infos> c_leaf_infos = nullptr;
        if (this->leaf_infos != nullptr) {
            leaves_infos c_leaf_infos_cnt = *this->leaf_infos;
            c_leaf_infos = std::make_unique<leaves_infos>(c_leaf_infos_cnt);
        }

//            pruning_triggers c_triggers = ;

        // WEAK VALUES ARE REBBUILT AFTER
//            std::list<std::weak_ptr<proof_node>> c_ancestors;
//            std::weak_ptr<proof_node> c_parent;
        std::shared_ptr<proof_node> c_node(
                new proof_node(c_path,
                                            c_uid,
                                            c_depth,
                                            c_invariants,
                                            c_node_infos,
                                            std::move(c_leaf_infos),
                                            this->triggers.clone(),
                                            std::list<std::weak_ptr<proof_node>>(),
                                            std::weak_ptr<proof_node>(),
                                            std::vector<std::shared_ptr<proof_node>>()));

        for (auto &&child : this->refinement_blocks) {
            std::shared_ptr<proof_node> c_child = child->memberwise_clone();
//                c_child->parent = c_node;
            c_node->refinement_blocks.push_back(c_child);
        }


        return c_node;
    };

    void proof_node::rebuild_weak_ptrs() {
        std::list<std::weak_ptr<proof_node>> last_ancestors = this->ancestors;
        std::shared_ptr<proof_node> this_shared(this->shared_from_this());
        last_ancestors.push_back(this_shared);
        for (auto &&child : this->refinement_blocks) {
            child->parent = this_shared;
            child->ancestors = last_ancestors;
            child->rebuild_weak_ptrs();
            last_ancestors.push_back(child);
        }
    }

    void proof_node::get_nodes(proof_node* node,
                               std::list<proof_node*>& list) {
        list.push_back(node);
        for (auto &&child : node->refinement_blocks) {
            get_nodes(child.get(), list);
        }
    };

    void proof_node::filter_nodes_tail(std::list<std::shared_ptr<proof_node>>& acc,
                                       std::function<bool(std::shared_ptr<proof_node>&)> fn) {
        std::shared_ptr<proof_node> _this = this->shared_from_this();
        if (fn(_this)) {
            acc.push_back(_this);
        }
        for (auto &&child : refinement_blocks) {
            filter_nodes_tail(acc, fn);
        }
    }

    void proof_node::get_tree_nodes_tail(std::list<std::shared_ptr<proof_node>>& ret_list) {
        ret_list.push_back(this->shared_from_this());
        for (auto &&child : refinement_blocks) {
            child->get_tree_nodes_tail(ret_list);
        }
    }

    void proof_node::JSON_stringify_node(std::stringstream& fmt, const std::string& prefix) {
        fmt << prefix << "{" << std::endl;
        std::string i_prefix = prefix + "\t";
        std::string omissis = "\"...\"";
        fmt << i_prefix << "uid: " << uid << "," << std::endl;
        fmt << i_prefix << "path: " << tree_path_to_string(path) << "," << std::endl;
        fmt << i_prefix << "depth: " << std::to_string(depth) << "," << std::endl;
        fmt << i_prefix << "node_infos: " << node_infos.JSON_stringify(i_prefix) << "," << std::endl;
        fmt << i_prefix << "leaf_infos: " << (leaf_infos == nullptr ? "null" : leaf_infos->JSON_stringify(i_prefix)) << "," << std::endl;
        fmt << i_prefix << "invariants: " << omissis << "," << std::endl;
        fmt << i_prefix << "triggers: " << triggers.JSON_stringify(i_prefix) << "," << std::endl;
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

    void proof_node::update_leaves_infos() {
        if (!this->is_leaf()) {
            return;
        }
        if (this->leaf_infos == nullptr) {
            throw unexpected("All leaves must have the associated leaf_infos != nullptr");
        }
//            if (this->node_infos.rules_c.empty()) {
//                //FIXME: ADD POSSIBILITY TO REMOVE CHILDREN FROM NODES
//                return;
//            }

        std::map<atomp, std::set<bool>> &map = this->leaf_infos->nondet_restriction;

        for (auto &&atom : this->node_infos.all_atoms) {
            std::set<bool> new_set;
            // ADDING POSSIBLE VALUES DEPENDING ON rules_A
            for (auto &&rule_a : this->node_infos.rules_a) {
                if (rule_a->target == atom) {
                    new_set.insert(rule_a->is_ca);
                }
            }
            map[atom] = new_set;
        }

        // REMOVING VALUES FORBIDDEN BY INVARIANTS
        for (auto &&invariant : this->invariants.inv_A_C.get_as_set()) {
            // IN CASE OF MULTIVALUED ATTRIBUTE REMOVE ALL
            bool forbidden_value = !invariant.value;
            map[invariant.atom].erase(forbidden_value);
        }

//            tree->leaf_infos->nondet_restriction = std::move(map);
    }

    bool proof_node::refine_tree_core(int max_depth, int child_count) {
        if ( // overapprox_strategy.depth_strategy == OverapproxOptions::AT_MOST_DEPTH &&
                this->depth >= max_depth &&
                max_depth > -1) {
            return false;
        } else if (this->node_infos.rules_c.empty() && !this->triggers.no_transition) {
            //TODO: CONSIDER ALSO REMOVING THE NODE FROM THE FATHER
            // _node subtree has to be removed
            log->warn("Removing subtree of node {}", this->uid);
            // REMOVE ITS SUBTREE
            this->refinement_blocks.clear();
            // ADD LEAVES INFOS TO IT
            std::unique_ptr<leaves_infos> new_infos(new leaves_infos());
            // MARK AS NOT EXPANDABLE
            new_infos->gap = maybe_bool::NO;
            this->leaf_infos = std::move(new_infos);
            // BLOCK ALL ITS NONDETERMINISM
            for (auto &&atom :this->node_infos.atoms_a) {
                this->leaf_infos->nondet_restriction[atom] = std::set<bool>();
            }
            return false;
        }
        if (!this->is_leaf()) {
            bool changed = false;
            for (auto &&child :this->refinement_blocks) {
                changed = child->refine_tree_core(max_depth, child_count) || changed;
            }
            return changed;
        } else {
            if (this->leaf_infos->gap == maybe_bool::YES) {
                std::shared_ptr<proof_node> shared_this = this->shared_from_this();
                int i = 0;
                tree_path first_path = this->path;
                first_path.push_back(i);
                node_policy_infos node_info(this->node_infos.rules_a,
                                            this->node_infos.rules_a,
                                            this->node_infos.all_atoms,
                                            this->node_infos.atoms_a,
                                            this->node_infos.policy_atoms_count);
                std::unique_ptr<leaves_infos> leaf_infos(new leaves_infos());
                std::list<std::weak_ptr<proof_node>> prec_ancestors = this->ancestors;
                prec_ancestors.push_back(shared_this);

                std::shared_ptr<proof_node> actual_child(
                        new proof_node(first_path,
                                                    this->depth + 1,
                                                    node_info,
                                                    std::move(leaf_infos),
                                                    prec_ancestors,
                                                    shared_this));
                this->refinement_blocks.push_back(actual_child);

                int budget = child_count;
                for (++i; i < budget; ++i) {
                    first_path = this->path;
                    first_path.push_back(i);
                    node_policy_infos act_info(this->node_infos.rules_a,
                                               this->node_infos.rules_a,
                                               this->node_infos.all_atoms,
                                               this->node_infos.atoms_a,
                                               this->node_infos.policy_atoms_count);
                    leaf_infos = std::make_unique<leaves_infos>(leaves_infos());

                    prec_ancestors = actual_child->ancestors;
                    prec_ancestors.push_back(actual_child);
                    actual_child = std::shared_ptr<proof_node>(
                            new proof_node(first_path,
                                                        this->depth + 1,
                                                        act_info,
                                                        std::move(leaf_infos),
                                                        prec_ancestors,
                                                        shared_this));
                    this->refinement_blocks.push_back(actual_child);
                }
                this->leaf_infos = nullptr;
                this->consolidate_tree();
                return true;
            } else {
                return false;
            }
        }
    }

    // TREE PUBLIC FUNCTIONS
    // CONSTRUCTORS
    proof_node::proof_node(tree_path _path,
                           int _depth,
                           const node_policy_infos& _node_infos,
                           std::unique_ptr<leaves_infos> _leaves_infos,
                           std::list<std::weak_ptr<proof_node>> _ancestors,
                           std::weak_ptr<proof_node> _parent) :
            path(std::move(_path)),
            uid(tree_path_to_string(path)),
            depth(_depth),
            invariants(node_invariants()),
            node_infos(_node_infos),
            leaf_infos(std::move(_leaves_infos)),
            triggers(pruning_triggers()),
            ancestors(std::move(_ancestors)),
            parent(_parent),
            refinement_blocks(std::vector<std::shared_ptr<proof_node>>()) { }

    proof_node::proof_node(tree_path _path,
                           std::string _uid,
                           int _depth,
                           node_invariants _invariants,
                           const node_policy_infos _node_infos,
                           std::unique_ptr<leaves_infos> _leaf_infos,
                           pruning_triggers _pruning_triggers,
                           std::list<std::weak_ptr<proof_node>> _ancestors,
                           std::weak_ptr<proof_node> _parent,
                           std::vector<std::shared_ptr<proof_node>> _refinement_blocks):
            path(std::move(_path)),
            uid(std::move(_uid)),
            depth(_depth),
            invariants(std::move(_invariants)),
            node_infos(_node_infos),
            leaf_infos(std::move(_leaf_infos)),
            triggers(std::move(_pruning_triggers)),
            ancestors(_ancestors),
            parent(_parent),
            refinement_blocks(_refinement_blocks) { }

    // PRINTING FUNCTIONS
    std::string proof_node::tree_to_string() {
        std::stringstream stream;
        tree_printer printer;
        stream << printer(this);
        return stream.str();
    }

    std::shared_ptr<proof_node> proof_node::clone() {
        std::shared_ptr<proof_node> cloned = this->memberwise_clone();
        cloned->rebuild_weak_ptrs();
        return cloned;
    }

    bool proof_node::is_leaf() {
        return refinement_blocks.empty();
    }

    bool proof_node::is_root() {
        return depth == 0;
    }

    bool proof_node::pruning_enabled() {
        if (triggers.probing_enabled()) {
            return true;
        }
        for (auto &&child : refinement_blocks) {
            if (child->pruning_enabled())
                return true;
        }
        return false;
    }

    void proof_node::tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node>)> fun) {
        fun(this->shared_from_this());
        for (auto &&child : this->refinement_blocks) {
            child->tree_pre_order_iter(fun);
        }
    }

    void proof_node::tree_bfs_iter(std::function<void(std::shared_ptr<proof_node>)> fun) {
        std::queue<std::shared_ptr<proof_node>> queue;
        queue.push(this->shared_from_this());
        while (!queue.empty()) {
            std::shared_ptr<proof_node> node = queue.front();
            queue.pop();
            fun(node);
            for (auto &&child : node->refinement_blocks) {
                queue.push(child);
            }
        }
    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_tree_nodes() {
        std::list<std::shared_ptr<proof_node>> ret;
        get_tree_nodes_tail(ret);
        return std::move(ret);
    }

    void proof_node::clean_pruning_triggers() {
        this->tree_pre_order_iter([](std::shared_ptr<proof_node> node) { node->triggers.clean();});
    }

    std::string proof_node::JSON_stringify() {
        std::stringstream fmt;
        fmt << "[" <<std::endl;
        this->tree_bfs_iter([&fmt](std::shared_ptr<proof_node> node) {
            node->JSON_stringify_node(fmt, "\t");
            fmt << "," << std::endl;
        });
        fmt << "]" <<std::endl;
        return fmt.str();
    }

    void proof_node::dump_tree(const std::string& fname,
                               bool javascript_compliant,
                               const std::string heading_name) {
        std::ofstream out(fname);
        std::string structure = this->tree_to_string();
        std::string details = this->JSON_stringify();
        if (heading_name != "") {
            out << "/**" << std::endl;
            out << " * " << heading_name << std::endl;
            out << " */" << std::endl;
        }
        out << "/*" << std::endl;
        out << structure;
        out << "*/" << std::endl << std::endl;
        if (javascript_compliant) {
            out << "x = " << std::endl;
        }
        out << details << ";";
        out << std::endl << std::endl;
        out.close();
    }

    std::shared_ptr<proof_node> proof_node::get_by_path(tree_path path) {
        if (path.empty())
            return this->shared_from_this();

        int i = path.front();
        path.pop_front();

        if (i < this->refinement_blocks.size()) {
            return this->refinement_blocks[i]->get_by_path(path);
        } else {
            log->critical("Cannot follow path {} in node {}", i, this->uid);
            throw std::runtime_error("Cannot follow path " + std::to_string(i) + " in node " + this->uid);
        }
    }

    void proof_node::consolidate_tree() {
        this->tree_pre_order_iter([](std::shared_ptr<proof_node> node) { node->update_leaves_infos(); });
//            expand_invariants(_tree);
    }

    bool proof_node::refine_tree(int max_depth, int child_count) {
        if (child_count < 0) {
            throw unexpected("Child count cannot be less than zero");
        }
        bool res = this->refine_tree_core(max_depth, child_count);
        this->consolidate_tree();
        return res;
    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_all_nodes() {
        std::list<std::shared_ptr<proof_node>> res;
        filter_nodes_tail(res, [] (std::shared_ptr<proof_node>& node) { return true; });
        return std::move(res);
    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_all_leaves() {
        std::list<std::shared_ptr<proof_node>> res;
        filter_nodes_tail(res, [] (std::shared_ptr<proof_node>& node) { return node->is_leaf(); });
        return std::move(res);
    }

}