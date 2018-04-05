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

        std::shared_ptr<rulep> _c_rule_check = nullptr;
        if (this->c_rule_check != nullptr) {
            rulep _c_rule_check_cnt = *this->c_rule_check;
            _c_rule_check = std::make_shared<rulep>(_c_rule_check_cnt);
        }
        std::shared_ptr<std::pair<atomp, bool>> _pre_A_check = nullptr;
        if (this->pre_A_check != nullptr) {
            std::pair<atomp, bool> _pre_A_check_cnt = *this->pre_A_check;
            _pre_A_check = std::make_shared<std::pair<atomp, bool>>(_pre_A_check_cnt);
        }
        std::shared_ptr<std::pair<atomp, bool>> _A_C_check = nullptr;
        if (this->A_C_check != nullptr) {
            std::pair<atomp, bool> _A_C_check_cnt = *this->A_C_check;
            _A_C_check = std::make_shared<std::pair<atomp, bool>>(_A_C_check_cnt);
        }
        std::shared_ptr<std::pair<atomp, bool>> _post_A_check = nullptr;
        if (this->post_A_check != nullptr) {
            std::pair<atomp, bool> _post_A_check_cnt = *this->post_A_check;
            _post_A_check = std::make_shared<std::pair<atomp, bool>>(_post_A_check_cnt);
        }
        std::shared_ptr<std::pair<atomp, bool>> _pre_A_blocked_check = nullptr;
        if (this->pre_A_blocked_check != nullptr) {
            std::pair<atomp, bool> _pre_A_blocked_check_cnt = *this->pre_A_blocked_check;
            _pre_A_blocked_check = std::make_shared<std::pair<atomp, bool>>(_pre_A_blocked_check_cnt);
        }
        std::shared_ptr<std::pair<atomp, bool>> _post_A_blocked_check = nullptr;
        if (this->post_A_blocked_check != nullptr) {
            std::pair<atomp, bool> _post_A_blocked_check_cnt = *this->post_A_blocked_check;
            _post_A_blocked_check = std::make_shared<std::pair<atomp, bool>>(_post_A_blocked_check_cnt);
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

    bool pruning_triggers::probing_enabled() const {
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

    std::string JSON_stringify_all(const pruning_triggers& pt, const std::string& prefix) {
        if (!pt.probing_enabled()) {
            return "false";
        }
        std::stringstream fmt;
        std::string i_prefix = prefix;
        fmt << "{" << std::endl;
        i_prefix = prefix + "\t";

        fmt << i_prefix << "c_rule_check: ";
        if (pt.c_rule_check != nullptr) {
            fmt << (*pt.c_rule_check)->to_string() << "," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "pre_A_check: ";
        if (pt.pre_A_check != nullptr) {
            fmt << "{" << pt.pre_A_check->first->name << ", " << pt.pre_A_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "A_C_check: ";
        if (pt.A_C_check != nullptr) {
            fmt << "{" << pt.A_C_check->first->name << ", " << pt.A_C_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "post_A_check: ";
        if (pt.post_A_check != nullptr) {
            fmt << "{" << pt.post_A_check->first->name << ", " << pt.post_A_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "pre_A_blocked_check: ";
        if (pt.pre_A_blocked_check != nullptr) {
            fmt << "{" << pt.pre_A_blocked_check->first->name << ", " << pt.pre_A_blocked_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "post_A_blocked_check: ";
        if (pt.post_A_blocked_check != nullptr) {
            fmt << "{" << pt.post_A_blocked_check->first->name << ", " << pt.post_A_blocked_check->second << "}," << std::endl;
        } else {
            fmt << "null," <<std::endl;
        }
        fmt << i_prefix << "no_transition: " << bool_to_true_false(pt.no_transition) << "," << std::endl;
        fmt << i_prefix << "no_skip: " << bool_to_true_false(pt.no_skip) << "," << std::endl;
        fmt << i_prefix << "no_priority: " << bool_to_true_false(pt.no_priority) << "," << std::endl;
        fmt << i_prefix << "no_sfogo: " << bool_to_true_false(pt.no_sfogo) << "," << std::endl;
        fmt << i_prefix << "overapprox: " << maybe_bool_to_string(pt.overapprox) << "," << std::endl;
        fmt << i_prefix << "check_gap: " << bool_to_true_false(pt.check_gap) << "," << std::endl;

        fmt << prefix << "}";

        return fmt.str();
    }

    std::string pruning_triggers::JSON_stringify(const std::string& prefix, bool only_active) const {
        if (!only_active)
            return JSON_stringify_all(*this, prefix);
        pruning_triggers def;
        std::stringstream fmt;
        std::string i_prefix = prefix;
        fmt << "{" << std::endl;
        i_prefix = prefix + "\t";

        if (this->c_rule_check != def.c_rule_check) {
            fmt << i_prefix << "c_rule_check: ";
            fmt << (*c_rule_check)->to_string() << "," << std::endl;
        }
        if (this->pre_A_check != def.pre_A_check) {
            fmt << i_prefix << "pre_A_check: ";
            fmt << "{" << pre_A_check->first->name << ", " << pre_A_check->second << "}," << std::endl;
        }
        if (this->A_C_check != def.A_C_check) {
            fmt << i_prefix << "A_C_check: ";
            fmt << "{" << A_C_check->first->name << ", " << A_C_check->second << "}," << std::endl;
        }
        if (this->post_A_check != def.post_A_check) {
            fmt << i_prefix << "post_A_check: ";
            fmt << "{" << post_A_check->first->name << ", " << post_A_check->second << "}," << std::endl;
        }
        if (this->pre_A_blocked_check != def.pre_A_blocked_check) {
            fmt << i_prefix << "pre_A_blocked_check: ";
            fmt << "{" << pre_A_blocked_check->first->name << ", " << pre_A_blocked_check->second << "}," << std::endl;
        }
        if (this->post_A_blocked_check != def.post_A_blocked_check) {
            fmt << i_prefix << "post_A_blocked_check: ";
            fmt << "{" << post_A_blocked_check->first->name << ", " << post_A_blocked_check->second << "}," << std::endl;
        }

        if (this->no_transition != def.no_transition) {
            fmt << i_prefix << "no_transition: " << bool_to_true_false(no_transition) << "," << std::endl;
        }
        if (this->no_skip != def.no_skip) {
            fmt << i_prefix << "no_skip: " << bool_to_true_false(no_skip) << "," << std::endl;
        }
        if (this->no_priority != def.no_priority) {
            fmt << i_prefix << "no_priority: " << bool_to_true_false(no_priority) << "," << std::endl;
        }
        if (this->no_sfogo != def.no_sfogo) {
            fmt << i_prefix << "no_sfogo: " << bool_to_true_false(no_sfogo) << "," << std::endl;
        }
        if (this->overapprox != def.overapprox) {
            fmt << i_prefix << "overapprox: " << maybe_bool_to_string(overapprox) << "," << std::endl;
        }
        if (this->check_gap != def.check_gap) {
            fmt << i_prefix << "check_gap: " << bool_to_true_false(check_gap) << "," << std::endl;
        }

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

            auto ite = tree->refinement_blocks().begin();

            while (ite != tree->refinement_blocks().end()) {
                const std::shared_ptr<proof_node>& child = *ite;
                ++ite;
                stream << depth << " `--";
                Push( ite != tree->refinement_blocks().end() ? '|' : ' ' );
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
                               std::list<std::weak_ptr<proof_node>>(),
                               std::weak_ptr<proof_node>(),
                               std::vector<std::shared_ptr<proof_node>>()));

        for (auto &&child : this->_refinement_blocks) {
            std::shared_ptr<proof_node> c_child = child->memberwise_clone();
//                c_child->_parent = c_node;
            c_node->_refinement_blocks.push_back(c_child);
        }


        return c_node;
    };

    void proof_node::rebuild_weak_ptrs() {
        std::list<std::weak_ptr<proof_node>> last_ancestors = this->_ancestors;
        std::shared_ptr<proof_node> this_shared(this->shared_from_this());
        last_ancestors.push_back(this_shared);
        for (auto &&child : this->_refinement_blocks) {
            child->_parent = this_shared;
            child->_ancestors = last_ancestors;
            child->rebuild_weak_ptrs();
            last_ancestors.push_back(child);
        }
    }

    void proof_node::get_nodes(proof_node* node,
                               std::list<proof_node*>& list) {
        list.push_back(node);
        for (auto &&child : node->_refinement_blocks) {
            get_nodes(child.get(), list);
        }
    };

    void proof_node::filter_nodes_tail(std::list<std::shared_ptr<proof_node>>& acc,
                                       std::function<bool(std::shared_ptr<proof_node>&)> fn) {
        std::shared_ptr<proof_node> _this = this->shared_from_this();
        if (fn(_this)) {
            acc.push_back(_this);
        }
        for (auto &&child : this->_refinement_blocks) {
            child->filter_nodes_tail(acc, fn);
        }
    }

    void proof_node::get_tree_nodes_tail(std::list<std::shared_ptr<proof_node>>& ret_list) {
        ret_list.push_back(this->shared_from_this());
        for (auto &&child : _refinement_blocks) {
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
        auto shared_parent = _parent.lock();
        fmt << i_prefix << "_parent: " << (shared_parent == nullptr ? "null" : shared_parent->uid) << "," << std::endl;
        fmt << i_prefix << "_ancestors: [" << std::endl;
        for (auto &&w_ancestor : _ancestors) {
            auto ancestor = w_ancestor.lock();
            fmt << i_prefix << "\t" << ancestor->uid << "," << std::endl;
        }
        fmt << i_prefix << "]," << std::endl;

        fmt << i_prefix << "_refinement_blocks: [" << std::endl;
        for (auto &&child : _refinement_blocks) {
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

    bool proof_node::refine_node(int max_depth, int child_count) {
        if ( // overapprox_strategy.depth_strategy == OverapproxOptions::AT_MOST_DEPTH &&
                this->depth >= max_depth &&
                max_depth > -1) {
            return false;
        } else if (this->node_infos.rules_a.empty()) {
            log->warn("No need to refine node {} since A is empty", this->uid);
            return false;
        } else if (this->node_infos.rules_c.empty()) {
            //TODO: CONSIDER ALSO REMOVING THE NODE FROM THE FATHER
            // _node subtree has to be removed
            log->warn("Node {} has empty C. Removing subtree...", this->uid);
            // REMOVE ITS SUBTREE
            this->_refinement_blocks.clear();
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
            throw unexpected("Cannot refine non leaf node: " + this->uid);
        } else {
            if (this->leaf_infos->gap == maybe_bool::NO) {
                log->critical("Node {} is leaf but marked as non gap", this->uid);
                return false;
            }

            // This node is not a leaf anymore
            this->leaf_infos = nullptr;

            std::shared_ptr<proof_node> shared_this = this->shared_from_this();
            int i = 0;
            tree_path first_path = this->path;
            first_path.push_back(i);
            node_policy_infos node_info = this->node_infos.clone();
            std::unique_ptr<leaves_infos> leaf_infos(new leaves_infos());
            std::list<std::weak_ptr<proof_node>> prec_ancestors = this->_ancestors;
            prec_ancestors.push_back(shared_this);

            std::shared_ptr<proof_node> actual_child(
                    new proof_node(first_path,
                                   this->depth + 1,
                                   node_info,
                                   std::move(leaf_infos),
                                   prec_ancestors,
                                   shared_this));
            this->_refinement_blocks.push_back(actual_child);

            for (++i; i < child_count; ++i) {
                first_path = this->path;
                first_path.push_back(i);
                node_info = this->node_infos.clone();
                leaf_infos = std::make_unique<leaves_infos>(leaves_infos());

                prec_ancestors = actual_child->_ancestors;
                prec_ancestors.push_back(actual_child);
                actual_child = std::make_shared<proof_node>(
                        proof_node(first_path,
                                   this->depth + 1,
                                   node_info,
                                   std::move(leaf_infos),
                                   prec_ancestors,
                                   shared_this));
                this->_refinement_blocks.push_back(actual_child);
            }
            this->consolidate_tree();
            return true;
        }
    }

    // TREE PUBLIC FUNCTIONS
    // CONSTRUCTORS
    proof_node::proof_node(tree_path _path,
                           int _depth,
                           const node_policy_infos& _node_infos,
                           std::unique_ptr<leaves_infos> _leaves_infos,
                           std::list<std::weak_ptr<proof_node>> ancestors,
                           std::weak_ptr<proof_node> parent) :
            _ancestors(std::move(ancestors)),
            _parent(std::move(parent)),
            _refinement_blocks(std::vector<std::shared_ptr<proof_node>>()),
            path(std::move(_path)),
            uid(tree_path_to_string(path)),
            depth(_depth),
            invariants(node_invariants()),
            node_infos(_node_infos),
            leaf_infos(std::move(_leaves_infos)) { }

    proof_node::proof_node(tree_path _path,
                           std::string _uid,
                           int _depth,
                           node_invariants _invariants,
                           const node_policy_infos _node_infos,
                           std::unique_ptr<leaves_infos> _leaf_infos,
                           std::list<std::weak_ptr<proof_node>> ancestors,
                           std::weak_ptr<proof_node> parent,
                           std::vector<std::shared_ptr<proof_node>> refinement_blocks):
            _ancestors(ancestors),
            _parent(std::move(parent)),
            _refinement_blocks(std::move(refinement_blocks)),
            path(std::move(_path)),
            uid(std::move(_uid)),
            depth(_depth),
            invariants(std::move(_invariants)),
            node_infos(_node_infos),
            leaf_infos(std::move(_leaf_infos)) { }

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
        return _refinement_blocks.empty();
    }

    bool proof_node::is_root() {
        return depth == 0;
    }

//    bool proof_node::pruning_enabled() {
//        if (triggers.probing_enabled()) {
//            return true;
//        }
//        for (auto &&child : _refinement_blocks) {
//            if (child->pruning_enabled())
//                return true;
//        }
//        return false;
//    }

    void proof_node::tree_pre_order_iter(std::function<void(std::shared_ptr<proof_node>)> fun) {
        fun(this->shared_from_this());
        for (auto &&child : this->_refinement_blocks) {
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
            for (auto &&child : node->_refinement_blocks) {
                queue.push(child);
            }
        }
    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_tree_nodes() {
        std::list<std::shared_ptr<proof_node>> ret;
        get_tree_nodes_tail(ret);
        return std::move(ret);
    }

//    void proof_node::clean_pruning_triggers() {
//        this->tree_pre_order_iter([](std::shared_ptr<proof_node> node) { node->triggers.clean();});
//    }

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

    const std::string proof_node::dump_tree_str(bool javascript_compliant, const std::string heading_name) {
        std::stringstream out;
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
        return out.str();
    }
    void proof_node::dump_tree(const std::string& fname,
                               bool javascript_compliant,
                               const std::string heading_name) {
        std::ofstream out(fname);
        out << this->dump_tree_str(javascript_compliant, heading_name);
        out.close();
    }

    std::shared_ptr<proof_node> proof_node::get_by_path(tree_path path) {
        if (path.empty())
            return this->shared_from_this();

        int i = path.front();
        path.pop_front();

        if (i < this->_refinement_blocks.size()) {
            return this->_refinement_blocks[i]->get_by_path(path);
        } else {
            log->critical("Cannot follow path {} in node {}", i, this->uid);
            throw std::runtime_error("Cannot follow path " + std::to_string(i) + " in node " + this->uid);
        }
    }

    void proof_node::consolidate_tree() {
        this->tree_pre_order_iter([](std::shared_ptr<proof_node> node) { node->update_leaves_infos(); });
//            expand_invariants(_tree);
    }

//    bool proof_node::refine_tree(int max_depth, int child_count) {
//        if (child_count < 0) {
//            throw unexpected("Child count cannot be less than zero");
//        }
//        bool res = this->refine_tree_core(max_depth, child_count);
//        this->consolidate_tree();
//        return res;
//    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_all_nodes() {
        std::list<std::shared_ptr<proof_node>> res;
        get_tree_nodes_tail(res);
        return std::move(res);
    }

    std::list<std::shared_ptr<proof_node>> proof_node::get_all_leaves() {
        std::list<std::shared_ptr<proof_node>> res;
        filter_nodes_tail(res, [] (std::shared_ptr<proof_node>& node) { return node->is_leaf(); });
        return std::move(res);
    }

    // PROOF_T FUNCTIONS
    // PRIVATE
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

    std::shared_ptr<proof_node> proof_t::init_get_root(const std::vector<atomp>& orig_atoms,
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

    std::shared_ptr<proof_node> proof_t::create_tree_root(const int policy_atom_count,
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

    proof_t::proof_t(const OverapproxOptions _overapprox_strategy,
                     const atomp _target_atom,
                     std::shared_ptr<proof_node> _proof_tree,
                     const std::set<userp, std::function<bool(const userp &, const userp &)>> _initial_confs) :
            overapprox_strategy(_overapprox_strategy),
            target_atom(_target_atom),
            proof_tree(std::move(_proof_tree)),
            initial_confs(_initial_confs) { }

    // PUBLIC
    proof_t::proof_t(const OverapproxOptions strategy,
                     const std::vector<atomp>& orig_atoms,
                     const std::vector<rulep>& orig_rules,
                     const std::shared_ptr<arbac_policy>& policy,
                     const Expr& to_check) :
            overapprox_strategy(strategy),
            target_atom(createAtomp("__overapprox__target__", policy->atom_count(), 1)),
            proof_tree(init_get_root(orig_atoms,
                                     orig_rules,
                                     policy,
                                     to_check)),
            initial_confs(policy->unique_configurations()) { }

    std::shared_ptr<proof_t> proof_t::clone() {
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

    std::string proof_t::tree_to_string() {
        return proof_tree->tree_to_string();
    }

    bool proof_t::refine_proof(std::list<std::shared_ptr<proof_node>>& nodes, int max_depth, int child_count) {
        if (child_count < 0) {
            throw unexpected("Child count cannot be less than zero");
        }
        //TODO: restore ifndef
//#ifndef NDEBUG
        std::list<std::shared_ptr<proof_node>> leaves = this->proof_tree->get_all_leaves();
        for (auto &&node : nodes) {
            auto findIter = std::find(leaves.begin(), leaves.end(), node);
            if (findIter == leaves.end()) {
                log->critical("Node {} is not a leaf.", node->uid);
                throw unexpected("Node " + node->uid + " is not a leaf.");
            }
        }
//#endif
        bool res = false;
        for (auto &&node : nodes) {
            bool tmp = node->refine_node(max_depth, child_count);
            res = res || tmp;
        }

        proof_tree->consolidate_tree();
        return res;
    }

    const std::string proof_t::dump_proof_str(bool javascript_compliant, const std::string heading_name) {
        std::string completed_heading = heading_name + "\n * " + get_timestamp();
        std::string tree = proof_tree->dump_tree_str(javascript_compliant, completed_heading);

        std::stringstream fmt;
        fmt << tree;
        fmt << "initial_confs = {" << std::endl;
        std::string indent = "\t";
        for (auto &&userp : initial_confs) {
            fmt << indent << userp->name << ": [" << std::endl;
            for (auto &&atom : userp->config()) {
                fmt << indent << indent << "\"" << atom->name<< "\"," << std::endl;
            }
            fmt << indent << "]," << std::endl;
        }
        fmt << "};";
        fmt << std::endl << std::endl;
        return fmt.str();
    }
    void proof_t::dump_proof(const std::string& fname, bool javascript_compliant, const std::string heading_name) {
        std::ofstream out(fname);
        out << this->dump_proof_str(javascript_compliant, heading_name);
        out.close();
    }
}