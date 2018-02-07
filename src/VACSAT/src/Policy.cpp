//
// Created by esteffin on 24/04/17.
//

#include <sstream>
#include <algorithm>
#include <unordered_set>
#include "Policy.h"
#include "old_parser/ARBACData.h"
#include "ARBACTransform.h"
#include "old_parser/ARBACExact.h"

namespace SMT {


    // ************  RULE  ****************
    rule::rule(bool _is_ca, Expr _admin, Expr _prec, atomp _target, int _original_idx) :
            is_ca(_is_ca), admin(normalize_expr(_admin)), prec(normalize_expr(_prec)), target(_target), original_idx(_original_idx) { }

    std::shared_ptr<rule> rule::clone_but_expr() {
        return std::make_shared<rule>(rule(this->is_ca, this->admin, this->prec, this->target, this->original_idx));
    }

    void rule::print() const {
        if (this->original_idx < 0) {
            fprintf(stderr, "Trying to print rule with index less than 0: %d\n", this->original_idx);
            return;
        }
        if (this->is_ca) {
            if (this->original_idx >= ca_array_size) {
                fprintf(stderr, "Trying to print ca rule with index greather than maximum %d: %d\n", this->original_idx,
                        ca_array_size);
                return;
            }
            print_ca_comment(stdout, this->original_idx);
            return;
        } else {
            if (this->original_idx >= cr_array_size) {
                fprintf(stderr, "Trying to print cr rule with index greather than maximum %d: %d\n", this->original_idx,
                        cr_array_size);
                return;
            }
            print_cr_comment(stdout, this->original_idx);
            return;
        }
    }

    rule* rule::create_ca(Expr admin, Expr prec, atomp target, int original_idx) {
        return new rule(true, admin, prec, target, original_idx);
    }

    rule* rule::create_cr(Expr admin, Expr prec, atomp target, int original_idx) {
        return new rule(false, admin, prec, target, original_idx);
    }

    const std::string rule::to_string() const {
        std::stringstream fmt;

        fmt << this->get_type();

        fmt << "; Id:" << this->original_idx << "; ";

        fmt << "<" << this->admin->to_string() << ", " << this->prec->to_string() << ", " << this->target->name << ">";

        return fmt.str();
    }

    const std::string rule::to_arbac_string() const {
        std::stringstream fmt;

        std::string sadmin = simplifyExpr(this->admin)->to_arbac_string();
        std::string sprec = simplifyExpr(this->prec)->to_arbac_string();

        if (this->is_ca) {
            fmt << "<" << sadmin << ", " << sprec << ", " << this->target->name << ">";
        }
        else {
            fmt << "<" << sadmin << ", " << this->target->name << ">";
        }

        return fmt.str();

    }

    const std::string rule::to_new_string() const {
        std::stringstream fmt;

        std::string adm("a");
        std::string user("t");

        std::string suffix = this->is_ca ? "=1" : "=0";

        Expr simpl_admin = simplifyExpr(this->admin);
        Expr simpl_prec = simplifyExpr(this->prec);

        fmt << "<" << simpl_admin->to_new_string(adm) << ", " << simpl_prec->to_new_string(user) << ": t." << this->target->name << suffix << ">";

        return fmt.str();

}

    const std::string rule::get_type() const {
        return this->is_ca ? "CA" : "CR";
    }


    std::ostream &operator<<(std::ostream &stream, const rule &self) {
        stream << self.to_string();
        return stream;
    }


    // ************  USER  ****************
    user::user(int _original_idx, bool _infinite) :
            original_idx(_original_idx), name(std::string(user_array[_original_idx])), infinite(_infinite) { }
    user::user(std::string _name, int _original_idx, bool _infinite) :
            original_idx(_original_idx), name(_name), infinite(_infinite) { }
    user::user(std::string _name, int _original_idx, std::set<atomp> config, bool _infinite) :
            original_idx(_original_idx), name(_name), infinite(_infinite), _config(config) { }
    user::user(int _original_idx, std::set<atomp> config, bool _infinite) :
            original_idx(_original_idx), name(std::string(user_array[_original_idx])), infinite(_infinite), _config(config) { }

    std::shared_ptr<user> user::clone_but_expr() {
        return std::make_shared<user>(user(this->name, this->original_idx, this->_config, this->infinite));
    }

    void user::add_atom(const atomp& atom1) {
        //TODO: Truc: check this stub
        _config.insert(atom1);
    }

    void user::remove_atom(const atomp& atom1) {
        _config.erase(atom1);
    }

    std::shared_ptr<user> user::extract_copy(int idx) const {
        if (!this->infinite) {
            log->error("Cannot extract a copy of a finite user: {}", this->to_full_string());
            throw std::runtime_error("Cannot extract a copy of a finite user: " + this->to_full_string());
        }
        std::string new_name("new_" + this->name + "_" + std::to_string(idx));
        user copy = user(new_name, -1, this->config(), false);
        return std::make_shared<user>(copy);
    }

    const std::string user::to_full_string() const {
        std::stringstream fmt;
        fmt << "name: " << this->name << ", id: " << original_idx << ", infinite: " << (infinite ? "TRUE" : "FALSE") << std::endl;
        fmt << "\t{";

        if (this->_config.size() > 0) {
            auto ite = this->_config.begin();
            fmt << **ite;
            for (++ite; ite != this->_config.end(); ++ite) {
                fmt << "; " << **ite;
            }
        }
        fmt << "}" << std::endl;

        return fmt.str();
    }

    const std::string user::to_arbac_string() const {
        if (!this->infinite) {
            return this->name;
        } else {
            std::stringstream fmt;
            fmt << "<" << this->name;
            if (this->config().size() > 0) {
                auto ite = this->_config.begin();
                fmt << ", " << (**ite);
                for (++ite; ite != _config.end(); ++ite) {
                    fmt << "&" << **ite;
                }
            }
            fmt << ">";
            return fmt.str();
        }
    }

    const std::string user::to_string() const {
        return this->name + (this->infinite ? "*" : "");
    }

    std::ostream& operator<< (std::ostream& stream, const user& self) {
        stream << self.to_string();
        return stream;
    }

    user user::from_old_policy(std::vector<atomp> &atoms, int original_idx, bool infinite) {
        if (!infinite) {
            if (original_idx >= user_array_size) {
                log->error("{} is not a valid user id...", original_idx);
                throw std::runtime_error("Not a valid user id.");
            }
            std::set<atomp> config;
            set init = user_config_array[original_idx];
            for (int i = 0; i < init.array_size; ++i) {
                config.insert(atoms[init.array[i]]);
            }

            return user(std::string(user_array[original_idx]), original_idx, config, infinite);
        } else {
            if (original_idx >= newuser_array_size) {
                log->error("{} is not a valid infinite user id...", original_idx);
                throw std::runtime_error("Not a valid infinite user id.");
            }
            std::set<atomp> config;
            for (int i = 0; i < newuser_array[original_idx].role_array_size; ++i) {
                config.insert(atoms[newuser_array[original_idx].role_array[i]]);
            }

            return user(std::string(newuser_array[original_idx].name), original_idx, config, infinite);
        }
    }


    // ************ POLICY_CACHE ****************
    std::vector<std::vector<Atomp>> create_user_assignment(std::vector<Atomp> &role_vars) {
        std::vector<std::vector<Atomp>> res = std::vector<std::vector<Atomp>>((unsigned long) user_array_size);
        for (int i = 0; i < user_array_size; ++i) {
            set user_config = user_config_array[i];
            for (int j = 0; j < user_config.array_size; ++j) {
                Atomp role = role_vars[user_config.array[j]];
                res[i].push_back(role);
            }
        }
        return res;
    }

    std::set<userp, std::function<bool (const userp&, const userp&)>> update_unique_confs(std::vector<userp> users) {
        auto user_comp = [](const userp& user1, const userp& user2){ return user1->config() < user2->config(); };
        auto confs = std::set<userp, std::function<bool (const userp&, const userp&)>>( user_comp );

        for (auto &&user : users) {
            confs.insert(user);
        }

        return confs;
    };

    policy_cache::policy_cache(const arbac_policy* policy) :
            _per_user_exprs(std::vector<Expr>((ulong) policy->user_count())),
            _per_role_ca_rules(std::vector<std::list<rulep>>((ulong) policy->atom_count())),
            _per_role_cr_rules(std::vector<std::list<rulep>>((ulong) policy->atom_count())),
            _finite_users(std::list<userp>()),
            _infinite_users(std::list<userp>()),
            _policy(policy) {
        for (auto &&rule : policy->can_assign_rules()) {
            _per_role_ca_rules[rule->target->role_array_index].push_back(rule);
        }
        for (auto &&rule : policy->can_revoke_rules()) {
            _per_role_cr_rules[rule->target->role_array_index].push_back(rule);
        }
        for (auto &&user : policy->_users) {
            if (user->infinite) {
                _infinite_users.push_back(user);
            } else {
                _finite_users.push_back(user);
            }
        }
        _unique_configurations = update_unique_confs(policy->users());
    }

    Expr policy_cache::_user_to_expr(int user_id) const {
        Expr conf = createConstantTrue();
        std::set<atomp> user_atoms = _policy->_users[user_id]->config();
        for (auto &&atom : _policy->_atoms) {
            Literalp lit = createLiteralp(atom);
            Expr node =
                    (contains(user_atoms.begin(), user_atoms.end(), atom)) ?
                    lit :
                    createNotExpr(lit);

            conf = createAndExpr(conf, node);
        }
        return conf;
    }

    const std::string policy_cache::to_string() const {
        std::stringstream fmt;

        fmt << "CA: " << std::endl;
        for (auto &&atom : _policy->atoms()) {
            fmt << "\t" << *atom << std::endl;
            for (auto &&ca_rule : _per_role_ca_rules[atom->role_array_index]) {
                fmt << "\t\t" << *ca_rule<< std::endl;
            }
        }

        fmt << "CR: " << std::endl;
        for (auto &&atom : _policy->atoms()) {
            fmt << "\t" << *atom << std::endl;
            for (auto &&cr_rule : _per_role_cr_rules[atom->role_array_index]) {
                fmt << "\t\t" << *cr_rule<< std::endl;
            }
        }

        fmt << "CONF: " << std::endl;
        for (auto &&conf : _unique_configurations) {
            fmt << "\t" << *conf << std::endl;
        }

        return fmt.str();
    }

    std::ostream& operator<< (std::ostream& stream, const policy_cache& self) {
        stream << self.to_string();
        return stream;
    }

    // ************ POLICY ****************
    Expr getCRAdmFormula(std::vector<Atomp> &role_vars, int ruleId) {
        Expr ret;
        if (cr_array[ruleId].admin_role_index == -1) {
            ret = createConstantTrue();
        }
        else {
            ret = createLiteralp(role_vars[cr_array[ruleId].admin_role_index]);
        }
        return ret;
    }

    Expr getCRPNFormula(std::vector<Atomp> &role_vars, int ruleId) {
        return createConstantExpr(true, 1);
    }

    Expr getCAAdmFormula(std::vector<Atomp> &role_vars, int ca_index) {
        Expr ret = createLiteralp(role_vars[ca_array[ca_index].admin_role_index]);
        return ret;
    }

    Expr getCAPNFormula(std::vector<Atomp> &role_vars, int ca_index) {
        Expr cond = createConstantTrue();

        if (ca_array[ca_index].type == 0) {     // Has precondition
            // P
            if (ca_array[ca_index].positive_role_array_size > 0) {
                int* ca_array_p = ca_array[ca_index].positive_role_array;
                std::string rp_name = std::string(role_array[ca_array_p[0]]);
                Expr ca_cond = createLiteralp(role_vars[ca_array_p[0]]);
                for (int j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                    rp_name = std::string(role_array[ca_array_p[j]]);
                    ca_cond = createAndExpr(ca_cond, createLiteralp(role_vars[ca_array_p[j]]));
                }
                cond = ca_cond;
            }
            // N
            if (ca_array[ca_index].negative_role_array_size > 0) {
                int* ca_array_n = ca_array[ca_index].negative_role_array;
                std::string rn_name = std::string(role_array[ca_array_n[0]]);
                Expr cr_cond = createNotExpr(createLiteralp(role_vars[ca_array_n[0]]));
                for (int j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                    rn_name = std::string(role_array[ca_array_n[j]]);
                    cr_cond = createAndExpr(cr_cond, createNotExpr(createLiteralp(role_vars[ca_array_n[j]])));
                }
                cond = createAndExpr(cond, cr_cond);
            }
        }

        return cond;
    }


    arbac_policy::arbac_policy(std::string _filename) :
            filename(_filename),
            _atoms(std::vector<Atomp>()),
            _users(std::vector<std::shared_ptr<user>>()),
            _rules(std::vector<std::shared_ptr<rule>>()),
            _can_assign_rules(std::vector<std::shared_ptr<rule>>()),
            _can_revoke_rules(std::vector<std::shared_ptr<rule>>()),
            _users_to_track(std::numeric_limits<int>::max()) { }

    arbac_policy::arbac_policy(std::string _filename, bool old_version) :
            filename(_filename),
            _atoms(std::vector<Atomp>()),
            _users(std::vector<std::shared_ptr<user>>()),
            _rules(std::vector<std::shared_ptr<rule>>()),
            _can_assign_rules(std::vector<std::shared_ptr<rule>>()),
            _can_revoke_rules(std::vector<std::shared_ptr<rule>>()),
            _users_to_track(std::numeric_limits<int>::max()) {

        int i;

        for (i = 0; i < role_array_size; i++) {
            std::string rname(role_array[i]);
            Atomp var = createAtomp(rname, i, 1);
            this->_atoms.push_back(var);
            if (goal_role_index == i) {
                goal_role = var;
            }
        }
        for (i = 0; i < ca_array_size; i++) {
            Expr ca_adm = getCAAdmFormula(this->_atoms, i);
            Expr ca_pn = getCAPNFormula(this->_atoms, i);
            Atomp ca_target = this->_atoms[ca_array[i].target_role_index];
            std::shared_ptr<rule> ca_rule(rule::create_ca(ca_adm, ca_pn, ca_target, i));
            this->_can_assign_rules.push_back(ca_rule);
            _rules.push_back(ca_rule);
            // print_ca_comment(stdout, i);
            // printf("%s\n", getCAPNFormula(i)->to_string().c_str());
        }
        for (i = 0; i < cr_array_size; i++) {
            Expr cr_adm = getCRAdmFormula(this->_atoms, i);
            Expr cr_pn = getCRPNFormula(this->_atoms, i);
            Atomp cr_target = this->_atoms[cr_array[i].target_role_index];
            std::shared_ptr<rule> cr_rule(rule::create_cr(cr_adm, cr_pn, cr_target, i));
            this->_can_revoke_rules.push_back(cr_rule);
            _rules.push_back(cr_rule);
            // print_cr_comment(stdout, i);
            // printf("%s\n", getCRPNFormula(i)->to_string().c_str());
        }
        for (i = 0; i < user_array_size; ++i) {
            _users.push_back(std::make_shared<user>(user::from_old_policy(this->_atoms, i, false)));
        }
        std::set<std::set<atomp>> infini_configs;
        for (i = 0; i < newuser_array_size; ++i) {
            auto new_infini_user = user::from_old_policy(this->_atoms, i, true);
            if (!contains(infini_configs, new_infini_user.config())) {
                _users.push_back(std::make_shared<user>(new_infini_user));
                infini_configs.insert(new_infini_user.config());
            } else {
                log->debug("Policy already contains an infinite user with same configuration of user: {}\tSKIPPING!", new_infini_user.to_full_string());
            }
        }
        this->update();
    }

    std::shared_ptr<arbac_policy> arbac_policy::clone_but_expr() {
        std::shared_ptr<arbac_policy> pol(new arbac_policy(filename));
        pol->_atoms = this->_atoms;
        for (auto &&rule : this->_rules) {
            auto nrule = rule->clone_but_expr();
            pol->_rules.push_back(nrule);
            if (nrule->is_ca) {
                pol->_can_assign_rules.push_back(nrule);
            } else {
                pol->_can_revoke_rules.push_back(nrule);
            }
        }
        for (auto &&user : this->_users) {
            pol->_users.push_back(user->clone_but_expr());
        }
        pol->goal_role = this->goal_role;
        pol->_users_to_track = this->_users_to_track;

        pol->update();

        return pol;
    }

    rulep remove_multiply_admin(const rulep& _rule,
                                const std::vector<userp>& users,
                                const userp& target_user,
                                const std::map<userp, std::map<atomp, atomp>>& user_atom_translation_map) {
        Expr new_admin;
        if (is_constant_true(_rule->admin)) {
            new_admin = createConstantTrue();
        } else {
            new_admin = createConstantFalse();
            for (auto &&user : users) {
                Expr uadmin = remap_atoms(_rule->admin, user_atom_translation_map.at(user));
                new_admin = createOrExpr(uadmin, new_admin);
            }
        }

        Expr remapped_precondition = remap_atoms(_rule->prec, user_atom_translation_map.at(target_user));

        Expr final_prec = createAndExpr(new_admin, remapped_precondition);

        atomp target_atom = user_atom_translation_map.at(target_user).at(_rule->target);

        rulep res(new rule(_rule->is_ca, createConstantTrue(), final_prec, target_atom, -1));

        return res;
    }

    std::shared_ptr<arbac_policy> arbac_policy::flatten_admin() {
        if (iterable_exists(this->_users.begin(), this->_users.end(), [](userp &u) { return u->infinite; })) {
            throw std::runtime_error("Cannot flatten a policy with infinite number of users");
        }

//        std::map<atomp, std::set<atomp>> translation_map;
        std::map<userp, std::map<atomp, atomp>> user_atom_translation_map;
        std::vector<Atomp> new_atoms;
        std::set<Atomp> owned_atoms;
        int u_idx = 0;
        for (auto &&user : this->_users) {
            for (auto &&atom : this->_atoms) {
                std::string nname = atom->name + "_" + user->name;
                int idx = atom->role_array_index + (u_idx * (int)_atoms.size());
                atomp new_atom(new Atom(nname,
                                        idx,
                                        atom->bv_size));
                new_atoms.emplace_back(new_atom);
                user_atom_translation_map[user][atom] = new_atom;
//                translation_map[atom].insert(new_atom);
                if (contains(user->config(), atom)) {
                    owned_atoms.insert(new_atom);
                }
            }
            u_idx++;
        }

        userp new_user(new user("merged_user", 0, owned_atoms));


        std::list<rulep> new_rules;

        for (auto &&user : this->_users) {
            for (auto &&r : this->_rules) {
                rulep new_rule = remove_multiply_admin(r, this->_users, user, user_atom_translation_map);
                new_rules.push_back(new_rule);
            }
        }

        atomp target_atom = createAtomp("flattened_target", (int)new_atoms.size(), 1);
        new_atoms.push_back(target_atom);
        Expr target_rule_cond = createConstantFalse();

        for (auto &&user : this->_users) {
            atomp& user_goal = user_atom_translation_map.at(user).at(this->goal_role);
            target_rule_cond = createOrExpr(createLiteralp(user_goal), target_rule_cond);
        }

        rulep goal_rule(new rule(true, createConstantTrue(), target_rule_cond, target_atom, -1));

        new_rules.push_back(goal_rule);

        std::shared_ptr<arbac_policy> flattened_policy(new arbac_policy());

        flattened_policy->_users.emplace_back(new_user);
        flattened_policy->_atoms = std::move(new_atoms);
        flattened_policy->goal_role = std::move(target_atom);
        flattened_policy->add_rules(new_rules);

        return flattened_policy;
    }

    int arbac_policy::admin_count() const {
        //FIXME: use semantics equivalence and not structural one
        std::set<Expr, deepCmpExprs> admin_exprs;

        Expr true_expr = createConstantTrue();
        for (auto &&rule : _rules) {
            if (!rule->admin->equals(true_expr)) {
                admin_exprs.insert(rule->admin);
            }
        }

        return (int) admin_exprs.size();
    }

    void arbac_policy::print_cache() {
        log->info(cache()->to_string());
    }

    void arbac_policy::show_policy_statistics(int wanted_threads_count) const {
        int threads_count = this->users_to_track();
        bool use_tracks = true;

        if (wanted_threads_count < 1) {
            if (this->users().size() <= this->users_to_track()) {
                threads_count = (int) this->users().size();
                use_tracks = false;
            }
            else {
                threads_count = this->users_to_track();
                use_tracks = true;
            }
        }
        else {
            if (this->users().size() <= wanted_threads_count) {
                log->error("Cannot spawn {} threads because are more than user count {}", wanted_threads_count, this->atom_count());
            }
            else {
                threads_count = this->users_to_track() + 1;
                use_tracks = true;
            }
        }

        log->info("Policy name: {}", this->filename);
        log->info("*  Users: {}", this->users().size());
        log->info("*  Atoms: {}", this->atom_count());
        log->info("*  Users to track: {}", this->users_to_track());
        log->info("*  CA: {}", this->can_assign_rules().size());
        log->info("*  CR: {}", this->can_revoke_rules().size());
        log->info("*  ThreadCount: {}", threads_count);
        log->info("*  Require tracks: {}", use_tracks ? "True" : "False");

    }

    void arbac_policy::unsafe_remove_atom(const Atomp& atom) {
        std::list<rulep> targeting_atom;
        std::list<rulep> using_atom;

        for (auto &&rule : this->_rules) {
            if (rule->target == atom) {
                targeting_atom.push_back(rule);
            } else {
                if (contains(rule->admin->atoms(), atom) ||
                    contains(rule->prec->atoms(), atom)) {
                    using_atom.push_back(rule);
                }
            }
        }
        for (auto &&t_r : targeting_atom) {
            log->trace(t_r->to_string());
            this->unsafe_remove_rule(t_r);
        }
        for (auto &&u_r : using_atom) {
            Expr adm = u_r->admin;
            Expr prec = u_r->prec;
            if (contains(u_r->admin->atoms(), atom)) {
                adm = delete_atom(adm, atom);
            }
            if (contains(u_r->prec->atoms(), atom)) {
                prec = delete_atom(prec, atom);
            }
//            std::cout << *u_r << std::endl;
            u_r->admin = adm;
            u_r->prec = prec;
//            std::cout << "\t===>" << std::endl;
//            std::cout << *u_r << std::endl;
        }
        for (auto &&user : _users) {
            user->remove_atom(atom);
        }
    }

    void arbac_policy::unsafe_remove_user(const userp& user) {
        std::vector<userp> res;
        auto filtered =
                std::copy_if(this->_users.begin(),
                             this->_users.end(),
                             std::back_inserter(res),
                             [&](const userp &u) { return u != user; });
        this->_users = res;
    }
    void arbac_policy::unsafe_remove_rule(const rulep& rule) {
        if (rule->is_ca) {
            this->unsafe_remove_can_assign(rule);
        }
        else {
            this->unsafe_remove_can_revoke(rule);
        }
    }
    void arbac_policy::unsafe_remove_can_assign(const rulep& rule) {
        std::vector<rulep> res;
        auto filtered =
                std::copy_if(this->_can_assign_rules.begin(),
                             this->_can_assign_rules.end(),
                             std::back_inserter(res),
                             [&](const rulep &r) { return r != rule; });
        this->_can_assign_rules = res;
    }
    void arbac_policy::unsafe_remove_can_revoke(const rulep& rule) {
        std::vector<rulep> res;
        auto filtered =
                std::copy_if(this->_can_revoke_rules.begin(),
                             this->_can_revoke_rules.end(),
                             std::back_inserter(res),
                             [&](const rulep &r) { return r != rule; });
        this->_can_revoke_rules = res;
    }

    void arbac_policy::update() {
        std::vector<rulep> result = _can_assign_rules;
        result.insert(result.end(), _can_revoke_rules.begin(), _can_revoke_rules.end());
        _rules = result;

        for (int i = 0; i < this->_rules.size(); ++i) {
            rulep rule = _rules[i];
            rule->original_idx = i;
        }

        for (int i = 0; i < _atoms.size(); ++i) {
            _atoms[i]->role_array_index = i;
        }

        for (auto &&user : _users) {
            for (auto &&atom : user->config()) {
                if (!contains(_atoms.begin(), _atoms.end(), atom)) {
                    user->remove_atom(atom);
                }
            }
        }

        for (int j = 0; j < _users.size(); ++j) {
            _users[j]->original_idx = j;
        }

        _users_to_track = std::numeric_limits<int>::max();

        _cache = std::shared_ptr<policy_cache>(new policy_cache(this));
    }

    const Expr arbac_policy::user_to_expr(int user_id, const std::set<Atomp>& atoms) const {
        userp user = _users[user_id];
        Expr conf = createConstantTrue();
        for (auto &&atom : atoms) {
            Expr node =
                    (contains(user->config(), atom)) ?
                    createLiteralp(atom) :
                    createNotExpr(createLiteralp(atom));
            conf = createAndExpr(conf, node);
        }
        return conf;
    }

    void arbac_policy::set_users(const std::vector<userp> &users) {
        _users = users;
        update();
    }

    void arbac_policy::set_atoms(const std::vector<Atomp> &atoms) {
        _atoms = atoms;
//        for (int i = 0; i < this->atom_count(); ++i) {
//            _atoms[i]-> = i;
//        }
        update();
    }

    // TODO(truc): please check these following function
    void arbac_policy::add_user(const userp& user){
        _users.push_back(user);
    }
    void arbac_policy::add_can_assign_no_update(const rulep& rule) {
        this->_can_assign_rules.push_back(rule);
        _rules.push_back(rule);
    }
    void arbac_policy::add_can_revoke_no_update(const rulep& rule) {
        this->_can_revoke_rules.push_back(rule);
        _rules.push_back(rule);
    }
//    void arbac_policy::update_query(const Literalp& goal_role) {
//        this->goal_role = goal_role;
//        // Only call update when finishing adding every rules
//        // this->update();
//    }

    void arbac_policy::update_query(const std::string username, const Atomp &goal_role) {
        userp user;
        for (auto &&tuser : _users) {
            if (tuser->name == username) {
                user = tuser;
                break;
            }
        }
        if (user == nullptr) {
//            log->warn("{} does not match any existing user. Considering all...", username);
            this->goal_role = goal_role;
            return;
        }

        Atomp toCheckRole = createAtomp("ToCheckRole", (int) _atoms.size(), 1);
        Atomp targetPrime = createAtomp("TargetPrime", (int) _atoms.size() + 1, 1);

        add_atom(toCheckRole);
        add_atom(targetPrime);

        user->add_atom(toCheckRole);

        Literalp toCheckRole_lit = createLiteralp(toCheckRole);
        Literalp goal_role_lit = createLiteralp(goal_role);

        rulep target_ca(new rule(true, createConstantTrue(), createAndExpr(toCheckRole_lit, goal_role_lit), targetPrime, (int) _rules.size()));

        add_can_assign(target_ca);

        this->goal_role = targetPrime;
    }

    void arbac_policy::add_atom(const atomp& atom) {
        _atoms.push_back(atom);
    }

    void arbac_policy::add_rule(const rulep& rule) {
        if (rule->is_ca) {
            this->add_can_assign(rule);
        }
        else {
            this->add_can_revoke(rule);
        }
    }
    void arbac_policy::add_can_assign(const rulep& rule) {
        this->_can_assign_rules.push_back(rule);
        this->update();
    }
    void arbac_policy::add_can_revoke(const rulep& rule) {
        this->_can_revoke_rules.push_back(rule);
        this->update();
    }
    void arbac_policy::add_rules(const std::list<rulep>& _rules) {
        for (auto &&rule : _rules) {
            if (rule->is_ca) {
                this->_can_assign_rules.push_back(rule);
            }
            else {
                this->_can_revoke_rules.push_back(rule);
            }
        }
        this->update();
    }

    void arbac_policy::remove_atoms(const std::list<Atomp>& atoms) {
        for (auto &&atom : atoms) {
            this->unsafe_remove_atom(atom);
        }
        this->update();
    }
    void arbac_policy::remove_atom(const Atomp& atom) {
        this->unsafe_remove_atom(atom);
        this->update();
    }
    void arbac_policy::remove_rule(const rulep& _rule) {
        this->unsafe_remove_rule(_rule);
        this->update();
    }
    void arbac_policy::remove_rules(const std::list<rulep>& _rules) {
        for (auto &&rule : _rules) {
            this->unsafe_remove_rule(rule);
        }
        this->update();
    }

    void arbac_policy::remove_can_assign(const rulep &_rule) {
        this->unsafe_remove_can_assign(_rule);
        this->update();
    }
    void arbac_policy::remove_can_assigns(const std::list<rulep>& _rules) {
        for (auto &&rule : _rules) {
            this->unsafe_remove_can_assign(rule);
        }
        this->update();
    }

    void arbac_policy::remove_can_revoke(const rulep &_rule) {
        this->unsafe_remove_can_revoke(_rule);
        this->update();
    }
    void arbac_policy::remove_can_revokes(const std::list<rulep>& _rules) {
        for (auto &&rule : _rules) {
            this->unsafe_remove_can_revoke(rule);
        }
        this->update();
    }

    void arbac_policy::remove_user(const userp& user) {
        unsafe_remove_user(user);
    }

    const std::string arbac_policy::to_string() const {
        std::stringstream stream;
        stream << "ROLES: " << std::endl;
        for (auto &&atom : this->_atoms) {
            stream << "\t" << atom->name << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "USERS: " << std::endl;
        for (auto &&user : this->_users) {
            if (!user->infinite) {
                stream << "\t" << user->name << std::endl;
            }
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "NEWUSERS: " << std::endl;
        for (auto &&user : this->_users) {
            if (user->infinite) {
                stream << "\t" << user->to_arbac_string() << std::endl;
            }
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "UA:" << std::endl;
        for (auto &&user : this->_users) {
            for (auto &&atom : user->config()) {
                stream << "\t<" << user->name << ", " << atom->name << ">" << std::endl;
            }
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "CR:" << std::endl;
        for (auto &&cr : this->_can_revoke_rules) {
            stream << "\t" << *cr << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "CA:" << std::endl;
        for (auto &&ca : this->_can_assign_rules) {
            stream << "\t" << *ca << std::endl;
        }

        stream << "\t;" << std::endl << std::endl;
        stream << "SPEC:" << std::endl;
        stream << "\t" << *this->goal_role << std::endl;
        stream << "\t;" << std::endl << std::endl;

        return stream.str();
    }
    const std::string arbac_policy::to_arbac_string() {
        bool has_TRUE_admin = false;
        for (auto &&rule : _rules) {
            if (is_constant_true(simplifyExpr(rule->admin))) {
                has_TRUE_admin = true;
                break;
            }
        }
        if (has_TRUE_admin) {
            this->preprocess_to_vac1();
        }

        std::stringstream stream;
        stream << "Users " << std::endl;
        for (auto &&user : this->_users) {
            stream << "\t" << user->name << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "Roles " << std::endl;
        for (auto &&atom : this->_atoms) {
            stream << "\t" << atom->name << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "UA" << std::endl;
        for (auto &&user : this->_users) {
            for (auto &&atom : user->config()) {
                stream << "\t<" << user->name << ", " << atom->name << ">" << std::endl;
            }
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "CR" << std::endl;
        for (auto &&cr : this->_can_revoke_rules) {
            stream << "\t" << cr->to_arbac_string() << std::endl;
        }

        stream << "\t;" << std::endl << std::endl;
        stream << "CA" << std::endl;
        for (auto &&ca : this->_can_assign_rules) {
            stream << "\t" << ca->to_arbac_string() << std::endl;
        }

        stream << "\t;" << std::endl << std::endl;
        stream << "SPEC" << std::endl;
        stream << "\t" << *this->goal_role << std::endl;
        stream << "\t;" << std::endl << std::endl;

        return stream.str();
    }
    const std::string arbac_policy::to_new_string() const {
        std::stringstream stream;
        stream << "// *" << std::endl;
        stream << "// * " << "Policy generated from: " << this->filename << std::endl;
        stream << "// *" << std::endl << std::endl;
        stream << "USERS " << std::endl;
        for (auto &&user : this->_users) {
            stream << "\t" << user->to_string() << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "ATTRIBUTES " << std::endl;
        for (auto &&atom : this->_atoms) {
            stream << "\t" << atom->name << "[1]" << std::endl;
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "INIT" << std::endl;
        for (auto &&user : this->_users) {
            for (auto &&atom : user->config()) {
                stream << "\t<" << user->name << ": " << atom->name << "=1>" << std::endl;
            }
        }
        stream << "\t;" << std::endl << std::endl;
        stream << "RULES" << std::endl;
        for (auto &&cr : this->_can_revoke_rules) {
            stream << "\t" << cr->to_new_string() << std::endl;
        }

        stream << std::endl;

        for (auto &&ca : this->_can_assign_rules) {
            stream << "\t" << ca->to_new_string() << std::endl;
        }

        stream << "\t;" << std::endl << std::endl;
        stream << "QUERY" << std::endl;
        stream << "\t" << "__any__." << *this->goal_role << "=1" << std::endl;
        stream << "\t;" << std::endl << std::endl;

        return stream.str();
    }

    std::ostream& operator<< (std::ostream& stream, const arbac_policy& self) {
        stream << self.to_string();
        return stream;
    }

    void arbac_policy::preprocess_to_vac1() {
        atomp true_role(new Atom("TRUE_ADM", -1, 1));
        this->add_atom(true_role);
        for (auto &&rule : _rules) {
            if (is_constant_true(simplifyExpr(rule->admin))) {
                rule->admin = createLiteralp(true_role);
            }
        }
        for (auto &&user : _users) {
            user->add_atom(true_role);
        }

        update();
    }

}