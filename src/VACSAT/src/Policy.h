//
// Created by esteffin on 24/04/17.
//

#ifndef VACSAT_POLICY_H
#define VACSAT_POLICY_H

#include <string>
#include <vector>
#include <list>
#include "Logics.h"
#include "prelude.h"

namespace SMT {

    typedef Atomp atomp;

    class rule {
    public:
        rule(bool is_ca, Expr admin, Expr prec, atomp target, int original_idx);

        std::shared_ptr<rule> clone_but_expr();

        void print() const;

        const std::string to_string() const;
        const std::string to_new_string() const;
        const std::string to_arbac_string() const;
        const std::string get_type() const;

        static rule* create_ca(Expr admin, Expr prec, atomp target, int original_idx);
        static rule* create_cr(Expr admin, Expr prec, atomp target, int original_idx);

        friend std::ostream& operator<< (std::ostream& stream, const rule& self);

        bool is_ca;
        Expr admin;
        Expr prec;
        atomp target;
        int original_idx;
    };

    typedef std::shared_ptr<rule> rulep;

    class user {
    public:
        user(int original_idx, bool _infinite = false);
        user(std::string _name, int original_idx, bool _infinite = false);
        user(std::string _name, int original_idx, std::set<atomp> config, bool _infinite = false);
        user(int original_idx, std::set<atomp> config, bool _infinite = false);

        std::shared_ptr<user> clone_but_expr();

        void add_atom(const atomp& atom1);
        void remove_atom(const atomp& atom1);

        std::shared_ptr<user> extract_copy(int idx) const;

        const std::string to_full_string() const;

        const std::string to_arbac_string() const;
        const std::string to_string() const;
        friend std::ostream& operator<< (std::ostream& stream, const user& self);

        inline const std::set<atomp>& config() const {
            return _config;
        }

        static user from_old_policy(std::vector<atomp> &atoms, int original_idx, bool infinite);

        int original_idx;
        const std::string name;
        const bool infinite;
    private:
        std::set<atomp> _config;
    };

    typedef std::shared_ptr<user> userp;

    class arbac_policy;

    class policy_cache {
    public:
        friend class arbac_policy;
        policy_cache(const arbac_policy* policy);

        const std::string to_string() const;

        friend std::ostream& operator<< (std::ostream& stream, const policy_cache& self);

        inline const Expr& user_expr(int user_id) {
            if (_per_user_exprs[user_id] == nullptr) {
                _per_user_exprs[user_id] = _user_to_expr(user_id);
            }
            return _per_user_exprs[user_id];
        }
        inline const std::vector<std::list<rulep>>& per_role_ca_rules() const {
            return _per_role_ca_rules;
        }
        inline const std::vector<std::list<rulep>>& per_role_cr_rules() const {
            return _per_role_cr_rules;
        }
        inline const std::set<userp, std::function<bool (const userp&, const userp&)>>& unique_configurations() const {
            return _unique_configurations;
        };

    private:
        Expr _user_to_expr(int user_id) const;
        std::vector<Expr> _per_user_exprs;
        std::vector<std::list<rulep>> _per_role_ca_rules;
        std::vector<std::list<rulep>> _per_role_cr_rules;
        std::set<userp, std::function<bool (const userp&, const userp&)>> _unique_configurations;
        std::list<userp> _finite_users;
        std::list<userp> _infinite_users;

        const arbac_policy* _policy;
    };

    class arbac_policy {
    public:

        arbac_policy(std::string filename);
        arbac_policy(std::string filename, bool old_version);

        std::shared_ptr<arbac_policy> clone_but_expr();

        std::shared_ptr<arbac_policy> flatten_admin();

        int admin_count() const;
        inline int atom_count() const {
            return (int) _atoms.size();
        }
        inline int user_count() const {
            return (int) _users.size();
        }
        inline int rules_count() const {
            return (int) _rules.size();
        }

//        void remove_can_assign(rule to_remove);
//        void remove_can_revoke(rule to_remove);

        inline const Expr user_to_expr(int user_id) {
            return cache()->user_expr(user_id);
        }

        const Expr user_to_expr(int user_id, const std::set<Atomp>& literals) const;

        void show_policy_statistics(int wanted_threads_count) const;

        void set_users(const std::vector<userp>& users);
        void set_atoms(const std::vector<atomp>& atoms);

        // TODO(truc) modify this
        void add_user(const userp& user);
        void add_atom(const atomp& atom);
        void add_can_assign_no_update(const rulep& rule);
        void add_can_revoke_no_update(const rulep& rule);
//        void update_query(const Atomp& goal_role);
        void update_query(const std::string username, const Atomp& goal_role);
        // END(truc)

        void add_rule(const rulep& rule);
        void add_can_assign(const rulep& rule);
        void add_can_revoke(const rulep& rule);
        void add_rules(const std::list<rulep>& _rules);

        void remove_rule(const rulep& rule);
        void remove_rules(const std::list<rulep>& rule);
        void remove_can_assign(const rulep& rule);
        void remove_can_assigns(const std::list<rulep>& rule);
        void remove_can_revoke(const rulep& rule);
        void remove_can_revokes(const std::list<rulep>& rule);
        void remove_atoms(const std::list<Atomp>& atoms);
        void remove_atom(const Atomp& atom);
        void remove_user(const userp& user);

        const std::string to_string() const;
        const std::string to_arbac_string();
        const std::string to_new_string() const;

        void print_cache();

        friend std::ostream& operator<< (std::ostream& stream, const arbac_policy& self);

        inline const std::vector<rulep>& rules() const {
            return _rules;
        }
        inline const std::vector<rulep>& can_assign_rules() const {
            return _can_assign_rules;
        }
        inline const std::vector<rulep>& can_revoke_rules() const {
            return _can_revoke_rules;
        }
        inline const std::vector<Atomp>& atoms() const {
            return _atoms;
        }
        inline const std::vector<userp>& users() const {
            return _users;
        }
        inline const std::set<userp, std::function<bool (const userp&, const userp&)>>& unique_configurations() {
            return cache()->unique_configurations();
        };
        inline int users_to_track() const {
            return _users_to_track;
        }

        inline const std::vector<std::list<rulep>>& per_role_can_assign_rule() {
            return this->cache()->_per_role_ca_rules;
        }
        inline const std::list<rulep>& per_role_can_assign_rule(atomp _atom) {
            return this->cache()->_per_role_ca_rules[_atom->role_array_index];
        }
        inline const std::vector<std::list<rulep>>& per_role_can_revoke_rule() {
            return this->cache()->_per_role_cr_rules;
        }
        inline const std::list<rulep>& per_role_can_revoke_rule(atomp _atom) {
            return this->cache()->_per_role_cr_rules[_atom->role_array_index];
        }
        inline const std::list<userp>& finite_users() {
            return cache()->_finite_users;
        }
        inline const std::list<userp>& infinite_users() {
            return cache()->_infinite_users;
        }

        inline const rulep& rules(int i) {
            return _rules[i];
        }
        inline const rulep& can_assign_rules(int i) {
            return _can_assign_rules[i];
        }
        inline const rulep& can_revoke_rules(int i) {
            return _can_revoke_rules[i];
        }
        inline const Atomp& atoms(int i) {
            return _atoms[i];
        }
        inline const userp& users(int i) {
            return _users[i];
        }

        inline const std::shared_ptr<policy_cache>& cache() {
            if (_cache == nullptr) {
                update();
            }
            return _cache;
        }


        Atomp goal_role;
        const std::string filename;

        private:

        explicit arbac_policy():
                goal_role(nullptr),
                filename("flattened"),
                _atoms(std::vector<Atomp>()),
                _users(std::vector<userp>()),
                _rules(std::vector<std::shared_ptr<rule>>()),
                _can_assign_rules(std::vector<std::shared_ptr<rule>>()),
                _can_revoke_rules(std::vector<std::shared_ptr<rule>>()),
                _users_to_track(1),
                _cache(nullptr) { }

        friend class policy_cache;

        void update();
        void unsafe_remove_atom(const Atomp& atom);
        void unsafe_remove_user(const userp& user);
        void unsafe_remove_rule(const rulep& rule);
        void unsafe_remove_can_assign(const rulep& rule);
        void unsafe_remove_can_revoke(const rulep& rule);

        std::vector<Atomp> _atoms;
        std::vector<userp> _users;
        std::vector<std::shared_ptr<rule>> _rules;
        std::vector<std::shared_ptr<rule>> _can_assign_rules;
        std::vector<std::shared_ptr<rule>> _can_revoke_rules;

        int _users_to_track;

        std::shared_ptr<policy_cache> _cache = nullptr;

        void preprocess_to_vac1();
    };

}

#endif //VACSAT_POLICY_H
