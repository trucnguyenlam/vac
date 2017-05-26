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

    typedef Literalp atom;

    class rule {
    public:
        rule(bool is_ca, Expr admin, Expr prec, atom target, int original_idx);

        void print() const;

        std::string to_string() const;
        std::string get_type() const;

        static rule* create_ca(Expr admin, Expr prec, atom target, int original_idx);
        static rule* create_cr(Expr admin, Expr prec, atom target, int original_idx);

        friend std::ostream& operator<< (std::ostream& stream, const rule& self);

        bool is_ca;
        Expr admin;
        Expr prec;
        atom target;
        int original_idx;
    };

    typedef std::shared_ptr<rule> rulep;

    class user {
    public:
        user(int original_idx, bool _infinite = false);
        user(std::string _name, int original_idx, bool _infinite = false);
        user(std::string _name, int original_idx, std::set<atom> config, bool _infinite = false);
        user(int original_idx, std::set<atom> config, bool _infinite = false);

        void add_atom(const atom& atom1);
        void remove_atom(const atom& atom1);

        const std::string to_full_string() const;

        const std::string to_string() const;
        friend std::ostream& operator<< (std::ostream& stream, const user& self);

        inline const std::set<atom>& config() const {
            return _config;
        }

        static user from_policy(std::vector<atom>& atoms, int original_idx);

        const bool infinite;
        const int original_idx;
        const std::string name;
    private:
        std::set<atom> _config;
    };

    typedef std::shared_ptr<user> userp;

    class arbac_policy;

    class policy_cache {
    public:
        policy_cache(const arbac_policy* policy);

        const std::string to_string() const;

        friend std::ostream& operator<< (std::ostream& stream, const policy_cache& self);

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
        std::vector<std::list<rulep>> _per_role_ca_rules;
        std::vector<std::list<rulep>> _per_role_cr_rules;
        std::set<userp, std::function<bool (const userp&, const userp&)>> _unique_configurations;

        const arbac_policy* _policy;
    };

    class arbac_policy {
    public:

        arbac_policy();
        arbac_policy(bool old_version);

        inline int atom_count() const {
            return (int) _atoms.size();
        }

//        void remove_can_assign(rule to_remove);
//        void remove_can_revoke(rule to_remove);

        Expr user_to_expr(int user_id) const;

        void add_user(const userp& user);
        void set_users(const std::vector<userp>& users);
        void set_atoms(const std::vector<atom>& atoms);
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
        void remove_atom(const Literalp& atom);
        void remove_user(const userp& user);

        const std::string to_string() const;

        void print_cache() const;

        friend std::ostream& operator<< (std::ostream& stream, const arbac_policy& self);

        Literalp goal_role;

        inline const std::vector<rulep>& rules() const {
            return _rules;
        }
        inline const std::vector<rulep>& can_assign_rules() const {
            return _can_assign_rules;
        }
        inline const std::vector<rulep>& can_revoke_rules() const {
            return _can_revoke_rules;
        }
        inline const std::vector<Literalp>& atoms() const {
            return _atoms;
        }
        inline const std::vector<userp>& users() const {
            return _users;
        }
        inline const std::set<userp, std::function<bool (const userp&, const userp&)>>& unique_configurations() {
            return _cache->unique_configurations();
        };
        inline const int users_to_track() const {
            return _users_to_track;
        }

        inline const std::vector<std::list<rulep>> per_role_can_assign_rule() {
            if (_cache == nullptr) {
                std::cerr << "Cache is not valid." << std::endl;
                throw std::runtime_error("Cache is not valid.");
            }
            return this->_cache->per_role_ca_rules();
        }
        inline const std::list<rulep> per_role_can_assign_rule(atom _atom) {
            if (_cache == nullptr) {
                std::cerr << "Cache is not valid." << std::endl;
                throw std::runtime_error("Cache is not valid.");
            }
            return this->_cache->per_role_ca_rules()[_atom->role_array_index];
        }
        inline const std::vector<std::list<rulep>> per_role_can_revoke_rule() {
            if (_cache == nullptr) {
                std::cerr << "Cache is not valid." << std::endl;
                throw std::runtime_error("Cache is not valid.");
            }
            return this->_cache->per_role_cr_rules();
        }
        inline const std::list<rulep> per_role_can_revoke_rule(atom _atom) {
            if (_cache == nullptr) {
                std::cerr << "Cache is not valid." << std::endl;
                throw std::runtime_error("Cache is not valid.");
            }
            return this->_cache->per_role_cr_rules()[_atom->role_array_index];
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
        inline const Literalp& atoms(int i) {
            return _atoms[i];
        }
        inline const userp& users(int i) {
            return _users[i];
        }

        private:

        void update();
        void unsafe_remove_atom(const Literalp& atom);
        void unsafe_remove_user(const userp& user);
        void unsafe_remove_rule(const rulep& rule);
        void unsafe_remove_can_assign(const rulep& rule);
        void unsafe_remove_can_revoke(const rulep& rule);

        int _users_to_track;

        std::vector<Literalp> _atoms;
        std::vector<std::shared_ptr<rule>> _rules;
        std::vector<std::shared_ptr<rule>> _can_assign_rules;
        std::vector<std::shared_ptr<rule>> _can_revoke_rules;

        std::vector<userp> _users;

        std::shared_ptr<policy_cache> _cache = nullptr;

    };

}

#endif //VACSAT_POLICY_H
