//
// Created by esteffin on 24/04/17.
//

#include <sstream>
#include <algorithm>
#include <unordered_set>
#include "Policy.h"
#include "ARBACData.h"
#include "ARBACTransform.h"
#include "ARBACExact.h"

namespace SMT {

    rule::rule(bool _is_ca, Expr _admin, Expr _prec, Literalp _target, int _original_idx) :
            is_ca(_is_ca), admin(_admin), prec(_prec), target(_target), original_idx(_original_idx) { }

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

    rule* rule::create_ca(Expr admin, Expr prec, Literalp target, int original_idx) {
        return new rule(true, admin, prec, target, original_idx);
    }

    rule* rule::create_cr(Expr admin, Expr prec, Literalp target, int original_idx) {
        return new rule(false, admin, prec, target, original_idx);
    }

    std::string rule::to_string() const {
        std::stringstream fmt;

        fmt << this->get_type();

        fmt << "; Id:" << this->original_idx << "; ";

        fmt << "<" << this->admin->to_string() << ", " << this->prec->to_string() << ", " << this->target->name << ">";

        return fmt.str();
    }

    std::string rule::get_type() const {
        return this->is_ca ? "CA" : "CR";
    }


    std::ostream &operator<<(std::ostream &stream, const rule &self) {
        stream << self.to_string();
        return stream;
    }


////    arbac_cache(arbac_policy policy);
//    arbac_cache(std::vector<Literalp> atoms,
//                std::vector<rulep> can_assign_rules,
//                std::vector<rulep> can_revoke_rules) {
//
//    }
//    std::list<rulep> get_assigning_r(Literalp atom) {
//        return assigning_r[atom->role_array_index];
//    }
//    std::list<rulep> get_revoking_r(Literalp atom) {
//        return revoking_r[atom->role_array_index];
//    }
//    std::list<rulep> get_ca_using_r(Literalp atom) {
//        return ca_using_r[atom->role_array_index];
//    }
//    std::list<rulep> get_cr_using_r(Literalp atom) {
//        return cr_using_r[atom->role_array_index];
//    }
//
//    void update(arbac_policy policy) {}


    // ************  USER  ****************

    user::user(int _original_idx) :
            original_idx(_original_idx), name(std::string(role_array[_original_idx])) { }
    user::user(int _original_idx, std::set<atom> config) :
            original_idx(_original_idx), name(std::string(role_array[_original_idx])), _config(config) { }

    void user::remove_atom(atom& atom1) {
        _config.erase(atom1);
    }

    std::ostream& operator<< (std::ostream& stream, const user& self) {
        stream << self.name;
        return stream;
    }

    user user::from_policy(std::vector<atom>& atoms, int original_idx) {
        if (original_idx > user_array_size) {
            std::cerr << original_idx << " is not a valid user id..." << std::endl;
            throw new std::runtime_error("Not a valid user id.");
        }
        std::set<atom> config;
        set init = user_config_array[original_idx];
        for (int i = 0; i < init.array_size; ++i) {
            config.insert(atoms[init.array[i]]);
        }

        return user(original_idx, config);
    }


    // ************ POLICY ****************

    Expr getCRAdmFormula(std::vector<Atom> &role_vars, int ruleId) {
        Expr ret = role_vars[cr_array[ruleId].admin_role_index];
        return ret;
    }

    Expr getCRPNFormula(std::vector<Atom> &role_vars, int ruleId) {
        return createConstantExpr(true, 1);
    }

    Expr getCAAdmFormula(std::vector<Atom> &role_vars, int ca_index) {
        Expr ret = role_vars[ca_array[ca_index].admin_role_index];
        return ret;
    }

    Expr getCAPNFormula(std::vector<Atom> &role_vars, int ca_index) {
        Expr cond = createConstantExpr(true, 1);

        if (ca_array[ca_index].type == 0) {     // Has precondition
            // P
            if (ca_array[ca_index].positive_role_array_size > 0) {
                int* ca_array_p = ca_array[ca_index].positive_role_array;
                std::string rp_name = std::string(role_array[ca_array_p[0]]);
                Expr ca_cond = role_vars[ca_array_p[0]];
                for (int j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                    rp_name = std::string(role_array[ca_array_p[j]]);
                    ca_cond = createAndExpr(ca_cond, role_vars[ca_array_p[j]]);
                }
                cond = createAndExpr(cond, ca_cond);
            }
            // N
            if (ca_array[ca_index].negative_role_array_size > 0) {
                int* ca_array_n = ca_array[ca_index].negative_role_array;
                std::string rn_name = std::string(role_array[ca_array_n[0]]);
                Expr cr_cond = createNotExpr(role_vars[ca_array_n[0]]);
                for (int j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                    rn_name = std::string(role_array[ca_array_n[j]]);
                    cr_cond = createAndExpr(cr_cond, createNotExpr(role_vars[ca_array_n[j]]));
                }
                cond = createAndExpr(cond, cr_cond);
            }
        }

        return cond;
    }

    std::vector<std::vector<Literalp>> create_user_assignment(std::vector<Atom> &role_vars) {
        std::vector<std::vector<Literalp>> res = std::vector<std::vector<Literalp>>((unsigned long) user_array_size);
        for (int i = 0; i < user_array_size; ++i) {
            set user_config = user_config_array[i];
            for (int j = 0; j < user_config.array_size; ++j) {
                Literalp role = role_vars[user_config.array[j]];
                res[i].push_back(role);
            }
        }
        return res;
    }

    arbac_policy::arbac_policy() :
            _atoms(std::vector<Literalp>()),
            _users(std::vector<std::shared_ptr<user>>()),
            _rules(std::vector<std::shared_ptr<rule>>()),
            _can_assign_rules(std::vector<std::shared_ptr<rule>>()),
            _can_revoke_rules(std::vector<std::shared_ptr<rule>>()) {

        int i;

        for (i = 0; i < role_array_size; i++) {
            std::string rname(role_array[i]);
            Literalp var = createLiteralp(rname, i, 1);
            this->_atoms.push_back(var);
            if (goal_role_index == i) {
                goal_role = var;
            }
        }
        for (i = 0; i < ca_array_size; i++) {
            Expr ca_adm = getCAAdmFormula(this->_atoms, i);
            Expr ca_pn = getCAPNFormula(this->_atoms, i);
            Atom ca_target = this->_atoms[ca_array[i].target_role_index];
            std::shared_ptr<rule> ca_rule(rule::create_ca(ca_adm, ca_pn, ca_target, i));
            this->_can_assign_rules.push_back(ca_rule);
            _rules.push_back(ca_rule);
            // print_ca_comment(stdout, i);
            // printf("%s\n", getCAPNFormula(i)->to_string().c_str());
        }
        for (i = 0; i < cr_array_size; i++) {
            Expr cr_adm = getCRAdmFormula(this->_atoms, i);
            Expr cr_pn = getCRPNFormula(this->_atoms, i);
            Atom cr_target = this->_atoms[cr_array[i].target_role_index];
            std::shared_ptr<rule> cr_rule(rule::create_cr(cr_adm, cr_pn, cr_target, i));
            this->_can_revoke_rules.push_back(cr_rule);
            _rules.push_back(cr_rule);
            // print_cr_comment(stdout, i);
            // printf("%s\n", getCRPNFormula(i)->to_string().c_str());
        }
        for (i = 0; i < user_array_size; ++i) {
            _users.push_back(std::make_shared<user>(user::from_policy(this->_atoms, i)));
        }
    }

    Expr arbac_policy::user_to_expr(int user_id) const {
        Expr conf = createConstantTrue();
        std::set<atom> user_atoms = _users[user_id]->config();
        for (auto &&atom : _atoms) {
            Expr node =
                    (contains(user_atoms.begin(), user_atoms.end(), atom)) ?
                    atom :
                    createNotExpr(atom);

            conf = createAndExpr(conf, node);
        }
        return conf;
    }

    void arbac_policy::reomove_atom(const Literalp &atom) {
        std::list<rulep> targeting_atom;
        std::list<rulep> using_atom;

        for (auto &&rule : this->_rules) {
            if (rule->target == atom) {
                targeting_atom.push_back(rule);
            } else {
                if (contains(rule->admin->literals(), atom) ||
                    contains(rule->prec->literals(), atom)) {
                    using_atom.push_back(rule);
                }
            }
        }
        for (auto &&t_r : targeting_atom) {
            //FIXME: avoid auto update every time...
            this->remove_rule(t_r);
        }
        for (auto &&u_r : using_atom) {
            Expr adm = u_r->admin;
            Expr prec = u_r->prec;
            if (contains(u_r->admin->literals(), atom)) {
                adm = delete_atom(adm, atom);
            }
            if (contains(u_r->prec->literals(), atom)) {
                prec = delete_atom(prec, atom);
            }
            u_r->admin = adm;
            u_r->prec = prec;
        }
        this->update();
    }

    void arbac_policy::update() {
        std::vector<rulep> result = _can_assign_rules;
        result.insert(result.end(), _can_revoke_rules.begin(), _can_revoke_rules.end());
        _rules = result;

        std::set<Literalp> new_atoms;
        for (auto &&rule : _rules) {
            new_atoms.insert(rule->admin->literals().begin(), rule->admin->literals().end());
            new_atoms.insert(rule->prec->literals().begin(), rule->prec->literals().end());
        }
        std::vector<Literalp> _old_atoms = _atoms;
        _atoms = std::vector<Literalp>(new_atoms.begin(), new_atoms.end());

        for (int i = 0; i < _atoms.size(); ++i) {
            _atoms[i]->role_array_index = i;
        }

        for (auto &&oldAtom : _old_atoms) {
            if (!contains(_atoms.begin(), _atoms.end(), oldAtom)) {
                for (auto &&user : _users) {
                    user->remove_atom(oldAtom);
                }
            }
        }
    }

    void arbac_policy::remove_rule(const rulep &_rule) {
        if (_rule->is_ca) {
            remove_can_assign(_rule);
        } else {
            remove_can_revoke(_rule);
        }
    }

    void arbac_policy::remove_can_assign(const rulep &_rule) {
        std::vector<std::shared_ptr<rule>> res;
        auto filtered =
                std::copy_if(this->_can_assign_rules.begin(),
                             this->_can_assign_rules.end(),
                             std::back_inserter(res),
                             [&](const std::shared_ptr<rule> &r) { return r->original_idx != _rule->original_idx; });
        this->_can_assign_rules = res;
        this->update();
    }

    void arbac_policy::remove_can_revoke(const rulep &_rule) {
        std::vector<std::shared_ptr<rule>> res;
        auto filtered =
                std::copy_if(this->_can_revoke_rules.begin(),
                             this->_can_revoke_rules.end(),
                             std::back_inserter(res),
                             [&](const std::shared_ptr<rule> &r) { return r->original_idx != _rule->original_idx; });
        this->_can_revoke_rules = res;
        this->update();
    }

//    void arbac_policy::remove_can_assign(int index) {
//        this->can_assign_rules.erase(can_assign_rules.begin() + index);
//    }
//    void arbac_policy::remove_can_revoke(int index) {
//        this->can_revoke_rules.erase(can_revoke_rules.begin() + index);
//    }

}