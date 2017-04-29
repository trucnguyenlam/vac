//
// Created by esteffin on 24/04/17.
//

#include <sstream>
#include <algorithm>
#include "Policy.h"
#include "ARBACData.h"
#include "ARBACTransform.h"

namespace SMT {

    rule::rule(bool _is_ca, Expr _admin, Expr _prec, Literalp _target, int _original_idx) :
            is_ca(_is_ca), admin(_admin), prec(_prec), target(_target), original_idx(_original_idx) { }

    void rule::print() const{
        if (this->original_idx < 0) {
            fprintf(stderr, "Trying to print rule with index less than 0: %d\n", this->original_idx);
            return;
        }
        if (this->is_ca) {
            if (this->original_idx >= ca_array_size) {
                fprintf(stderr, "Trying to print ca rule with index greather than maximum %d: %d\n", this->original_idx, ca_array_size);
                return;
            }
            print_ca_comment(stdout, this->original_idx);
            return;
        }
        else {
            if (this->original_idx >= cr_array_size) {
                fprintf(stderr, "Trying to print cr rule with index greather than maximum %d: %d\n", this->original_idx, cr_array_size);
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

    std::string rule::to_string() const{
        std::stringstream fmt;

        fmt << this->get_type();

        fmt << "; Id:" << this->original_idx << "; ";

        fmt << "<" << this->admin->to_string() << ", " << this->prec->to_string() << ", " << this->target->name << ">";

        return fmt.str();
    }

    std::string rule::get_type() const{
        return this->is_ca ? "CA": "CR";
    }


    std::ostream& operator<< (std::ostream& stream, const rule& self) {
        stream << self.to_string();
        return stream;
    }



    // ************ POLICY ****************

    Expr getCRAdmFormula(std::vector<Atom>& role_vars, int ruleId) {
        Expr ret = role_vars[cr_array[ruleId].admin_role_index];
        return ret;
    }

    Expr getCRPNFormula(std::vector<Atom>& role_vars, int ruleId) {
        return createConstantExpr(true, 1);
    }

    Expr getCAAdmFormula(std::vector<Atom>& role_vars, int ca_index) {
        Expr ret = role_vars[ca_array[ca_index].admin_role_index];
        return ret;
    }

    Expr getCAPNFormula(std::vector<Atom>& role_vars, int ca_index) {
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

    arbac_policy::arbac_policy() :
        atoms(std::vector<Literalp>()),
        can_assign_rules(std::vector<std::shared_ptr<rule>>()),
        can_revoke_rules(std::vector<std::shared_ptr<rule>>()) {

        int i;

        for (i = 0; i < role_array_size; i++) {
            std::string rname(role_array[i]);
            Literalp var = createLiteralp(rname, i, 1);
            this->atoms.push_back(var);
            if (goal_role_index == i) {
                goal_role = var;
            }
        }
        for (i = 0; i < ca_array_size; i++) {
            Expr ca_adm = getCAAdmFormula(this->atoms, i);
            Expr ca_pn = getCAPNFormula(this->atoms, i);
            Atom ca_target = this->atoms[ca_array[i].target_role_index];
            std::shared_ptr<rule> ca_rule(rule::create_ca(ca_adm, ca_pn, ca_target, i));
            this->can_assign_rules.push_back(ca_rule);
            // print_ca_comment(stdout, i);
            // printf("%s\n", getCAPNFormula(i)->to_string().c_str());
        }
        for (i = 0; i < cr_array_size; i++) {
            Expr cr_adm = getCRAdmFormula(this->atoms, i);
            Expr cr_pn = getCRPNFormula(this->atoms, i);
            Atom cr_target = this->atoms[cr_array[i].target_role_index];
            std::shared_ptr<rule> cr_rule(rule::create_cr(cr_adm, cr_pn, cr_target, i));
            this->can_revoke_rules.push_back(cr_rule);
            // print_cr_comment(stdout, i);
            // printf("%s\n", getCRPNFormula(i)->to_string().c_str());
        }
    }

    void arbac_policy::remove_can_assign(std::shared_ptr<rule>& _rule) {
        std::vector<std::shared_ptr<rule>> res;
        auto filtered =
            std::copy_if(this->can_assign_rules.begin(),
                           this->can_assign_rules.end(),
                           std::back_inserter(res),
                           [&](const std::shared_ptr<rule>& r)
                                { return r->original_idx != _rule->original_idx; } );
        this->can_assign_rules = res;
    }
    void arbac_policy::remove_can_revoke(std::shared_ptr<rule>& _rule) {
        std::vector<std::shared_ptr<rule>> res;
        auto filtered =
            std::copy_if(this->can_revoke_rules.begin(),
                           this->can_revoke_rules.end(),
                           std::back_inserter(res),
                           [&](const std::shared_ptr<rule>& r)
                                { return r->original_idx != _rule->original_idx; } );
        this->can_revoke_rules = res;
    }

//    void arbac_policy::remove_can_assign(int index) {
//        this->can_assign_rules.erase(can_assign_rules.begin() + index);
//    }
//    void arbac_policy::remove_can_revoke(int index) {
//        this->can_revoke_rules.erase(can_revoke_rules.begin() + index);
//    }

}