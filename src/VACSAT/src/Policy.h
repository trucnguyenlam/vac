//
// Created by esteffin on 24/04/17.
//

#ifndef VACSAT_POLICY_H
#define VACSAT_POLICY_H

#include <string>
#include <vector>
#include "Logics.h"

namespace SMT {

    class rule {
    public:
        rule(bool is_ca, Expr admin, Expr prec, Literalp target, int original_idx);

        void print() const;

        std::string to_string() const;
        std::string get_type() const;

        static rule* create_ca(Expr admin, Expr prec, Literalp target, int original_idx);
        static rule* create_cr(Expr admin, Expr prec, Literalp target, int original_idx);

        friend std::ostream& operator<< (std::ostream& stream, const rule& self);

        bool is_ca;
        Expr admin;
        Expr prec;
        Literalp target;
        int original_idx;
    };



    class arbac_policy {
    public:
        arbac_policy();

        inline int atom_count() {
            return (int) atoms.size();
        }

//        void remove_can_assign(rule to_remove);
//        void remove_can_revoke(rule to_remove);

        void remove_can_assign(std::shared_ptr<rule>& rule);
        void remove_can_revoke(std::shared_ptr<rule>& rule);

        std::vector<Literalp> atoms;

        std::vector<std::shared_ptr<rule>> can_assign_rules;
        std::vector<std::shared_ptr<rule>> can_revoke_rules;
    };

}

#endif //VACSAT_POLICY_H
