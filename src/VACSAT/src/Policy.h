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

        void print();

        std::string to_string();
        std::string get_type();

        static rule* create_ca(Expr admin, Expr prec, Literalp target, int original_idx);
        static rule* create_cr(Expr admin, Expr prec, Literalp target, int original_idx);

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

        void remove_can_assign(int index);
        void remove_can_revoke(int index);

        std::vector<Literalp> atoms;

        std::vector<std::shared_ptr<rule>> can_assign_rules;
        std::vector<std::shared_ptr<rule>> can_revoke_rules;
    };

}

#endif //VACSAT_POLICY_H
