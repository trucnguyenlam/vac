//
// Created by esteffin on 22/05/17.
//

#ifndef VACSAT_BMC_STRUCT_H
#define VACSAT_BMC_STRUCT_H

#include "Logics.h"

namespace SMT {
    enum var_type {
        BOOLEAN,
        BIT_VECTOR
    };

    template <typename TVar, typename TExpr>
    struct generic_variable : public TVarWrapper<TVar> {

        SMTFactory<TVar, TExpr>* solver;
        int bv_size;
        std::string name;
        std::string full_name;
        int idx;
        var_type type;

        generic_variable() :
                TVarWrapper<TVar>(nullptr),
                bv_size(-1), name(""), full_name(""), idx(-1), solver(nullptr), type(BOOLEAN) { }

        generic_variable(const std::string _name, int _idx, int _bv_size, SMTFactory<TVar, TExpr>* _solver, var_type _type) :
                TVarWrapper<TVar>(nullptr),
                bv_size(_bv_size), name(_name), full_name(_name + "_" + std::to_string(_idx)), idx(_idx), solver(_solver), type(_type)  {
            switch (type) {
                case BIT_VECTOR:
                    this->solver_varp = std::make_shared<TVar>(solver->createBVVar(full_name, bv_size));
                    break;
                case BOOLEAN:
                    this->solver_varp = std::make_shared<TVar>(solver->createVar2(full_name, bv_size));
                    break;
            }
        }

        friend std::ostream& operator<< (std::ostream& stream, const generic_variable<TVar, TExpr>& var) {
            stream << var.full_name;
            return stream;
        }

        generic_variable<TVar, TExpr> createFrom() {
            // printf("GF: %s\n", this->full_name.c_str());
            auto res = generic_variable<TVar, TExpr>(this->name, this->idx + 1, this->bv_size, this->solver, this->type);
            return res;
        }

        static generic_variable<TVar, TExpr> dummy() {
            generic_variable<TVar, TExpr> res;
            res.name = std::string("dummy");
            res.idx = -1;
            res.bv_size = -1;
            res.type = BOOLEAN;
            return res;
        }

    };
}

#endif //VACSAT_BMC_STRUCT_H
