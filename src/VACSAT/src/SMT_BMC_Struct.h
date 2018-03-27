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

    struct generic_variable : public TVarWrapper {

        int bv_size;
        std::string name;
        std::string full_name;
        int idx;
        SMTFactory* solver;
        var_type type;

        generic_variable() :
                TVarWrapper(nullptr),
                bv_size(-1),
                name(""),
                full_name(""),
                idx(-1),
                solver(nullptr),
                type(BOOLEAN) { }

        generic_variable(const std::string _name, int _idx, int _bv_size, SMTFactory* _solver, var_type _type) :
                TVarWrapper(nullptr),
                bv_size(_bv_size),
                name(_name),
                full_name(_name + "_" + std::to_string(_idx)),
                idx(_idx),
                solver(_solver),
                type(_type)  {
            switch (type) {
                case BIT_VECTOR:
                    this->solver_varp = solver->createBVVar(full_name, bv_size);
                    break;
                case BOOLEAN:
                    this->solver_varp = solver->createVar2(full_name, bv_size);
                    break;
            }
        }

        friend std::ostream& operator<< (std::ostream& stream, const generic_variable& var) {
            stream << var.full_name;
            return stream;
        }

        generic_variable createFrom() {
            // printf("GF: %s\n", this->full_name.c_str());
            auto res = generic_variable(this->name, this->idx + 1, this->bv_size, this->solver, this->type);
            return res;
        }

        static generic_variable dummy() {
            generic_variable res;
            res.name = std::string("dummy");
            res.idx = -1;
            res.bv_size = -1;
            res.type = BOOLEAN;
            return res;
        }

    };
}

#endif //VACSAT_BMC_STRUCT_H
