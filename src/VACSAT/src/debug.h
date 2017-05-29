//
// Created by esteffin on 18/05/17.
//

#ifndef VACSAT_DEBUG_H
#define VACSAT_DEBUG_H

#include <string>

namespace SMT {
    class Debug {
    public:
        static bool experimental;
        static bool log;
        static bool merge;

        static std::string dump_smt_formula;

    };

}

#endif //VACSAT_DEBUG_H
