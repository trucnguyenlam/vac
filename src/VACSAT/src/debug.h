//
// Created by esteffin on 18/05/17.
//

#ifndef VACSAT_DEBUG_H
#define VACSAT_DEBUG_H

#include <string>
#include <ostream>

namespace SMT {
    class Config {
    public:
        enum Verbosity {
            LOG,
            OUT,
            ERROR
        };
        static bool experimental;
        static Verbosity verbosity;
        static bool merge;

        static std::string input_file;


        static std::string dump_smt_formula;

    };

//    class log {
//        static std::ostream log;
//        static FILE* flog;
//        static std::ostream out;
//        static FILE* fout;
//        static std::ostream err;
//        static FILE* ferr;
//    };

}

#endif //VACSAT_DEBUG_H
