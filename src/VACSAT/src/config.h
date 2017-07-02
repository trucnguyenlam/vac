//
// Created by esteffin on 18/05/17.
//

#ifndef VACSAT_CONFIG_H
#define VACSAT_CONFIG_H

#include <string>
#include <ostream>
#include <spdlog/logger.h>
#include <spdlog/fmt/ostr.h>
//#include <boost/log/trivial.hpp>
//#include <boost/log/core.hpp>
//#include <boost/log/expressions.hpp>

namespace SMT {
    class Config {
    public:
        enum Verbosity {
            TRACE,
            DEBUG,
            INFO,
            WARNING,
            ERROR,
            FATAL
        };
        static bool experimental;
        static Verbosity verbosity;
        static bool merge;
        static int rule_6_max_depth;
        static bool simplify_toplevel_or;
        static std::string dump_smt_formula;

        static bool no_infinity_bmc;
        static int infinity_bmc_rounds_count;
        static int infinity_bmc_steps_count;

        static std::string input_file;

    };

    extern std::shared_ptr<spdlog::logger> log;

    inline bool can_write(spdlog::level::level_enum lvl) {
        return log->level() <= lvl;
    }
}

#endif //VACSAT_CONFIG_H
