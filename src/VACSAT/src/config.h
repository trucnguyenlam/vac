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
    struct OverapproxOptions {
        enum OverapproxVersion {
            JUNE,
            TRACE_ALL,
            SELECTIVE,
            ADMIN,
            LEARNING
        };
        /*enum BlocksChoice {
            STRICT,
            AT_MOST,
            AT_LEAST
        };*/
        OverapproxVersion version;
        int depth;
        int blocks_count;

        static OverapproxVersion parse(const std::string& version) {
            if (version == "June") {
                return JUNE;
            } else if (version == "selective") {
                return SELECTIVE;
            } else if (version == "total") {
                return TRACE_ALL;
            } else if (version == "admin") {
                return ADMIN;
            } else if (version == "learning") {
                return LEARNING;
            } else {
                throw std::runtime_error("Unknown overapproximated analysis version");
            }
        }
    };

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
        static bool do_not_merge;
        static int rule_6_max_depth;
        static bool use_tampone;
        static OverapproxOptions overapproxOptions;
        //static int overapprox_merge_precs;
        static bool simplify_toplevel_or;
        static std::string dump_smt_formula;
        static bool show_solver_statistics;
        static bool print_old_model;

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
