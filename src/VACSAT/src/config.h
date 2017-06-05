//
// Created by esteffin on 18/05/17.
//

#ifndef VACSAT_CONFIG_H
#define VACSAT_CONFIG_H

#include <string>
#include <ostream>
#include <spdlog/logger.h>
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
        static std::string dump_smt_formula;

        static std::string input_file;

    };

    extern std::shared_ptr<spdlog::logger> log;
    inline bool can_write(spdlog::level::level_enum lvl) {
        return log->level() <= lvl;
    }

//    class logger {
//    public:
////        std::ostream _trace;
////        std::ostream _debug;
////        std::ostream _info;
////        std::ostream _warning;
////        std::ostream _error;
////        std::ostream _fatal;
////
////        FILE* flog;
////        std::ostream out;
////        FILE* fout;
////        std::ostream err;
////        FILE* ferr;
//
////        void init()
////        {
////            logging::core::get()->set_filter
////                    (
////                            logging::trivial::severity >= logging::trivial::info
////                    );
////        }
////
////        int main(int, char*[])
////        {
////            init();
////
////            BOOST_LOG_TRIVIAL(trace) << "A trace severity message";
////            BOOST_LOG_TRIVIAL(debug) << "A debug severity message";
////            BOOST_LOG_TRIVIAL(info) << "An informational severity message";
////            BOOST_LOG_TRIVIAL(warning) << "A warning severity message";
////            BOOST_LOG_TRIVIAL(error) << "An error severity message";
////            BOOST_LOG_TRIVIAL(fatal) << "A fatal severity message";
////
////            return 0;
////        }
//
//        logger() {
//            BOOST_LOG_TRIVIAL(trace) << "asd";
//        }
//
//    };

}

#endif //VACSAT_CONFIG_H
