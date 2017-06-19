//
// Created by esteffin on 23/05/17.
//

#include <iostream>
//#include <boost/log/trivial.hpp>
#include "config.h"

namespace SMT {

    bool Config::experimental = false;

    Config::Verbosity Config::verbosity = Config::TRACE;
    bool Config::merge = false;
    bool Config::simplify_toplevel_or = false;

    int infinity_bmc_rounds_count = -1;
    int infinity_bmc_steps_count = -1;


    std::string Config::dump_smt_formula = "";

    std::string Config::input_file = "";

    std::shared_ptr<spdlog::logger> log = nullptr;

//    std::ostream log::log = std::cout;
//    FILE* log::flog = stdout;
//    std::ostream log::out = std::cout;
//    FILE* log::fout = stdout;
//    std::ostream log::err = std::cerr;
//    FILE* log::ferr = stderr;
}