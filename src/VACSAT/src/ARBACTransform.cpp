#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
#include "ARBACTransform.h"
#include "SMT_Pruning.h"
#include "SMT_Analysis.h"
#include <iostream>
#include <boost/program_options.hpp>
#include "spdlog/spdlog.h"

#define EXIT_UNREACHABLE EXIT_SUCCESS
#define EXIT_REACHABLE 1
#define EXIT_ERROR 2


void
wait_keypressed() {
    std::cout << "Press enter to continue ...";
    getchar();
}

void
error_exit(){
    #ifdef WAIT_ON_EXIT
    wait_keypressed();
    #endif
    exit(EXIT_ERROR);
}

void
success_exit() {
    #ifdef WAIT_ON_EXIT
    wait_keypressed();
    #endif
    exit(EXIT_SUCCESS);
}

void exit_with_result(bool res) {
    if (res) {
        exit(EXIT_REACHABLE);
    } else {
        exit(EXIT_UNREACHABLE);
    }
}

namespace po = boost::program_options;


class options {
public:
    const std::string output_file;
    const bool old_inline;
    const std::string new_backend;
    const bool old_parser;
    const bool new_prune_only;
    const bool new_reachability_only;
    const bool do_not_merge;
    const int rule_6_max_depth;
    const int overapprox_depth;
    const bool experimental_simplify_toplevel_or;
    const int bmc_rounds_count;
    const int bmc_steps_count;
    const int bmc_thread_count;
    const bool no_infinity_bmc;
    const int infinity_bmc_rounds_count;
    const int infinity_bmc_steps_count;
    const std::string mem_limit;
    const int verbosity;
    const bool profile;
    const bool print_old_model;
    const bool update_model;
    const bool solver_statistics;
    const bool show_statistics;
    const bool show_help;
    const std::string input_file;

    //DEBUGGING OPTIONS
    const std::string dump_smt_formula;

    options(std::string _output_file,
            bool _old_inline,
            std::string _new_backend,
            bool _old_parser,
            bool _new_prune_only,
            bool _new_reachability_only,
            bool _do_not_merge,
            int _rule_6_max_depth,
            int _overapprox_depth,
            bool _experimental_simplify_toplevel_or,
            int _bmc_rounds_count,
            int _bmc_steps_count,
            int _bmc_thread_count,
            bool _no_infinity_bmc,
            int _infinity_bmc_rounds_count,
            int _infinity_bmc_steps_count,
            std::string _mem_limit,
            int _verbosity,
            bool _profile,
            bool _print_old_model,
            bool _update_model,
            bool _solver_statistics,
            bool _show_statistics,
            bool _show_help,
            std::string _input_file,
            std::string _dump_smt_formula
    ) : output_file(_output_file),
        old_inline(_old_inline),
        new_backend(_new_backend),
        old_parser(_old_parser),
        new_prune_only(_new_prune_only),
        new_reachability_only(_new_reachability_only),
        do_not_merge(_do_not_merge),
        rule_6_max_depth(_rule_6_max_depth),
        overapprox_depth(_overapprox_depth),
        experimental_simplify_toplevel_or(_experimental_simplify_toplevel_or),
        bmc_rounds_count(_bmc_rounds_count),
        bmc_steps_count(_bmc_steps_count),
        bmc_thread_count(_bmc_thread_count),
        no_infinity_bmc(_no_infinity_bmc),
        infinity_bmc_rounds_count(_infinity_bmc_rounds_count),
        infinity_bmc_steps_count(_infinity_bmc_steps_count),
        mem_limit(_mem_limit),
        verbosity(_verbosity),
        profile(_profile),
        print_old_model(_print_old_model),
        update_model(_update_model),
        solver_statistics(_solver_statistics),
        show_statistics(_show_statistics),
        show_help(_show_help),
        input_file(_input_file),
        dump_smt_formula(_dump_smt_formula) { }

};

template <typename TArg>
struct arg_obj {
public:
    const std::string name;
    const TArg default_value;
    const std::string description;
    TArg result;

    arg_obj(std::string _name,
            TArg _default_value,
            std::string _description) :
            name(_name), default_value(_default_value), description (_description), result(_default_value) { }

    TArg value(po::variables_map vm) {
//        if (vm.count(name.c_str()) < 1) {
//            return default_value;
//        }
//        else {
//            return vm[name.c_str()].as<TArg>();
//        }
        return result;
    }
};

static arg_obj<std::string> create_arg_obj_string(std::string name, std::string default_value, std::string description) {
    return arg_obj<std::string>(name, default_value, description);
}
static arg_obj<std::string> create_arg_obj_string(std::string name, std::string description) {
    return arg_obj<std::string>(name, "", description);
}
static arg_obj<int> create_arg_obj_int(std::string name, int def, std::string description) {
    return arg_obj<int>(name, def, description);
}
static arg_obj<int> create_arg_obj_int(std::string name, std::string description) {
    return arg_obj<int>(name, -1, description);
}
static arg_obj<bool> create_arg_obj_bool(std::string name, std::string description) {
    return arg_obj<bool>(name, false, description);
}

template <typename TArg>
static void add_option_description(arg_obj<TArg>& arg, po::options_description& desc);
static void add_option_description(po::options_description& desc, arg_obj<std::string>& arg) {
    if (arg.default_value != "") {
        desc.add_options()
                (arg.name.c_str(), po::value<std::string>(&arg.result)->default_value(arg.default_value), arg.description.c_str());
    }
    else {
        desc.add_options()
                (arg.name.c_str(), po::value<std::string>(&arg.result), arg.description.c_str());
    }
}

static void add_option_description(po::options_description& desc, arg_obj<int>& arg) {
    if (arg.default_value != -1) {
        desc.add_options()
                (arg.name.c_str(), po::value<int>(&arg.result)->default_value(arg.default_value), arg.description.c_str());
    }
    else {
        desc.add_options()
                (arg.name.c_str(), po::value<int>(&arg.result), arg.description.c_str());
    }
}

static void add_option_description(po::options_description& desc, arg_obj<bool>& arg) {
    desc.add_options()
            (arg.name.c_str(), po::bool_switch(&arg.result), arg.description.c_str());
}

static options parse_args(int ac, const char* const* av) {
    // Declare a group of options that will be
    // allowed only on command line
    po::options_description generic("Generic options");

    // Declare a group of options that will be
    // allowed both on command line and in
    // config file
    po::options_description desc("Analysis option");

    // POSITIONAL ARGUMENT FOR INPUT_FILE
    po::positional_options_description p;


    arg_obj<std::string> output_file = create_arg_obj_string("out,o", "Specify the output file");
    arg_obj<bool> old_inline = create_arg_obj_bool("inline", "Inline the program (lazycseq only)");
    arg_obj<std::string> new_backend = create_arg_obj_string("backend,b", "yices", "SMT backend (Z3, YICES, BOOLECTOR, MATHSAT)");
    arg_obj<bool> old_parser = create_arg_obj_bool("old-parser,O", "Prune the policy using sat based approaches only");
    arg_obj<bool> new_prune_only = create_arg_obj_bool("prune-only,p", "Prune the policy using sat based approaches only");
    arg_obj<bool> new_reachability_only = create_arg_obj_bool("reachability-only,q", "Check reachability with bmc only");
    arg_obj<bool> do_not_merge = create_arg_obj_bool("do-not-merge", "Do not use the pruning merge rule");
    arg_obj<int> rule_6_max_depth = create_arg_obj_int("rule6-max-depth", -1, "Set the max depth of expression that should be tested in rule 6. (< 0 for any)");
    arg_obj<int> overapprox_depth = create_arg_obj_int("overapprox-depth,d", 3, "Set the max depth of over approximation.");
    arg_obj<bool> experimental_simplify_toplevel_or = create_arg_obj_bool("simplify-or,X", "Simplify toplevel or expressions");
    arg_obj<int> bmc_rounds_count = create_arg_obj_int("rounds,r", "Number of rounds for the bmc");
    arg_obj<int> bmc_steps_count = create_arg_obj_int("steps,s", "Number of steps per round for the bmc");
    arg_obj<int> bmc_thread_count = create_arg_obj_int("threads,t", "Number of threads (tracked users) for the bmc");
    arg_obj<bool> no_infinity_bmc = create_arg_obj_bool("no-infinity-bmc,I", "Do not apply infinity bmc during pruning phase");
    arg_obj<int> infinity_bmc_rounds_count = create_arg_obj_int("infinity-rounds", 10, "Number of rounds for the infinity bmc");
    arg_obj<int> infinity_bmc_steps_count = create_arg_obj_int("infinity-steps", 2, "Number of steps per round for the infinity bmc");
    arg_obj<int> verbosity = create_arg_obj_int("verbose,v", 2, "Verbosity level (1=info, 2=debug, 3=trace)");
    arg_obj<bool> profile = create_arg_obj_bool("profile,P", "Show times");
    arg_obj<bool> print_old_model = create_arg_obj_bool("print-old-model,m", "Print using the VAC1 syntax");
    arg_obj<bool> update_model = create_arg_obj_bool("update-model,U", "Update the model from VAC syntax to VAC2 one");
    arg_obj<bool> solver_statistics = create_arg_obj_bool("solver-statistics,T", "Print solver stetistics (over/under-approximation)");
    arg_obj<bool> show_statistics = create_arg_obj_bool("show-statistics,S", "Print policy stetistics");
    arg_obj<std::string> memory_limit = create_arg_obj_string("memlimit,M", "10G", "Set a specific memory limit for the process");
    arg_obj<bool> show_help = create_arg_obj_bool("help,h", "Show this message");
    arg_obj<std::string> input_file = create_arg_obj_string("input-file", "FILE is the input ARBAC file format");
    arg_obj<std::string> dump_smt_formula = create_arg_obj_string("dump-smt,D", "Dump the SMT formula to file");

    add_option_description(desc, output_file);
    add_option_description(desc, old_inline);
    add_option_description(desc, new_backend);
    add_option_description(desc, old_parser);
    add_option_description(desc, new_prune_only);
    add_option_description(desc, new_reachability_only);
    add_option_description(desc, do_not_merge);
    add_option_description(desc, rule_6_max_depth);
    add_option_description(desc, overapprox_depth);
    add_option_description(desc, experimental_simplify_toplevel_or);
    add_option_description(desc, bmc_rounds_count);
    add_option_description(desc, bmc_steps_count);
    add_option_description(desc, bmc_thread_count);
    add_option_description(desc, no_infinity_bmc);
    add_option_description(desc, infinity_bmc_rounds_count);
    add_option_description(desc, infinity_bmc_steps_count);
    add_option_description(desc, verbosity);
    add_option_description(desc, profile);
    add_option_description(desc, print_old_model);
    add_option_description(desc, update_model);
    add_option_description(desc, solver_statistics);
    add_option_description(desc, show_statistics);
    add_option_description(desc, memory_limit);
    add_option_description(desc, input_file);

    add_option_description(desc, dump_smt_formula);

    add_option_description(generic, show_help);

    p.add(input_file.name.c_str(), 1);


    po::options_description cmdline_options;
    cmdline_options.add(generic).add(desc);


    po::variables_map vm;
    po::store(po::command_line_parser(ac, av).options(cmdline_options).positional(p).run(), vm);
    po::notify(vm);


    options result =
            options(output_file.result,
                    old_inline.result,
                    new_backend.result,
                    old_parser.result,
                    new_prune_only.result,
                    new_reachability_only.result,
                    do_not_merge.result,
                    rule_6_max_depth.result,
                    overapprox_depth.result,
                    experimental_simplify_toplevel_or.result,
                    bmc_rounds_count.result,
                    bmc_steps_count.result,
                    bmc_thread_count.result,
                    no_infinity_bmc.result,
                    infinity_bmc_rounds_count.result,
                    infinity_bmc_steps_count.result,
                    memory_limit.result,
                    verbosity.result,
                    profile.result,
                    print_old_model.result,
                    update_model.result,
                    solver_statistics.result,
                    show_statistics.result,
                    show_help.result,
                    input_file.result,
                    dump_smt_formula.result);

    if (result.show_help) {
        std::cout << desc << std::endl;
        success_exit();
    }

    return result;
}

uint64_t read_mem_spec(const char *str) {
    uint64_t mult;
    int len = strlen(str);
    if (!isdigit(str[len-1])) {
        switch (str[len-1]) {
            case 'b':
            case 'B':
                mult = 1;
                break;
            case 'k':
            case 'K':
                mult = 1024;
                break;
            case 'm':
            case 'M':
                mult = 1024*1024;
                break;
            case 'g':
            case 'G':
                mult = 1024*1024*1024;
                break;
            default:
                std::cerr << "Unrecognized memlimit suffix" << std::endl;
                abort();
        }
    } else {
        mult = 1024*1024;
    }

    uint64_t size = strtoul(str, NULL, 10);
    size *= mult;
    return size;
}

#include <sys/resource.h>

static void set_mem_limit(std::string memlimit) {
    uint64_t size = read_mem_spec(memlimit.c_str());

    struct rlimit lim;
    lim.rlim_cur = size;
    lim.rlim_max = size;
    if(setrlimit(RLIMIT_DATA, &lim) != 0)
    {
        perror("Couldn't set memory limit");
        abort();
    }

}

spdlog::level::level_enum int_to_level(int i) {
    switch (i) {
        case 1:
            return spdlog::level::info;
        case 2:
            return spdlog::level::debug;
        case 3:
            return spdlog::level::trace;
        default:
            return spdlog::level::err;
    }
}

void set_logger_err_handler() {
    spdlog::set_error_handler([](const std::string& msg) {
        std::cerr << "Error setting up the logger: " << msg << std::endl;
        throw std::runtime_error(msg);
    });
    // (or logger->set_error_handler(..) to set for specific logger)
}

int main(int argc, const char * const *argv) {
    std::string filename;
    bool logging_on_console = true;
    try {
        set_logger_err_handler();
        options config = parse_args(argc, argv);

        SMT::Config::rule_6_max_depth = config.rule_6_max_depth;
        SMT::Config::overapproxOptions.depth = config.overapprox_depth;
        SMT::Config::no_infinity_bmc = config.no_infinity_bmc;
        SMT::Config::infinity_bmc_rounds_count = config.infinity_bmc_rounds_count;
        SMT::Config::infinity_bmc_steps_count = config.infinity_bmc_steps_count;
        SMT::Config::show_solver_statistics = config.solver_statistics;
        SMT::Config::print_old_model = config.print_old_model;

        if (config.output_file != "") {
            SMT::log = spdlog::basic_logger_mt("log", config.output_file, true);
            logging_on_console = false;
        } else {
            SMT::log = spdlog::stdout_color_mt("log");
        }
        SMT::log->set_level(int_to_level(config.verbosity));
//    SMT::log->set_pattern("[%L] %v");
        SMT::log->set_pattern("%v");

        set_mem_limit(config.mem_limit);

        if (access(config.input_file.c_str(), R_OK) == -1) {
            throw std::runtime_error("Input file does not exists: " + filename);
        }

//        if (config.show_statistics) {
//            show_policy_statistics(filename, out_file, config.bmc_thread_count);
//        }

        SMT::bmc_config bmc_conf(config.bmc_rounds_count, config.bmc_steps_count, config.bmc_thread_count);
        SMT::AnalysisType an_ty;
        if (config.new_prune_only && config.new_reachability_only) {
            throw std::runtime_error("Cannot perform prune-only and reachability-only at the same time.");
        } else if (config.new_reachability_only && config.show_statistics) {
            throw std::runtime_error("show-statistics option is incompatible with reachability-only.");
        } else if (config.update_model && (config.new_prune_only || config.show_statistics || config.new_reachability_only)) {
            throw std::runtime_error("update-model option is incompatible with prune-only, reachability-only, and show-statistics.");
        } else if (config.update_model) {
            an_ty = SMT::UPDATE_MODEL;
        } else if (config.new_prune_only && !config.show_statistics) {
            an_ty = SMT::PRUNE_ONLY;
        } else if (config.new_reachability_only) {
            an_ty = SMT::BMC_ONLY;
        } else if (config.new_prune_only && config.show_statistics) {
            an_ty = SMT::SHOW_AFTERPRUNE_STATISTICS;
        } else if (config.show_statistics) {
            an_ty = SMT::SHOW_INITIAL_STATISTICS;
        } else {
            an_ty = SMT::FULL_ANALYSIS;
        }

        SMT::Config::do_not_merge = config.do_not_merge;

        if (config.dump_smt_formula != "") {
            SMT::Config::dump_smt_formula = config.dump_smt_formula;
        }
        auto global_start = std::chrono::high_resolution_clock::now();
        bool analysis_result =
                SMT::perform_analysis(config.input_file,
                                      config.old_parser,
                                      an_ty,
                                      config.new_backend,
                                      bmc_conf);


        auto global_end = std::chrono::high_resolution_clock::now();
        auto delta_t = global_end - global_start;

        if (config.profile) {
            SMT::log->info("------------ Whole analysis done in {} ms. ------------",
                           std::chrono::duration_cast<std::chrono::milliseconds>(delta_t).count());
        }

        exit_with_result(analysis_result);
    }
        //FIXME: remove comment in deploy
//    catch (const std::runtime_error& err) {
//        if (logging_on_console) {
//            SMT::log->error("Unexpected exception raised: {}", err.what());
//        } else {
//            std::cerr << "Unexpected exception raised: {}" << err.what() << std::endl;
//        }
//        error_exit();
//    }
//    catch (const SMT::unexpected_error& err) {
//        if (logging_on_console) {
//            SMT::log->critical("Unexpected exception raised: {}", err.what());
//        } else {
//            std::cerr << "Unexpected exception raised: " << err.what() << std::endl;
//        }
//    }
    catch (const spdlog::spdlog_ex& ex) {
        std::cerr << "Log init failed: " << ex.what() << std::endl;
        error_exit();
    }
//    catch (const std::exception& ex) {
//        if (logging_on_console) {
//            SMT::log->error("Unexpected exception raised: {}", ex.what());
//        } else {
//            std::cerr << "Unexpected exception raised: {}" << ex.what() << std::endl;
//        }
//        error_exit();
//    }
//    catch (...) {
//        if (logging_on_console) {
//            SMT::log->critical("Unknown unexpected exception raised");
//        } else {
//            std::cerr << "Unknown unexpected exception raised" << std::endl;
//        }
//        error_exit();
//    }


#ifdef WAIT_ON_EXIT
    wait_keypressed();
#endif
    return EXIT_SUCCESS;
}

//int
//old_main(int argc, const char * const *argv)
//{
//    int c;
//    int help_opt = 0;
//    char *algo_arg = NULL;
//    char *format_arg = 0;
//    char *formula_filename = 0;
//    char *filename = 0;
//    char *out_name = NULL;
//    std::string backend = "yices";
//    int rounds = -1;
//    int steps = -1;
//    int wanted_threads = -1;
//    int show_statistics = 0;
//    int _inline = 0;
//    int prune = 0;
//    SMT::AnalysisType analysis_type = SMT::FULL_ANALYSIS;
//
//    static struct option long_options[] = {
//        { "out", required_argument, 0, 'o' },
//        { "prune-only", required_argument, 0, 'p' },
//        { "reachability-only", required_argument, 0, 'q' },
//        { "merge", required_argument, 0, 'm' },
//        { "backend", required_argument, 0, 'b' },
//        { "algorithm", required_argument, 0, 'a' },
//        { "format", required_argument, 0, 'f' },
//        { "formula", required_argument, 0, 'l' },
//        { "rounds", required_argument, 0, 'r' },
//        { "steps", required_argument, 0, 's' },
//        { "threads", required_argument, 0, 't' },
//        { "show-statistics", no_argument, 0, 'S'},
//        { "inline", no_argument, 0, 'i'},
//        { "help", no_argument, 0, 'h'},
//        { 0, 0, 0, 0 }
//    };
//
//    while (1)
//    {
//        int option_index = 0;
//        c = getopt_long(argc, argv, "Sihpqmf:b:a:l:r:s:t:o:", long_options, &option_index);
//
//        if (c == -1)
//            break;
//
//        switch (c)
//        {
//        case 'h':
//
//            printf("ARBAC Translation Tool\
//                    \nTransform ABRAC policies to analysable program.\
//                    \nUsage: translate [OPTION] FILE\
//                    \n-o,--out {filename}                :Specify the output file (default=stdout)\
//                    \n-f,--format <X>                    :Output formats\
//                    \n                                      moped\
//                    \n                                      interproc\
//                    \n                                      cbmc\
//                    \n                                      nusmv\
//                    \n                                      mucke\
//                    \n                                      mucke-cav\
//                    \n                                      lazycseq\
//                    \n                                      completeness_query\
//                    \n                                      concurc\
//                    \n                                      smt\
//                    \n-b,--backend                       :SMT backend (default=yices)\
//                    \n                                      Z3\
//                    \n                                      YICES\
//                    \n-i,--inline                        :Inline the program (lazycseq only)\
//                    \n-p,--prune-only                    :Prune the policy using sat based approaches only\
//                    \n-q,--reachability-only             :Check reachability with bmc only\
//                    \n-m,--merge                         :Use the pruning merge rule\
//                    \n-l,--formula <X>                   :Formula for mucke\
//                    \n-r,--rounds <X>                    :Number of rounds (mucke-cav, lazycseq, ssa and completeness_query only)\
//                    \n-s,--steps <X>                     :Number of steps (lazycseq, ssa and completeness_query only)\
//                    \n-t,--threads <X>                   :Number of tracked user (concurc, lazycseq, ssa and completeness_query only) (Default: auto)\
//                    \n-S,--show-statistics               :Print policy stetistics\
//                    \n-h,--help                          :This message\
//                    \nFILE is the input ARBAC file format\
//                    \nThe formats {cbmc, moped, hsf, eldarica, smt, nusmv, getafix, mucke, mucke-cav, lazycseq, ssa, completeness_query} use a 'precise' algorithm\
//                    \nThe format {interproc} uses an 'abstract' algorithm\n");
//            help_opt = 1;
//            success_exit();
//            break;
//        case 'S':
//            show_statistics = 1;
//            break;
//        case 'p':
//            prune = 1;
//            break;
//        case 'm':
//            SMT::Debug::merge = true;
//            break;
//        case 'i':
//            _inline = 1;
//            break;
//        case 'o':
//            out_name = (char *) malloc(strlen(optarg) + 1);
//            strcpy(out_name, optarg);
//            break;
//        case 'a':
//            algo_arg = (char *) malloc(strlen(optarg) + 1);
//            strcpy(algo_arg, optarg);
//            break;
//        case 'f':
//            format_arg = (char *) malloc(strlen(optarg) + 1);
//            strcpy(format_arg, optarg);
//            break;
//        case 'b':
//            backend = std::string(optarg);
//            break;
//        case 'l':
//            formula_filename = (char *) malloc(strlen(optarg) + 1);
//            strcpy(formula_filename, optarg);
//            break;
//        case 'r':
//            rounds = atoi(optarg);
//            break;
//        case 's':
//            steps = atoi(optarg);
//            break;
//        case 't':
//            wanted_threads = atoi(optarg);
//            break;
//        default:
//            error_exit();
//            break;
//        }
//    }
//
//    if (algo_arg == NULL && !show_statistics && !prune){
//        if (format_arg == NULL) {
//            error_exit();
//        }
//        if (strcmp(format_arg, "interproc") == 0) {
//            algo_arg = (char *) malloc(strlen("abstract") + 1);
//            strcpy(algo_arg, "abstract");
//        }
//        else {
//            algo_arg = (char *) malloc(strlen("precise") + 1);
//            strcpy(algo_arg, "precise");
//        }
//    }
//
//    if (optind < argc)
//    {
//        FILE * out_file = NULL;
//        filename = (char *) malloc(strlen(argv[optind]) + 1);
//        strcpy(filename, argv[optind]);
//
//        if (access(filename, R_OK ) == -1) {
//            fprintf(stderr, "%s: No such file.\n", filename);
//            error_exit();
//        }
//
//        if (out_name == NULL) {
//            out_file = stdout;
//        }
//        else {
//            out_file = fopen(out_name, "w");
//            if (out_file == NULL){
//                fprintf(stderr, "Cannot save in %s.\n", out_name);
//                error_exit();
//            }
//        }
//
//        if (show_statistics) {
//            show_policy_statistics(filename, out_file, wanted_threads);
//            success_exit();
//        }
//        if (prune) {
////            SMT::transform_2_lazycseq_r6(filename, out_file, 61, true);
////            success_exit();
//            SMT::perform_analysis_old_style(SMT::PRUNE_ONLY, std::string(filename), backend, SMT::bmc_config(-1,-1,-1));
//            success_exit();
//        }
//
//
//        if (algo_arg == 0 || format_arg == 0)
//        {
//            error_exit();
//        }
//        else if (strcmp(algo_arg, "precise") == 0)
//        {
//            if (strcmp(format_arg, "moped") == 0)
//            {
//                transform_2_GETAFIX_ExactAlg(filename, out_file);
//            }
//            else if (strcmp(format_arg, "cbmc") == 0)
//            {
//                transform_2_CBMC_ExactAlg(filename, out_file);
//            }
//            else if (strcmp(format_arg, "nusmv") == 0)
//            {
//                transform_2_NuSMV_ExactAlg(filename, out_file);
//            }
//            else if (strcmp(format_arg, "mucke") == 0)
//            {
//                transform_2_MUCKE_ExactAlg(filename, out_file);
//            }
//            else if (strcmp(format_arg, "mucke-cav") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "MUCKE requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (formula_filename == NULL) {
//                    fprintf(stderr, "MUCKE requires to specify the formula (-f)\n");
//                    error_exit();
//                }
//                transform_2_MUCKE_CAV2010(filename, out_file, formula_filename, rounds);
//            }
//            else if (strcmp(format_arg, "lazycseq") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "lazycseq requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (steps == -1) {
//                    fprintf(stderr, "lazycseq requires to specify the steos number (-s)\n");
//                    error_exit();
//                }
//                if (_inline) {
//                    transform_2_lazycseq_inlined(filename, out_file, rounds, steps, wanted_threads);
//                }
//                else {
//                    transform_2_lazycseq(filename, out_file, rounds, steps, wanted_threads);
//                }
//            }
////            else if (strcmp(format_arg, "ssa") == 0)
////            {
////                if (rounds == -1) {
////                    fprintf(stderr, "ssa requires to specify the rounds number (-r)\n");
////                    error_exit();
////                }
////                if (steps == -1) {
////                    fprintf(stderr, "ssa requires to specify the steos number (-s)\n");
////                    error_exit();
////                }
////                SSA::transform_2_ssa(filename, out_file, rounds, steps, wanted_threads);
////            }
////            else if (strcmp(format_arg, "yices") == 0)
////            {
////                if (rounds == -1) {
////                    fprintf(stderr, "yices requires to specify the rounds number (-r)\n");
////                    error_exit();
////                }
////                if (steps == -1) {
////                    fprintf(stderr, "yices requires to specify the steos number (-s)\n");
////                    error_exit();
////                }
////
////                SSA::transform_2_yices(filename, out_file, rounds, steps, wanted_threads);
////            }
//            else if (strcmp(format_arg, "smt") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "smt requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (steps == -1) {
//                    fprintf(stderr, "smt requires to specify the steos number (-s)\n");
//                    error_exit();
//                }
//
//                SMT::transform_2_bounded_smt(filename, out_file, rounds, steps, wanted_threads);
//            }
//            else if (strcmp(format_arg, "completeness_query") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "completeness_query requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (steps == -1) {
//                    fprintf(stderr, "completeness_query requires to specify the steos number (-s)\n");
//                    error_exit();
//                }
//                transform_2_lazycseq_completeness_query(filename, out_file, rounds, steps, wanted_threads);
//            }
//            else if (strcmp(format_arg, "concurc") == 0)
//            {
//                transform_2_concurC(filename, out_file, wanted_threads);
//            }
//            else
//            {
//                error_exit();
//            }
//        }
//        else if (strcmp(algo_arg, "abstract") == 0)
//        {
//            if (strcmp(format_arg, "interproc") == 0)
//            {
//                Abstract::transform_2_INTERPROC_OverApr(filename, out_file);
//            }
//            else {
//                error_exit();
//            }
//        }
//        else
//        {
//            error_exit();
//        }
//
//        if (out_name != NULL) {
//            fclose(out_file);
//        }
//
//        free(filename);
//    }
//    else if (!help_opt)
//    {
//        error_exit();
//    }
//    #ifdef WAIT_ON_EXIT
//    wait_keypressed();
//    #endif
//    return EXIT_SUCCESS;
//}
