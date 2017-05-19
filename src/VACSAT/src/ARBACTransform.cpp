#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
#include "ARBACTransform.h"
#include "ARBACAbstract.h"
#include "SMT_Pruning.h"
#include "SMT_Analysis.h"
#include <iostream>

// using namespace Abstract;

void
wait_keypressed() {
    std::cout << "Press enter to continue ..."; 
    getchar();
}

void
error_exit(){
    fprintf(stderr, "Please set correct arguments for the translation.\nTry translate -h for help.\n");
    #ifdef WAIT_ON_EXIT
    wait_keypressed();
    #endif
    exit(EXIT_FAILURE);
}

void
success_exit() {
    #ifdef WAIT_ON_EXIT
    wait_keypressed();
    #endif
    exit(EXIT_SUCCESS);
}

int
main(int argc, char **argv)
{
    int c;
    int help_opt = 0;
    char *algo_arg = NULL;
    char *format_arg = 0;
    char *formula_filename = 0;
    char *filename = 0;
    char *out_name = NULL;
    std::string backend = "yices";
    int rounds = -1;
    int steps = -1;
    int wanted_threads = -1;
    int show_statistics = 0;
    int _inline = 0;
    int prune = 0;

    static struct option long_options[] = {
        { "out", required_argument, 0, 'o' },
        { "prune", required_argument, 0, 'p' },
        { "backend", required_argument, 0, 'b' },
        { "algorithm", required_argument, 0, 'a' },
        { "format", required_argument, 0, 'f' },
        { "formula", required_argument, 0, 'l' },
        { "rounds", required_argument, 0, 'r' },
        { "steps", required_argument, 0, 's' },
        { "threads", required_argument, 0, 't' },
        { "show-statistics", no_argument, 0, 'S'},
        { "inline", no_argument, 0, 'i'},
        { "help", no_argument, 0, 'h'},
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;
        c = getopt_long(argc, argv, "Sihpf:b:a:l:r:s:t:o:", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
        case 'h':
/*                    \n-a,--algorithm {precise, abstract} :Specify the algorithm\*/
            printf("ARBAC Translation Tool\
                    \nTransform ABRAC policies to analysable program.\
                    \nUsage: translate [OPTION] FILE\
                    \n-o,--out {filename}                :Specify the output file (default=stdout)\
                    \n-f,--format <X>                    :Output formats\
                    \n                                      moped\
                    \n                                      interproc\
                    \n                                      cbmc\
                    \n                                      nusmv\
                    \n                                      mucke\
                    \n                                      mucke-cav\
                    \n                                      lazycseq\
                    \n                                      completeness_query\
                    \n                                      concurc\
                    \n                                      smt\
                    \n-b,--backend                       :SMT backend (default=yices)\
                    \n                                      Z3\
                    \n                                      YICES\
                    \n-i,--inline                        :Inline the program (lazycseq only)\
                    \n-p,--prune                         :Prune the policy using sat based approaches\
                    \n-l,--formula <X>                   :Formula for mucke\
                    \n-r,--rounds <X>                    :Number of rounds (mucke-cav, lazycseq, ssa and completeness_query only)\
                    \n-s,--steps <X>                     :Number of steps (lazycseq, ssa and completeness_query only)\
                    \n-t,--threads <X>                   :Number of tracked user (concurc, lazycseq, ssa and completeness_query only) (Default: auto)\
                    \n-S,--show-statistics               :Print policy stetistics\
                    \n-h,--help                          :This message\
                    \nFILE is the input ARBAC file format\
                    \nThe formats {cbmc, moped, hsf, eldarica, smt, nusmv, getafix, mucke, mucke-cav, lazycseq, ssa, completeness_query} use a 'precise' algorithm\
                    \nThe format {interproc} uses an 'abstract' algorithm\n");
            help_opt = 1;
            success_exit();
            break;
        case 'S':
            show_statistics = 1;
            break;
        case 'p':
            prune = 1;
            break;
        case 'i':
            _inline = 1;
            break;
        case 'o':
            out_name = (char *) malloc(strlen(optarg) + 1);
            strcpy(out_name, optarg);
            break;
        case 'a':
            algo_arg = (char *) malloc(strlen(optarg) + 1);
            strcpy(algo_arg, optarg); 
            break;
        case 'f':
            format_arg = (char *) malloc(strlen(optarg) + 1);
            strcpy(format_arg, optarg);
            break;
        case 'b':
            backend = std::string(optarg);
            break;
        case 'l':
            formula_filename = (char *) malloc(strlen(optarg) + 1);
            strcpy(formula_filename, optarg);
            break;
        case 'r':
            rounds = atoi(optarg);
            break;
        case 's':
            steps = atoi(optarg);
            break;
        case 't':
            wanted_threads = atoi(optarg);
            break;
        default:
            error_exit();
            break;
        }
    }

    if (algo_arg == NULL && !show_statistics && !prune){
        if (format_arg == NULL) {
            error_exit();
        }
        if (strcmp(format_arg, "interproc") == 0) {
            algo_arg = (char *) malloc(strlen("abstract") + 1);
            strcpy(algo_arg, "abstract"); 
        }
        else {
            algo_arg = (char *) malloc(strlen("precise") + 1);
            strcpy(algo_arg, "precise"); 
        }
    }

    if (optind < argc)
    {
        FILE * out_file = NULL;
        filename = (char *) malloc(strlen(argv[optind]) + 1);
        strcpy(filename, argv[optind]);

        if (access(filename, R_OK ) == -1) {
            fprintf(stderr, "%s: No such file.\n", filename);
            error_exit();
        }

        if (out_name == NULL) {
            out_file = stdout;
        }
        else {
            out_file = fopen(out_name, "w");
            if (out_file == NULL){
                fprintf(stderr, "Cannot save in %s.\n", out_name);
                error_exit();
            }
        }

        if (show_statistics) {
            show_policy_statistics(filename, out_file, wanted_threads);
            success_exit();
        }
        if (prune) {
//            SMT::transform_2_lazycseq_r6(filename, out_file, 61, true);
//            success_exit();
            SMT::perform_analysis_old_style(SMT::PRUNE_ONLY, std::string(filename), backend);
            success_exit();
        }


        if (algo_arg == 0 || format_arg == 0)
        {
            error_exit();
        }
        else if (strcmp(algo_arg, "precise") == 0)
        {
            if (strcmp(format_arg, "moped") == 0)
            {
                transform_2_GETAFIX_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "cbmc") == 0)
            {
                transform_2_CBMC_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "nusmv") == 0)
            {
                transform_2_NuSMV_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "mucke") == 0)
            {
                transform_2_MUCKE_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "mucke-cav") == 0)
            {
                if (rounds == -1) {
                    fprintf(stderr, "MUCKE requires to specify the rounds number (-r)\n");
                    error_exit();
                }
                if (formula_filename == NULL) {
                    fprintf(stderr, "MUCKE requires to specify the formula (-f)\n");
                    error_exit();
                }
                transform_2_MUCKE_CAV2010(filename, out_file, formula_filename, rounds);
            }
            else if (strcmp(format_arg, "lazycseq") == 0)
            {
                if (rounds == -1) {
                    fprintf(stderr, "lazycseq requires to specify the rounds number (-r)\n");
                    error_exit();
                }
                if (steps == -1) {
                    fprintf(stderr, "lazycseq requires to specify the steos number (-s)\n");
                    error_exit();
                }
                if (_inline) {
                    transform_2_lazycseq_inlined(filename, out_file, rounds, steps, wanted_threads);
                }
                else {
                    transform_2_lazycseq(filename, out_file, rounds, steps, wanted_threads);
                }
            }
//            else if (strcmp(format_arg, "ssa") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "ssa requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (steps == -1) {
//                    fprintf(stderr, "ssa requires to specify the steos number (-s)\n");
//                    error_exit();
//                }
//                SSA::transform_2_ssa(filename, out_file, rounds, steps, wanted_threads);
//            }
//            else if (strcmp(format_arg, "yices") == 0)
//            {
//                if (rounds == -1) {
//                    fprintf(stderr, "yices requires to specify the rounds number (-r)\n");
//                    error_exit();
//                }
//                if (steps == -1) {
//                    fprintf(stderr, "yices requires to specify the steos number (-s)\n");
//                    error_exit();
//                }
//
//                SSA::transform_2_yices(filename, out_file, rounds, steps, wanted_threads);
//            }
            else if (strcmp(format_arg, "smt") == 0)
            {
                if (rounds == -1) {
                    fprintf(stderr, "smt requires to specify the rounds number (-r)\n");
                    error_exit();
                }
                if (steps == -1) {
                    fprintf(stderr, "smt requires to specify the steos number (-s)\n");
                    error_exit();
                }

                SMT::transform_2_bounded_smt(filename, out_file, rounds, steps, wanted_threads);
            }            
            else if (strcmp(format_arg, "completeness_query") == 0)
            {
                if (rounds == -1) {
                    fprintf(stderr, "completeness_query requires to specify the rounds number (-r)\n");
                    error_exit();
                }
                if (steps == -1) {
                    fprintf(stderr, "completeness_query requires to specify the steos number (-s)\n");
                    error_exit();
                }
                transform_2_lazycseq_completeness_query(filename, out_file, rounds, steps, wanted_threads);
            }
            else if (strcmp(format_arg, "concurc") == 0)
            {
                transform_2_concurC(filename, out_file, wanted_threads);
            }
            else
            {
                error_exit();
            }
        }
        else if (strcmp(algo_arg, "abstract") == 0)
        {
            if (strcmp(format_arg, "interproc") == 0)
            {
                Abstract::transform_2_INTERPROC_OverApr(filename, out_file);
            }
            else {
                error_exit();
            }
        }
        else
        {
            error_exit();
        }

        if (out_name != NULL) {
            fclose(out_file);
        }

        free(filename);
    }
    else if (!help_opt)
    {
        error_exit();
    }
    #ifdef WAIT_ON_EXIT
    wait_keypressed();
    #endif
    return EXIT_SUCCESS;
}
