#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include "ARBACTransform.h"

void
error_exit(){
    fprintf(stderr, "Please set correct arguments for the translation.\nTry translate -h for help.\n");
    exit(EXIT_FAILURE);
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
    int rounds = -1;
    int steps = -1;

    static struct option long_options[] = {
        { "out", required_argument, 0, 'o' },
        { "algorithm", required_argument, 0, 'a' },
        { "format", required_argument, 0, 'f' },
        { "formula", required_argument, 0, 'l' },
        { "rounds", required_argument, 0, 'r' },
        { "steps", required_argument, 0, 'r' },
        { "help", no_argument, 0, 'h'},
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;
        c = getopt_long(argc, argv, "hf:a:l:r:s:o:", long_options, &option_index);

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
                    \n                                      hsf\
                    \n                                      eldarica\
                    \n                                      smt\
                    \n                                      nusmv\
                    \n                                      getafix\
                    \n                                      mucke\
                    \n                                      mucke-cav\
                    \n                                      lazycseq\
                    \n-l,--formula <X>                   :Formula for mucke\
                    \n-r,--rounds <X>                    :Number of rounds (mucke-cav and lazycseq only)\
                    \n-s,--steps <X>                     :Number of steps (lazycseq only)\
                    \n-h,--help                          :This message\
                    \nFILE is the input ARBAC file format\
                    \nThe formats {cbmc, moped, hsf, eldarica, smt, nusmv, getafix, mucke, mucke-cav lazycseq} use a 'precise' algorithm\
                    \nThe format {interproc} uses an 'abstract' algorithm\n");
            help_opt = 1;
            exit(EXIT_SUCCESS);
            break;
        case 'o':
            out_name = malloc(strlen(optarg) + 1);
            strcpy(out_name, optarg);
            break;
        case 'a':
            algo_arg = malloc(strlen(optarg) + 1);
            strcpy(algo_arg, optarg);
            break;
        case 'f':
            format_arg = malloc(strlen(optarg) + 1);
            strcpy(format_arg, optarg);
            break;
        case 'l':
            formula_filename = malloc(strlen(optarg) + 1);
            strcpy(formula_filename, optarg);
            break;
        case 'r':
            rounds = atoi(optarg);
            break;
        case 's':
            steps = atoi(optarg);
            break;
        default:
            error_exit();
        }
    }

    if (algo_arg == NULL){
        if (format_arg == NULL) {
            error_exit();
        }
        if (strcmp(format_arg, "interproc") == 0) {
            algo_arg = malloc(strlen("abstract") + 1);
            strcpy(algo_arg, "abstract"); 
        }
        else {
            algo_arg = malloc(strlen("precise") + 1);
            strcpy(algo_arg, "precise"); 
        }
    }

    if (optind < argc)
    {
        FILE * out_file = NULL;
        filename = malloc(strlen(argv[optind]) + 1);
        strcpy(filename, argv[optind]);

        if (out_name == NULL) {
            out_file = stdout;
        }
        else {
            out_file = fopen(out_name, "w");
            if (out_file == NULL){
                printf("Cannot save in %s.\n", out_name);
                error_exit();
            }
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
            else if (strcmp(format_arg, "hsf") == 0)
            {
                transform_2_HSF_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "eldarica") == 0)
            {
                transform_2_ELDARICA_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "smt") == 0)
            {
                transform_2_SMT2_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "nusmv") == 0)
            {
                transform_2_NuSMV_ExactAlg(filename, out_file);
            }
            else if (strcmp(format_arg, "getafix") == 0)
            {
                transform_2_GETAFIX_parallel_ExactAlg(filename, out_file);
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
                transform_2_lazycseq(filename, out_file, rounds, steps);
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
                transform_2_INTERPROC_OverApr(filename, out_file);
            }
            else
            {
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
    return EXIT_SUCCESS;
}
