#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include "ARBACTransform.h"

int
main(int argc, char **argv)
{
    int c;
    int help_opt = 0;
    char *algo_arg = 0;
    char *format_arg = 0;
    char *filename = 0;

    static struct option long_options[] = {
        { "algorithm", required_argument, 0, 'a' },
        { "format", required_argument, 0, 'f' },
        { "help", no_argument, 0, 'h'},
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;
        c = getopt_long(argc, argv, "hf:a:", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
        case 'h':
            printf("ARBAC Translation Tool\
                    \nTransform ABRAC policies to analysable program.\
                    \nUsage: translate [OPTION]...FILE\
                    \n-a, --algorithm {precise, abstract}\t\t\t\t\t:Specify the algorithm\
                    \n-f, --format {moped, interproc, cbmc, hsf, eldarica, smt, nusmv}\t:Output formats\
                    \n-h, --help\t\t\t\t\t\t\t\t:This message\
                    \nFILE is the input ARBAC file format\
                    \nFor 'precise' option, there are several formats of {cbmc, moped, hsf, eldarica, smt, nusmv}\
                    \nFor 'abstract' option, there are several formats of {interproc}\n");
            help_opt = 1;
            break;
        case 'a':
            algo_arg = malloc(strlen(optarg) + 1);
            strcpy(algo_arg, optarg);
            break;
        case 'f':
            format_arg = malloc(strlen(optarg) + 1);
            strcpy(format_arg, optarg);
            break;
        default:
            abort();
        }
    }

    if (optind < argc)
    {
        filename = malloc(strlen(argv[optind]) + 1);
        strcpy(filename, argv[optind]);

        if (algo_arg == 0 || format_arg == 0)
        {
            printf("Please set arguments for the translation. Try translate -h for help.\n");
        }
        else if (strcmp(algo_arg, "precise") == 0)
        {
            if (strcmp(format_arg, "moped") == 0)
            {
                transform_2_GETAFIX_ExactAlg(filename);
            }
            else if (strcmp(format_arg, "cbmc") == 0)
            {
                transform_2_CBMC_ExactAlg(filename);
            }
            else if (strcmp(format_arg, "hsf") == 0)
            {
                transform_2_HSF_ExactAlg(filename);
            }
            else if (strcmp(format_arg, "eldarica") == 0)
            {
                transform_2_ELDARICA_ExactAlg(filename);
            }
            else if (strcmp(format_arg, "smt") == 0)
            {
                transform_2_SMT2_ExactAlg(filename);
            }
            else if (strcmp(format_arg, "nusmv") == 0)
            {
                transform_2_NuSMV_ExactAlg(filename);
            }
            else
            {
                printf("Please set correct options for the format file output. Try translate -h for help.\n");
            }
        }
        else if (strcmp(algo_arg, "abstract") == 0)
        {
            if (strcmp(format_arg, "interproc") == 0)
            {
                transform_2_INTERPROC_OverApr(filename);
            }
            else
            {
                printf("Please set correct options for the format file output. Try translate -h for help.\n");
            }
        }
        else
        {
            printf("Please set correct options for the translation algorithm. Try translate -h for help.\n");
        }
        free(filename);
    }
    else if (!help_opt)
    {
        printf("Please use correct options of this program. Try translate -h for help.\n");
    }
    return 1;
}