#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include "CounterExample.h"

void
error_exit(){
    fprintf(stderr, "Please set correct arguments for the counterexample.\nTry counterexample -h for help.\n");
    exit(EXIT_FAILURE);
}

int
main(int argc, char **argv)
{
    int c;
    int help_opt = 0;

    char *cbmc_xml = NULL;
    char *cbmc_c_input = NULL;
    char *simpl_pol = NULL;
    char *simpl_log = NULL;
    char *out_name = NULL;
    char *arbac_file = NULL;

    static struct option long_options[] = {
        { "help", no_argument, 0, 'h' },
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;

        c = getopt_long(argc, argv, "hx:c:p:l:o:", long_options, &option_index);

        if (c == -1)
            break;

        static struct option long_options[] = {
            { "cbmc-xml", required_argument, 0, 'x' },
            { "cbmc-input", required_argument, 0, 'c' },
            { "simplified-policy", required_argument, 0, 'p' },
            { "simplified-log", required_argument, 0, 'l' },
            { "out", required_argument, 0, 'o' },
            { "help", no_argument, 0, 'h'},
            { 0, 0, 0, 0 }
        };

        switch (c)
        {
        case 'h':
            printf(
                "Counter Example Generator for VAC\n"
                "Usage: counterexample OPTIONS ARBAC_FILE\n"
                "OPTIONS:\n"
                "  -x,--cbmc-xml          {XML_FILE}                Mandatory: the XML file got from CBMC on the translated ABRAC policies\n"
                "  -c,--cbmc-input        {TRANSLATED_FILE}         Mandatory: is the program for CBMC that is translated from ABRAC policies\n"
                "  -p,--simplified-policy {ARBAC_SIMPLIFIED_FILE}   If simplification: is the simplified of ARBAC policies\n"
                "  -d,--simplified-debug  {SIMPLIFY_DEBUG_FILE}     If simplification: is the recorded debug information of simplification process (invoke ./simplify -g command)\n"
                "  -o,--out               {filename}                Optional: Specify the output file (default=stdout)\n"
                "  -h,--help                                        Shows this message then exit\n"
                "  ARBAC_FILE is the original (not simplfiedied) ARBAC policies\n"
                );
            help_opt = 1;
            exit(EXIT_SUCCESS);
            break;
        case 'x':
            cbmc_xml = malloc(strlen(optarg) + 1);
            strcpy(cbmc_xml, optarg);
            break;
        case 'c':
            cbmc_c_input = malloc(strlen(optarg) + 1);
            strcpy(cbmc_c_input, optarg);
            break;
        case 'p':
            simpl_pol = malloc(strlen(optarg) + 1);
            strcpy(simpl_pol, optarg);
            break;
        case 'l':
            simpl_log = malloc(strlen(optarg) + 1);
            strcpy(simpl_log, optarg);
            break;
        case 'o':
            out_name = malloc(strlen(optarg) + 1);
            strcpy(out_name, optarg);
            break;
        default:
            error_exit();
        }
    }

    if (optind < argc) {
        FILE * out_file = NULL;
        arbac_file = malloc(strlen(argv[optind]) + 1);
        strcpy(arbac_file, argv[optind]);

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

        if (cbmc_xml != NULL && cbmc_c_input != NULL && simpl_pol != NULL && simpl_log != NULL && arbac_file != NULL) {
            generate_counter_example_full(cbmc_xml, cbmc_c_input, simpl_pol, simpl_log, arbac_file, out_file);
        }
        else if (cbmc_xml != NULL && cbmc_c_input != NULL && arbac_file != NULL) {
            generate_counter_example(cbmc_xml, cbmc_c_input, arbac_file, out_file);            
        }
        else {
            error_exit();
        }

        if (out_name != NULL) {
            fclose(out_file);
        }
        return EXIT_SUCCESS;
    }
    else if (!help_opt)
    {
        error_exit();
    }
    return EXIT_SUCCESS;
}
