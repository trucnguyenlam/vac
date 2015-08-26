#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <getopt.h>
#include "CounterExample.h"

int
main(int argc, char **argv)
{
    int c;
    int help_opt = 0;

    static struct option long_options[] = { { "help", no_argument, 0, 'h' }, { 0, 0, 0, 0 } };

    while (1)
    {
        int option_index = 0;

        c = getopt_long(argc, argv, "h", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
        case 'h':
            printf(
                "Counter Example for VAC\
                \nUsage:\
                \n\tcounterexample XML_FILE TRANSLATED_FILE ARBAC_SIMPLIFIED_FILE SIMPLIFY_LOG_FILE ARBAC_FILE\
                \n\nThose above FILES must follow exactly the order\
                \nXML_FILE is the XML file got from the output of CBMC model checker on the translated ABRAC policies\
                \nTRANSLATED_FILE is the program for CBMC model checker that is translated from ABRAC policies\
                \nARBAC_SIMPLIFIED_FILE is the simplied of ARBAC policies\
                \nSIMPLIFY_LOG_FILE is the recorded log file of simplification process (simplify -g)\
                \nARBAC_FILE is the original ARBAC policies\n");
            help_opt = 1;
            break;
        default:
            abort();
        }
    }

    if (optind < argc)
    {
        if (argc < 6)
        {
            printf("Please try the correct use of this tool. Try counterexample -h for more information.\n");
            return 0;
        }
        else
        {
        	generate_counter_example(argc, argv);
        	return 0;
        }
    }
    else if (!help_opt)
    {
        printf("Please try the correct use of this tool. Try counterexample -h for more information.\n");
        return 0;
    }
    return 0;
}
