#include <getopt.h>
#include "ARBACSimplify.h"

void
reduceAdmin(char *inputFile)
{
    int precheck_success = 0, hasPruning = 0;
    // Read ARBAC Policy
    read_ARBAC(inputFile);

    fprintf(tmp_log, "***************************************************\n");
    fprintf(tmp_log, "**********              LOG           *************\n");
    fprintf(tmp_log, "***************************************************\n");
    fprintf(tmp_log, "ARBAC system before pruning:\n");
    fprintf(tmp_log, "Roles: %d\n", role_array_size);
    fprintf(tmp_log, "Users: %d\n", user_array_size);
    fprintf(tmp_log, "CR rules: %d\n", cr_array_size);
    fprintf(tmp_log, "CA rules: %d\n", ca_array_size);
    fprintf(tmp_log, "Total rules: %d\n", cr_array_size + ca_array_size);
    fprintf(tmp_log, "***************************************************\n");

    // Reduction
    reduction_finiteARBAC();

    trace_array = 0;
    trace_array_size = 0;

    promoted_users.array = 0;
    promoted_users.array_size = 0;

    // Launch Pruning algorithm
    while (1)
    {
        // Applying heuristic to quickly find things
        if (precheck(hasPruning, inputFile))
        {
            precheck_success = 1;
            break;
        }

        if ((immaterial() + slicing() + aggressive_pruning()) == 0)
        {
            break;
        }

        hasPruning = 1;
    }
    if(!precheck_success)
    {
        write_ARBAC(inputFile);
    }

    fprintf(tmp_log, "***************************************************\n");
    fprintf(tmp_log, "**********          END LOG           *************\n");
    fprintf(tmp_log, "***************************************************\n");

    // Free data structure of ARBAC
    free_data();
}

void
generateMohawk(char * inputFile)
{
    // Read ARBAC Policy
    read_ARBAC(inputFile);

    reduction_finiteARBAC();
    generateADMIN();

    write_ARBACMOHAWK(inputFile);
    // Free data structure
    free_data();
}

void
tmp_file_to_file(FILE* in, FILE* out) {
    // Write the in tmpfile to out without closing out
    
    rewind(in);

    while (!feof(in))
    {
        char c = fgetc(in);
        fputc(c, out);
    }
}

int
main(int argc, char **argv)
{
    /*int debug_opt = 0;*/
    int help_opt     = 0;
    int mohawk_opt   = 0;
    char *out_name   = NULL;
    char *log_name   = NULL;
    char *debug_name = NULL;
    FILE *out_file   = NULL;

    static struct option long_options[] = {
        { "logfile", required_argument, 0, 'l' },
        { "out", required_argument, 0, 'o' },
        { "debug", required_argument, 0, 'g' },
        { "mohawk", no_argument, 0, 'm' },
        { "help", no_argument, 0, 'h' },
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;

        int c = getopt_long(argc, argv, "hg:l:o:m", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
        case 'h':
            printf(
                "VAC Pruning Algorithm Tool\
					\nUsage: simplify [OPTIONS] FILE\
					\nSimplify ARBAC policies to their fixed point.\
                    \n\n  -o, --out {out_file}\t\t\t:The simplified out file (default=stdout)\
					\n  -l, --logfile {log_file}\t\t:Produce the log file (default=none)\
                    \n  -g, --debug {debug_file}\t\t:Generate simplify log one-to-one map (default=none)\
                    \n  -m, --mohawk\t\t\t\t:Generate equivalen Mohawk benchmark\
					\n  -h, --help\t\t\t\t:This message\
					\nFILE is the input ARBAC format file\
					\nReturn ARBAC policies file in the same directory as input FILE\n");
            help_opt = 1;
            break;
        case 'o':
            out_name = malloc(strlen(optarg) + 1);
            strcpy(out_name, optarg);
            break;
        case 'l':
            log_name = malloc(strlen(optarg) + 1);
            strcpy(log_name, optarg);
            break;
        case 'g':
            debug_name = malloc(strlen(optarg) + 1);
            strcpy(debug_name, optarg);
            break;
        case 'm':
            mohawk_opt = 1;
            break;
        default:
            abort();
        }
    }

    if (optind < argc)
    {
        if (mohawk_opt)
        {
            generateMohawk(argv[optind]);
            return 0;
        }

        tmp_out   = tmpfile(); // Temp out file
        tmp_log   = tmpfile(); // Temp log file
        tmp_debug = tmpfile(); // Temp debug file

        reduceAdmin(argv[optind]);

        // Write out to file (or stdout)
        if (out_name != NULL) {
            out_file = fopen(out_name, "w");
        }
        else {
            out_file = stdout;
        }


        // Write out file
        tmp_file_to_file(tmp_out, out_file);

        if (out_name != NULL) {
            fclose(out_file);
        }
        fclose(tmp_out);


        // Write log file
        if (log_name != NULL)
        {
            FILE* log_file = fopen(log_name, "w");
            tmp_file_to_file(tmp_log, log_file);
            fclose(log_file);
        }
        fclose(tmp_log);

        // Write the debug file (for counter example)
        if (debug_name != NULL)
        {
            FILE* debug_file = fopen(debug_name, "w");
            tmp_file_to_file(tmp_debug, debug_file);
            fclose(debug_file);
        }
        fclose(tmp_debug);
    }
    else if (!help_opt)
    {
        printf("Please input ARBAC FILE. Try simplify -h for help.\n");
    }
}
