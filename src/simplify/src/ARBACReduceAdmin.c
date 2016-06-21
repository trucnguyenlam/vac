#include <getopt.h>
#include "ARBACSimplify.h"

void
reduceAdmin(char *inputFile)
{
    int precheck_success = 0, hasPruning = 0;
    // Read ARBAC Policy
    read_ARBAC(inputFile);

    fprintf(tmplog, "***************************************************\n");
    fprintf(tmplog, "**********              LOG           *************\n");
    fprintf(tmplog, "***************************************************\n");
    fprintf(tmplog, "ARBAC system before pruning:\n");
    fprintf(tmplog, "Roles: %d\n", role_array_size);
    fprintf(tmplog, "Users: %d\n", user_array_size);
    fprintf(tmplog, "CR rules: %d\n", cr_array_size);
    fprintf(tmplog, "CA rules: %d\n", ca_array_size);
    fprintf(tmplog, "Total rules: %d\n", cr_array_size + ca_array_size);
    fprintf(tmplog, "***************************************************\n");

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

    fprintf(tmplog, "***************************************************\n");
    fprintf(tmplog, "**********          END LOG           *************\n");
    fprintf(tmplog, "***************************************************\n");

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

int
main(int argc, char **argv)
{
    int c;
    int help_opt = 0;
    int debug_opt = 0;
    int mohawk_opt = 0;
    char *l_arg = 0;
    char *debugfilename;
    FILE *logfile;
    FILE *debugfile;

    static struct option long_options[] = {
        { "logfile", required_argument, 0, 'l' },
        { "debug", no_argument, 0, 'g' },
        { "mohawk", no_argument, 0, 'm' },
        { "help", no_argument, 0, 'h' },
        { 0, 0, 0, 0 }
    };

    while (1)
    {
        int option_index = 0;

        c = getopt_long(argc, argv, "hgl:m", long_options, &option_index);

        if (c == -1)
            break;

        switch (c)
        {
        case 'h':
            printf(
                "VAC Pruning Algorithm Tool\
					\nUsage: simplify [OPTIONS] FILE\
					\nSimplify ARBAC policies to their fixed point.\
					\n\n  -l, --logfile {log_name}\t\t:Produce the log file\
                    \n  -g, --debug\t\t\t\t:Generate simplify log one-to-one map\
                    \n  -m, --mohawk\t\t\t\t:Generate equivalen Mohawk benchmark\
					\n  -h, --help\t\t\t\t:This message\
					\nFILE is the input ARBAC format file\
					\nReturn ARBAC policies file in the same directory as input FILE\n");
            help_opt = 1;
            break;
        case 'l':
            l_arg = malloc(strlen(optarg) + 1);
            strcpy(l_arg, optarg);
            break;
        case 'g':
            debug_opt = 1;
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

        tmplog = tmpfile(); // Temp file
        simplifyLog = tmpfile(); // Temp file
        reduceAdmin(argv[optind]);

        // Write log file
        if (l_arg != 0)
        {
            rewind(tmplog);
            logfile = fopen(l_arg, "w");
            while (1)
            {
                c = fgetc(tmplog);
                if (!feof(tmplog))
                {
                    fputc(c, logfile);
                }
                else
                {
                    break;
                }
            }
            fclose(logfile);
        }
        fclose(tmplog);

        // Write the debug file (for counter example)
        if (debug_opt == 1)
        {
            rewind(simplifyLog);
            debugfilename = malloc(strlen(argv[optind]) + 10);
            sprintf(debugfilename, "%s_debug", argv[optind]);
            debugfile = fopen(debugfilename, "w");
            while (1)
            {
                c = fgetc(simplifyLog);
                if (!feof(simplifyLog))
                {
                    fputc(c, debugfile);
                }
                else
                {
                    break;
                }
            }
            fclose(debugfile);
            free(debugfilename);
        }
        fclose(simplifyLog);
    }
    else if (!help_opt)
    {
        printf("Please input ARBAC FILE. Try simplify -h for help.\n");
    }
}
