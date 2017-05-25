#include "ARBACExact.h"


void
show_policy_statistics(std::string inputFile, FILE *outputFile, int wanted_threads_count) {
	int threads_count, use_tracks;
    read_ARBAC(inputFile.c_str());
    // Preprocess the ARBAC Policies
    preprocess(0);
    build_config_array();

    if (wanted_threads_count < 1) {
        if (user_array_size <= admin_role_array_index_size + 1) {
            threads_count = user_array_size;
            use_tracks = 0;
        }
        else {
            threads_count = admin_role_array_index_size + 1;
            use_tracks = 1;
        }
    }
    else {
        if (user_array_size <= wanted_threads_count) {
            fprintf(stderr, "Cannot spawn %d threads because are more than user count (%d)\n", wanted_threads_count, user_array_size);
        }
        else {
            threads_count = admin_role_array_index_size + 1;
            use_tracks = 1;
        }   
    }

    fprintf(outputFile, "Policy name: %s\n", inputFile.c_str());
   	fprintf(outputFile, "*  Users: %d\n", user_array_size);
    fprintf(outputFile, "*  Roles: %d\n", role_array_size);
    fprintf(outputFile, "*  AdminRoles: %d\n", admin_role_array_index_size);
    fprintf(outputFile, "*  CA: %d\n", ca_array_size);
    fprintf(outputFile, "*  CR: %d\n", cr_array_size);
    fprintf(outputFile, "*  ThreadCount: %d\n", threads_count);
    fprintf(outputFile, "*  Require tracks: %s\n", use_tracks ? "True" : "False");

}