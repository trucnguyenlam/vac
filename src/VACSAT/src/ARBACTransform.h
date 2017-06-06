#ifndef _ARBACTransform_H
#define _ARBACTransform_H

#include <stdio.h>
#include <string>

void
read_ARBAC(const char *);

void
reduction_finiteARBAC(void);

void
preprocess(int);

void
free_data();

void
print_ca_comment(FILE *, int);

void
print_cr_comment(FILE *, int);
//void
//print_cr_comment_hsf(FILE *, int);

// Policy statistics function


namespace SSA {
    void transform_2_ssa(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
    void transform_2_yices(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
}


void
wait_keypressed();

#endif
