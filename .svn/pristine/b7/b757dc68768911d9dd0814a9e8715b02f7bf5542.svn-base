#ifndef _ARBACTransform_H
#define _ARBACTransform_H

#include <stdio.h>

void
read_ARBAC(char *);

void
preprocess();

void
free_data();

void
print_ca_comment(FILE *, int);
void
print_ca_comment_z3(FILE *, int);
void
print_ca_comment_hsf(FILE *, int);
void
print_ca_comment_smt2(FILE *, int);

void
print_cr_comment(FILE *, int);
void
print_cr_comment_z3(FILE *, int);
void
print_cr_comment_hsf(FILE *, int);
void
print_cr_comment_smt2(FILE *, int);


// Precise translate functions
void
transform_2_GETAFIX_ExactAlg(char *);
void
transform_2_CBMC_ExactAlg(char *);
void
transform_2_HSF_ExactAlg(char *);
void
transform_2_ELDARICA_ExactAlg(char *);
void
transform_2_SMT2_ExactAlg(char *);
void
transform_2_NuSMV_ExactAlg(char *);

// Abstract translate functions
void
transform_2_INTERPROC_OverApr(char *);

#endif