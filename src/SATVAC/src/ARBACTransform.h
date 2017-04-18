#ifndef _ARBACTransform_H
#define _ARBACTransform_H

#include <stdio.h>

void
read_ARBAC(char *);

void
reduction_finiteARBAC(void);

void
preprocess(int);

void
free_data();

int gen_comb_norep_lex_init(int *vector, const int n, const int k);
int gen_comb_norep_lex_next(int *vector, const int n, const int k);

void
print_ca_comment(FILE *, int);
void
print_ca_comment_z3(FILE *, int);
//void
//print_ca_comment_hsf(FILE *, int);
void
print_ca_comment_smt2(FILE *, int);

void
print_cr_comment(FILE *, int);
void
print_cr_comment_z3(FILE *, int);
//void
//print_cr_comment_hsf(FILE *, int);
void
print_cr_comment_smt2(FILE *, int);

// Policy statistics function
void
show_policy_statistics(char *, FILE *, int);


// Precise translate functions
void
transform_2_GETAFIX_ExactAlg(char *, FILE *outputFile);
//void
//transform_2_GETAFIX_parallel_ExactAlg(char *, FILE *outputFile);
void
transform_2_MUCKE_CAV2010(char *, FILE *outputFile, char *, int);
void
transform_2_MUCKE_ExactAlg(char *, FILE *outputFile/*, char **/);
void
transform_2_concurC(char *, FILE *outputFile, int wanted_threads_count);
void
transform_2_lazycseq(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
/*TODO: Remove and merge with previous*/
void
transform_2_lazycseq_inlined(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
void
transform_2_lazycseq_completeness_query(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
void
transform_2_CBMC_ExactAlg(char *, FILE *outputFile);
//void
//transform_2_HSF_ExactAlg(char *, FILE *outputFile);
//void
//transform_2_ELDARICA_ExactAlg(char *, FILE *outputFile);
//void
//transform_2_SMT2_ExactAlg(char *, FILE *outputFile);
void
transform_2_NuSMV_ExactAlg(char *, FILE *outputFile);

namespace SSA {
    void transform_2_ssa(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
    void transform_2_yices(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
}

namespace SMT {
    void transform_2_bounded_smt(char *, FILE *outputFile, int rounds, int steps, int wanted_threads_count);
}

void
wait_keypressed();

#endif
