#pragma once

#include <memory>
#include <vector>
#include "SMT.h"
#include "Logics.h"


namespace SMT {

    template <typename TVar, typename TExpr>
    bool apply_r6(std::shared_ptr<SMTFactory<TVar, TExpr>> solver,
                  std::vector<Expr>& ca_exprs, std::vector<Expr>& cr_exprs, Expr to_check,
                  int exclude_idx, bool excluded_is_ca);


    void prune(char* inputFile, FILE* output);
//    void transform_2_lazycseq_r6(char* inputFile, FILE *outputFile, int rule_index, int is_ca);
    
    // template <typename TVar, typename TExpr>
    bool apply_r6(int rule_index, bool is_ca);
}
