//
// Created by esteffin on 25/04/17.
//

#ifndef VACSAT_SMT_PRUNING_H
#define VACSAT_SMT_PRUNING_H

#include <memory>
#include <vector>
#include "SMT.h"
#include "Logics.h"
#include "Policy.h"


namespace SMT {

    template <typename TVar, typename TExpr>
    bool apply_r6(std::shared_ptr<SMTFactory<TVar, TExpr>> solver,
                  std::shared_ptr<arbac_policy>& policy, std::shared_ptr<rule>& to_check, bool check_adm);


    void prune(char* inputFile, FILE* output);
//    void transform_2_lazycseq_r6(char* inputFile, FILE *outputFile, int rule_index, int is_ca);

}


#endif //VACSAT_SMT_PRUNING_H