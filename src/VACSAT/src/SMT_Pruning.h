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
    bool apply_r6(const std::shared_ptr<SMTFactory<TVar, TExpr>> solver,
                  const std::shared_ptr<arbac_policy>& policy,
                  const std::shared_ptr<rule>& to_check, bool check_adm);

    template <typename TVar, typename TExpr>
    void prune_policy(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                      const std::shared_ptr<arbac_policy>& policy);

}


#endif //VACSAT_SMT_PRUNING_H