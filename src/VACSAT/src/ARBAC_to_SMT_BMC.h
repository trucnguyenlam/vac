//
// Created by esteffin on 22/05/17.
//

#ifndef VACSAT_ARBAC_TO_SMT_BMC_H
#define VACSAT_ARBAC_TO_SMT_BMC_H

#include "memory"
#include "Policy.h"
#include "Logics.h"
#include "SMT.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    bool arbac_to_smt_bmc(const std::shared_ptr<SMTFactory<TVar, TExpr>> &solver,
                          const std::shared_ptr<arbac_policy> &policy,
                          int steps,
                          int rounds,
                          int wanted_threads_count);
}

#endif //VACSAT_ARBAC_TO_SMT_BMC_H
