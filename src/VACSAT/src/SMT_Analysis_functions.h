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

    bool arbac_to_smt_bmc(const std::shared_ptr<SMT::SMTFactory> &solver,
                          const std::shared_ptr<arbac_policy> &policy,
                          int steps,
                          int rounds,
                          int wanted_threads_count);

    bool overapprox(const std::shared_ptr<SMT::SMTFactory>& solver,
                    const std::shared_ptr<arbac_policy>& policy,
                    const Expr& to_check);

    bool extended_overapprox(const std::shared_ptr<SMT::SMTFactory>& solver,
                             const std::shared_ptr<arbac_policy>& policy,
                             const Expr& to_check);

    bool super_overapprox(const std::shared_ptr<SMT::SMTFactory>& solver,
                          const std::shared_ptr<arbac_policy>& policy,
                          const Expr& to_check);

    bool overapprox_admin(const std::shared_ptr<SMT::SMTFactory>& solver,
                          const std::shared_ptr<arbac_policy>& policy,
                          const int user_count,
                          const Expr& to_check);

    bool overapprox_learning(const std::shared_ptr<SMT::SMTFactory>& solver,
                             const std::shared_ptr<arbac_policy>& policy,
                             const std::vector<atomp>& atoms,
                             const std::vector<rulep>& rules,
                             const Expr& to_check);

}

#endif //VACSAT_ARBAC_TO_SMT_BMC_H
