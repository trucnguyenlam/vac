//
// Created by esteffin on 11/05/17.
//

#ifndef VACSAT_SMT_ANALYSIS_H
#define VACSAT_SMT_ANALYSIS_H

#include <string>
#include <memory>
#include "ARBACTransform.h"
#include "ARBACExact.h"
#include "SMT.h"
#include "SMTSolvers/Z3.h"
#include "SMTSolvers/yices.h"
#include "prelude.h"

namespace SMT {

    void perform_analysis(const std::string& inputFile, const std::string& solver_name);
}

#endif //VACSAT_SMT_ANALYSIS_H
