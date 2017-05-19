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
    enum AnalysisType {
        PRUNE_ONLY,
        CHECK_ONLY,
        FULL_ANALYSIS
    };

    void perform_analysis_old_style(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name);

    void perform_analysis(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name);
}

#endif //VACSAT_SMT_ANALYSIS_H
