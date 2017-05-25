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
        BMC_ONLY,
        FULL_ANALYSIS
    };

    struct bmc_config {
    public:
        bmc_config(int _steps, int _rounds, int _wanted_threads_count) :
            steps(_steps), rounds(_rounds), wanted_threads_count(_wanted_threads_count) { }

        const int steps;
        const int rounds;
        const int wanted_threads_count;
    };

    void perform_analysis_old_style(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name, bmc_config config);

    void perform_analysis(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name, bmc_config config);
}

#endif //VACSAT_SMT_ANALYSIS_H
