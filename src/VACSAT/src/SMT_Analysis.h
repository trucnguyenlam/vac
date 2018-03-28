//
// Created by esteffin on 11/05/17.
//

#ifndef VACSAT_SMT_ANALYSIS_H
#define VACSAT_SMT_ANALYSIS_H

#include <string>
#include <memory>
#include "ARBACTransform.h"
#include "old_parser/ARBACExact.h"
#include "SMT.h"
#include "SMTSolvers/Z3.h"
#include "SMTSolvers/yices.h"
#include "SMTSolvers/boolector.h"
#include "SMTSolvers/mathsat.h"
#include "prelude.h"

namespace SMT {
    enum class AnalysisType {
        UPDATE_MODEL,
        SHOW_INITIAL_STATISTICS,
        SHOW_AFTERPRUNE_STATISTICS,
        PRUNE_ONLY,
        ANALYSIS_ONLY,
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

    bool perform_analysis_old_style(const std::string& filename,
                                    AnalysisType analysis_type,
                                    const std::string &solver_name,
                                    bmc_config config);

    bool perform_analysis(const std::string& filename,
                          bool use_old_parser,
                          AnalysisType analysis_type,
                          const std::string &solver_name,
                          bmc_config config);
}

#endif //VACSAT_SMT_ANALYSIS_H
