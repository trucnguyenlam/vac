//
// Created by esteffin on 11/05/17.
//

#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"
#include "parser/translator.h"

namespace SMT {

    void perform_analysis(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name) {

        std::shared_ptr<arbac_policy> policy = Parser::parse_new_ac(inputFile);

//        set_solver_execute(analysis_type, policy, solver_name);

    }
}