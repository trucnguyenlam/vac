//
// Created by esteffin on 11/05/17.
//

#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"

namespace SMT {

    void perform_analysis(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name) {

        std::cerr << "Not implemented yet" << std::endl;
        throw new std::runtime_error("Not implemented yet");
        //std::shared_ptr<arbac_policy> policy = parse_new_ac(inputFile);

//        set_solver_execute(analysis_type, policy, solver_name);


    }
}