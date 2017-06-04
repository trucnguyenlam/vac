//
// Created by esteffin on 11/05/17.
//

#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"
#include "parser/translator.h"
#include "ARBAC_to_SMT_BMC.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    void execute(AnalysisType analysis_type,
                 const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                 const std::shared_ptr<arbac_policy>& policy, bmc_config config) {
        switch (analysis_type) {
            case PRUNE_ONLY:
                prune_policy(solver, policy);
                return;
            case BMC_ONLY:
//                std::cout << *policy;
                break;
            case FULL_ANALYSIS:
                prune_policy(solver, policy);
                break;
            default:
                throw std::runtime_error("Uh?");
        }
        arbac_to_smt_bmc(solver, policy, config.rounds, config.steps, config.wanted_threads_count);
    };

    void set_solver_execute(AnalysisType analysis_type, const std::shared_ptr<arbac_policy>& policy, const std::string& solver_name, bmc_config config) {

        if (str_to_lower(solver_name) == str_to_lower(YicesSolver::solver_name())) {
            log->info("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
            execute(analysis_type,solver, policy, config);
        }
        else if (str_to_lower(solver_name) == str_to_lower(Z3Solver::solver_name())) {
            log->info("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
            execute(analysis_type,solver, policy, config);
        }
        else {
            log->error("Backend {} is not supported.", solver_name);
            throw std::runtime_error("Backend " + solver_name + " is not supported.");
        }

    };

    void perform_analysis(AnalysisType analysis_type, const std::string &inputFile,
                                    const std::string &solver_name, bmc_config config) {
        std::shared_ptr<arbac_policy> policy = Parser::parse_new_ac(inputFile);
//        std::string pol = policy->to_string();
//        std::cout << pol << std::endl;
//        std::cout << policy->atom_count() << std::endl;
        set_solver_execute(analysis_type, policy, solver_name, config);

    }

}