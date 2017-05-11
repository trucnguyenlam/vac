//
// Created by esteffin on 11/05/17.
//

#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    void execute(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, const std::shared_ptr<arbac_policy>& policy) {
        prune_policy(solver, policy);
    };

    void set_solver_execute(const std::shared_ptr<arbac_policy>& policy, const std::string& solver_name) {

        if (str_to_lower(solver_name) == str_to_lower(YicesSolver::solver_name())) {
            std::cout << "Using " << solver_name << " as backend" << std::endl;
            std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
            execute(solver, policy);
        }
        else if (str_to_lower(solver_name) == str_to_lower(Z3Solver::solver_name())) {
            std::cout << "Using " << solver_name << " as backend" << std::endl;
            std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
            execute(solver, policy);
        }
        else {
            std::cout << "Backend " << solver_name << " is not supported" << std::endl;
        }

    };

    void perform_analysis(const std::string& inputFile, const std::string& solver_name) {
        read_ARBAC(inputFile.c_str());
        // Preprocess the ARBAC Policies
        preprocess(false);
        build_config_array();

        std::shared_ptr<arbac_policy> policy(new arbac_policy());
        set_solver_execute(policy, solver_name);


        free_data();
        free_precise_temp_data();

    }
}