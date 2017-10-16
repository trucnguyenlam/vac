//
// Created by esteffin on 11/05/17.
//

#include <mathsat.h>
#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"
#include "parser/translator.h"
#include "SMT_Analysis_functions.h"
#include "SMTSolvers/mathsat.h"

namespace SMT {

    template <typename TVar, typename TExpr>
    bool execute(const std::string& filename,
                 AnalysisType analysis_type,
                 const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                 const std::shared_ptr<arbac_policy>& policy,
                 bmc_config config) {
        switch (analysis_type) {
            case UPDATE_MODEL:
                log->info(policy->to_new_string());
                return true;
            case SHOW_AFTERPRUNE_STATISTICS:
                prune_policy(solver, policy);
            case SHOW_INITIAL_STATISTICS:
                policy->show_policy_statistics(config.wanted_threads_count);
                return true;
            case PRUNE_ONLY:
                prune_policy(solver, policy);
                if (Config::print_old_model) {
                    log->info(policy->to_arbac_string());
                } else {
                    log->info(policy->to_new_string());
                }
                return true;
            case BMC_ONLY:
//                std::cout << *policy;
                break;
            case FULL_ANALYSIS:
                prune_policy(solver, policy);
                break;
            default:
                throw std::runtime_error("Uh?");
        }
        log->debug("Performing underapproximated analysis");

        std::list<rulep> assigning_target = policy->per_role_can_assign_rule(policy->goal_role);
        Expr to_check = createConstantFalse();
        for (auto &&rule : assigning_target) {
            to_check = createOrExpr(to_check, rule->prec);
        }

//#ifndef NDEBUG
//        bool over_result = overapprox_multi(solver, policy, to_check, std::set<rulep>(assigning_target.begin(), assigning_target.end()));
//#else
        bool over_result = overapprox(solver, policy, createEqExpr(createLiteralp(policy->goal_role), createConstantTrue()), std::set<rulep>(assigning_target.begin(), assigning_target.end()));
//        bool over_result = extended_overapprox(solver, policy, createEqExpr(createLiteralp(policy->goal_role), createConstantTrue()));
//        bool over_result = extended_overapprox(solver, policy, to_check); //, std::set<rulep>(assigning_target.begin(), assigning_target.end()));
//#endif
        if (!over_result) {
            return false;
        }
        return arbac_to_smt_bmc(solver, policy, config.rounds, config.steps, config.wanted_threads_count);
    };

    bool set_solver_execute(const std::string& filename,
                            AnalysisType analysis_type,
                            const std::shared_ptr<arbac_policy>& policy,
                            const std::string& solver_name,
                            bmc_config config) {

        if (str_to_lower(solver_name) == str_to_lower(YicesSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<term_t, term_t>> solver(new YicesSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
        else if (str_to_lower(solver_name) == str_to_lower(Z3Solver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<expr, expr>> solver(new Z3Solver());
            return execute(filename, analysis_type,solver, policy, config);
        }
        else if (str_to_lower(solver_name) == str_to_lower(BoolectorSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<BoolectorExpr, BoolectorExpr>> solver(new BoolectorSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
        else if (str_to_lower(solver_name) == str_to_lower(MathsatSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory<msat_term, msat_term>> solver(new MathsatSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
        else {
            log->error("Backend {} is not supported.", solver_name);
            throw std::runtime_error("Backend " + solver_name + " is not supported.");
        }

    };

    std::shared_ptr<arbac_policy> parse_old(const std::string& filename) {
        read_ARBAC(filename.c_str());
        // Preprocess the ARBAC Policies
        preprocess(false);
        build_config_array();

        std::shared_ptr<arbac_policy> policy(new arbac_policy(filename, true));

        free_data();
        free_precise_temp_data();

        return policy;
    }
    std::shared_ptr<arbac_policy> parse_new(const std::string& filename) {
        std::shared_ptr<arbac_policy> policy = Parser::parse_new_ac(filename);
        return policy;
    }

    bool perform_analysis(const std::string& filename,
                          bool use_old_parser,
                          AnalysisType analysis_type,
                          const std::string &solver_name,
                          bmc_config config) {

        auto policy = use_old_parser ? parse_old(filename) : parse_new(filename);
        bool res = set_solver_execute(filename, analysis_type, policy, solver_name, config);

        return res;
    }

}