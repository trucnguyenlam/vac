//
// Created by esteffin on 11/05/17.
//

#include <mathsat.h>
#include "SMT_Analysis.h"
#include "Policy.h"
#include "SMT_Pruning.h"
#include "parser/translator.h"
#include "SMT_Analysis_functions.h"
#include "SMT.h"

#ifdef USE_Z3
#include "SMTSolvers/Z3.h"
#endif
#ifdef USE_BOOLECTOR
#include "SMTSolvers/boolector.h"
#endif
#ifdef USE_YICES
#include "SMTSolvers/yices.h"
#endif
#ifdef USE_MATHSAT
#include "SMTSolvers/mathsat.h"
#endif
#ifdef USE_CVC4
#include "SMTSolvers/cvc4.h"
#endif

namespace SMT {

    bool execute_overapprox(const std::shared_ptr<SMTFactory>& solver,
                            const std::shared_ptr<arbac_policy>& policy,
                            const Expr& target_expr,
                            const bmc_config& config) {
//        overapprox_admin(solver, policy, policy->user_count(), target_expr);
//        int a;
//        std::cin >> a;
//        arbac_to_smt_bmc(solver, policy, config.rounds, config.steps, config.wanted_threads_count);
//        exit(0);

        switch (Config::overapproxOptions.version) {
            case OverapproxOptions::JUNE:
                log->debug("Using June overapprox version");
                break;
            case OverapproxOptions::TRACE_ALL:
                log->debug("Using total overapprox version");
                break;
            case OverapproxOptions::SELECTIVE:
                log->debug("Using selective overapprox version");
                break;
            case OverapproxOptions::ADMIN:
                log->debug("Using admin overapprox version");
                break;
            case OverapproxOptions::LEARNING:
                log->debug("Using learning overapprox version");
                break;
        }
        bool over_result = false;
        switch (Config::overapproxOptions.version) {
            case OverapproxOptions::JUNE:
                over_result = overapprox(solver, policy, target_expr);
                break;
            case OverapproxOptions::TRACE_ALL:
                over_result = extended_overapprox(solver, policy, target_expr);
                break;
            case OverapproxOptions::SELECTIVE:
                over_result = super_overapprox(solver, policy, target_expr);
                break;
            case OverapproxOptions::ADMIN:
                over_result = overapprox_admin(solver, policy, policy->user_count(), target_expr);
                break;
            case OverapproxOptions::LEARNING:
                over_result = overapprox_learning(solver, policy, policy->atoms(), policy->rules(), target_expr);
                break;
            default:
                throw unexpected("OVERAPPROX VERSION SWITCH MUST BE COMPLETE");
        }
        return over_result;
    };

    bool execute(const std::string& filename,
                 AnalysisType analysis_type,
                 const std::shared_ptr<SMTFactory>& solver,
                 const std::shared_ptr<arbac_policy>& policy,
                 bmc_config config) {
        switch (analysis_type) {
            case AnalysisType::UPDATE_MODEL:
                log->info(policy->to_new_string());
                return true;
            case AnalysisType::SHOW_AFTERPRUNE_STATISTICS:
                prune_policy(solver, policy);
                /* FALLTHRU */
            case AnalysisType::SHOW_INITIAL_STATISTICS:
                policy->show_policy_statistics(config.wanted_threads_count);
                return true;
            case AnalysisType::PRUNE_ONLY:
                prune_policy(solver, policy);
                if (Config::print_old_model) {
                    log->info(policy->to_arbac_string());
                } else {
                    log->info(policy->to_new_string());
                }
                return true;
            case AnalysisType::ANALYSIS_ONLY:
//                std::cout << *policy;
                break;
            case AnalysisType::FULL_ANALYSIS:
                prune_policy(solver, policy);
                break;
            default:
                throw unexpected("Uh?");
        }
        if (Config::flatten_admin) {
            std::shared_ptr<arbac_policy> flattened = policy->flatten_admin();
            log->info("Flattened pre-pruning");
            log->info("{}", *flattened);
            prune_policy(solver, flattened);
            log->info("Flattened after-pruning");
            log->info("{}", flattened->to_new_string());
        }
        log->debug("Performing underapproximated analysis");

//        std::list<rulep> assigning_target = policy->per_role_can_assign_rule(policy->goal_role);
//        Expr to_check = createConstantFalse();
//        for (auto &&rule : assigning_target) {
//            to_check = createOrExpr(to_check, rule->prec);
//        }

//#ifndef NDEBUG
//        bool over_result = overapprox_multi(solver, policy, to_check, std::set<rulep>(assigning_target.begin(), assigning_target.end()));
//#else
//        bool under_result = arbac_to_smt_bmc(solver, policy, config.rounds, config.steps, config.wanted_threads_count);

//        bool over_result = overapprox(solver, policy, createEqExpr(createLiteralp(policy->goal_role), createConstantTrue()));
//        solver->deep_clean();
        bool over_result = execute_overapprox(solver, policy, createEqExpr(createLiteralp(policy->goal_role), createConstantTrue()), config);


//        log->info("old over: {}", over_result);
//        log->info("new over: {}", ext_over_result);
//        log->info("under: {}", under_result);
//
//        exit(0);

//        bool over_result = extended_overapprox(solver, policy, to_check); //, std::set<rulep>(assigning_target.begin(), assigning_target.end()));
//#endif
        if (!over_result) {
            return false;
        } else { return true; }
        return arbac_to_smt_bmc(solver, policy, config.rounds, config.steps, config.wanted_threads_count);
    };

    bool set_solver_execute(const std::string& filename,
                            AnalysisType analysis_type,
                            const std::shared_ptr<arbac_policy>& policy,
                            const std::string& solver_name,
                            bmc_config config) {

        std::shared_ptr<SMTFactory> solver = nullptr;
        if (false) {
            throw unexpected("if (false) ???");
        }
#ifdef USE_Z3
        else if (str_to_lower(solver_name) == str_to_lower(Z3Solver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new Z3Solver(false));
            return execute(filename, analysis_type,solver, policy, config);
        }
        else if (str_to_lower(solver_name) == str_to_lower(Z3Solver::fast_solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new Z3Solver(true));
            return execute(filename, analysis_type,solver, policy, config);
        }
#endif
#ifdef USE_BOOLECTOR
        else if (str_to_lower(solver_name) == str_to_lower(BoolectorSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new BoolectorSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
#endif
#ifdef USE_YICES
        else if (str_to_lower(solver_name) == str_to_lower(YicesSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new YicesSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
#endif
#ifdef USE_MATHSAT
        else if (str_to_lower(solver_name) == str_to_lower(MathsatSolver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new MathsatSolver());
            return execute(filename, analysis_type,solver, policy, config);
        }
#endif
#ifdef USE_CVC4
        else if (str_to_lower(solver_name) == str_to_lower(Cvc4Solver::solver_name())) {
            log->debug("Using {} as backend", solver_name);
            std::shared_ptr<SMTFactory> solver(new Cvc4Solver());
            return execute(filename, analysis_type,solver, policy, config);
        }
#endif
        else {
            log->error("Backend {} is not supported.", solver_name);
            throw std::runtime_error("Backend " + solver_name + " is not supported.");
        }
        throw unexpected("Uh?");
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