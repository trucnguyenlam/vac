
#include <vector>
#include <set>
#include <memory>
#include <string>
#include <chrono>
#include <iostream>

#include "ARBACExact.h"
#include "SMT_Pruning.h"
#include "SMT.h"
#include "SMTSolvers/yices.h"

namespace SMT {

    template <typename TType, typename TVar, typename TExpr>
    class Pruning {
        struct formula {
            TExpr formula;
            std::set<std::string> variables;
        };

        void generateRoleVars() {
            for (int i = 0; i < role_array_size; i++) {
                std::string rname(role_array[i]);
                TVar var = solver->createVar(rname, solver->createBoolType());
                role_vars.push_back(var);
            }
        }

        formula getCRAdmFormula(int ruleId) {
            formula ret;
            ret.formula = role_vars[cr_array[ruleId].admin_role_index];
            ret.variables.insert(std::string(role_array[cr_array[ruleId].admin_role_index]));
            return ret;
        }

        formula getCAAdmFormula(int ca_index) {
            formula ret;
            ret.formula = role_vars[ca_array[ca_index].admin_role_index];
            ret.variables.insert(std::string(role_array[ca_array[ca_index].admin_role_index]));
            return ret;
        }

        formula getCAPNFormula(int ca_index) {
            TExpr cond;
            formula ret;
            cond = solver->createBoolConst(true);

            if (ca_array[ca_index].type == 0) {     // Has precondition
                // P
                if (ca_array[ca_index].positive_role_array_size > 0) {
                    int* ca_array_p = ca_array[ca_index].positive_role_array;
                    std::string rp_name = std::string(role_array[ca_array_p[0]]);
                    ret.variables.insert(rp_name);
                    TExpr ca_cond = role_vars[ca_array_p[0]];
                    for (int j = 1; j < ca_array[ca_index].positive_role_array_size; j++) {
                        rp_name = std::string(role_array[ca_array_p[j]]);
                        ret.variables.insert(rp_name);
                        ca_cond = solver->createAndExpr(ca_cond, role_vars[ca_array_p[j]]);
                    }
                    cond = solver->createAndExpr(cond, ca_cond);
                }
                // N
                if (ca_array[ca_index].negative_role_array_size > 0) {
                    int* ca_array_n = ca_array[ca_index].negative_role_array;
                    std::string rn_name = std::string(role_array[ca_array_n[0]]);
                    ret.variables.insert(rn_name);
                    TExpr cr_cond = solver->createNotExpr(role_vars[ca_array_n[0]]);
                    for (int j = 1; j < ca_array[ca_index].negative_role_array_size; j++) {
                        rn_name = std::string(role_array[ca_array_n[j]]);
                        ret.variables.insert(rn_name);
                        cr_cond = solver->createAndExpr(cr_cond, solver->createNotExpr(role_vars[ca_array_n[j]]));
                    }
                    cond = solver->createAndExpr(cond, cr_cond);
                }
            }

            ret.formula = cond;
            return ret;
        }

        void generate_ca_cr_formulae() {
            int i;
            for (i = 0; i < ca_array_size; i++) {
                ca_adm_formulae.push_back(getCAAdmFormula(i));
                ca_pn_formulae.push_back(getCAPNFormula(i));
            }
            for (i = 0; i < cr_array_size; i++) {
                cr_adm_formulae.push_back(getCRAdmFormula(i));
            }
        }

        int nonPositive(int roleId) {
            std::string role_name(role_array[roleId]);
            std::vector<formula> to_check;
            formula f;
            auto ite = ca_adm_formulae.begin();
            for ( ; ite != ca_adm_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }
            ite = ca_pn_formulae.begin();
            for ( ; ite != ca_pn_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }
            ite = cr_adm_formulae.begin();
            for ( ; ite != cr_adm_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                ite = to_check.begin();
                TExpr cond = ite->formula;
                for ( ; ite != to_check.end(); ++ite) {
                    cond = solver->createOrExpr(cond, ite->formula);
                }
                solver->assertNow(role_vars[roleId]);
                solver->assertNow(cond);
            }
            solver->loadToSolver();
            switch (solver->solve()) {
                case SAT: 
                    return false;
                case UNSAT:
                    return true;
                case UNKNOWN:
                    return false;
            }
        }

        int nonNegative(int roleId) {
            std::string role_name(role_array[roleId]);
            std::vector<formula> to_check;
            formula f;
            auto ite = ca_adm_formulae.begin();
            for ( ; ite != ca_adm_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }
            ite = ca_pn_formulae.begin();
            for ( ; ite != ca_pn_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }
            ite = cr_adm_formulae.begin();
            for ( ; ite != cr_adm_formulae.end(); ++ite) {
                f = *ite;
                if (f.variables.count(role_name) > 0) {
                    to_check.push_back(*ite);
                }
            }

            if (to_check.empty()) {
                return true;
            }
            else {
                ite = to_check.begin();
                TExpr cond = ite->formula;
                for ( ; ite != to_check.end(); ++ite) {
                    cond = solver->createOrExpr(cond, ite->formula);
                }
                solver->assertNow(solver->createNotExpr(role_vars[roleId]));
                solver->assertNow(cond);
            }
            solver->loadToSolver();
            switch (solver->solve()) {
                case SAT: 
                    // fprintf(stdout, "System is SAT. Printing model...\n");
                    // solver->printModel();
                    return false;
                case UNSAT:
                    return true;
                case UNKNOWN:
                    return false;
            }
        }

        int irrelevantPositive(int roleId) {

            // IMPROVE!!! ASSERT ALL TOGETHER!!!
            if (nonNegative(roleId)) {
                std::string role_name = role_array[roleId];                
                for (int i = 0; i < ca_array_size; ++i) {
                    int wit = 0;
                    formula _using = ca_pn_formulae[i];
                    if (_using.variables.count(role_name) == 0) {
                        continue;
                    }
                    else {
                        for (int j = 0; j < ca_array_size; j++) {
                            if (i == j || ca_array[j].target_role_index != roleId) {
                                continue;
                            }
                            else {
                                solver->push();
                                solver->assertNow(ca_adm_formulae[i].formula);
                                solver->assertNow(solver->createNotExpr(ca_adm_formulae[j].formula));
                                Result res = solver->solve();
                                solver->pop();
                                if (res == UNSAT) {
                                    solver->push();
                                    solver->assertNow(ca_pn_formulae[i].formula);
                                    solver->assertNow(solver->createNotExpr(ca_pn_formulae[j].formula));
                                    Result res = solver->solve();
                                    solver->pop();
                                }
                            }
                        }

                        

                    }
                } 
            }
            else {
                return false;
            }
        }


        std::shared_ptr<SMTFactory<TType, TVar, TExpr>> solver;

        std::vector<int> nonPositiveRoles;
        std::vector<int> nonNegativeRoles;

        std::vector<TVar> role_vars;

        std::vector<formula> ca_adm_formulae;
        std::vector<formula> ca_pn_formulae;
        std::vector<formula> cr_adm_formulae;

        public:

        void printNonPos() {
            for (int i = 0; i < role_array_size; i++) {
                solver->push();
                int res = nonPositive(i);
                if (res) {
                    fprintf(stdout, "Role %s is nonPositive\n", role_array[i]);
                    nonPositiveRoles.push_back(i);
                }
                else {
                    // fprintf(stdout, "Role %s is Positive\n", role_array[i]);
                }
                solver->pop();
            }
            
        }

        void printNonNeg() {
            for (int i = 0; i < role_array_size; i++) {
                solver->push();
                int res = nonNegative(i);
                if (res) {
                    fprintf(stdout, "Role %s is nonNegative\n", role_array[i]);
                    nonNegativeRoles.push_back(i);
                }
                else {
                    // fprintf(stdout, "Role %s is Negative\n", role_array[i]);
                }
                solver->pop();
            }            
        }

        Pruning(std::shared_ptr<SMTFactory<TType, TVar, TExpr>> _solver) : solver(_solver) {
            generateRoleVars();
            generate_ca_cr_formulae();
         }
    };

    void prune(char* inputFile, FILE* output) { 

        read_ARBAC(inputFile);
        // Preprocess the ARBAC Policies
        preprocess(0);
        build_config_array();

        std::shared_ptr<SMTFactory<term_t, term_t, term_t>> solver(new YicesSolver());
        Pruning<term_t, term_t, term_t> core(solver);

        auto start = std::chrono::high_resolution_clock::now();

        core.printNonPos();

        auto end = std::chrono::high_resolution_clock::now();
        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        std::cout << "------------ printNonPos " << milliseconds.count() << " ms ------------\n";


        start = std::chrono::high_resolution_clock::now();
        core.printNonNeg();

        end = std::chrono::high_resolution_clock::now();
        milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        std::cout << "------------ printNonNeg " << milliseconds.count() << " ms ------------\n";

        free_data();
        free_precise_temp_data();

    }
}
