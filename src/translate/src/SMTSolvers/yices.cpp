#include "yices.h"
#include <stdexcept>

namespace SMT {

        YicesSolver::YicesSolver() {
            yices_init();
            context = yices_new_context(NULL);
        }
        YicesSolver::~YicesSolver() {
            yices_exit();
        }

        term_t YicesSolver::createBoolType() {
            return yices_bool_type();
        }
        term_t YicesSolver::createBVType(int size) {
            return yices_bv_type(size);
        }

        term_t YicesSolver::createVar(const std::string name, term_t type) {
            term_t var = yices_new_uninterpreted_term(type);
            yices_set_term_name(var, name.c_str());
            return var;
        }

        term_t YicesSolver::createBVConst(int value, int size) {
            return yices_bvconst_uint32(size, value);
        }
        term_t YicesSolver::createBoolConst(int value) {
            return value ? yices_true() : yices_false();
        }
        term_t YicesSolver::createOrExpr(term_t lhs, term_t rhs) {
            term_t res = yices_or2(lhs, rhs);
            if (res < 0) {
                fprintf(stderr, "Error! Term is less than 0!\n");
            }
            return res;
        }
        term_t YicesSolver::createAndExpr(term_t lhs, term_t rhs) {
            term_t res = yices_and2(lhs, rhs);
            if (res < 0) {
                fprintf(stderr, "Error! Term is less than 0!\n");
            }
            return res;
        }
        term_t YicesSolver::createNotExpr(term_t expr) {
            term_t res = yices_not(expr);
            if (res < 0) {
                fprintf(stderr, "Error! Term is less than 0!\n");
            }
            return res;
        }
        term_t YicesSolver::createCondExpr(term_t cond, term_t choice1, term_t choice2) {
            term_t res = yices_ite(cond, choice1, choice2);
            if (res < 0) {
                fprintf(stderr, "Error! Term is less than 0!\n");
            }
            return res;
        }
        term_t YicesSolver::createEqExpr(term_t lhs, term_t rhs) {
            term_t res = yices_eq(lhs, rhs);
            if (res < 0) {
                fprintf(stderr, "Error! Term is less than 0!\n");
            }
            return res;
        }

        void YicesSolver::assert(term_t expr) {
            assertions.push_back(expr);
        }

        void YicesSolver::assertNow(term_t expr) {
            yices_assert_formula(context, expr);
        }        

        SMTResult YicesSolver::solve() {
            smt_status_t res = yices_check_context(context, NULL);

            switch (res) {
                case STATUS_SAT: {
                    // model_t* model = yices_get_model(context, 1);
                    // yices_pp_model(stdout, model, 120, 40, 0);
                    // yices_free_model(model);
                    return SAT;
                    break;
                }
                case STATUS_UNSAT:
                    return UNSAT;
                    break;
                case STATUS_UNKNOWN:
                    return UNKNOWN;
                    break;

                case STATUS_IDLE:
                    fprintf(stderr, "Idle...\n");
                    break;
                case STATUS_SEARCHING:
                case STATUS_INTERRUPTED:
                case STATUS_ERROR:
                    fprintf(stderr, "Error in check_context\n");
                    yices_print_error(stderr);
                    break;
            }
            return ERROR;
        }

        void YicesSolver::printModel() {
            model_t* model = yices_get_model(context, false);
            if (model == NULL) {
                fprintf(stdout, "Model is NULL...\n");
            }
            else {
                yices_pp_model(stdout, model, 120, 40, 0);
                yices_free_model(model);
            }
        }
        
        void YicesSolver::loadToSolver() {
            //TODO: consider using 
            /*
            int count = assertions.size();
            term_t arr = new term_t[count];
            std::copy(assertions.begin(), assertions.end(), arr);
            yices_assert_formulas(context, count, arr);
            delete[] arr;
            */

            if (assertions.empty()) {
                yices_assert_formula(context, yices_true());
            }
            else {
                auto ite = assertions.begin();
                term_t body = *ite;
                for ( ; ite != assertions.end(); ++ite) {
                    body = yices_and2(body, *ite);
                }
                yices_assert_formula(context, body);
                // yices_pp_term(stderr, body, 120, 40, 0);
            }
        }
        void YicesSolver::clean() { }

        void YicesSolver::push() { 
            loadToSolver();
            int res = yices_push(context);
            if (res != 0) {
                fprintf(stderr, "Failed to push yices context!\n");
                throw new std::runtime_error("Failed to push yices context!\n");
            }
            assertions.clear();
        }
        void YicesSolver::pop() { 
            int res = yices_pop(context);
            if (res != 0) {
                fprintf(stderr, "Failed to pop yices context!\n");
                throw new std::runtime_error("Failed to pop yices context!\n");
            }
        }
}