#include <stdexcept>

#include "Solvers.h"

namespace Solvers {

    YicesSolver::YicesSolver(int bv_size) : SMTSolver(bv_size) {
        yices_init();
        ctx = yices_new_context(NULL);
    }
    YicesSolver::~YicesSolver() {
        yices_free_context(ctx);
        yices_exit();
    }
    void YicesSolver::addAssertion(SSA::Expr expr) {
        term_t yexpr = exprToTerm(expr);
        int code = yices_assert_formula(ctx, yexpr);
        if (code < 0) {
            fprintf(stderr, "Assert failed: code = %d, error = %d\n", code, yices_error_code());
            yices_print_error(stderr);
            throw std::runtime_error("CANNOT ASSERT THE EXPRESSION");
        }
    }
    void YicesSolver::declareVariable(SSA::Variablep variable, int add_init_assert) {
        term_t type = yices_bool_type();
        if (variable->bv_size > 1) {
            type = yices_bv_type(variable->bv_size);
        }
        term_t var = yices_new_uninterpreted_term(type);
        yices_set_term_name(var, variable->print().c_str());
        if (variable->value->type != SSA::Exprv::NONDET_EXPR && add_init_assert) {
            term_t val = exprToTerm(variable->value);
            int code = yices_assert_formula(ctx, yices_eq(var, val));
            if (code < 0) {
                fprintf(stderr, "Assert failed: code = %d, error = %d\n", code, yices_error_code());
                yices_print_error(stderr);
                throw std::runtime_error("CANNOT ASSERT THE VALUE OF THE VARIABLE");
            }
        }
    }

    SSA::SMTSolver::Result YicesSolver::getResult() {
        auto res = yices_check_context(ctx, NULL);
        switch (res) {
            case STATUS_SAT:
                return SMTSolver::SAT;
            case STATUS_UNSAT:
                return SMTSolver::UNSAT;
            case STATUS_UNKNOWN:
            case STATUS_IDLE:
            case STATUS_SEARCHING:
            case STATUS_INTERRUPTED:
            case STATUS_ERROR:
                return SMTSolver::UNKNOWN;
        }
    }

    term_t YicesSolver::exprToTerm(SSA::Expr expr) {
        switch (expr->type) {
            case SSA::Exprv::CONSTANT: {
                    auto c = std::dynamic_pointer_cast<SSA::Constant>(expr);
                    if (c->var_type == SSA::BOOL) {
                        if (c->value) {
                            return yices_true();
                        }
                        else {
                            return yices_false();
                        }
                    }
                    return yices_bvconst_uint32(this->bv_size, c->value);
                }
            case SSA::Exprv::VARIABLE: {
                    auto var = std::dynamic_pointer_cast<SSA::Variable>(expr);
                    return yices_get_term_by_name(var->print().c_str());
                }
            case SSA::Exprv::EQ_EXPR: {
                    auto eq = std::dynamic_pointer_cast<SSA::EqExpr>(expr);
                    term_t lhs = exprToTerm(eq->lhs);
                    term_t rhs = exprToTerm(eq->rhs);
                    return yices_eq(lhs, rhs);
                }
            case SSA::Exprv::NOT_EXPR: {
                    auto nexpr = std::dynamic_pointer_cast<SSA::NotExpr>(expr);
                    term_t nin = exprToTerm(nexpr->expr);
                    return yices_not(nin);
                }
            case SSA::Exprv::OR_EXPR: {
                    auto orexpr = std::dynamic_pointer_cast<SSA::OrExpr>(expr);
                    term_t lhs = exprToTerm(orexpr->lhs);
                    term_t rhs = exprToTerm(orexpr->rhs);
                    return yices_or2(lhs, rhs);
                }
            case SSA::Exprv::AND_EXPR: {
                    auto andexpr = std::dynamic_pointer_cast<SSA::AndExpr>(expr);
                    term_t lhs = exprToTerm(andexpr->lhs);
                    term_t rhs = exprToTerm(andexpr->rhs);
                    return yices_and2(lhs, rhs);
                }
            case SSA::Exprv::COND_EXPR: {
                    auto itexpr = std::dynamic_pointer_cast<SSA::CondExpr>(expr);
                    term_t t_cond = exprToTerm(itexpr->cond);
                    term_t t_choice1 = exprToTerm(itexpr->choice1);
                    term_t t_choice2 = exprToTerm(itexpr->choice2);
                    return yices_ite(t_cond, t_choice1, t_choice2);
                }
            case SSA::Exprv::NONDET_EXPR: {
                    throw std::runtime_error("CANNOT PRINT A NONDET EXPRESSION IN SMT");
                }
        }
    }
}