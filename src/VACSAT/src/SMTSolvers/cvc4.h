//
// Created by esteffin on 3/16/18.
//

#ifndef VACSAT_CVC4_H
#define VACSAT_CVC4_H

#include "../SMT.h"
#include <vector>
#include <cvc4/cvc4.h>

namespace SMT {

    class cvc4_expr_t : public smt_expr_t {
    public:
        const CVC4::Expr e;
        explicit cvc4_expr_t(CVC4::Expr expr) : e(expr) { };
//        explicit yices_expr_t(const term_t& expr) : e(expr) { };
//        explicit yices_expr_t(term_t& expr) : e(expr) { };

        Solver get_solver() override { return Solver::CVC4; }
    };

    typedef std::shared_ptr<cvc4_expr_t> Cvc4Expr;

    class Cvc4Solver : public SMTFactory {
    public:
        static inline const std::string solver_name() {
            return "cvc4";
        };

        Cvc4Solver();
        ~Cvc4Solver();

        // term_t createBoolType() override;
        // term_t createBVType(int size) override;

        SMTExpr createVar2(const std::string name, int size) override;
        SMTExpr createBoolVar(const std::string name) override;
        SMTExpr createBVVar(const std::string name, int size) override;

        SMTExpr createBVConst(int value, int size) override;
        SMTExpr createBoolConst(bool value) override;
        SMTExpr createTrue() override;
        SMTExpr createFalse() override;
        SMTExpr createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createNotExpr(const SMTExpr& expr) override;
        SMTExpr createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) override;
        SMTExpr createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;

        SMTExpr createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) override;
        SMTExpr createDistinct(std::list<SMTExpr>& exprs) override;

        SMTExpr joinExprsWithAnd(std::list<SMTExpr>& exprs) override;
        SMTExpr joinExprsWithOr(std::list<SMTExpr>& exprs) override;

        void assertLater(const SMTExpr& expr) override;
        void assertNow(const SMTExpr& expr) override;

        SMTResult solve() override;
        void printExpr(const SMTExpr& expr) override;
        std::string exprValueAsString(const SMTExpr& expr) override;
        void printModel() override;
        bool get_bool_value(const SMTExpr& expr) override;
        void print_statistics() override;
        void loadToSolver() override;
        void clean() override;
        void deep_clean() override;
        void printContext() override;
        void printContext(std::string filename) override;

        // void push() override;
        // void pop() override;

    private:
        std::list<CVC4::Expr> to_be_asserted;
        CVC4::ExprManager exprManager;
        CVC4::SmtEngine solver;
        std::shared_ptr<CVC4::Model> model;

        void mk_config();
        void extract_model();
    };
}
#endif //VACSAT_CVC4_H
