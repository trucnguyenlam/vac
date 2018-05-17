//
// Created by esteffin on 19/07/17.
//

#include "../SMT.h"
#include <mathsat.h>
#include <list>

#ifndef VACSAT_MATHSAT_H
#define VACSAT_MATHSAT_H

namespace SMT {
    class msat_expr_t : public smt_expr_t {
    public:
        const msat_term e;
        explicit msat_expr_t(msat_term expr) : e(expr) { };
//        explicit yices_expr_t(const term_t& expr) : e(expr) { };
//        explicit yices_expr_t(term_t& expr) : e(expr) { };

        Solver get_solver() override { return Solver::MATHSAT; }
    };

    typedef std::shared_ptr<msat_expr_t> MsatExpr;

    class MathsatSolver : public SMTFactory {
    public:
        static inline const std::string solver_name() {
            return "mathsat";
        };

        MathsatSolver();
        ~MathsatSolver();

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
        int exprValueAsInt(const SMTExpr& expr) override;
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
        std::list<msat_term> to_be_asserted;
//        std::list<msat_term> asserted;
        msat_env context;
        msat_model model;

        msat_config mk_config();
        void mathsat_fail(const std::string& error_message);

        void check_msat_error(msat_term term);
    };
}

#endif //VACSAT_MATHSAT_H
