//
// Created by esteffin on 24/04/17.
//

#ifndef VACSAT_SMT_H
#define VACSAT_SMT_H

#include <string>
#include <set>
#include <memory>
#include <vector>
#include <list>

namespace SMT {
    enum class SMTResult {
        SAT,
        UNSAT,
        UNKNOWN,
        ERROR
    };

    enum class Solver {
        YICES,
        Z3,
        MATHSAT,
        BOOLECTOR
    };

    class smt_expr_t {
    public:
        virtual Solver get_solver() = 0;
    };

    typedef std::shared_ptr<smt_expr_t> SMTExpr;

    class SMTFactory {
        public:

        // virtual TType createBoolType() = 0;
        // virtual TType createBVType(int size) = 0;

        virtual SMTExpr createVar2(const std::string name, int size) = 0;
        virtual SMTExpr createBoolVar(const std::string name) = 0;
        virtual SMTExpr createBVVar(const std::string name, int bv_size) = 0;

        virtual SMTExpr createBVConst(int value, int size) = 0;
        virtual SMTExpr createBoolConst(int value) = 0;
        virtual SMTExpr createTrue() = 0;
        virtual SMTExpr createFalse() = 0;
        virtual SMTExpr createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createNotExpr(const SMTExpr& expr) = 0;
        virtual SMTExpr createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) = 0;
        virtual SMTExpr createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) = 0;
        virtual SMTExpr createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) = 0;
        virtual SMTExpr createDistinct(std::list<SMTExpr>& exprs) = 0;

        virtual SMTExpr joinExprsWithAnd(std::list<SMTExpr>& exprs) = 0;
        virtual SMTExpr joinExprsWithOr(std::list<SMTExpr>& exprs) = 0;

        virtual void assertLater(const SMTExpr& expr) = 0;
        virtual void assertNow(const SMTExpr& expr) = 0;
        virtual SMTResult solve() = 0;
        virtual void printExpr(const SMTExpr& expr) = 0;
        virtual void printModel() = 0;
        virtual void print_statistics() = 0;
        virtual bool get_bool_value(const SMTExpr& expr) = 0;
//        virtual bool get_bv_value(TExpr expr) = 0;

        virtual void loadToSolver() = 0;
        virtual void clean() = 0;
        virtual void deep_clean() = 0;
        virtual void printContext() = 0;
        virtual void printContext(std::string filename) = 0;

        SMTFactory() = delete;
        SMTFactory(Solver _solver_name) : solver_name(_solver_name) { }

        const Solver solver_name;

        // virtual void push() = 0;
        // virtual void pop() = 0;
    };

}

#endif //VACSAT_SMT_H