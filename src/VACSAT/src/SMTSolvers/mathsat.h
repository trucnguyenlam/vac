//
// Created by esteffin on 19/07/17.
//

#include "../SMT.h"
#include <mathsat.h>
#include <list>

#ifndef VACSAT_MATHSAT_H
#define VACSAT_MATHSAT_H

namespace SMT {
    class MathsatSolver : public SMTFactory<msat_term, msat_term> {
    public:
        static inline const std::string solver_name() {
            return "mathsat";
        };

        MathsatSolver();
        ~MathsatSolver();

        // term_t createBoolType() override;
        // term_t createBVType(int size) override;

        msat_term createVar2(const std::string name, int size) override;
        msat_term createBoolVar(const std::string name) override;
        msat_term createBVVar(const std::string name, int size) override;

        msat_term createBVConst(int value, int size) override;
        msat_term createBoolConst(int value) override;
        msat_term createTrue() override;
        msat_term createFalse() override;
        msat_term createOrExpr(msat_term lhs, msat_term rhs) override;
        msat_term createXorExpr(msat_term lhs, msat_term rhs) override;
        msat_term createAndExpr(msat_term lhs, msat_term rhs) override;
        msat_term createNotExpr(msat_term expr) override;
        msat_term createCondExpr(msat_term cond, msat_term choice1, msat_term choice2) override;
        msat_term createEqExpr(msat_term lhs, msat_term rhs) override;
        msat_term createGtExpr(msat_term lhs, msat_term rhs) override;
        msat_term createGEqExpr(msat_term lhs, msat_term rhs) override;
        msat_term createLtExpr(msat_term lhs, msat_term rhs) override;
        msat_term createLEqExpr(msat_term lhs, msat_term rhs) override;
        msat_term createImplExpr(msat_term lhs, msat_term rhs) override;

        msat_term createBitSet(msat_term container, unsigned int ith, msat_term value) override;
        msat_term createDistinct(std::list<msat_term> exprs) override;

        msat_term joinExprsWithAnd(std::list<msat_term>& exprs) override;
        msat_term joinExprsWithOr(std::list<msat_term>& exprs) override;

        void assertLater(msat_term expr) override;
        void assertNow(msat_term expr) override;

        SMTResult solve() override;
        void printExpr(msat_term expr) override;
        void printModel() override;
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
        std::list<msat_term> asserted;
        msat_env context;

        msat_config mk_config();
        void mathsat_fail(const std::string& error_message);

        void check_msat_error(msat_term term);
    };
}

#endif //VACSAT_MATHSAT_H
