#ifndef Z3_H
#define Z3_H

#include "../SMT.h"
#include <memory>
#include <vector>
#include <z3++.h>

namespace SMT {
    using namespace z3;

    // class Z3Expr {
    //     std::shared_ptr<>
    // }
    class Z3Solver : public SMTFactory<expr, expr> {
        public:
        Z3Solver();
        ~Z3Solver();

        // sort createBoolType() override;
        // sort createBVType(int size) override;

        expr createVar2(const std::string name, int size) override;
        expr createBoolVar(const std::string name) override;
        expr createBVVar(const std::string name, int size) override;

        expr createBVConst(int value, int size) override;
        expr createBoolConst(int value) override;
        expr createTrue() override;
        expr createFalse() override;
        expr createOrExpr(expr lhs, expr rhs) override;
        expr createAndExpr(expr lhs, expr rhs) override;
        expr createNotExpr(expr _expr) override;
        expr createCondExpr(expr cond, expr choice1, expr choice2) override;
        expr createEqExpr(expr lhs, expr rhs) override;
        expr createImplExpr(expr lhs, expr rhs) override;

        void assertLater(expr e) override;
        void assertNow(expr e) override;

        SMTResult solve() override;
        void printModel() override;
        void loadToSolver() override;
        void clean() override;
        void printContext() override;
        
        // void push() override;
        // void pop() override;

        private:
        z3::context context;
        z3::solver solver;
    };
}

#endif