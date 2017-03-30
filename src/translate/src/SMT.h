#pragma once

#include <string>
#include <set>
#include <memory>

namespace SMT {
    enum SMTResult {
        SAT,
        UNSAT,
        UNKNOWN,
        ERROR
    };

    class AvailableSolvers {
        public:
        enum Solver {
            YICES
        };
    };

    template <typename TVar, typename TExpr>
    class SMTFactory {
        public:

        // virtual TType createBoolType() = 0;
        // virtual TType createBVType(int size) = 0;
        
        virtual TVar createVar2(const std::string name, int size) = 0;
        virtual TVar createBoolVar(const std::string name) = 0;
        virtual TVar createBVVar(const std::string name, int bv_size) = 0;

        virtual TExpr createBVConst(int value, int size) = 0;
        virtual TExpr createBoolConst(int value) = 0;
        virtual TExpr createTrue() = 0;
        virtual TExpr createFalse() = 0;
        virtual TExpr createOrExpr(TExpr lhs, TExpr rhs) = 0;
        virtual TExpr createAndExpr(TExpr lhs, TExpr rhs) = 0;
        virtual TExpr createNotExpr(TExpr expr) = 0;
        virtual TExpr createCondExpr(TExpr cond, TExpr choice1, TExpr choice2) = 0;
        virtual TExpr createEqExpr(TExpr lhs, TExpr rhs) = 0;
        virtual TExpr createImplExpr(TExpr lhs, TExpr rhs) = 0;

        virtual void assert(TExpr expr) = 0;
        virtual void assertNow(TExpr expr) = 0;
        virtual SMTResult solve() = 0;
        virtual void printModel() = 0;

        virtual void loadToSolver() = 0;
        virtual void clean() = 0;

        // virtual void push() = 0;
        // virtual void pop() = 0;
    };

}