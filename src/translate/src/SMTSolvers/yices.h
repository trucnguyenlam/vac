#ifndef YICES_H
#define YICES_H

#include "../SMT.h"
#include <yices.h>
#include <vector>

namespace SMT {
    class YicesSolver : public SMTFactory<term_t, term_t, term_t> {
        public:
        YicesSolver();
        ~YicesSolver();

        term_t createBoolType() override;
        term_t createBVType(int size) override;

        term_t createVar(const std::string name, term_t type) override;

        term_t createBVConst(int value, int size) override;
        term_t createBoolConst(int value) override;
        term_t createOrExpr(term_t lhs, term_t rhs) override;
        term_t createAndExpr(term_t lhs, term_t rhs) override;
        term_t createNotExpr(term_t expr) override;
        term_t createCondExpr(term_t cond, term_t choice1, term_t choice2) override;
        term_t createEqExpr(term_t lhs, term_t rhs) override;
        term_t createImplExpr(term_t lhs, term_t rhs) override;

        void assert(term_t expr) override;
        void assertNow(term_t expr) override;

        SMTResult solve() override;
        void printModel() override;
        void loadToSolver() override;
        void clean() override;
        
        void push() override;
        void pop() override;

        private:
        std::vector<term_t> assertions;
        context_t* context;
    };
}

#endif