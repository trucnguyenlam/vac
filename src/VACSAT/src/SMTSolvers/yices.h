#ifndef YICES_H
#define YICES_H

#include "../SMT.h"
#include <yices.h>
#include <list>

namespace SMT {
    class YicesSolver : public SMTFactory<term_t, term_t> {
        public:
        static inline const std::string solver_name() {
            return "yices";
        };

        YicesSolver();
        ~YicesSolver();

        // term_t createBoolType() override;
        // term_t createBVType(int size) override;

        term_t createVar2(const std::string name, int size) override;
        term_t createBoolVar(const std::string name) override;
        term_t createBVVar(const std::string name, int size) override;

        term_t createBVConst(int value, int size) override;
        term_t createBoolConst(int value) override;
        term_t createTrue() override;
        term_t createFalse() override;
        term_t createOrExpr(term_t lhs, term_t rhs) override;
        term_t createAndExpr(term_t lhs, term_t rhs) override;
        term_t createNotExpr(term_t expr) override;
        term_t createCondExpr(term_t cond, term_t choice1, term_t choice2) override;
        term_t createEqExpr(term_t lhs, term_t rhs) override;
        term_t createGtExpr(term_t lhs, term_t rhs) override;
        term_t createGEqExpr(term_t lhs, term_t rhs) override;
        term_t createLtExpr(term_t lhs, term_t rhs) override;
        term_t createLEqExpr(term_t lhs, term_t rhs) override;
        term_t createImplExpr(term_t lhs, term_t rhs) override;

        term_t createBitSet(term_t container, unsigned int ith, term_t value) override;
        term_t createDistinct(std::list<term_t> exprs) override;

        term_t joinExprsWithAnd(std::list<term_t>& exprs) override;
        term_t joinExprsWithOr(std::list<term_t>& exprs) override;

        void assertLater(term_t expr) override;
        void assertNow(term_t expr) override;

        SMTResult solve() override;
        void printExpr(term_t expr) override;
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
        std::list<term_t> to_be_asserted;
        std::list<term_t> asserted;
        context_t* context;
    };
}

#endif