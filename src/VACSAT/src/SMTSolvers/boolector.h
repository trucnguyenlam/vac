//
// Created by esteffin on 17/07/17.
//

#ifndef VACSAT_BOOLECTOR_H
#define VACSAT_BOOLECTOR_H

#include "../SMT.h"
#include <vector>
extern "C" {
    #include <boolector.h>
};

namespace SMT {
    typedef BoolectorNode* BoolectorExpr;
    class BoolectorSolver : public SMTFactory<BoolectorExpr, BoolectorExpr> {
    public:
        static inline const std::string solver_name() {
            return "boolector";
        };

        BoolectorSolver();
        ~BoolectorSolver();

        // term_t createBoolType() override;
        // term_t createBVType(int size) override;

        BoolectorExpr createVar2(const std::string name, int size) override;
        BoolectorExpr createBoolVar(const std::string name) override;
        BoolectorExpr createBVVar(const std::string name, int size) override;

        BoolectorExpr createBVConst(int value, int size) override;
        BoolectorExpr createBoolConst(int value) override;
        BoolectorExpr createTrue() override;
        BoolectorExpr createFalse() override;
        BoolectorExpr createOrExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createXorExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createAndExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createNotExpr(BoolectorExpr expr) override;
        BoolectorExpr createCondExpr(BoolectorExpr cond, BoolectorExpr choice1, BoolectorExpr choice2) override;
        BoolectorExpr createEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createGtExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createGEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createLtExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createLEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;
        BoolectorExpr createImplExpr(BoolectorExpr lhs, BoolectorExpr rhs) override;

        BoolectorExpr createBitSet(BoolectorExpr container, unsigned int ith, BoolectorExpr value) override;
        BoolectorExpr createDistinct(std::list<BoolectorExpr> exprs) override;

        BoolectorExpr joinExprsWithAnd(std::list<BoolectorExpr>& exprs) override;
        BoolectorExpr joinExprsWithOr(std::list<BoolectorExpr>& exprs) override;

        void assertLater(BoolectorExpr expr) override;
        void assertNow(BoolectorExpr expr) override;

        SMTResult solve() override;
        void printExpr(BoolectorExpr expr) override;
        void printModel() override;
        bool get_bool_value(BoolectorExpr expr) override;
        void print_statistics() override;
        void loadToSolver() override;
        void clean() override;
        void deep_clean() override;
        void printContext() override;
        void printContext(std::string filename) override;

        // void push() override;
        // void pop() override;

    private:
        void mk_config();
        std::list<BoolectorExpr> to_be_asserted;
//        std::list<BoolectorExpr> asserted;
        Btor* context;
    };
}

#endif //VACSAT_BOOLECTOR_H
