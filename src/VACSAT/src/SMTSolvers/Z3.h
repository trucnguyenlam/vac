#ifndef Z3_H
#define Z3_H

#include "../SMT.h"
#include <memory>
#include <vector>
#include <z3++.h>

namespace SMT {
    using namespace z3;

    class z3_expr_t : public smt_expr_t {
    public:
        const z3::expr e;
        explicit z3_expr_t(z3::expr expr) : e(std::move(expr)) { };
//        explicit z3_expr_t(const z3::expr& expr) : e(expr) { };
//        explicit z3_expr_t(z3::expr& expr) : e(expr) { };

        Solver get_solver() override { return Solver::Z3; }
    };

    typedef std::shared_ptr<z3_expr_t> Z3Expr;

    class Z3Solver : public SMTFactory {
        public:
        static inline const std::string solver_name() {
            return "Z3";
        };
        static inline const std::string fast_solver_name() {
            return "Z3Fast";
        };
//        static std::shared_ptr<z3::config> config;

        explicit Z3Solver(bool _fast);
        ~Z3Solver();

        // sort createBoolType() override;
        // sort createBVType(int size) override;

        SMTExpr createVar2(const std::string name, int size) override;
        SMTExpr createBoolVar(const std::string name) override;
        SMTExpr createBVVar(const std::string name, int size) override;

        SMTExpr createBVConst(int value, int size) override;
        SMTExpr createBoolConst(int value) override;
        SMTExpr createTrue() override;
        SMTExpr createFalse() override;
        SMTExpr createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) override;
        SMTExpr createNotExpr(const SMTExpr& _expr) override;
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

        void assertLater(const SMTExpr& e) override;
        void assertNow(const SMTExpr& e) override;

        SMTResult solve() override;
        void printModel() override;
        bool get_bool_value(const SMTExpr& expr) override;
//        unsigned int get_bv_value(expr expr) override;
        void print_statistics() override;
        void loadToSolver() override;
        void clean() override;
        void deep_clean() override;

        void printExpr(const SMTExpr& e) override;
        void printContext() override;
        void printContext(std::string filename) override;

        
        // void push() override;
        // void pop() override;

        private:
        z3::config cfg;
        z3::context context;
        z3::solver solver;
        std::shared_ptr<z3::model> model;
        bool fast;
        std::vector<z3::expr> to_be_asserted;

        void extract_model();
    };
}

#endif