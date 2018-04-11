//
// Created by esteffin on 3/16/18.
//

#include "cvc4.h"
#include "../config.h"
#include "../prelude.h"

namespace SMT {
#define cto_e(expr) std::make_shared<cvc4_expr_t>(cvc4_expr_t(expr))

    inline CVC4::Expr eto_c(const SMTExpr &expr) {
#ifdef NDEBUG
        return std::static_pointer_cast<cvc4_expr_t>(expr)->e;
#else
        Cvc4Expr e = std::dynamic_pointer_cast<cvc4_expr_t>(expr);
        if (e == nullptr) {
            throw unexpected("Operand is of the wrong type");
        }
        return e->e;
#endif
    }

    void Cvc4Solver::mk_config() {
        solver.setLogic("QF_BV");                       // Set the logic
        solver.setOption("produce-models", true);       // Produce Models
        solver.setOption("output-language", "smtlib2"); // output-language

    }

    Cvc4Solver::Cvc4Solver() :
            SMTFactory(Solver::CVC4),
            solver(&exprManager) {
        mk_config();
    }

    Cvc4Solver::~Cvc4Solver() {
        deep_clean();
    }

    static unsigned int var_counter = 0;

    SMTExpr Cvc4Solver::createBoolVar(const std::string name) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        CVC4::Type sort = exprManager.booleanType();
        CVC4::Expr ret = exprManager.mkVar(enum_name, sort);
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createBVVar(const std::string name, int size) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        CVC4::Type sort = exprManager.mkBitVectorType((uint) size);
        CVC4::Expr ret = exprManager.mkVar(enum_name, sort);
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createVar2(const std::string name, int size) {
        return size == 1 ? createBoolVar(name) : createBVVar(name, size);
    }

    SMTExpr Cvc4Solver::createBVConst(int value, int size) {
        CVC4::Expr ret = exprManager.mkConst(CVC4::BitVector((uint) size, (uint) value));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createTrue() {
        CVC4::Expr ret = exprManager.mkConst(true);
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createFalse() {
        CVC4::Expr ret = exprManager.mkConst(false);
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createBoolConst(int value) {
        return value ? createTrue() : createFalse();
    }

    SMTExpr Cvc4Solver::createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::OR, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::XOR, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::AND, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createNotExpr(const SMTExpr& expr) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::NOT, eto_c(expr));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::ITE, eto_c(cond), eto_c(choice1), eto_c(choice2));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::EQUAL, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::BITVECTOR_UGT, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::BITVECTOR_UGE, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::BITVECTOR_ULT, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::BITVECTOR_ULE, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        CVC4::Expr ret = exprManager.mkExpr(CVC4::kind::IMPLIES, eto_c(lhs), eto_c(rhs));
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) {
//        SMTExpr bit = cto_e(exprManager.mkExpr(CVC4::kind::BITVECTOR_EXTRACT, eto_c(container), ith, ith));
////            log->info("bit: {}; value: {}", bit.get_sort(), bit);
//        SMTExpr b0 = createBVConst(0, 1);
//        SMTExpr b1 = createBVConst(1, 1);
//
//        SMTExpr bv_value = createCondExpr(value,
//                                          b0,
//                                          b1);
////            log->info("bv_value: {}; value: {}", bv_value.get_sort(), bv_value);
//        SMTExpr res = createEqExpr(bit, bv_value);
////            log->info("res: {}; value: {}", res.get_sort(), res);
//        return res;
        log->error("CVC4 does not support createBitSet yet");
        throw std::runtime_error("CVC4 does not support createBitSet yet");
    }

    SMTExpr Cvc4Solver::createDistinct(std::list<SMTExpr>& exprs) {
        log->error("CVC4 does not support distinct yet");
        throw std::runtime_error("CVC4 does not support distinct yet");
    }

    SMTExpr Cvc4Solver::joinExprsWithAnd(std::list<SMTExpr> &exprs) {
        if (exprs.empty()) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        CVC4::Expr ret = eto_c(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = exprManager.mkExpr(CVC4::kind::AND, ret, eto_c(*ite));
        }
        return cto_e(ret);
    }

    SMTExpr Cvc4Solver::joinExprsWithOr(std::list<SMTExpr> &exprs) {
        if (exprs.empty()) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        CVC4::Expr ret = eto_c(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = exprManager.mkExpr(CVC4::kind::OR, ret, eto_c(*ite));
        }
        return cto_e(ret);
    }

    void Cvc4Solver::assertLater(const SMTExpr& expr) {
        to_be_asserted.push_back(eto_c(expr));
    }

    void Cvc4Solver::assertNow(const SMTExpr& expr) {
        solver.assertFormula(eto_c(expr));
    }

    SMTResult Cvc4Solver::solve() {
//        log->warn(++i);
//        if (i == 80) {
//            log->warn("Break");
//        }
        this->loadToSolver();
        CVC4::Result cvc4_res = solver.checkSat();
        if (cvc4_res.isSat()) {
            return SMTResult::SAT;
        } else if (!cvc4_res.isSat()) {
            return SMTResult::UNSAT;
        } else {
            log->error("UNKNOWN CVC4 result");
            throw std::runtime_error("UNKNOWN CVC4 result");
        }
    }

    void Cvc4Solver::printExpr(const SMTExpr& expr) {
        std::cout << eto_c(expr) << std::endl;
    }

    void Cvc4Solver::printModel() {
        std::cout << solver.getAssignment() << std::endl;
    }

    bool Cvc4Solver::get_bool_value(const SMTExpr& expr) {
        CVC4::Expr e = solver.getValue(eto_c(expr));
        if (e.isConst()) {
            bool res = e.getConst<bool>();
            return res;
        } else {
            throw std::runtime_error("Cannot get a non const value");
        }
    }

    void Cvc4Solver::print_statistics() {
        CVC4::Statistics stats = solver.getStatistics();
        for (auto &&stat : stats) {
            std::cout << stat.first << ": " << stat.second << std::endl;
        }
    }

    void Cvc4Solver::loadToSolver() {
        if (to_be_asserted.empty()) {
            return;
        }
        else {
            auto ite = to_be_asserted.begin();
            CVC4::Expr body = *ite;
//            asserted.push_back(body);
            for (++ite; ite != to_be_asserted.end(); ++ite) {
                body = exprManager.mkExpr(CVC4::kind::AND, body, *ite);
//                asserted.push_back(body);
            }
            solver.assertFormula(body);
            // yices_pp_term(stderr, body, 120, 40, 0);
            this->to_be_asserted.clear();
        }
    }

    void Cvc4Solver::clean() {
        to_be_asserted.clear();
        solver.resetAssertions();
    }

    void Cvc4Solver::deep_clean() {
        var_counter = 0;
        to_be_asserted.clear();
        solver.resetAssertions();
        solver.reset();
        mk_config();
    }

    void Cvc4Solver::printContext() {
        for (auto &&assertion : solver.getAssertions()) {
            std::cout << assertion << std::endl;
        }
    }

    void Cvc4Solver::printContext(std::string filename) {
        std::fstream out(filename);
        for (auto &&assertion : solver.getAssertions()) {
            out << assertion << std::endl;
        }
        out.close();
    }

    void Cvc4Solver::extract_model() { }

}