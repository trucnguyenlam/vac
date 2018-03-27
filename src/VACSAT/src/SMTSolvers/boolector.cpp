//
// Created by esteffin on 17/07/17.
//

#include "boolector.h"
#include "../config.h"
#include "../prelude.h"

namespace SMT {
    #define bto_e(expr) std::make_shared<btor_expr_t>(btor_expr_t(expr))

    inline BoolectorExpr eto_b(const SMTExpr &expr) {
#ifdef NDEBUG
        return std::static_pointer_cast<btor_expr_t>(expr)->e;
#else
        BtorExpr e = std::dynamic_pointer_cast<btor_expr_t>(expr);
        if (e == nullptr) {
            throw unexpected("Operand is of the wrong type");
        }
        return e->e;
#endif
    }

    void BoolectorSolver::mk_config() {
#ifdef NDEBUG
#else
//        log->warn("Mk config!");
//        log->warn("enabling model generation for boolector");
#endif
//        boolector_set_opt(this->context, BTOR_OPT_MODEL_GEN, 1);
//        boolector_set_opt(this->context, BTOR_OPT_ENGINE, 2);
//        // Simplifier options
//        boolector_set_opt(this->context, BTOR_OPT_REWRITE_LEVEL, 1);
//        boolector_set_opt(this->context, BTOR_OPT_SKELETON_PREPROC, 1);
//        boolector_set_opt(this->context, BTOR_OPT_ACKERMANN, 0);
//        boolector_set_opt(this->context, BTOR_OPT_BETA_REDUCE_ALL, 0);
//        boolector_set_opt(this->context, BTOR_OPT_ELIMINATE_SLICES, 1);
//        boolector_set_opt(this->context, BTOR_OPT_VAR_SUBST, 1);
//        boolector_set_opt(this->context, BTOR_OPT_UCOPT, 1);
//        boolector_set_opt(this->context, BTOR_OPT_MERGE_LAMBDAS, 0);
//        boolector_set_opt(this->context, BTOR_OPT_EXTRACT_LAMBDAS, 0);
//        boolector_set_opt(this->context, BTOR_OPT_NORMALIZE_ADD, 0);
//
//
//        boolector_set_opt(this->context, BTOR_OPT_AUTO_CLEANUP, 1);

        boolector_set_opt(this->context, BTOR_OPT_MODEL_GEN, 1);
        boolector_set_opt(this->context, BTOR_OPT_AUTO_CLEANUP, 1);

    }

    BoolectorSolver::BoolectorSolver() :
            SMTFactory(Solver::BOOLECTOR),
            context(boolector_new()) {
        mk_config();
    }

    BoolectorSolver::~BoolectorSolver() {
        if (context != nullptr) {
            boolector_delete(context);
            context = nullptr;
        }
    }

    static unsigned int var_counter = 0;

    SMTExpr BoolectorSolver::createBoolVar(const std::string name) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        BoolectorSort sort = boolector_bool_sort(context);
        BoolectorExpr ret = boolector_var(context, sort, enum_name.c_str());
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createBVVar(const std::string name, int size) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        BoolectorSort sort = boolector_bitvec_sort(context, size);
        BoolectorExpr ret = boolector_var(context, sort, enum_name.c_str());
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createVar2(const std::string name, int size) {
        return size == 1 ? createBoolVar(name) : createBVVar(name, size);
    }

    SMTExpr BoolectorSolver::createBVConst(int value, int size) {
        BoolectorSort sort = boolector_bitvec_sort(context, size);
        BoolectorExpr ret = boolector_unsigned_int(context, (uint) value, sort);
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createTrue() {
        BoolectorExpr ret = boolector_true(context);
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createFalse() {
        BoolectorExpr ret = boolector_false(context);
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createBoolConst(int value) {
        return value ? createTrue() : createFalse();
    }

    SMTExpr BoolectorSolver::createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_or(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_xor(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_and(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createNotExpr(const SMTExpr& expr) {
        BoolectorExpr ret = boolector_not(context, eto_b(expr));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) {
        BoolectorExpr ret = boolector_cond(context, eto_b(cond), eto_b(choice1), eto_b(choice2));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_eq(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_ugt(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_ugte(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_ult(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_ulte(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        BoolectorExpr ret = boolector_implies(context, eto_b(lhs), eto_b(rhs));
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) {
        SMTExpr bit = bto_e(boolector_slice(context, eto_b(container), ith, ith));
//            log->info("bit: {}; value: {}", bit.get_sort(), bit);
        SMTExpr b0 = createBVConst(0, 1);
        SMTExpr b1 = createBVConst(1, 1);

        SMTExpr bv_value = createCondExpr(value,
                                                b0,
                                                b1);
//            log->info("bv_value: {}; value: {}", bv_value.get_sort(), bv_value);
        SMTExpr res = createEqExpr(bit, bv_value);
//            log->info("res: {}; value: {}", res.get_sort(), res);
        return res;
    }

    SMTExpr BoolectorSolver::createDistinct(std::list<SMTExpr>& exprs) {
        log->error("Boolector does not support distinct yet");
        throw std::runtime_error("Boolector does not support distinct yet");
    }

    SMTExpr BoolectorSolver::joinExprsWithAnd(std::list<SMTExpr> &exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        BoolectorExpr ret = eto_b(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = boolector_and(context, ret, eto_b(*ite));
        }
        return bto_e(ret);
    }

    SMTExpr BoolectorSolver::joinExprsWithOr(std::list<SMTExpr> &exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        BoolectorExpr ret = eto_b(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = boolector_or(context, ret, eto_b(*ite));
        }
        return bto_e(ret);
    }

    void BoolectorSolver::assertLater(const SMTExpr& expr) {
        to_be_asserted.push_back(eto_b(expr));
    }

    void BoolectorSolver::assertNow(const SMTExpr& expr) {
        boolector_assert(context, eto_b(expr));
    }
    static int i = 0;
    SMTResult BoolectorSolver::solve() {
//        log->warn(++i);
//        if (i == 80) {
//            log->warn("Break");
//        }
        this->loadToSolver();
        int boolector_res = boolector_sat(context);
        if (boolector_res == BOOLECTOR_SAT) {
            return SMTResult::SAT;
        } else if (boolector_res == BOOLECTOR_UNSAT) {
            return SMTResult::UNSAT;
        } else {
            log->error("UNKNOWN Boolector result");
            throw std::runtime_error("UNKNOWN Boolector result");
        }
    }

    void BoolectorSolver::printExpr(const SMTExpr& expr) {
        boolector_dump_smt2_node(context, stdout, eto_b(expr));
    }

    void BoolectorSolver::printModel() {
        boolector_print_model(context, "smt2", stdout);
    }

    bool BoolectorSolver::get_bool_value(const SMTExpr& expr) {
        const char *result = boolector_bv_assignment(this->context, eto_b(expr));

        bool res;

        if (result != nullptr) {
            throw std::runtime_error("Boolector returned null bv assignment string");
        }

        switch (*result) {
            case '1':
                res = true;
                break;
            case '0':
                res = false;
                break;
            case 'x':
                log->critical("Boolector bv model string \"{}\" is unknown", result);
                throw std::runtime_error("Boolector bv model string is unknown");
                break;
            default:
                log->critical("Boolector bv model string \"{}\" not of the expected format", result);
                throw std::runtime_error("Boolector bv model string not of the expected format");
        }

        boolector_free_bv_assignment(this->context, result);
        return res;
    }

    void BoolectorSolver::print_statistics() {
        boolector_print_stats(context);
    }

    void BoolectorSolver::loadToSolver() {
        if (to_be_asserted.empty()) {
            return;
        }
        else {
            auto ite = to_be_asserted.begin();
            BoolectorExpr body = *ite;
//            asserted.push_back(body);
            for (++ite; ite != to_be_asserted.end(); ++ite) {
                body = boolector_and(context, body, *ite);
//                asserted.push_back(body);
            }
            boolector_assert(context, body);
            // yices_pp_term(stderr, body, 120, 40, 0);
            this->to_be_asserted.clear();
        }
    }

    void BoolectorSolver::clean() {
        boolector_delete(context);
        context = boolector_new();
        mk_config();
    }

    void BoolectorSolver::deep_clean() {
        boolector_delete(context);
        context = boolector_new();
        mk_config();
    }

    void BoolectorSolver::printContext() {
        boolector_dump_smt2(context, stdout);
    }

    void BoolectorSolver::printContext(std::string filename) {
        FILE* out = fopen(filename.c_str(), "w");
        boolector_dump_smt2(context, out);
        fclose(out);
    }

}