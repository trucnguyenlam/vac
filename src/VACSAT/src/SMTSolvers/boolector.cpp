//
// Created by esteffin on 17/07/17.
//

#include "boolector.h"
#include "../config.h"

namespace SMT {

    void BoolectorSolver::mk_config() {
#ifdef NDEBUG
#else
//        log->warn("Mk config!");
//        log->warn("enabling model generation for boolector");
#endif
        boolector_set_opt(this->context, BTOR_OPT_MODEL_GEN, 0);
        boolector_set_opt(this->context, BTOR_OPT_ENGINE, 2);
        // Simplifier options
        boolector_set_opt(this->context, BTOR_OPT_REWRITE_LEVEL, 1);
        boolector_set_opt(this->context, BTOR_OPT_SKELETON_PREPROC, 1);
        boolector_set_opt(this->context, BTOR_OPT_ACKERMANN, 0);
        boolector_set_opt(this->context, BTOR_OPT_BETA_REDUCE_ALL, 0);
        boolector_set_opt(this->context, BTOR_OPT_ELIMINATE_SLICES, 1);
        boolector_set_opt(this->context, BTOR_OPT_VAR_SUBST, 1);
        boolector_set_opt(this->context, BTOR_OPT_UCOPT, 1);
        boolector_set_opt(this->context, BTOR_OPT_MERGE_LAMBDAS, 0);
        boolector_set_opt(this->context, BTOR_OPT_EXTRACT_LAMBDAS, 0);
        boolector_set_opt(this->context, BTOR_OPT_NORMALIZE_ADD, 0);


        boolector_set_opt(this->context, BTOR_OPT_AUTO_CLEANUP, 1);
    }

    BoolectorSolver::BoolectorSolver() : context(boolector_new()) {
        mk_config();
    }

    BoolectorSolver::~BoolectorSolver() {
        if (context != nullptr) {
            boolector_delete(context);
            context = nullptr;
        }
    }

    static unsigned int var_counter = 0;

    BoolectorExpr BoolectorSolver::createBoolVar(const std::string name) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        BoolectorSort sort = boolector_bool_sort(context);
        BoolectorExpr ret = boolector_var(context, sort, enum_name.c_str());
        return ret;
    }

    BoolectorExpr BoolectorSolver::createBVVar(const std::string name, int size) {
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        BoolectorSort sort = boolector_bitvec_sort(context, size);
        BoolectorExpr ret = boolector_var(context, sort, enum_name.c_str());
        return ret;
    }

    BoolectorExpr BoolectorSolver::createVar2(const std::string name, int size) {
        return size == 1 ? createBoolVar(name) : createBVVar(name, size);
    }

    BoolectorExpr BoolectorSolver::createBVConst(int value, int size) {
        BoolectorSort sort = boolector_bitvec_sort(context, size);
        BoolectorExpr ret = boolector_unsigned_int(context, (uint) value, sort);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createTrue() {
        BoolectorExpr ret = boolector_true(context);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createFalse() {
        BoolectorExpr ret = boolector_false(context);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createBoolConst(int value) {
        return value ? createTrue() : createFalse();
    }

    BoolectorExpr BoolectorSolver::createOrExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_or(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createXorExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_xor(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createAndExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_and(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createNotExpr(BoolectorExpr expr) {
        BoolectorExpr ret = boolector_not(context, expr);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createCondExpr(BoolectorExpr cond, BoolectorExpr choice1, BoolectorExpr choice2) {
        BoolectorExpr ret = boolector_cond(context, cond, choice1, choice2);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_eq(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createGtExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_ugt(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createGEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_ugte(context, lhs, rhs);
        return ret;

    }

    BoolectorExpr BoolectorSolver::createLtExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_ult(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createLEqExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_ulte(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createImplExpr(BoolectorExpr lhs, BoolectorExpr rhs) {
        BoolectorExpr ret = boolector_implies(context, lhs, rhs);
        return ret;
    }

    BoolectorExpr BoolectorSolver::createBitSet(BoolectorExpr container, unsigned int ith, BoolectorExpr value) {
        BoolectorExpr bit = boolector_slice(context, container, ith, ith);
//            log->info("bit: {}; value: {}", bit.get_sort(), bit);
        BoolectorExpr bv_value = createCondExpr(value,
                                       createBVConst(0, 1),
                                       createBVConst(1, 1));
//            log->info("bv_value: {}; value: {}", bv_value.get_sort(), bv_value);
        BoolectorExpr res = createEqExpr(bit, bv_value);
//            log->info("res: {}; value: {}", res.get_sort(), res);
        return res;
    }

    BoolectorExpr BoolectorSolver::createDistinct(std::list<BoolectorExpr> exprs) {
        log->error("Boolector does not support distinct yet");
        throw std::runtime_error("Boolector does not support distinct yet");
    }

    BoolectorExpr BoolectorSolver::joinExprsWithAnd(std::list<BoolectorExpr> &exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        BoolectorExpr ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = boolector_and(context, ret, *ite);
        }
        return ret;
    }

    BoolectorExpr BoolectorSolver::joinExprsWithOr(std::list<BoolectorExpr> &exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        BoolectorExpr ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = boolector_or(context, ret, *ite);
        }
        return ret;
    }

    void BoolectorSolver::assertLater(BoolectorExpr expr) {
        to_be_asserted.push_back(expr);
    }

    void BoolectorSolver::assertNow(BoolectorExpr expr) {
        boolector_assert(context, expr);
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
            return SAT;
        } else if (boolector_res == BOOLECTOR_UNSAT) {
            return UNSAT;
        } else {
            log->error("UNKNOWN Boolector result");
            throw std::runtime_error("UNKNOWN Boolector result");
        }
    }

    void BoolectorSolver::printExpr(BoolectorExpr expr) {
        boolector_dump_smt2_node(context, stdout, expr);
    }

    void BoolectorSolver::printModel() {
        boolector_print_model(context, "smt2", stdout);
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
            asserted.push_back(body);
            for (++ite; ite != to_be_asserted.end(); ++ite) {
                body = boolector_and(context, body, *ite);
                asserted.push_back(body);
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