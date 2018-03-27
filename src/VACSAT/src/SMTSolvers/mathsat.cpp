//
// Created by esteffin on 19/07/17.
//
#include <sstream>
#include <iostream>
#include "mathsat.h"
#include "../config.h"
#include "../prelude.h"

namespace SMT {

    #define mto_e(expr) std::make_shared<msat_expr_t>(msat_expr_t(expr))

    inline const msat_term& eto_m(const SMTExpr &expr) {
#ifdef NDEBUG
        return std::static_pointer_cast<msat_expr_t>(expr)->e;
#else
        MsatExpr e = std::dynamic_pointer_cast<msat_expr_t>(expr);
        if (e == nullptr) {
            throw unexpected("Operand is not of the mathsat type");
        }
        return e->e;
#endif
    }

//    void raise_error(const std::string error) {
//        throw std::runtime_error(error);
//    }

    void MathsatSolver::mathsat_fail(const std::string& error_message) { //, std::list<msat_term> parts) {
//        std::stringstream fmt;
//        auto ite = parts.begin();
//        fmt << "Error in " << function_name << "! Term is less than 0!";
//        if (parts.size() > 0) {
//            fmt << " (parts: " << *ite;
//            for (ite++; ite != parts.end(); ++ite) {
//                fmt << ", " << *ite;
//            }
//            fmt << ")";
//            fprintf(stderr, "%s\n", fmt.str().c_str());
//        }
//        fprintf(stderr, "%s\n", fmt.str().c_str());
//        for (auto &&part : parts) {
//            yices_pp_term(stderr, part, 160, 80, 0);
//        }
//        yices_print_error(stderr);
        const char* error = msat_last_error_message(context);
        std::string error_str(error);
        log->error("mathsat_error in " + error_message + ":\n\t" + error_str);
//        msat_free((void*) error);
        throw std::runtime_error("mathsat_error in " + error_message + ":\n\t" + error_str);
    }


    static unsigned int var_counter = 0;

    msat_config MathsatSolver::mk_config() {
//        static const char* mathsat_config =
//                "preprocessor.toplevel_propagation = true\n"
//                "preprocessor.simplification = 7\n"
//                "dpll.branching_random_frequency = 0.01\n"
//                "dpll.branching_random_invalidate_phase_cache = true\n"
//                "dpll.restart_strategy = 3\n"
//                "dpll.glucose_var_activity = true\n"
//                "dpll.glucose_learnt_minimization = true\n"
//                "theory.bv.eager = true\n"
//                "theory.bv.delay_propagated_eqs = true\n"
//                "theory.arr.mode = 1\n"
//                "theory.la.enabled = false\n"
//                "theory.eq_propagation = false\n"
//                "theory.arr.enabled = false\n"
//                "theory.bv.bit_blast_mode = 2\n"
//                "dpll.preprocessor.mode = 1\n";
        const char* mathsat_config =
                "preprocessor.toplevel_propagation = true\n"
                        "preprocessor.simplification = 1\n"
                        "dpll.branching_random_frequency = 0.01\n"
                        "dpll.branching_random_invalidate_phase_cache = true\n"
                        "dpll.restart_strategy = 3\n"
                        "dpll.glucose_var_activity = true\n"
                        "dpll.glucose_learnt_minimization = true\n"
                        "dpll.preprocessor.mode = 1\n"
                        "theory.bv.eager = true\n"
                        "theory.bv.bit_blast_mode = 2\n"
                        "theory.bv.delay_propagated_eqs = true\n"
                        "theory.la.enabled = false\n"
                        "theory.fp.mode = 1\n"
                        "theory.fp.bit_blast_mode = 2\n"
                        "theory.fp.bv_combination_enabled = true\n"
                        "theory.arr.permanent_lemma_inst = true\n"
                        "theory.arr.enable_witness = true";


        msat_config cfg = msat_parse_config(mathsat_config);
        msat_set_option(cfg, "model_generation", "true");
        return cfg;
    }

    MathsatSolver::MathsatSolver() : SMTFactory(Solver::MATHSAT) {
        msat_config cfg = mk_config();
        context = msat_create_env(cfg);
    }
    MathsatSolver::~MathsatSolver() {
        msat_destroy_env(context);
    }

    // term_t createBoolType() override;
    // term_t createBVType(int size) override;



    SMTExpr MathsatSolver::createVar2(const std::string name, int size) {
        if (size == 1) {
            return createBoolVar(name);
        } else {
            return createBVVar(name, size);
        }
    }
    SMTExpr MathsatSolver::createBoolVar(const std::string name) {
        msat_type sort = msat_get_bool_type(context);
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        msat_decl decl = msat_declare_function(context, enum_name.c_str(), sort);
        msat_term res = msat_make_constant(context, decl);
        if (MSAT_ERROR_DECL(decl) || MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createBoolVar(" + name + ")...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createBVVar(const std::string name, int size) {
        msat_type sort = msat_get_bv_type(context, (size_t) size);
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        msat_decl decl = msat_declare_function(context, enum_name.c_str(), sort);
        msat_term res = msat_make_constant(context, decl);
        if (MSAT_ERROR_DECL(decl) || MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createBVVar(" + name + ", " + std::to_string(size) + ")...");
        }
        return mto_e(res);
    }

    SMTExpr MathsatSolver::createBVConst(int value, int size) {
        msat_term res = msat_make_bv_number(context, std::to_string(value).c_str(), (size_t) size, 10);
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createBVConst(" + std::to_string(value) + ", " + std::to_string(size) + ")...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createBoolConst(int value) {
        return value ? createTrue() : createFalse();
    }
    SMTExpr MathsatSolver::createTrue() {
        msat_term res = msat_make_true(context);
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createTrue()...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createFalse() {
        msat_term res = msat_make_false(context);
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createFalse()...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_or(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createOrExpr...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        //FIXME: check this, or use the logic circuit for XOR
        msat_term res = msat_make_bv_xor(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createOrExpr...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_and(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createAndExpr...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createNotExpr(const SMTExpr& expr) {
        msat_term res = msat_make_not(context, eto_m(expr));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createNotExpr...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) {
        msat_term res;
        if (true) {
            // MathSAT shows a dislike of implementing this with booleans. Follow
            // CBMC's CNF flattening and make this
            // (with c = cond, t = trueval, f = falseval):
            //
            //   or(and(c,t),and(not(c), f))
            msat_term land1 = msat_make_and(context, eto_m(cond), eto_m(choice1));
            check_msat_error(land1);

            msat_term notval = msat_make_not(context, eto_m(cond));
            check_msat_error(notval);

            msat_term land2 = msat_make_and(context, notval, eto_m(choice2));
            check_msat_error(land2);

            res = msat_make_or(context, land1, land2);
        } else {
            res = msat_make_term_ite(context, eto_m(cond), eto_m(choice1), eto_m(choice2));
        }
        if (MSAT_ERROR_TERM(res)) {
            auto ty = msat_type_repr(msat_term_get_type(eto_m(cond)));
            log->warn("{}", ty);
            msat_to_smtlib2_ext_file(context, eto_m(cond), "QF_BV", 0, stdout);
            msat_to_smtlib2_ext_file(context, eto_m(choice1), "QF_BV", 0, stdout);
            msat_to_smtlib2_ext_file(context, eto_m(choice2), "QF_BV", 0, stdout);
            mathsat_fail("Invalid term in MathsatSolver::createCondExpr...");
        }
        return mto_e(res);
    }
    SMTExpr MathsatSolver::createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_eq(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createEqExpr...");
        }
        return mto_e(res);

    }
    SMTExpr MathsatSolver::createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_or(context, eto_m(rhs), msat_make_not(context, eto_m(lhs)));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createImplExpr...");
        }
        return mto_e(res);

    }
    SMTExpr MathsatSolver::createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_not(context, msat_make_bv_uleq(context, eto_m(lhs), eto_m(rhs)));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createGtExpr...");
        }
        return mto_e(res);

    }
    SMTExpr MathsatSolver::createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_not(context, msat_make_bv_ult(context, eto_m(lhs), eto_m(rhs)));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createGEqExpr...");
        }
        return mto_e(res);

    }
    SMTExpr MathsatSolver::createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_bv_ult(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createLtExpr...");
        }
        return mto_e(res);

    }
    SMTExpr MathsatSolver::createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        msat_term res = msat_make_bv_uleq(context, eto_m(lhs), eto_m(rhs));
        if (MSAT_ERROR_TERM(res)) {
            mathsat_fail("Invalid term in MathsatSolver::createLEqExpr...");
        }
        return mto_e(res);
    }

    SMTExpr MathsatSolver::createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) {
        log->critical("MathsatSolver::createBitSet is not implemented since there is no distinct");
        throw unexpected_error("MathsatSolver::createBitSet is not implemented since there is no distinct", __FILE__, __LINE__, __FUNCTION__, __PRETTY_FUNCTION__);
    }
    SMTExpr MathsatSolver::createDistinct(std::list<SMTExpr>& exprs) {
        log->critical("MathsatSolver::createDistinct is not implemented since there is no distinct");
        throw unexpected_error("MathsatSolver::createDistinct is not implemented since there is no distinct", __FILE__, __LINE__, __FUNCTION__, __PRETTY_FUNCTION__);
    }

    SMTExpr MathsatSolver::joinExprsWithAnd(std::list<SMTExpr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        msat_term ret = eto_m(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = msat_make_and(context, ret, eto_m(*ite));
        }
        return mto_e(ret);
    }
    SMTExpr MathsatSolver::joinExprsWithOr(std::list<SMTExpr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        msat_term ret = eto_m(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = msat_make_or(context, ret, eto_m(*ite));
        }
        return mto_e(ret);
    }

    void MathsatSolver::assertLater(const SMTExpr& expr) {
//        msat_assert_formula(context, expr);
        to_be_asserted.push_back(eto_m(expr));
    }
    void MathsatSolver::assertNow(const SMTExpr& expr) {
        msat_assert_formula(context, eto_m(expr));
    }

    SMTResult MathsatSolver::solve() {
        loadToSolver();
        msat_result res = msat_solve(context);
        switch (res) {
            case MSAT_UNKNOWN:
                log->error("UNKNOWN RESULT FROM SOLVER");
                throw std::runtime_error("UNKNOWN RESULT FROM SOLVER");
            case MSAT_UNSAT:
                return SMTResult::UNSAT;
            case MSAT_SAT:
                return SMTResult::SAT;
            default:
                log->critical("Uh?");
                throw unexpected_error("Uh?", __FILE__, __LINE__, __FUNCTION__, __PRETTY_FUNCTION__);
        }
    }
    void MathsatSolver::printExpr(const SMTExpr& expr) {
        char* res = msat_to_smtlib2_term(context, eto_m(expr));
        log->info("{}", res);
        msat_free(res);
    }
    void MathsatSolver::printModel() {
        log->critical("MathsatSolver::printModel is not implemented");
        throw unexpected_error("MathsatSolver::printModel is not implemented", __FILE__, __LINE__, __FUNCTION__, __PRETTY_FUNCTION__);
    }
    bool MathsatSolver::get_bool_value(const SMTExpr& expr) {
        msat_term t = msat_get_model_value(this->context, eto_m(expr));
        check_msat_error(t);

        bool res;

        if (msat_term_is_true(this->context, t)) {
            res = true;
        } else if (msat_term_is_false(this->context, t)) {
            res = false;
        } else {
            throw std::runtime_error("Boolean model value is neither true or false");
        }

        msat_free(msat_term_repr(t));
        return res;
    }
    void MathsatSolver::print_statistics() {
        size_t size = 0;
        msat_term * terms = msat_get_asserted_formulas(context, &size);
        log->info("(:assertions\t{})", size);
        msat_free(terms);
    }
    void MathsatSolver::loadToSolver() {
        if (to_be_asserted.empty()) {
            return;
        }
        else {
            auto ite = to_be_asserted.begin();
            msat_term body = *ite;
//            asserted.push_back(body);
            for (++ite; ite != to_be_asserted.end(); ++ite) {
                body = msat_make_and(context, body, *ite);
//                asserted.push_back(body);
            }
            msat_assert_formula(context, body);
            // yices_pp_term(stderr, body, 120, 40, 0);
            this->to_be_asserted.clear();
        }
    }
    void MathsatSolver::clean() {
        msat_reset_env(context);
    }
    void MathsatSolver::deep_clean() {
        msat_reset_env(context);
        msat_destroy_env(context);
        context = msat_create_env(mk_config());
    }

    void print_w_decl(msat_env context, msat_term expr) {
        char* res = msat_to_smtlib2_ext(context, expr, "QF_BV", 1);
        log->info("{}", res);
        msat_free(res);
    }
    
    void MathsatSolver::printContext() {
        size_t size = 0;
        msat_term * terms = msat_get_asserted_formulas(context, &size);
        for (int i = 0; i < size; ++i) {
            print_w_decl(context, terms[i]);
        }
        msat_free(terms);
    }
    void MathsatSolver::printContext(std::string filename) {
        FILE* out = fopen(filename.c_str(), "w");
        size_t size = 0;
        msat_term * terms = msat_get_asserted_formulas(context, &size);
        for (int i = 0; i < size; ++i) {
            msat_to_smtlib2_ext_file(context, terms[i], "QF_BV", 1, out);
        }
        msat_free(terms);
        fclose(out);
    }

    void MathsatSolver::check_msat_error(msat_term term) {

    }

    // void push() override;
    // void pop() override;
}