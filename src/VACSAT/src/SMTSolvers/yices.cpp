#include "yices.h"
#include "../config.h"
#include "../prelude.h"
#include <stdexcept>
#include <iostream>
#include <sstream>
#include <list>

namespace SMT {

    #define yexp(expr) std::make_shared<yices_expr_t>(yices_expr_t(expr))

    inline const term_t& eto_y(const SMTExpr &expr) {
#ifdef NDEBUG
        return std::static_pointer_cast<yices_expr_t>(expr)->e;
#else
        YicesExpr e = std::dynamic_pointer_cast<yices_expr_t>(expr);
        if (e == nullptr) {
            throw unexpected("Operand is of the wrong type");
        }
        return e->e;
#endif
    }

    void raise_error(const std::string error) {
        throw std::runtime_error(error);
    }

    void yices_fail(const std::string function_name, std::list<SMTExpr>& parts) {
        std::stringstream fmt;
        auto ite = parts.begin();
        fmt << "Error in " << function_name << "! Term is less than 0!";
        if (parts.size() > 0) {
            fmt << " (parts: " << eto_y(*ite);
            for (++ite; ite != parts.end(); ++ite) {
                fmt << ", " << eto_y(*ite);
            }
            fmt << ")";
            fprintf(stderr, "%s\n", fmt.str().c_str());
        }
        fprintf(stderr, "%s\n", fmt.str().c_str());
        for (auto &&part : parts) {
            yices_pp_term(stderr, eto_y(part), 160, 80, 0);
        }
        yices_print_error(stderr);
        throw std::runtime_error(fmt.str());
    }

    ctx_config_t* mk_config() {
        int res_code = 0;
        ctx_config_t* res = yices_new_config();
        res_code = yices_default_config_for_logic(res, "QF_BV");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "mode", "one-shot");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "solver-type", "dpllt");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "uf-solver", "none");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "bv-solver", "default");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "array-solver", "none");
        res_code = res_code < 0 ? res_code : yices_set_config(res, "arith-solver", "none");
        if (res_code < 0) {
            yices_print_error(stdout);
            log->error("Got code < 1 in yices_set_config");
            throw std::runtime_error("Got code < 1 in yices_set_config");
        }
        return res;
    }

    context_t* mk_context() {
        int res_code = 0;
        ctx_config_t* cfg = mk_config();
        context_t* ctx = yices_new_context(cfg);
        yices_free_config(cfg);
        res_code = yices_context_enable_option(ctx, "var-elim");
        res_code = res_code < 0 ? res_code : yices_context_enable_option(ctx, "flatten");
        res_code = res_code < 0 ? res_code : yices_context_enable_option(ctx, "learn-eq");

        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "keep-ite");
//        : whether to eliminate term if-then-else or keep them as terms

        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "arith-elim");
        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "bvarith-elim");
        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "eager-arith-lemmas");
        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "break-symmetries");
        res_code = res_code < 0 ? res_code : yices_context_disable_option(ctx, "assert-ite-bounds");
//        : try to determine upper and lower bound on if-then-else
//            *   terms and assert these bounds. For example, if term t is defined as
//        *   (ite c 10 (ite d 3 20)), then the context with include the assertion
//        *   3 <= t <= 20.

        if (res_code < 0) {
            log->error("Got code < 1 in yices_set_config");
            throw std::runtime_error("Got code < 1 in yices_set_config");
        }
        return ctx;

    }


    YicesSolver::YicesSolver() :
        SMTFactory(Solver::YICES),
        model(nullptr) {
        yices_init();

        context = mk_context();
//        context = yices_new_context(NULL);
    }
    YicesSolver::~YicesSolver() {
        if (model != nullptr) {
            yices_free_model(model);
        }
        yices_exit();
    }

    // term_t YicesSolver::createBoolType() {
    //     return yices_bool_type();
    // }
    // term_t YicesSolver::createBVType(int size) {
    //     return yices_bv_type(size);
    // }

    SMTExpr YicesSolver::createVar2(const std::string name, int size) {
        if (size == 1) {
            return createBoolVar(name);
        }
        return createBVVar(name, size);
    }

    SMTExpr YicesSolver::createBoolVar(const std::string name) {
        term_t type = yices_bool_type();
        term_t var = yices_new_uninterpreted_term(type);
        yices_set_term_name(var, name.c_str());
        if (var < 0) {
            std::list<SMTExpr> parts;
            yices_fail("YicesSolver::createBoolVar", parts);
        }
        return yexp(var);
    }

    SMTExpr YicesSolver::createBVVar(const std::string name, int size) {
        term_t type = yices_bv_type(size);
        term_t var = yices_new_uninterpreted_term(type);
        yices_set_term_name(var, name.c_str());
        if (var < 0) {
            std::list<SMTExpr> parts;
            yices_fail("YicesSolver::createBVVar", parts);
        }
        return yexp(var);
    }

    SMTExpr YicesSolver::createBVConst(int value, int size) {
        term_t res = yices_bvconst_uint32(size, value);
        if (res < 0) {
            std::list<SMTExpr> parts;
            yices_fail("YicesSolver::createBVConst", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createBoolConst(bool value) {
        term_t res = value ? yices_true() : yices_false();
        if (res < 0) {
            std::list<SMTExpr> parts;
            yices_fail("YicesSolver::createBoolConst", parts);
        }
        return yexp(res);
    }        
    SMTExpr YicesSolver::createTrue() {
        return yexp(yices_true());
    }
    SMTExpr YicesSolver::createFalse() {
        return yexp(yices_false());
    }
    SMTExpr YicesSolver::createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        term_t res = yices_or2(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createOrExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        term_t res = yices_xor2(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createOrExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        term_t res = yices_and2(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createAndExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createNotExpr(const SMTExpr& expr) {
        term_t res = yices_not(eto_y(expr));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(expr);
            yices_fail("YicesSolver::createNotExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) {
        term_t res = yices_ite(eto_y(cond), eto_y(choice1), eto_y(choice2));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(cond);
            parts.push_back(choice1);
            parts.push_back(choice2);
            yices_fail("YicesSolver::createCondExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        term_t res = yices_eq(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createEqExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        term_t res = yices_implies(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createImplExpr", parts);
        }
        return yexp(res);
    }

    SMTExpr YicesSolver::createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // // WARNING: default Gt is unsigned. Do not use signed!
        term_t res = yices_bvgt_atom(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createGtExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // // WARNING: default GEq is unsigned. Do not use signed!
        term_t res = yices_bvge_atom(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createGEqExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // // WARNING: default Lt is unsigned. Do not use signed!
        term_t res = yices_bvlt_atom(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createLtExpr", parts);
        }
        return yexp(res);
    }
    SMTExpr YicesSolver::createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // // WARNING: default LEq is unsigned. Do not use signed!
        term_t res = yices_bvle_atom(eto_y(lhs), eto_y(rhs));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createLEqExpr", parts);
        }
        return yexp(res);
    }

    SMTExpr YicesSolver::createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) {
        SMTExpr elem = yexp(yices_bitextract(eto_y(container), ith));
        SMTExpr res = yexp(yices_eq(eto_y(elem), eto_y(value)));
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(container);
            parts.push_back(value);
            yices_fail("YicesSolver::createBitExtract", parts);
        }
        return res;
    }

    SMTExpr YicesSolver::createDistinct(std::list<SMTExpr>& exprs) {
        uint32_t size = (uint32_t) exprs.size();
        if (size > YICES_MAX_ARITY){
            std::list<SMTExpr> parts;
            for (auto &&expr : exprs) {
                parts.push_back(expr);
            }
            yices_fail("YicesSolver::createDistinct, size greater than YICES_MAX_ARITY", parts);
        }
        else if (size <= 0) {
            std::list<SMTExpr> parts;
            yices_fail("YicesSolver::createDistinct, size <= 0", parts);
        }
        term_t* elems = new term_t[size];
        int i = 0;
        for (auto &&expr : exprs) {
            elems[i++] = eto_y(expr);
        }

        term_t res = yices_distinct(size, elems);

        if (res < 0) {
            std::list<SMTExpr> parts;
            for (auto &&expr : exprs) {
                parts.push_back(expr);
            }
            yices_fail("YicesSolver::createDistinct", parts);
        }
        return yexp(res);
    }

    SMTExpr YicesSolver::joinExprsWithAnd(std::list<SMTExpr>& exprs) {
        if (exprs.empty()) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        term_t ret = eto_y(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = yices_and2(ret, eto_y(*ite));
        }
        return yexp(ret);
    }
    SMTExpr YicesSolver::joinExprsWithOr(std::list<SMTExpr>& exprs) {
        if (exprs.empty()) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        term_t ret = eto_y(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = yices_or2(ret, eto_y(*ite));
        }
        return yexp(ret);
    }

    void YicesSolver::assertLater(const SMTExpr& expr) {
        to_be_asserted.push_back(eto_y(expr));
    }

    void YicesSolver::assertNow(const SMTExpr& expr) {
        // printf("%p: ", context);
        // yices_pp_term(stdout, expr, 140, 40, 0);
        yices_assert_formula(context, eto_y(expr));
        asserted.push_back(eto_y(expr));
    }        

    SMTResult YicesSolver::solve() {
        this->loadToSolver();
        smt_status_t res = yices_check_context(context, NULL);

        switch (res) {
            case STATUS_SAT: {
                // model_t* model = yices_get_model(context, 1);
                // yices_pp_model(stdout, model, 120, 40, 0);
                // yices_free_model(model);
                return SMTResult::SAT;
                break;
            }
            case STATUS_UNSAT:
                return SMTResult::UNSAT;
                break;
            case STATUS_UNKNOWN:
                return SMTResult::UNKNOWN;
                break;

            case STATUS_IDLE:
                fprintf(stderr, "Idle...\n");
                break;
            case STATUS_SEARCHING:
            case STATUS_INTERRUPTED:
            case STATUS_ERROR:
                fprintf(stderr, "Error in check_context\n");
                yices_print_error(stderr);
                break;
        }
        return SMTResult::ERROR;
    }

    void YicesSolver::extract_model() {
        if (model == nullptr) {
            // Do not know the meaning of the second boolean parameter.
            // Using true because Mikhail does so
            model = yices_get_model(context, true);
//            yices_pp_model(stdout, model, 120, 40, 0);
        }
    }

    void YicesSolver::printModel() {
        extract_model();
        if (model == NULL) {
            fprintf(stdout, "Model is NULL...\n");
        } else {
            yices_pp_model(stdout, model, 120, 40, 0);
        }
    }

    bool YicesSolver::get_bool_value(const SMTExpr& expr) {
        extract_model();
        if (model == NULL) {
            throw std::runtime_error("YICES Model is null");
        }
        int val = -1;
        int res = yices_get_bool_value(model, eto_y(expr), &val);

        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(expr);
            yices_fail("YicesSolver::get_bool_value", parts);
        }

        return val == 0 ? false : true;


    }

    void YicesSolver::printExpr(const SMTExpr& expr) {
        yices_pp_term(stdout, eto_y(expr), 120, 40, 0);
    }
    std::string YicesSolver::exprValueAsString(const SMTExpr& expr) {
        extract_model();

        std::stringstream fmt;
        bool is_bool = true;
        int val = -1;
        int res = yices_get_bool_value(model, eto_y(expr), &val);
        if (res < 0) {
            res = yices_get_bv_value(model, eto_y(expr), &val);
            is_bool = false;
            if (res < 0) {
                std::list<SMTExpr> parts;
                parts.push_back(expr);
                yices_fail("YicesSolver::exprValueAsString", parts);
            }
        }
        fmt << (is_bool ? bool_to_true_false((bool) val) : std::to_string(val));
        return fmt.str();
    }

    int YicesSolver::exprValueAsInt(const SMT::SMTExpr &expr) {
        extract_model();

        term_t yexpr = eto_y(expr);

        int bitsize = yices_term_bitsize(yexpr);

        auto bv_val = new int[bitsize];
        int res = yices_get_bv_value(model, eto_y(expr), bv_val);
        if (res < 0) {
            std::list<SMTExpr> parts;
            parts.push_back(expr);
            yices_fail("YicesSolver::exprValueAsInt", parts);
        }

        int value = 0;

        for (int i = 0; i < bitsize; ++i) {
            value += (int) pow(2, i) * bv_val[i];
        }

        return value;
    }

    void YicesSolver::loadToSolver() {
        //TODO: consider using 
        /*
        int count = assertions.size();
        term_t arr = new term_t[count];
        std::copy(assertions.begin(), assertions.end(), arr);
        yices_assert_formulas(context, count, arr);
        delete[] arr;
        */

        if (to_be_asserted.empty()) {
            return;
        }
        else {
            auto ite = to_be_asserted.begin();
            term_t body = *ite;
            asserted.push_back(body);
            for (++ite; ite != to_be_asserted.end(); ++ite) {
                body = yices_and2(body, *ite);
                asserted.push_back(body);
            }
            yices_assert_formula(context, body);
            // yices_pp_term(stderr, body, 120, 40, 0);
            this->to_be_asserted.clear();
        }

    }
    void YicesSolver::clean() {
        yices_free_context(this->context);
        if (model != nullptr) {
            yices_free_model(model);
            model = nullptr;
        }
//        this->context = yices_new_context(NULL);
        this->context = mk_context();
        this->to_be_asserted.clear();
        this->asserted.clear();
    }
    void YicesSolver::deep_clean() {
        yices_free_context(this->context);
        if (model != nullptr) {
            yices_free_model(model);
            model = nullptr;
        }
//        this->context = yices_new_context(NULL);
        yices_reset();
        this->context = mk_context();
//        yices_garbage_collect(NULL, 0, NULL, 0, 0);
        this->to_be_asserted.clear();
        this->asserted.clear();
    }
    void YicesSolver::printContext() {
        for (auto &&term : this->asserted) {
            yices_pp_term(stdout, term, 160, 20, 0);
        }
    }
    void YicesSolver::printContext(std::string filename) {
        FILE* out = fopen(filename.c_str(), "w");
        if (out == NULL) {
            throw std::runtime_error("Cannot open file: " + filename);
        }
        for (auto &&term : this->asserted) {
            yices_pp_term(out, term, 1600, 20000, 0);
        }
        fclose(out);
    }
    void YicesSolver::printTerm(std::string filename, const SMTExpr& term) {
        FILE* out = fopen(filename.c_str(), "w");
        if (out == NULL) {
            throw std::runtime_error("Cannot open file: " + filename);
        }
        yices_pp_term(out, eto_y(term), 1600, 20000, 0);
        fclose(out);
    }
    void YicesSolver::print_statistics() {
        log->info("(:assertions\t{})", to_be_asserted.size());
    }
    // void YicesSolver::push() { 
    //     // loadToSolver();
    //     // int res = yices_push(context);
    //     // if (res != 0) {
    //     //     fprintf(stderr, "Failed to push yices context!\n");
    //     //     throw std::runtime_error("Failed to push yices context!\n");
    //     // }
    //     // assertions.clear();
    // }
    // void YicesSolver::pop() { 
    //     // int res = yices_pop(context);
    //     // if (res != 0) {
    //     //     fprintf(stderr, "Failed to pop yices context!\n");
    //     //     throw std::runtime_error("Failed to pop yices context!\n");
    //     // }
    //     // printf("Popping: %p\t", context);
    //     auto tmp = this->context;
    //     this->context = yices_new_context(NULL);
    //     yices_free_context(tmp);
    //     // printf("new one: %p\n", context);
    // }
}