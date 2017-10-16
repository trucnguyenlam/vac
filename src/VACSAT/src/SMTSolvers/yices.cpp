#include "yices.h"
#include "../config.h"
#include <stdexcept>
#include <iostream>
#include <sstream>
#include <list>

namespace SMT {

    void raise_error(const std::string error) {
        throw std::runtime_error(error);
    }

    void yices_fail(const std::string function_name, std::list<term_t> parts) {
        std::stringstream fmt;
        auto ite = parts.begin();
        fmt << "Error in " << function_name << "! Term is less than 0!";
        if (parts.size() > 0) {
            fmt << " (parts: " << *ite;
            for (ite++; ite != parts.end(); ++ite) {
                fmt << ", " << *ite;
            }
            fmt << ")";
            fprintf(stderr, "%s\n", fmt.str().c_str());
        }
        fprintf(stderr, "%s\n", fmt.str().c_str());
        for (auto &&part : parts) {
            yices_pp_term(stderr, part, 160, 80, 0);
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


    YicesSolver::YicesSolver() {
        yices_init();

        context = mk_context();
//        context = yices_new_context(NULL);
    }
    YicesSolver::~YicesSolver() {
        yices_exit();
    }

    // term_t YicesSolver::createBoolType() {
    //     return yices_bool_type();
    // }
    // term_t YicesSolver::createBVType(int size) {
    //     return yices_bv_type(size);
    // }

    term_t YicesSolver::createVar2(const std::string name, int size) {
        if (size == 1) {
            return createBoolVar(name);
        }
        return createBVVar(name, size);
    }

    term_t YicesSolver::createBoolVar(const std::string name) {
        term_t type = yices_bool_type();
        term_t var = yices_new_uninterpreted_term(type);
        yices_set_term_name(var, name.c_str());
        if (var < 0) {
            yices_fail("YicesSolver::createBoolVar", std::list<term_t>());
        }
        return var;
    }

    term_t YicesSolver::createBVVar(const std::string name, int size) {
        term_t type = yices_bv_type(size);
        term_t var = yices_new_uninterpreted_term(type);
        yices_set_term_name(var, name.c_str());
        if (var < 0) {
            yices_fail("YicesSolver::createBVVar", std::list<term_t>());
        }
        return var;
    }

    term_t YicesSolver::createBVConst(int value, int size) {
        term_t res = yices_bvconst_uint32(size, value);
        if (res < 0) {
            yices_fail("YicesSolver::createBVConst", std::list<term_t>());
        }
        return res;
    }
    term_t YicesSolver::createBoolConst(int value) {
        term_t res = value ? yices_true() : yices_false();
        if (res < 0) {
            yices_fail("YicesSolver::createBoolConst", std::list<term_t>());
        }
        return res;
    }        
    term_t YicesSolver::createTrue() {
        return yices_true();
    }
    term_t YicesSolver::createFalse() {
        return yices_false();
    }
    term_t YicesSolver::createOrExpr(term_t lhs, term_t rhs) {
        term_t res = yices_or2(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createOrExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createXorExpr(term_t lhs, term_t rhs) {
        term_t res = yices_xor2(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createOrExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createAndExpr(term_t lhs, term_t rhs) {
        term_t res = yices_and2(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createAndExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createNotExpr(term_t expr) {
        term_t res = yices_not(expr);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(expr);
            yices_fail("YicesSolver::createNotExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createCondExpr(term_t cond, term_t choice1, term_t choice2) {
        term_t res = yices_ite(cond, choice1, choice2);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(cond);
            parts.push_back(choice1);
            parts.push_back(choice2);
            yices_fail("YicesSolver::createCondExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createEqExpr(term_t lhs, term_t rhs) {
        term_t res = yices_eq(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createEqExpr", parts);
        }
        return res;
    }

    term_t YicesSolver::createGtExpr(term_t lhs, term_t rhs) {
        // // WARNING: default Gt is unsigned. Do not use signed!
        term_t res = yices_bvgt_atom(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createGtExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createGEqExpr(term_t lhs, term_t rhs) {
        // // WARNING: default GEq is unsigned. Do not use signed!
        term_t res = yices_bvge_atom(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createGEqExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createLtExpr(term_t lhs, term_t rhs) {
        // // WARNING: default Lt is unsigned. Do not use signed!
        term_t res = yices_bvlt_atom(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createLtExpr", parts);
        }
        return res;
    }
    term_t YicesSolver::createLEqExpr(term_t lhs, term_t rhs) {
        // // WARNING: default LEq is unsigned. Do not use signed!
        term_t res = yices_bvle_atom(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createLEqExpr", parts);
        }
        return res;
    }

    term_t YicesSolver::createBitSet(term_t container, unsigned int ith, term_t value) {
        term_t elem = yices_bitextract(container, ith);
        term_t res = yices_eq(elem, value);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(container);
            parts.push_back(value);
            yices_fail("YicesSolver::createBitExtract", parts);
        }
        return res;
    }
    term_t YicesSolver::createDistinct(std::list<term_t> exprs) {
        uint32_t size = (uint32_t) exprs.size();
        if (size > YICES_MAX_ARITY){
            std::list<term_t> parts;
            yices_fail("YicesSolver::createDistinct, size greater than YICES_MAX_ARITY", parts);
        }
        else if (size <= 0) {
            std::list<term_t> parts;
            yices_fail("YicesSolver::createDistinct, size <= 0", parts);
        }
        term_t* elems = new term_t[size];
        int i = 0;
        for (auto &&expr : exprs) {
            elems[i++] = expr;
        }

        term_t res = yices_distinct(size, elems);

        if (res < 0) {
            std::list<term_t> parts;
            yices_fail("YicesSolver::createDistinct", parts);
        }
        return res;
    }

    term_t YicesSolver::createImplExpr(term_t lhs, term_t rhs) {
        term_t res = yices_implies(lhs, rhs);
        if (res < 0) {
            std::list<term_t> parts;
            parts.push_back(lhs);
            parts.push_back(rhs);
            yices_fail("YicesSolver::createImplExpr", parts);
        }
        return res;
    }

    term_t YicesSolver::joinExprsWithAnd(std::list<term_t>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        term_t ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = yices_and2(ret, *ite);
        }
        return ret;
    }
    term_t YicesSolver::joinExprsWithOr(std::list<term_t>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        term_t ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = yices_or2(ret, *ite);
        }
        return ret;
    }

    void YicesSolver::assertLater(term_t expr) {
        to_be_asserted.push_back(expr);
    }

    void YicesSolver::assertNow(term_t expr) {
        // printf("%p: ", context);
        // yices_pp_term(stdout, expr, 140, 40, 0);
        yices_assert_formula(context, expr);
        asserted.push_back(expr);
    }        

    SMTResult YicesSolver::solve() {
        this->loadToSolver();
        smt_status_t res = yices_check_context(context, NULL);

        switch (res) {
            case STATUS_SAT: {
                // model_t* model = yices_get_model(context, 1);
                // yices_pp_model(stdout, model, 120, 40, 0);
                // yices_free_model(model);
                return SAT;
                break;
            }
            case STATUS_UNSAT:
                return UNSAT;
                break;
            case STATUS_UNKNOWN:
                return UNKNOWN;
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
        return ERROR;
    }

    void YicesSolver::printModel() {
        model_t* model = yices_get_model(context, false);
        if (model == NULL) {
            fprintf(stdout, "Model is NULL...\n");
        }
        else {
            yices_pp_model(stdout, model, 120, 40, 0);
            yices_free_model(model);
        }
    }

    void YicesSolver::printExpr(term_t expr) {
        yices_pp_term(stdout, expr, 120, 40, 0);
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
//        this->context = yices_new_context(NULL);
        this->context = mk_context();
        this->to_be_asserted.clear();
        this->asserted.clear();
    }
    void YicesSolver::deep_clean() {
        yices_free_context(this->context);
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