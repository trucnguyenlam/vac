#include "Z3.h"
#include "../prelude.h"
#include <z3++.h>
#include <fstream>
#include <ostream>

namespace SMT {
    static unsigned int var_counter = 0;
//    static std::shared_ptr<z3::config> default_config() {
////        - proof  (Boolean)           Enable proof generation
////        - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
////        - trace  (Boolean)           Tracing support for VCC
////        - trace_file_name (String)   Trace out file for VCC traces
////        - timeout (unsigned)         default timeout (in milliseconds) used for solvers
////        - well_sorted_check          type checker
////        - auto_config                use heuristics to automatically select solver and configure it
////        - model                      model generation for solvers, this parameter can be overwritten when creating a solver
////        - model_validate             validate models produced by solvers
////        - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
//        std::shared_ptr<z3::config> conf(new z3::config());
//
////        conf->set("proof", false);
////        conf->set("debug_ref_count", );
////        conf->set("trace", false);
////        conf->set("trace_file_name", );
////        conf->set("timeout", );
////        conf->set("well_sorted_check", false);
////        conf->set("auto_config", true);
////        conf->set("model", );
////        conf->set("model_validate", false);
////        conf->set("unsat_core", false);
//
//        return conf;
//
//    }

//    std::shared_ptr<z3::config> Z3Solver::config = default_config();
    Z3Solver::Z3Solver() /*context(new z3::context()),*/  {
        z3::config cfg;
        cfg.set("proof", false);
//        cfg.set("debug_ref_count", false);
        cfg.set("trace", false);
//        cfg.set("trace_file_name", false);
//        cfg.set("timeout", false);
        cfg.set("well_sorted_check", false);
        cfg.set("auto_config", false);
        cfg.set("model", false);
        cfg.set("model_validate", false);
        cfg.set("unsat_core", false);
        context.init(cfg, false);
        solver = z3::solver(context);
    }
    Z3Solver::~Z3Solver() { /*delete context;*/ }

    // expr YicesSolver::createBoolType() {
    //     return yices_bool_type();
    // }
    // expr YicesSolver::createBVType(int size) {
    //     return yices_bv_type(size);
    // }

    expr Z3Solver::createVar2(const std::string name, int size) {
//        std::cout << name << std::endl;
        if (size == 1) {
            return createBoolVar(name);
        }
        return createBVVar(name, size);
    }

    expr Z3Solver::createBoolVar(const std::string name) {
//        std::cout << name << std::endl;
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        return context.bool_const(enum_name .c_str());
    }

    expr Z3Solver::createBVVar(const std::string name, int size) {
//        std::cout << name << std::endl;
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        return context.bv_const(enum_name .c_str(), size);;
    }

    expr Z3Solver::createBVConst(int value, int size) {
        return context.bv_val(value, size);
    }
    expr Z3Solver::createBoolConst(int value) {
        return value ? context.bool_val(true) : context.bool_val(false);
    }        
    expr Z3Solver::createTrue() {
        return createBoolConst(true);
    }
    expr Z3Solver::createFalse() {
        return createBoolConst(false);
    }
    expr Z3Solver::createOrExpr(expr lhs, expr rhs) {
        expr res =  lhs || rhs;
        return res;
    }
    expr Z3Solver::createAndExpr(expr lhs, expr rhs) {
        expr res = lhs && rhs;
        return res;
    }
    expr Z3Solver::createNotExpr(expr _expr) {
        expr res = !_expr;
        return res;
    }
    expr Z3Solver::createCondExpr(expr cond, expr choice1, expr choice2) {
        expr res = ite(cond, choice1, choice2);
        return res;
    }
    expr Z3Solver::createEqExpr(expr lhs, expr rhs) {
        expr res = lhs == rhs;
        return res;
    }

    expr Z3Solver::createGtExpr(expr lhs, expr rhs) {
        // WARNING: default > is signed. Use unsigned!
        expr res = z3::ugt(lhs, rhs);
        return res;
    }
    expr Z3Solver::createGEqExpr(expr lhs, expr rhs) {
        // WARNING: default >= is signed. Use unsigned!
        expr res = z3::uge(lhs, rhs);
        return res;
    }
    expr Z3Solver::createLtExpr(expr lhs, expr rhs) {
        // WARNING: default < is signed. Use unsigned!
        expr res = z3::ult(lhs, rhs);
        return res;
    }
    expr Z3Solver::createLEqExpr(expr lhs, expr rhs) {
        // WARNING: default <= is signed. Use unsigned!
        expr res = z3::ule(lhs, rhs);
        return res;
    }

    expr Z3Solver::createImplExpr(expr lhs, expr rhs) {
        expr res = implies(lhs, rhs);
        return res;
    }

    expr Z3Solver::createBitSet(expr container, unsigned int ith, expr value) {
            expr bit = container.extract(ith, ith);
//            log->info("bit: {}; value: {}", bit.get_sort(), bit);
            expr bv_value = createCondExpr(value,
                                           createBVConst(0, 1),
                                           createBVConst(1, 1));
//            log->info("bv_value: {}; value: {}", bv_value.get_sort(), bv_value);
            expr res = createEqExpr(bit, bv_value);
//            log->info("res: {}; value: {}", res.get_sort(), res);
            return res;
    }
    expr Z3Solver::createDistinct(std::list<expr> exprs) {
        expr_vector z3_exps(this->context);

        for (auto &&expr : exprs) {
            z3_exps.push_back(expr);
        }
        expr res = z3::distinct(z3_exps);
        return res;
    }

    expr Z3Solver::joinExprsWithAnd(std::list<expr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        expr ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = ret && *ite;
        }
        return ret;
    }
    expr Z3Solver::joinExprsWithOr(std::list<expr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        expr ret = *ite;
        for (++ite; ite != exprs.end(); ++ite) {
            ret = ret || *ite;
        }
        return ret;
    }

    void Z3Solver::assertLater(expr e) {
        solver.add(e);
    }

    void Z3Solver::assertNow(expr e) {
        // printf("%p: ", context);
        // yices_pp_term(stdout, expr, 140, 40, 0);
        solver.add(e);
    }

    SMTResult Z3Solver::solve() {
        this->loadToSolver();
        check_result res = solver.check();

//        std::cout << solver.get_model() << std::endl;

        switch (res) {
            case sat: {
                // model_t* model = yices_get_model(context, 1);
                // yices_pp_model(stdout, model, 120, 40, 0);
                // yices_free_model(model);
                return SAT;
                break;
            }
            case unsat:
                return UNSAT;
                break;
            case unknown:
                return UNKNOWN;
                break;

            default:
            std::cerr << "Error in check_context" << std::endl;
                break;
        }
        return ERROR;
    }

    void Z3Solver::print_statistics() {
        auto state = this->solver.statistics();
        std::cout << state << std::endl;
    }
    void Z3Solver::printExpr(expr e) {
        std::cout << e << std::endl;
    }
    void Z3Solver::printModel() {
        try {
            model model = solver.get_model();
            if (model == NULL) {
                std::cerr << "Model is NULL..." << std::endl;
            }
            std::cout << model << std::endl;

        }
        catch (z3::exception e) {
            std::cerr << "Model is NULL..." << std::endl;
        }
    }
    
    void Z3Solver::loadToSolver() { }

    void Z3Solver::clean() {
        //TODO: both var_counter and context should be cleaned
        this->solver = z3::solver(context, "QF_BV");
    }
    void Z3Solver::deep_clean() {
        var_counter = 0;
        //FIXME: nondtext should be regenerated
        /*delete context;
        context = new z3::context();*/
        this->solver = z3::solver(context, "QF_BV");
    }
    void Z3Solver::printContext() {
        std::cout << this->solver << std::endl;
    }
    void Z3Solver::printContext(std::string filename) {
        std::ofstream myfile;
        myfile.open(filename);
        myfile << this->solver << std::endl;
        myfile.close();
    }

    // void Z3Solver::push() { 
    //     // loadToSolver();
    //     // int res = yices_push(context);
    //     // if (res != 0) {
    //     //     fprintf(stderr, "Failed to push yices context!\n");
    //     //     throw std::runtime_error("Failed to push yices context!\n");
    //     // }
    //     // assertions.clear();
    // }
    // void Z3Solver::pop() { 
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