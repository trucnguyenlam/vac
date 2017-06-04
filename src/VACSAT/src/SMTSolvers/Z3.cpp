#include "Z3.h"
#include <z3++.h>
#include <fstream>
#include <ostream>

namespace SMT {
    static unsigned int var_counter = 0;
    Z3Solver::Z3Solver() : /*context(new z3::context()),*/ solver(context) { }
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
    
    void Z3Solver::loadToSolver() {
    //     //TODO: consider using 
    //     /*
    //     int count = assertions.size();
    //     expr arr = new expr[count];
    //     std::copy(assertions.begin(), assertions.end(), arr);
    //     yices_assert_formulas(context, count, arr);
    //     delete[] arr;
    //     */

    //     if (to_be_asserted.empty()) {
    //         return;
    //     }
    //     else {
    //         auto ite = to_be_asserted.begin();
    //         expr body = *ite;
    //         asserted.push_back(body);
    //         for ( ; ite != to_be_asserted.end(); ++ite) {
    //             body = yices_and2(body, *ite);
    //             asserted.push_back(body);
    //         }
    //         yices_assert_formula(context, body);
    //         // yices_pp_term(stderr, body, 120, 40, 0);
    //         this->to_be_asserted.clear();
    //     }
    }

    void Z3Solver::clean() {
        //TODO: both var_counter and context should be cleaned
        this->solver = z3::solver(context);
    }
    void Z3Solver::deep_clean() {
        var_counter = 0;
        //FIXME: nondtext should be regenerated
        /*delete context;
        context = new z3::context();*/
        this->solver = z3::solver(context);
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