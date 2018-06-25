#include "Z3.h"
#include "../prelude.h"
#include <z3++.h>
#include <fstream>
#include <ostream>

namespace SMT {
    static unsigned int var_counter = 0;

#define z3expr(expr) std::make_shared<z3_expr_t>(z3_expr_t(expr))

    inline const z3::expr& eto_z3(const SMTExpr &expr) {
#ifdef NDEBUG
        return std::static_pointer_cast<z3_expr_t>(expr)->e;
#else
        Z3Expr e = std::dynamic_pointer_cast<z3_expr_t>(expr);
        if (e == nullptr) {
            throw unexpected("Operand is of the wrong type");
        }
        return e->e;
#endif
    }

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

    static void get_default_conf(z3::config& cfg) {
        cfg.set("proof", false);
//        cfg.set("debug_ref_count", false);
        cfg.set("trace", false);
//        cfg.set("trace_file_name", false);
//        cfg.set("timeout", false);
        cfg.set("well_sorted_check", false);
        cfg.set("auto_config", false);
        cfg.set("model", true);
        cfg.set("model_validate", false);
        cfg.set("unsat_core", false);
        return (void) 0;
    }

    Z3Solver::Z3Solver(bool _fast) :
            SMTFactory(Solver::Z3),
            context((get_default_conf(this->cfg), this->cfg)),
            solver(context),
            fast(_fast) {

//        context.init(cfg, false);
//        solver = z3::solver(context);
        z3::params p(context);
        p.set("relevancy", (unsigned int) 0);
        p.set("model", true);
        p.set("proof", false);
        solver.set(p);
    }
    Z3Solver::~Z3Solver() { /*delete context;*/ }

    // expr YicesSolver::createBoolType() {
    //     return yices_bool_type();
    // }
    // expr YicesSolver::createBVType(int size) {
    //     return yices_bv_type(size);
    // }

    SMTExpr Z3Solver::createVar2(const std::string name, int size) {
//        std::cout << name << std::endl;
        if (size == 1) {
            return createBoolVar(name);
        }
        return createBVVar(name, size);
    }

    SMTExpr Z3Solver::createBoolVar(const std::string name) {
//        std::cout << name << std::endl;
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        return z3expr(context.bool_const(enum_name .c_str()));
    }

    SMTExpr Z3Solver::createBVVar(const std::string name, int size) {
//        std::cout << name << std::endl;
        std::string enum_name = name + "_" + std::to_string(var_counter++);
        return z3expr(context.bv_const(enum_name .c_str(), size));
    }

    SMTExpr Z3Solver::createBVConst(int value, int size) {
        return z3expr(context.bv_val(value, size));
    }
    SMTExpr Z3Solver::createBoolConst(bool value) {
        return z3expr(value ? context.bool_val(true) : context.bool_val(false));
    }        
    SMTExpr Z3Solver::createTrue() {
        return createBoolConst(true);
    }
    SMTExpr Z3Solver::createFalse() {
        return createBoolConst(false);
    }
    SMTExpr Z3Solver::createOrExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        expr res = eto_z3(lhs) || eto_z3(rhs);
        return z3expr(res);
    }
    SMTExpr Z3Solver::createXorExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        //FIXME: check this, or use the logic circuit for XOR
        expr res = eto_z3(lhs) ^ eto_z3(rhs);
        return z3expr(res);
    }
    SMTExpr Z3Solver::createAndExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        expr res = eto_z3(lhs) && eto_z3(rhs);
        return z3expr(res);
    }
    SMTExpr Z3Solver::createNotExpr(const SMTExpr& _expr) {
        expr res = !eto_z3(_expr);
        return z3expr(res);
    }
    SMTExpr Z3Solver::createCondExpr(const SMTExpr& cond, const SMTExpr& choice1, const SMTExpr& choice2) {
        expr res = ite(eto_z3(cond), eto_z3(choice1), eto_z3(choice2));
        return z3expr(res);
    }
    SMTExpr Z3Solver::createEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        expr res = eto_z3(lhs) == eto_z3(rhs);
        return z3expr(res);
    }

    SMTExpr Z3Solver::createGtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // WARNING: default > is signed. Use unsigned!
        expr res = z3::ugt(eto_z3(lhs), eto_z3(rhs));
        return z3expr(res);
    }
    SMTExpr Z3Solver::createGEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // WARNING: default >= is signed. Use unsigned!
        expr res = z3::uge(eto_z3(lhs), eto_z3(rhs));
        return z3expr(res);
    }
    SMTExpr Z3Solver::createLtExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // WARNING: default < is signed. Use unsigned!
        expr res = z3::ult(eto_z3(lhs), eto_z3(rhs));
        return z3expr(res);
    }
    SMTExpr Z3Solver::createLEqExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        // WARNING: default <= is signed. Use unsigned!
        expr res = z3::ule(eto_z3(lhs), eto_z3(rhs));
        return z3expr(res);
    }

    SMTExpr Z3Solver::createImplExpr(const SMTExpr& lhs, const SMTExpr& rhs) {
        expr res = implies(eto_z3(lhs), eto_z3(rhs));
        return z3expr(res);
    }

    SMTExpr Z3Solver::createBitSet(const SMTExpr& container, unsigned int ith, const SMTExpr& value) {
        expr bit = eto_z3(container).extract(ith, ith);

//            log->info("bit: {}; value: {}", bit.get_sort(), bit);
        expr bv_value = ite(eto_z3(value),
                               context.bv_val(0, 1),
                               context.bv_val(1, 1));
//            log->info("bv_value: {}; value: {}", bv_value.get_sort(), bv_value);
        expr res = bit == bv_value;
//            log->info("res: {}; value: {}", res.get_sort(), res);
        return z3expr(res);
    }
    SMTExpr Z3Solver::createDistinct(std::list<SMTExpr>& exprs) {
        expr_vector z3_exps(this->context);

        for (auto &&expr : exprs) {
            z3_exps.push_back(eto_z3(expr));
        }
        expr res = z3::distinct(z3_exps);
        return z3expr(res);
    }

    SMTExpr Z3Solver::joinExprsWithAnd(std::list<SMTExpr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        expr ret = eto_z3(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = ret && eto_z3(*ite);
        }
        return z3expr(ret);
    }
    SMTExpr Z3Solver::joinExprsWithOr(std::list<SMTExpr>& exprs) {
        if (exprs.size() < 1) {
            return createTrue();
//            fprintf(stderr, "Cannot join zero expressions...\n");
//            throw std::runtime_error("Cannot join zero expressions");
        }
        auto ite = exprs.begin();
        expr ret = eto_z3(*ite);
        for (++ite; ite != exprs.end(); ++ite) {
            ret = ret || eto_z3(*ite);
        }
        return z3expr(ret);
    }

    void Z3Solver::assertLater(const SMTExpr& e) {
        if (!fast) {
            solver.add(eto_z3(e));
        } else {
            to_be_asserted.push_back(eto_z3(e));
        }
    }

    void Z3Solver::assertNow(const SMTExpr& e) {
        // printf("%p: ", context);
        // yices_pp_term(stdout, expr, 140, 40, 0);
        solver.add(eto_z3(e));
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
                return SMTResult::SAT;
                break;
            }
            case unsat:
                return SMTResult::UNSAT;
                break;
            case unknown:
                return SMTResult::UNKNOWN;
                break;

            default:
            std::cerr << "Error in check_context" << std::endl;
                break;
        }
        return SMTResult::ERROR;
    }

    void Z3Solver::print_statistics() {
        auto state = this->solver.statistics();
        std::cout << state << std::endl;
    }
    void Z3Solver::printExpr(const SMTExpr& e) {
        std::cout << e << std::endl;
    }
    std::string Z3Solver::exprValueAsString(const SMTExpr& expr) {
        extract_model();

        std::stringstream fmt;
        z3::expr value = model->eval(eto_z3(expr), false);
        fmt << value;
        return fmt.str();
    }
    int Z3Solver::exprValueAsInt(const SMTExpr& expr) {
        extract_model();

        z3::expr value = model->eval(eto_z3(expr), false);

        // Not a numeral? Let's not try to convert it
        if(Z3_get_ast_kind(this->context, value) != Z3_NUMERAL_AST) {
            return (int) get_bool_value(expr);
        }

        int val = std::stoi(Z3_get_numeral_decimal_string(this->context, value, 64));
        return val;
    }
    void Z3Solver::printModel() {
        extract_model();
        std::cout << *model << std::endl;
    }

    bool Z3Solver::get_bool_value(const SMTExpr& expr) {
        extract_model();
        try {
            z3::expr res = model->eval(eto_z3(expr), false);
            return Z3_get_bool_value(this->context, res) == Z3_L_TRUE;
        } catch (z3::exception &e) {
            // No model value
            log->critical("Cannot extract z3 value from {}", expr);
            throw std::runtime_error("Cannot extract z3 value");
        }
    }

//    unsigned int Z3Solver::get_bv_value(z3::expr expr) {
//        extract_model();
//        try {
//            z3::expr res = model->eval(expr, false);
//            return Z3_get_bool_value(this->context, res) == Z3_L_TRUE;
//        } catch (z3::exception &e) {
//            // No model value
//            log->critical("Cannot extract z3 value from {}", expr);
//            throw std::runtime_error("Cannot extract z3 value");
//        }
//    }

    void Z3Solver::loadToSolver() {
        if (fast) {
            if (to_be_asserted.empty()) {
                return;
            } else {
                auto ite = to_be_asserted.begin();
                z3::expr body = *ite;
                for (++ite; ite != to_be_asserted.end(); ++ite) {
                    body = body && *ite;
                }
                solver.add(body);
                // yices_pp_term(stderr, body, 120, 40, 0);
                this->to_be_asserted.clear();
            }
        }
    }

    void Z3Solver::clean() {
        //TODO: both var_counter and context should be cleaned
        this->model = nullptr;
        this->solver = z3::solver(context, "QF_BV");
    }
    void Z3Solver::deep_clean() {
        var_counter = 0;
        to_be_asserted.clear();
        //FIXME: nondtext should be regenerated
        /*delete context;
        context = new z3::context();*/
        this->model = nullptr;
        this->solver = z3::solver(context, "QF_BV");
    }
    void Z3Solver::printContext() {
        std::cout << this->solver << std::endl;
    }
    void Z3Solver::printContext(std::string filename) {
        std::ofstream myfile;
        myfile.open(filename);
        myfile << "; " << get_timestamp() << std::endl << std::endl;
        myfile << this->solver << std::endl << std::endl;
        myfile << "(check-sat)" << std::endl;
        myfile << "(get-model)" << std::endl << std::endl;
        myfile.close();
    }

    void Z3Solver::extract_model() {
        bool error = false;
        try {
            model = std::make_shared<z3::model>(solver.get_model());
            if (model == nullptr) {
                error = true;
            }
        } catch (z3::exception e) {
            error = true;
        }
        if (error) {
            throw std::runtime_error("Z3 model is NULL...");
        }
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