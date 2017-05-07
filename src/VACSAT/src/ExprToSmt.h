////
//// Created by esteffin on 27/04/17.
////
//
//#ifndef VACSAT_EXPRTOSMT_H
//#define VACSAT_EXPRTOSMT_H
//
//#include "Logics.h"
//#include "SMTSolvers/Z3.h"
//#include "SMTSolvers/yices.h"
//#include <sstream>
//
//using namespace SMT;
//
////    template <typename TVar>
////    struct TVarWrapper {
////    public:
////        TVarWrapper(std::shared_ptr<TVar> _solver_varp) : solver_varp(_solver_varp) { }
////
////        inline TVar get_solver_var() {
////            if (solver_varp == nullptr)
////                throw new std::runtime_error("Null variable");
////            else {
////                return *solver_varp;
////            }
////        }
////
////        std::shared_ptr<TVar> solver_varp;
////    };
//
////    template <typename TVar, typename TLookup>
////    TLookup update_tlookup(const TLookup& base_lookup, const TLookup& new_lookup);
////
////    template <typename TVar>
////    std::map<std::string, TVar> update_tlookup(const std::map<std::string, TVar>& base_lookup,
////                                               const std::map<std::string, TVar>& new_lookup) {
////        std::map<std::string, TVar> res(base_lookup);
////
////        for (auto ite = new_lookup.begin(); ite != new_lookup.end(); ++ite) {
////            res[ite->first] = ite->second;
////        }
////        return res;
////    };
////
////    template <typename TVar>
////    std::vector<std::shared_ptr<TVar>> update_tlookup(const std::vector<std::shared_ptr<TVar>>& base_lookup,
////                                                      const std::vector<std::shared_ptr<TVar>>& new_lookup) {
////        if (base_lookup.size() != new_lookup.size()) {
////            std::cerr << "Cannot update vector of different size." << std::endl;
////            throw new std::runtime_error("Cannot update vector of different size.");
////        }
////        std::vector<std::shared_ptr<TVar>> res(base_lookup);
////
////        for (int i = 0; i < new_lookup.size(); ++i) {
////            res[i] = new_lookup[i];
////        }
////        return res;
////    };
////
////    template <typename TVar, typename TExpr, typename TLookup>
////    TExpr
////    generateSMTFunction2(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Expr& expr, TLookup& lookup,
////                        std::string& suffix);
////
////
////
////    template <typename TVar, typename TExpr, typename TLookup>
////    TExpr literalToSMT(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Literalp& lit, TLookup& lookup,
////                       std::string& suffix);
////
////    template <typename TVar, typename TExpr>
////    TExpr literalToSMT(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Literalp& lit,
////                       std::vector<std::shared_ptr<TExpr>>& var_vector,
////                       std::string& suffix) {
////        if (lit->value == nullptr) {
////            std::string name = lit->nameWithSuffix(suffix);
////            if (var_vector[lit->role_array_index] != nullptr) {
////                return var_vector[lit->role_array_index];
////            }
////            else {
////                TVar var = solver->createVar2(name, lit->bv_size);
////                var_vector[lit->role_array_index] = std::make_shared<TVar>(var);
////                // printf("%s not found. Creating it: %d\n", name.c_str(), var);
////                return var;
////            }
////        }
////        else {
////            return generateSMTFunction(solver, lit->value, var_vector, suffix);
////        }
////    }
////
////    template <typename TVar, typename TExpr>
////    TExpr literalToSMT(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Literalp& lit,
////                       std::map<std::string, TVar>& var_map,
////                       std::string& suffix) {
////        if (lit->value == nullptr) {
////            std::string name = lit->nameWithSuffix(suffix);
////            if(var_map.find(name) != var_map.end()) {
////                return var_map[name];
////            }
////            else {
////                TVar var = solver->createVar2(name, lit->bv_size);
////                var_map[name] = var;
////                // printf("%s not found. Creating it: %d\n", name.c_str(), var);
////                return var;
////            }
////        }
////        else {
////            return generateSMTFunction(solver, lit->value, var_map, suffix);
////        }
////    }
////
////    template <typename TVar, typename TExpr, typename TWrapper>
////    TExpr literalToSMT(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Literalp& lit,
////                       std::vector<TWrapper>& var_vector,
////                       std::string& suffix) {
////        static_assert(std::is_base_of<TVarWrapper<TVar>, TWrapper>::value, "TWrapper not derived from TWrapper<TVar>");
////
////        if (lit->value == nullptr) {
////            std::string name = lit->nameWithSuffix(suffix);
////            if (var_vector[lit->role_array_index].solver_varp != nullptr) {
////                return *var_vector[lit->role_array_index].solver_varp;
////            } else {
////                std::stringstream fmt;
////                fmt << "Error in literalToSMT with vector<TWrapper>." << std::endl;
////                fmt << "Lookup table does not contain item with index " << lit->role_array_index
////                    << " and could not be instantiated.";
////                throw new std::runtime_error(fmt.str());
////            }
////        } else {
////            return generateSMTFunction(solver, lit->value, var_vector, suffix);
////        }
////
////    }
////
////
//////    template <typename TVar, typename TExpr>
//////    TExpr literalToSMT<std::map<std::string, TVar>>(std::shared_ptr<SMTFactory<TVar, TExpr>> solver, Literalp lit, std::map<std::string, TVar>& var_map, std::string suffix) {
//////        if (lit->value == nullptr) {
//////            std::string name = lit->nameWithSuffix(suffix);
//////            if(var_map.find(name) != var_map.end()) {
//////                return var_map[name];
//////            }
//////            else {
//////                TVar var = solver->createVar2(name, lit->bv_size);
//////                var_map[name] = var;
//////                // printf("%s not found. Creating it: %d\n", name.c_str(), var);
//////                return var;
//////            }
//////        }
//////        else {
//////            return generateSMTFunction(solver, lit->value, var_map, suffix);
//////        }
//////    };
////
////    template <typename TVar, typename TExpr, typename TLookup>
////    TExpr generateSMTFunction2(std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, Expr& expr, TLookup& lookup,
////                              std::string&& suffix) {
////        switch (expr->type) {
////            case Exprv::CONSTANT: {
////                std::shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(expr);
////                if (c->bv_size == 1) {
////                    return solver->createBoolConst(c->value);
////                } else {
////                    return solver->createBVConst(c->value, c->bv_size);
////                }
////            }
////            case Exprv::LITERAL: {
////                Literalp lit = std::dynamic_pointer_cast<Literal>(expr);
////                return literalToSMT<TVar, TExpr, TLookup>(solver, lit, lookup, suffix);
////
////            }
////            case Exprv::AND_EXPR: {
////                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
////                TExpr slhs = generateSMTFunction2(solver, andExpr->lhs, lookup, suffix);
////                TExpr srhs = generateSMTFunction2(solver, andExpr->rhs, lookup, suffix);
////                return solver->createAndExpr(slhs, srhs);
////            }
////            case Exprv::OR_EXPR: {
////                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
////                TExpr slhs = generateSMTFunction2(solver, orExpr->lhs, lookup, suffix);
////                TExpr srhs = generateSMTFunction2(solver, orExpr->rhs, lookup, suffix);
////                return solver->createOrExpr(slhs, srhs);
////            }
////            case Exprv::IMPL_EXPR: {
////                std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
////                TExpr slhs = generateSMTFunction2(solver, implExpr->lhs, lookup, suffix);
////                TExpr srhs = generateSMTFunction2(solver, implExpr->rhs, lookup, suffix);
////                return solver->createImplExpr(slhs, srhs);
////            }
////            case Exprv::COND_EXPR: {
////                std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
////                TExpr scond = generateSMTFunction2(solver, condExpr->cond, lookup, suffix);
////                TExpr schoice1 = generateSMTFunction2(solver, condExpr->choice1, lookup, suffix);
////                TExpr schoice2 = generateSMTFunction2(solver, condExpr->choice2, lookup, suffix);
////                return solver->createCondExpr(scond, schoice1, schoice2);
////            }
////            case Exprv::EQ_EXPR: {
////                std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
////                TExpr slhs = generateSMTFunction2(solver, eqExpr->lhs, lookup, suffix);
////                TExpr srhs = generateSMTFunction2(solver, eqExpr->rhs, lookup, suffix);
////                return solver->createEqExpr(slhs, srhs);
////            }
////            case Exprv::NOT_EXPR: {
////                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
////                TExpr sexpr = generateSMTFunction2(solver, notExpr->expr, lookup, suffix);
////                return solver->createNotExpr(sexpr);
////            }
////            default:
////                break;
////        }
////        throw new std::runtime_error("Cannot translate expression to SMT");
////        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
////    }
//
//
//#endif //VACSAT_EXPRTOSMT_H
