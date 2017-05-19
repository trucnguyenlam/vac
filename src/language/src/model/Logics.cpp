#include "Logics.h"

#include <iostream>
#include <sstream>
#include <chrono>
#include <regex>
#include <stdexcept>
#include <assert.h>
#include <algorithm>
#include <utility>


namespace Parser {

    template <typename T>
    std::set<T> setUnion(const std::set<T>& a, const std::set<T>& b) {
        std::set<T> result = a;
        result.insert(b.begin(), b.end());
        return result;
    }

/*DEFS*/
    constexpr char Defs::line_end[];
    constexpr char Defs::and_op[];
    constexpr char Defs::or_op[];
    constexpr char Defs::not_op[];
    constexpr char Defs::assign_op[];
    constexpr char Defs::eq_op[];
    constexpr char Defs::impl_op[];
    constexpr char Defs::open_comment[];
    constexpr char Defs::assume_str[];
    constexpr char Defs::assert_str[];
    constexpr char Defs::nondet_str[];
    constexpr char Defs::int_ty_str[];
    constexpr char Defs::bool_ty_str[];
    constexpr char Defs::true_str[];
    constexpr char Defs::false_str[];

/*SMT*/
    constexpr char SMTKeyword::comment[];
    constexpr char SMTKeyword::and_op[];
    constexpr char SMTKeyword::or_op[];
    constexpr char SMTKeyword::not_op[];
    constexpr char SMTKeyword::eq_op[];
    constexpr char SMTKeyword::declare[];
    constexpr char SMTKeyword::cond_expr[];
    constexpr char SMTKeyword::assume[];
    constexpr char SMTKeyword::assert[];
    constexpr char SMTKeyword::check[];
    constexpr char SMTKeyword::nondet_str[];
    constexpr char SMTKeyword::int_ty_str[];
    constexpr char SMTKeyword::bool_ty_str[];
    constexpr char SMTKeyword::true_str[];
    constexpr char SMTKeyword::false_str[];

    std::string SMTKeyword::bv_ty_str(int bv_size) {
        std::stringstream fmt;
        fmt << "(_ BitVec " << bv_size << ")";
        return fmt.str();
    }

/*EXPR OPS*/
    Exprv::Exprv(ExprType ty, std::set<Literalp> literals) : type(ty), _literals(literals) { }

    bool Exprv::containsLiteral(std::string full_name) {
        for (auto ite = _literals.begin(); ite != _literals.end(); ++ite) {
            if ((*ite)->fullName() == full_name)
                return true;
        }
        return false;
    }
    bool Exprv::containsLiteral(Literalp lit) {
        return this->_literals.count(lit) > 0;
    }
    void Exprv::setSuffix(std::string suffix) {
        auto lits = this->literals();
        for (std::set<Literalp>::iterator ite = lits.begin(); ite != lits.end(); ++ite) {
            Literalp lit = *ite;
            lit->setSuffix(suffix);
        }
    }
    void Exprv::setSuffix(int idx) {
        this->setSuffix(std::to_string(idx));
    }
    void Exprv::resetSuffix() {
        auto lits = this->literals();
        for (std::set<Literalp>::iterator ite = lits.begin(); ite != lits.end(); ++ite) {
            Literalp lit = *ite;
            lit->resetSuffix();
        }
    }

    void Exprv::setLiteralValue(Literalp lit, Expr value) {
        lit->setValue(value);
    }

    void Exprv::setLiteralValue(std::string lit_name, Expr value) {
        auto lits = this->literals();
        for (std::set<Literalp>::iterator ite = lits.begin(); ite != lits.end(); ++ite) {
            Literalp lit = *ite;
            if (lit->name == lit_name) {
                lit->setValue(value);
            }
        }
    }
    void Exprv::resetValue(std::string lit_name) {
        auto lits = this->literals();
        for (std::set<Literalp>::iterator ite = lits.begin(); ite != lits.end(); ++ite) {
            Literalp lit = *ite;
            if (lit_name == "" || lit_name == lit->name) {
                lit->resetValue();
            }
        }
    }

    std::ostream & operator<<(std::ostream & out, Exprv const & expr) {
        out << expr.to_string();

        return out;
    }

    std::set<Literalp> Exprv::literals() {
        return this->_literals;
    }

/*LITERAL OPS*/
    Literal::Literal(const std::string _name, int _role_array_index, int _bv_size, Expr _value):
        Exprv(Exprv::LITERAL, std::set<Literalp>()),
        name(_name), role_array_index(_role_array_index), bv_size(_bv_size), value(_value) { }

    void Literal::setLiterals(Literalp &self) {
        this->_literals.insert(self);
    }
    void Literal::setSuffix(std::string suffix) {
        this->suffix = suffix;
    }
    void Literal::setSuffix(int index) {
        this->setSuffix(std::to_string(index));
    }
    void Literal::resetSuffix() {
        this->suffix = "";
    }
    void Literal::setValue(Expr value) {
        this->value = value;
    }
    void Literal::resetValue() {
        this->value = nullptr;
    }
    std::string Literal::getSMTName() const {
        return this->fullName();
    }

    std::string Literal::fullName() const {
        if (this->suffix == "") {
            return this->name;
        }
        else {
            std::stringstream fmt;
            fmt << this->name + "_" + this->suffix;
            return fmt.str();
        }
    }

    std::string Literal::nameWithSuffix(std::string suffix) const {
        if (this->suffix == "") {
            return this->fullName() + "_" + suffix;
        }
        else {
            std::stringstream fmt;
            fmt << this->name + "_" + this->suffix;
            return fmt.str();
        }
    }

    std::string Literal::to_string() const {
        std::stringstream fmt;
        // fmt << "|" << this->fullName() << "|";
        fmt << this->fullName();
        return fmt.str();
    }

/*CONSTANT OPS*/
    Constant::Constant(int _value, int _bv_size) :
        Exprv(Exprv::CONSTANT, std::set<Literalp>()),
        value(_value), bv_size(_bv_size) { }

    std::string Constant::to_string() const {
        if (this->bv_size == 1) {
            if (this->value) {
                return Defs::true_str;
            }
            else {
                return Defs::false_str;
            }
        }
        else {
            std::stringstream fmt;
            fmt << this->value;
            return fmt.str();
        }
    }

/*OR OPS*/
    OrExpr::OrExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::OR_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }

    std::string OrExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::or_op << rhsv << ")";
        return fmt.str();
    }

/*AND OPS*/
    AndExpr::AndExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::AND_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }

    std::string AndExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::and_op << rhsv << ")";
        return fmt.str();
    }

/*EQ OPS*/
    EqExpr::EqExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::EQ_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }

    std::string EqExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::eq_op << rhsv << ")";
        return fmt.str();
    }

/*IMPLICATION OPS*/
    ImplExpr::ImplExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::IMPL_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }

    std::string ImplExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::impl_op << rhsv << ")";
        return fmt.str();
    }

/*NOT OPS*/
    NotExpr::NotExpr(Expr _expr) :
        Exprv(Exprv::NOT_EXPR, _expr->literals()),
        expr(_expr) { }

    std::string NotExpr::to_string() const {
        std::stringstream fmt;
        std::string exprv = this->expr->to_string();
        fmt << Defs::not_op << "(" << exprv << ")";
        return fmt.str();
    }

/*COND OPS*/
    CondExpr::CondExpr(Expr _cond, Expr _choice1, Expr _choice2) :
        Exprv(Exprv::COND_EXPR,
              setUnion(_cond->literals(), setUnion(_choice1->literals(), _choice2->literals()))),
        cond(_cond), choice1(_choice1), choice2(_choice2) { }

    std::string CondExpr::to_string() const {
        std::stringstream fmt;
        std::string cond = this->cond->to_string();
        std::string ch1 = this->choice1->to_string();
        std::string ch2 = this->choice2->to_string();
        fmt << "((" << cond << ") ? (" << ch1 << ") : (" << ch2 << "))";
        return fmt.str();
    }

/*SIMPLIFICATION OPS*/
    // Simplifier::Simplifier(SimplLevel _level) : level(_level) { }

    // void Simplifier::simplifyStmt(Stmt stmt) {
    //     switch (stmt->type) {
    //         case Stmtv::ASSERT:
    //             this->simplifyAssertion(std::dynamic_pointer_cast<Assertion>(stmt));
    //             break;
    //         case Stmtv::ASSUME:
    //             this->simplifyAssumption(std::dynamic_pointer_cast<Assumption>(stmt));
    //             break;
    //         case Stmtv::ASSIGNMENT:
    //             this->simplifyAssignment(std::dynamic_pointer_cast<Assignment>(stmt));
    //             break;
    //         case Stmtv::COMMENT:
    //             break;
    //         case Stmtv::OUTPUT:
    //             break;
    //     }
    // }

    // Expr Simplifier::simplifyExpr(Expr expr) {
    //     switch (expr->type) {
    //         case Exprv::CONSTANT:
    //             // CAN REMOVED SINCE IS ID
    //             return simplifyConstant(std::dynamic_pointer_cast<Constant>(expr));
    //         case Exprv::VARIABLE:
    //             return simplifyVariable(std::dynamic_pointer_cast<Variable>(expr));
    //         case Exprv::EQ_EXPR:
    //             return simplifyEqExpr(std::dynamic_pointer_cast<EqExpr>(expr));
    //         case Exprv::NOT_EXPR:
    //             return simplifyNotExpr(std::dynamic_pointer_cast<NotExpr>(expr));
    //         case Exprv::OR_EXPR:
    //             return simplifyOrExpr(std::dynamic_pointer_cast<OrExpr>(expr));
    //         case Exprv::AND_EXPR:
    //             return simplifyAndExpr(std::dynamic_pointer_cast<AndExpr>(expr));
    //         case Exprv::COND_EXPR:
    //             return simplifyCondExpr(std::dynamic_pointer_cast<CondExpr>(expr));
    //         case Exprv::NONDET_EXPR:
    //             return expr;
    //         default:
    //             break;
    //     }
    //     // return expr;
    // }

    // int Simplifier::canInline(Expr expr) {
    //     switch (this->level) {
    //         //WARNING: Switch without break to fall in previous cases
    //         case ALL:
    //             return true;
    //         case EQUALITY:
    //             if (expr->type == Exprv::EQ_EXPR) {
    //                 return true;
    //             }
    //         case LBIN_OPS:
    //             if (expr->type == Exprv::OR_EXPR || expr->type == Exprv::AND_EXPR) {
    //                 return true;
    //             }
    //         case UN_OPS:
    //             if (expr->type == Exprv::NOT_EXPR) {
    //                 return true;
    //             }
    //         case CONST_VARS:
    //             if (expr->type == Exprv::CONSTANT || expr->type == Exprv::VARIABLE) {
    //                 return true;
    //             }
    //         case NOTHING:
    //             return false;
    //     }
    //     return false;
    // }
    // void Simplifier::simplifyAssignment(shared_ptr<Assignment> assignment) {
    //     //TODO: put here redundancy after simplification check
    //     Expr nval = this->simplifyExpr(assignment->variable->value);

    //     assignment->value = nval;
    //     assignment->variable->value = nval;
    //     assignment->variable->_inline = assignment->variable->_inline && canInline(nval);

    // }
    // void Simplifier::simplifyAssertion(shared_ptr<Assertion> assertion) {
    //     //TODO: put here redundancy after simplification check
    //     Expr nval = this->simplifyExpr(assertion->assertion);
    //     assertion->assertion = nval;
    // }
    // void Simplifier::simplifyAssumption(shared_ptr<Assumption> assumption) {
    //     //TODO: put here redundancy after simplification check
    //     Expr nval = this->simplifyExpr(assumption->assumption);
    //     assumption->assumption = nval;
    // }

    // Expr Simplifier::simplifyVariable(shared_ptr<Variable> var) {
    //     if (!var->_inline) {
    //         return var;
    //     }
    //     Expr res = var->value;
    //     while (res->type == Exprv::VARIABLE && std::dynamic_pointer_cast<Variable>(res)->_inline) {
    //         res = std::dynamic_pointer_cast<Variable>(res)->value;
    //     }
    //     return res;
    // }
    // Expr Simplifier::simplifyConstant(shared_ptr<Constant> expr) {
    //     //TODO: could be removed
    //     return expr;
    // }
    // Expr Simplifier::simplifyOrExpr(shared_ptr<OrExpr> or_expr) {
    //     Expr nlhs, nrhs;
    //     nlhs = simplifyExpr(or_expr->lhs);
    //     if (nlhs->type == Exprv::CONSTANT) {
    //         int v = (std::dynamic_pointer_cast<Constant>(nlhs))->value;
    //         if (v) {
    //             return nlhs;
    //         }
    //         else {
    //             return simplifyExpr(or_expr->rhs);
    //         }
    //     }
    //     nrhs = simplifyExpr(or_expr->rhs);
    //     if (nrhs->type == Exprv::CONSTANT) {
    //         if ((std::dynamic_pointer_cast<Constant>(nrhs))->value) {
    //             return std::dynamic_pointer_cast<Constant>(nrhs);
    //         }
    //         else {
    //             return nlhs;
    //         }
    //     }
    //     return createOrExpr(nlhs, nrhs);
    // }
    // Expr Simplifier::simplifyAndExpr(shared_ptr<AndExpr> and_expr) {
    //     Expr nlhs, nrhs;
    //     nlhs = simplifyExpr(and_expr->lhs);
    //     if (nlhs->type == Exprv::CONSTANT) {
    //         int v = std::dynamic_pointer_cast<Constant>(nlhs)->value;
    //         if (!v) {
    //             return nlhs;
    //         }
    //         else {
    //             return simplifyExpr(and_expr->rhs);
    //         }
    //     }
    //     nrhs = simplifyExpr(and_expr->rhs);
    //     if (nrhs->type == Exprv::CONSTANT) {
    //         if (!(std::dynamic_pointer_cast<Constant>(nrhs)->value)) {
    //             return nrhs;
    //         }
    //         else {
    //             return nlhs;
    //         }
    //     }
    //     return createAndExpr(nlhs, nrhs);
    // }
    // Expr Simplifier::simplifyEqExpr(shared_ptr<EqExpr> expr) {
    //     //TODO: COULD BE IMPROVED
    //     Expr nlhs = simplifyExpr(expr->lhs);
    //     Expr nrhs = simplifyExpr(expr->rhs);

    //     if (nlhs == nrhs) {
    //         return createConstantExpr(1, 1);
    //     }

    //     if (nlhs->type == Exprv::CONSTANT && nrhs->type == Exprv::CONSTANT) {
    //         std::shared_ptr<Constant> nl = std::dynamic_pointer_cast<Constant>(nlhs);
    //         std::shared_ptr<Constant> nr = std::dynamic_pointer_cast<Constant>(nrhs);
    //         return createConstantExpr(nl->value == nr->value, 1);
    //     }

    //     return createEqExpr(nlhs, nrhs);

    // }
    // Expr Simplifier::simplifyNotExpr(shared_ptr<NotExpr> not_expr) {
    //     Expr nexpr = simplifyExpr(not_expr->expr);
    //     if (nexpr->type == Exprv::CONSTANT) {
    //         return createConstantExpr(!(std::dynamic_pointer_cast<Constant>(nexpr))->value, 1);
    //     }
    //     if (nexpr->type == Exprv::NOT_EXPR) {
    //         return std::dynamic_pointer_cast<NotExpr>(nexpr)->expr;
    //     }
    //     return createNotExpr(nexpr);
    // }
    // Expr Simplifier::simplifyCondExpr(shared_ptr<CondExpr> cond_expr) {
    //     Expr ncond = simplifyExpr(cond_expr->cond);
    //     // If condition is true or false return the selected branch simplified...
    //     if (ncond->type == Exprv::CONSTANT) {
    //         if ((std::dynamic_pointer_cast<Constant>(ncond))->value) {
    //             return simplifyExpr(cond_expr->choice1);
    //         }
    //         else {
    //             return simplifyExpr(cond_expr->choice2);
    //         }
    //     }

    //     Expr nch1 = simplifyExpr(cond_expr->choice1);
    //     Expr nch2 = simplifyExpr(cond_expr->choice2);
    //     // If simplified branches are equals simplify removing conditional expression and return it
    //     if (nch1 == nch2) {
    //         //TODO: Reference comparison!?!
    //         return nch1;
    //     }

    //     // If branches are 1, 0 or 0, 1 replace conditional expression with guard or negation of it respectively
    //     if (nch1->type == Exprv::CONSTANT && nch2->type == Exprv::CONSTANT) {
    //         std::shared_ptr<Constant> nc2 = std::dynamic_pointer_cast<Constant>(nch2);
    //         std::shared_ptr<Constant> nc1 = std::dynamic_pointer_cast<Constant>(nch1);
    //         if (nc1->value == 0 && nc2->value == 1) {
    //             return createNotExpr(ncond);
    //         }
    //         if (nc1->value == 1 && nc2->value == 0) {
    //             return ncond;
    //         }
    //     }
    //     // Otherwise return the simplified conditional expression.
    //     return createCondExpr(ncond, nch1, nch2);
    // }
    // // Expr Simplifier::simplifyNondetExpr(shared_ptr<NondetExpr> nondet_expr) {
    // //     return nondet_expr;
    // // }



/*OTHER OPS*/
    Literalp createLiteralp(const std::string name, int role_array_index, int bv_size, Expr value) {
        std::shared_ptr<Literal> res(new Literal(name, role_array_index, bv_size, value));
        res->setLiterals(res);
        return res;
    }

    Expr createLiteralExpr(const std::string name, int role_array_index, int bv_size, Expr value) {
        return std::shared_ptr<Exprv>(new Literal(name, role_array_index, bv_size, value));
    }
    Expr createConstantExpr(int value, int bv_size) {
        return std::shared_ptr<Exprv>(new Constant(value, bv_size));
    }
    Expr createConstantTrue() {
        return createConstantExpr(true, 1);
    }
    Expr createConstantFalse() {
        return createConstantExpr(false, 1);
    }
    Expr createOrExpr(Expr lhs, Expr rhs) {
        return std::shared_ptr<Exprv>(new OrExpr(lhs, rhs));
    }
    Expr createAndExpr(Expr lhs, Expr rhs) {
        return std::shared_ptr<Exprv>(new AndExpr(lhs, rhs));
    }
    Expr createEqExpr(Expr lhs, Expr rhs) {
        return std::shared_ptr<Exprv>(new EqExpr(lhs, rhs));
    }
    Expr createImplExpr(Expr lhs, Expr rhs) {
        return std::shared_ptr<Exprv>(new ImplExpr(lhs, rhs));
    }
    Expr createNotExpr(Expr expr) {
        return std::shared_ptr<Exprv>(new NotExpr(expr));
    }
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2) {
        return std::shared_ptr<Exprv>(new CondExpr(cond, choice1, choice2));
    }
    // Expr createNondetExpr(VarType type) {
    //     return std::shared_ptr<Exprv>(new NondetExpr(type));
    // }

    Expr normalize_expr(Expr expr) {
        switch (expr->type) {
            case Exprv::CONSTANT: {
                return expr;
            }
            case Exprv::LITERAL: {
                return expr;
            }
            case Exprv::AND_EXPR: {
                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                Expr nlhs = normalize_expr(andExpr->lhs);
                Expr nrhs = normalize_expr(andExpr->rhs);
                return createAndExpr(nlhs, nrhs);
            }
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                Expr nlhs = normalize_expr(orExpr->lhs);
                Expr nrhs = normalize_expr(orExpr->rhs);
                return createOrExpr(nlhs, nrhs);
            }
            case Exprv::NOT_EXPR:{
                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                Expr inner = notExpr->expr;
                switch (inner->type) {
                    case Exprv::AND_EXPR: {
                        std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(inner);
                        Expr nlhs = normalize_expr(createNotExpr(andExpr->lhs));
                        Expr nrhs = normalize_expr(createNotExpr(andExpr->rhs));
                        return createOrExpr(nlhs, nrhs);
                    }
                    case Exprv::OR_EXPR: {
                        std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(inner);
                        Expr nlhs = normalize_expr(createNotExpr(orExpr->lhs));
                        Expr nrhs = normalize_expr(createNotExpr(orExpr->rhs));
                        return createAndExpr(nlhs, nrhs);
                    }
                    case Exprv::NOT_EXPR: {
                        std::shared_ptr<NotExpr> inner_not = std::dynamic_pointer_cast<NotExpr>(inner);
                        Expr nexpr = normalize_expr(inner_not);
                        return nexpr;
                    }
                    default:
                        return notExpr;
                }
            }
//            case Exprv::IMPL_EXPR: {
//                std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
//                TExpr slhs = generateSMTFunction(solver, implExpr->lhs, var_array, suffix);
//                TExpr srhs = generateSMTFunction(solver, implExpr->rhs, var_array, suffix);
//                return solver->createImplExpr(slhs, srhs);
//            }
//            case Exprv::COND_EXPR: {
//                std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
//                TExpr scond = generateSMTFunction(solver, condExpr->cond, var_array, suffix);
//                TExpr schoice1 = generateSMTFunction(solver, condExpr->choice1, var_array, suffix);
//                TExpr schoice2 = generateSMTFunction(solver, condExpr->choice2, var_array, suffix);
//                return solver->createCondExpr(scond, schoice1, schoice2);
//            }
//            case Exprv::EQ_EXPR: {
//                std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
//                TExpr slhs = generateSMTFunction(solver, eqExpr->lhs, var_array, suffix);
//                TExpr srhs = generateSMTFunction(solver, eqExpr->rhs, var_array, suffix);
//                return solver->createEqExpr(slhs, srhs);
//            }
            default:
                fprintf(stderr, "Could not normalize an expression that is not an OR, AND, NOT, CONSTANT, LITERAL.\n\tExpr is %s",
                        expr->to_string().c_str());
                throw new std::runtime_error("Could not normalize this expression");
                return expr;
        }
        throw new std::runtime_error("Cannot translate expression to SMT");
        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    }


    // Variable* createConstVar(const char* var_name, int occ, int value) {
    //     Expr var_e = createVariable(var_name, occ, 0, NULL);
    //     Variable* var = (Variable*)var_e->value;
    //     Stmt res = createAssignment(var, createConstant(value));
    //     free(var_e);
    //     return res;
    // }

    // Stmt createAssign(const char* var_name, int occ, Expr value) {
    //     Expr var_e = createVariable(var_name, occ, 0, NULL);
    //     Variable* var = (Variable*)var_e->value;
    //     Stmt res = createAssignment(var, value);
    //     free(var_e);
    //     return res;
    // }
/*TRANSLATION FUNCTION*/
    // template <typename TVar, typename TExpr>
    // TExpr generateSMTFunction(std::shared_ptr<SMTFactory<TVar, TExpr>> solver, Expr expr, std::map<std::string, TVar> var_map, std::string suffix) {
    //     switch (expr->type) {
    //         case Exprv::CONSTANT: {
    //             std::shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(expr);
    //             if (c->bv_size == 1) {
    //                 return solver->createBoolConst(c->value);
    //             }
    //             else {
    //                 return solver->createBVConst(c->value, c->bv_size);
    //             }
    //         }
    //         case Exprv::LITERAL: {
    //             Literalp lit = std::dynamic_pointer_cast<Literal>(expr);
    //             if (lit->value == nullptr) {
    //                 std::string name = lit->nameWithSuffix(suffix);
    //                 if(var_map.find(name) != var_map.end()) {
    //                     return var_map[name];
    //                 }
    //                 else {
    //                     TVar var = solver->createVar2(name, lit->bv_size);
    //                     var_map[name] = var;
    //                     // printf("%s not found. Creating it: %d\n", name.c_str(), var);
    //                     return var;
    //                 }
    //             }
    //             else {
    //                 return generateSMTFunction(solver, lit->value, var_map, suffix);
    //             }

    //         }
    //         case Exprv::AND_EXPR: {
    //             std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
    //             TExpr slhs = generateSMTFunction(solver, andExpr->lhs, var_map, suffix);
    //             TExpr srhs = generateSMTFunction(solver, andExpr->rhs, var_map, suffix);
    //             return solver->createAndExpr(slhs, srhs);
    //         }
    //         case Exprv::OR_EXPR: {
    //             std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
    //             TExpr slhs = generateSMTFunction(solver, orExpr->lhs, var_map, suffix);
    //             TExpr srhs = generateSMTFunction(solver, orExpr->rhs, var_map, suffix);
    //             return solver->createOrExpr(slhs, srhs);
    //         }
    //         case Exprv::IMPL_EXPR: {
    //             std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
    //             TExpr slhs = generateSMTFunction(solver, implExpr->lhs, var_map, suffix);
    //             TExpr srhs = generateSMTFunction(solver, implExpr->rhs, var_map, suffix);
    //             return solver->createImplExpr(slhs, srhs);
    //         }
    //         case Exprv::COND_EXPR: {
    //             std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
    //             TExpr scond = generateSMTFunction(solver, condExpr->cond, var_map, suffix);
    //             TExpr schoice1 = generateSMTFunction(solver, condExpr->choice1, var_map, suffix);
    //             TExpr schoice2 = generateSMTFunction(solver, condExpr->choice2, var_map, suffix);
    //             return solver->createCondExpr(scond, schoice1, schoice2);
    //         }
    //         case Exprv::EQ_EXPR: {
    //             std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
    //             TExpr slhs = generateSMTFunction(solver, eqExpr->lhs, var_map, suffix);
    //             TExpr srhs = generateSMTFunction(solver, eqExpr->rhs, var_map, suffix);
    //             return solver->createEqExpr(slhs, srhs);
    //         }
    //         case Exprv::NOT_EXPR:{
    //             std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
    //             TExpr sexpr = generateSMTFunction(solver, notExpr->expr, var_map, suffix);
    //             return solver->createNotExpr(sexpr);
    //         }
    //         default:
    //             break;
    //     }
    //     throw new std::runtime_error("Cannot translate expression to SMT");
    //     fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    // }

}
