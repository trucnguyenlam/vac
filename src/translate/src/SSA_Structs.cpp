#include "SSA_Structs.h"

#include <iostream>
#include <sstream>

#include <assert.h>

namespace SSA {

/*DEFS*/
    constexpr char Defs::line_end[];
    constexpr char Defs::and_op[];
    constexpr char Defs::or_op[];
    constexpr char Defs::not_op[];
    constexpr char Defs::assign_op[];
    constexpr char Defs::eq_op[];
    constexpr char Defs::open_comment[];
    constexpr char Defs::assume_str[];
    constexpr char Defs::assert_str[];
    constexpr char Defs::nondet_str[];
    constexpr char Defs::int_ty_str[];
    constexpr char Defs::bool_ty_str[];
    constexpr char Defs::true_str[];
    constexpr char Defs::false_str[];

/*STMT OPS*/
    Stmtv::Stmtv(StmtType ty) : type(ty) { }

/*ASSIGNMENT OPS*/
    Assignment::Assignment(shared_ptr<Variable> var, Expr val): 
        Stmtv(Stmtv::ASSIGNMENT),
        variable(var), value(val), useless(0) {
    }

    Assignment::Assignment(shared_ptr<Variable> var) :
        Stmtv(Stmtv::ASSIGNMENT),
        variable(var), value(var->value), useless(0) {
    }

    string Assignment::print() {
        std::stringstream fmt;

        string var = this->variable->print();
        string expr = this->value->print();
        if (this->useless) {
            fmt << "/* " << var << Defs::assign_op << expr << Defs::line_end << " */";
        }
        else {
            fmt << var << Defs::assign_op << expr << Defs::line_end;
        }
        return fmt.str();
    }

/*ASSERTION OPS*/
    Assertion::Assertion(Expr cond) :
        Stmtv(Stmtv::ASSERT), 
        assertion(cond) { }
    string Assertion::print() {
        std::stringstream fmt;
        string asserted = this->assertion->print();
        fmt << Defs::assert_str << "(" << asserted << ")" << Defs::line_end;
        return fmt.str();
    }
    
/*ASSUMPTION OPS*/
    Assumption::Assumption(Expr cond) :
        Stmtv(Stmtv::ASSUME), 
        assumption(cond) { }

    string Assumption::print() {
        std::stringstream fmt;
        string assumed = this->assumption->print();
        fmt << Defs::assume_str << "(" << assumed << ")" << Defs::line_end;
        return fmt.str();
    }

/*COMMENT OPS*/
    Comment::Comment(const string _comment) :
        Stmtv(Stmtv::COMMENT), comment(_comment) { }

    string Comment::print() {
        std::stringstream fmt;
        if (this->comment.length() > 0) {
            fmt << "/*" << this->comment << "*/";
            return fmt.str();
        }
        else {
            return "";
        }
    }
    
/*EXPR OPS*/
    Exprv::Exprv(ExprType ty) : type(ty) { } 
    
/*VARIABLE OPS*/
    Variable::Variable(const string _name, int _idx, Expr _value, int _no_simplify):
        Exprv(Exprv::VARIABLE), 
        name(_name), idx(_idx), value(_value), no_simplify(_no_simplify) { }

    string Variable::print() {
        std::stringstream fmt;
        fmt << this->name << "_" << this->idx;
        return fmt.str();
    }
         
/*CONSTANT OPS*/
    Constant::Constant(int _value, VarType _var_type) :
        Exprv(Exprv::CONSTANT),
        value(_value), var_type(_var_type) { }
    
    string Constant::print() {
        if (this->var_type == VarType::BOOL) {
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
        Exprv(Exprv::OR_EXPR),
        lhs(_lhs), rhs(_rhs) { }

    string OrExpr::print() {
        std::stringstream fmt;
        string lhsv = this->lhs->print();
        string rhsv = this->rhs->print();
        fmt << "(" << lhsv << Defs::or_op << rhsv << ")";
        return fmt.str();
    }

/*AND OPS*/
    AndExpr::AndExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::AND_EXPR),
        lhs(_lhs), rhs(_rhs) { }

    string AndExpr::print() {
        std::stringstream fmt;
        string lhsv = this->lhs->print();
        string rhsv = this->rhs->print();
        fmt << "(" << lhsv << Defs::and_op << rhsv << ")";
        return fmt.str();
    }

/*EQ OPS*/
    EqExpr::EqExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::EQ_EXPR),
        lhs(_lhs), rhs(_rhs) { }

    string EqExpr::print() {
        std::stringstream fmt;
        string lhsv = this->lhs->print();
        string rhsv = this->rhs->print();
        fmt << "(" << lhsv << Defs::eq_op << rhsv << ")";
        return fmt.str();
    }
/*NOT OPS*/
    NotExpr::NotExpr(Expr _expr) :
        Exprv(Exprv::NOT_EXPR),
        expr(_expr) { }

    string NotExpr::print() {
        std::stringstream fmt;
        string exprv = this->expr->print();
        fmt << Defs::not_op << "(" << exprv << ")";
        return fmt.str();
    }

/*COND OPS*/
    CondExpr::CondExpr(Expr _cond, Expr _choice1, Expr _choice2) :
        Exprv(Exprv::COND_EXPR),
        cond(_cond), choice1(_choice1), choice2(_choice2) { }

    string CondExpr::print() {
        std::stringstream fmt;
        string cond = this->cond->print();
        string ch1 = this->choice1->print();
        string ch2 = this->choice2->print();
        fmt << "((" << cond << ") ? (" << ch1 << ") : (" << ch2 << "))";
        return fmt.str();
    }

/*NONDET OPS*/
    NondetExpr::NondetExpr(VarType _nondet_type) : 
        Exprv(Exprv::NONDET_EXPR),
        nondet_type(_nondet_type) { }

    string NondetExpr::print() {
        std::stringstream fmt;
        const char* ty_name = this->nondet_type == INT ? Defs::int_ty_str : Defs::bool_ty_str;
        fmt << Defs::nondet_str << ty_name << "()";
        return fmt.str();
    }

/*SIMPLIFICATION OPS*/
    Simplifier::Simplifier(SimplLevel _level) : level(_level) { }

    void Simplifier::simplifyStmt(Stmt stmt) {
        switch (stmt->type) {
            case Stmtv::ASSERT:
                this->simplifyAssertion(std::dynamic_pointer_cast<Assertion>(stmt));
                break;
            case Stmtv::ASSUME:
                this->simplifyAssumption(std::dynamic_pointer_cast<Assumption>(stmt));
                break;
            case Stmtv::ASSIGNMENT:
                this->simplifyAssignment(std::dynamic_pointer_cast<Assignment>(stmt));
                break;
            case Stmtv::COMMENT: 
                break;
            case Stmtv::OUTPUT: 
                break;        
        }
    }

    Expr Simplifier::simplifyExpr(Expr expr) {
        switch (expr->type) {
            case Exprv::CONSTANT:
                // CAN REMOVED SINCE IS ID
                return simplifyConstant(std::dynamic_pointer_cast<Constant>(expr));
            case Exprv::VARIABLE:
                return simplifyVariable(std::dynamic_pointer_cast<Variable>(expr));
            case Exprv::EQ_EXPR:
                return simplifyEqExpr(std::dynamic_pointer_cast<EqExpr>(expr));
            case Exprv::NOT_EXPR:
                return simplifyNotExpr(std::dynamic_pointer_cast<NotExpr>(expr));
            case Exprv::OR_EXPR:
                return simplifyOrExpr(std::dynamic_pointer_cast<OrExpr>(expr));
            case Exprv::AND_EXPR:
                return simplifyAndExpr(std::dynamic_pointer_cast<AndExpr>(expr));
            case Exprv::COND_EXPR:
                return simplifyCondExpr(std::dynamic_pointer_cast<CondExpr>(expr));
            case Exprv::NONDET_EXPR:
                return expr;
            default:
                break;
        }
        // return expr;
    }

    void Simplifier::simplifyAssignment(shared_ptr<Assignment> assignment) {
        //TODO: put here redundancy after simplification check
        Expr nval = this->simplifyExpr(assignment->variable->value);
        assignment->value = nval;
        assignment->variable->value = nval;
    }
    void Simplifier::simplifyAssertion(shared_ptr<Assertion> assertion) {
        //TODO: put here redundancy after simplification check
        Expr nval = this->simplifyExpr(assertion->assertion);
        assertion->assertion = nval;
    }
    void Simplifier::simplifyAssumption(shared_ptr<Assumption> assumption) {
        //TODO: put here redundancy after simplification check
        Expr nval = this->simplifyExpr(assumption->assumption);
        assumption->assumption = nval;
    }

    Expr Simplifier::simplifyVariable(shared_ptr<Variable> var) {
        if (var->no_simplify) {
            return var;
        }
        Expr value = var->value;
        switch (this->level) {
            //WARNING: Switch without break to fall in previous cases
            case ALL:
                return value;
            case EQUALITY:
                if (value->type == Exprv::EQ_EXPR) {
                    return value;
                }
            case LBIN_OPS:
                if (value->type == Exprv::OR_EXPR || value->type == Exprv::AND_EXPR) {
                    return value;
                }
            case UN_OPS:
                if (value->type == Exprv::NOT_EXPR) {
                    return value;
                }
            case CONST_VARS:
                if (value->type == Exprv::CONSTANT) {
                    return value;
                }
                if (value->type == Exprv::VARIABLE) {
                    Variablep var = std::dynamic_pointer_cast<Variable>(value);
                    // assert(!var->no_simplify);
                    return simplifyVariable(var);
                }
            case NOTHING:
                return var;
            default:
                break;
        }
        return var;
    }
    Expr Simplifier::simplifyConstant(shared_ptr<Constant> expr) {
        //FIXME: could be removed
        return expr;
    }
    Expr Simplifier::simplifyOrExpr(shared_ptr<OrExpr> or_expr) {
        Expr nlhs, nrhs;
        nlhs = simplifyExpr(or_expr->lhs);
        if (nlhs->type == Exprv::CONSTANT) {
            int v = (std::dynamic_pointer_cast<Constant>(nlhs))->value;
            if (v) {
                return nlhs;
            }
            else {
                return simplifyExpr(or_expr->rhs);
            }
        }
        nrhs = simplifyExpr(or_expr->rhs);
        if (nrhs->type == Exprv::CONSTANT) {
            if ((std::dynamic_pointer_cast<Constant>(nrhs))->value) {
                return std::dynamic_pointer_cast<Constant>(nrhs);
            }
            else {
                return nlhs;            
            }
        }
        return createOrExpr(nlhs, nrhs);
    }
    Expr Simplifier::simplifyAndExpr(shared_ptr<AndExpr> and_expr) {
        Expr nlhs, nrhs;
        nlhs = simplifyExpr(and_expr->lhs);
        if (nlhs->type == Exprv::CONSTANT) {
            int v = std::dynamic_pointer_cast<Constant>(nlhs)->value;
            if (!v) {
                return nlhs;
            }
            else {
                return simplifyExpr(and_expr->rhs);
            }
        }
        nrhs = simplifyExpr(and_expr->rhs);
        if (nrhs->type == Exprv::CONSTANT) {
            if (!(std::dynamic_pointer_cast<Constant>(nrhs)->value)) {
                return nrhs;
            }
            else {
                return nlhs;
            }
        }
        return createAndExpr(nlhs, nrhs);
    }
    Expr Simplifier::simplifyEqExpr(shared_ptr<EqExpr> expr) {
        //TODO: COULD BE IMPROVED
        Expr nlhs = simplifyExpr(expr->lhs);
        Expr nrhs = simplifyExpr(expr->rhs);

        if (nlhs == nrhs) {
            return createConstantExpr(1);
        }

        if (nlhs->type == Exprv::CONSTANT && nrhs->type == Exprv::CONSTANT) {
            shared_ptr<Constant> nl = std::dynamic_pointer_cast<Constant>(nlhs);
            shared_ptr<Constant> nr = std::dynamic_pointer_cast<Constant>(nrhs);
            return createConstantExpr(nl->value == nr->value);
        }

        return createEqExpr(nlhs, nrhs);
            
    }
    Expr Simplifier::simplifyNotExpr(shared_ptr<NotExpr> not_expr) {
        Expr nexpr = simplifyExpr(not_expr->expr);
        if (nexpr->type == Exprv::CONSTANT) {
            return createConstantExpr(!(std::dynamic_pointer_cast<Constant>(nexpr))->value);
        }
        return createNotExpr(nexpr);
    }
    Expr Simplifier::simplifyCondExpr(shared_ptr<CondExpr> cond_expr) {
        Expr ncond = simplifyExpr(cond_expr->cond);
        // If condition is true or false return the selected branch simplified...
        if (ncond->type == Exprv::CONSTANT) {
            if ((std::dynamic_pointer_cast<Constant>(ncond))->value) {
                return simplifyExpr(cond_expr->choice1);
            }
            else {
                return simplifyExpr(cond_expr->choice2);
            }
        }

        Expr nch1 = simplifyExpr(cond_expr->choice1);
        Expr nch2 = simplifyExpr(cond_expr->choice2);
        // If simplified branches are equals simplify removing conditional expression and return it
        if (nch1 == nch2) {
            //TODO: Reference comparison!?!
            return nch1;
        }

        // If branches are 1, 0 or 0, 1 replace conditional expression with guard or negation of it respectively
        if (nch1->type == Exprv::CONSTANT && nch2->type == Exprv::CONSTANT) {
            shared_ptr<Constant> nc2 = std::dynamic_pointer_cast<Constant>(nch2);
            shared_ptr<Constant> nc1 = std::dynamic_pointer_cast<Constant>(nch1);
            if (nc1->value == 0 && nc2->value == 1) {
                return createNotExpr(ncond);
            }
            if (nc1->value == 1 && nc2->value == 0) {
                return ncond;
            }
        }
        // Otherwise return the simplified conditional expression.
        return createCondExpr(ncond, nch1, nch2);
    }
    // Expr Simplifier::simplifyNondetExpr(shared_ptr<NondetExpr> nondet_expr) {
    //     return nondet_expr;
    // }
    
/*OTHER OPS*/
    Variablep createVariablep(string name, int idx, Expr value, bool no_simplify) {
        return shared_ptr<Variable>(new Variable(name, idx, value, no_simplify));        
    }

    Stmt createAssignment(Variablep var, Expr val) {
        return std::shared_ptr<Stmtv>(new Assignment(var, val));
    }
    Stmt createAssignment(Variablep var) {
        return std::shared_ptr<Stmtv>(new Assignment(var));
    }
    Stmt createAssertion(Expr cond) {
        return std::shared_ptr<Stmtv>(new Assertion(cond));
    }
    Stmt createAssumption(Expr cond) {
        return std::shared_ptr<Stmtv>(new Assumption(cond));
    }
    Stmt createComment(const string comment) {
        return std::shared_ptr<Stmtv>(new Comment(comment));
    }
    Expr createVariableExpr(const string name, int idx, Expr value, int no_simplify) {
        return std::shared_ptr<Exprv>(new Variable(name, idx, value, no_simplify));
    }
    Expr createConstantExpr(int value, VarType _var_type) {
        return std::shared_ptr<Exprv>(new Constant(value, _var_type));
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
    Expr createNotExpr(Expr expr) {
        return std::shared_ptr<Exprv>(new NotExpr(expr));
    }
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2) {
        return std::shared_ptr<Exprv>(new CondExpr(cond, choice1, choice2));
    }
    Expr createNondetExpr(VarType type) {
        return std::shared_ptr<Exprv>(new NondetExpr(type));
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


}