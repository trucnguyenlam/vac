#include "SSA_Structs.h"

#include <iostream>
#include <sstream>

namespace SSA {

/*STMT OPS*/
    Stmtv::Stmtv(StmtType ty) : type(ty) { }

/*ASSIGNMENT OPS*/
    Assignment::Assignment(shared_ptr<Variable> var, Expr val): 
        Stmtv(Stmtv::ASSIGNMENT),
        variable(var), value(val), useless(0) {
            //FIXME: Fix useless
    }

    Assignment::Assignment(shared_ptr<Variable> var) :
        Stmtv(Stmtv::ASSIGNMENT),
        variable(var), value(var->value), useless(0) {
        //FIXME: Fix useless
    }

    void Assignment::simplify() {
            //        Expr nval = simplifyExpr(assign->value);
            //        if (expr->type != COND_EXPR) {
            //            assign->value = nval;
            //            assign->useless = true;
            //        }
            //        return assign;
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
    void Assertion::simplify() { /* TODO: simplify */ }
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

    void Assumption::simplify() { /* TODO: simplify */ }

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
        return this->comment;
    }
    
/*EXPR OPS*/
    Exprv::Exprv(ExprType ty) : type(ty) { } 
    
/*VARIABLE OPS*/
    Variable::Variable(const string _name, int _idx, Expr _value, int _no_simplify):
        Exprv(Exprv::VARIABLE), 
        idx(_idx), value(_value), no_simplify(_no_simplify) { }

    Expr Variable::simplify() {
        //FIXME: simplify
        //        Variable *inner = (Variable*) var->value;
        //        if (inner->value != NULL) {
        //            Expr res = simplifyExpr(inner->value);
        //            free(inner->name);
        //            free(inner);
        //            free(var);
        //            return res;
        //        }
        //        else {
        //            printf("Could not simplify variable %s.\nRetrning NULL\n", printVariable(var));
        //            return NULL;
        //        }
    }
    string Variable::print() {
        std::stringstream fmt;
        fmt << this->name << "_" << this->idx;
        return fmt.str();
    }
         
/*CONSTANT OPS*/
    Constant::Constant(int _value, VarType _var_type) :
        Exprv(Exprv::CONSTANT),
        value(_value), var_type(_var_type) { }
    
    Expr Constant::simplify() {
        //        Expr res = createConstant(((Constant)constant->value)->value);
        //        freeExpr(constant);
        //        return res;
    }
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

    Expr OrExpr::simplify() {
        //FIXME: simplify
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
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

    Expr AndExpr::simplify() {
        //FIXME: simplify
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
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

    Expr EqExpr::simplify() {
        //FIXME: simplify
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
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

    Expr NotExpr::simplify() {
        //FIXME: simplify
    }
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

    Expr CondExpr::simplify()  {
        //        Exprc ncond = cond->simplify();
        //        if (ncond->type == CONSTANT) {
        //            if (((shared_ptr<Constant>) ncond)->value) {
        //                return choice1->simplify();
        //            }
        //            else {
        //                return choice2->simplify();
        //            }
        //        }
        //
        //        return new CondExpr(ncond, choice1->simplify(), choice2->simplify());
    }
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

    Expr NondetExpr::simplify() {
        //
    }
    string NondetExpr::print() {
        std::stringstream fmt;
        const char* ty_name = this->nondet_type == INT ? Defs::int_ty_str : Defs::bool_ty_str;
        fmt << ty_name << "()";
        return fmt.str();
    }
    
/*OTHER OPS*/


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