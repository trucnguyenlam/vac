#include "SSA_Structs.h"
#include "Solvers.h"

#include <iostream>
#include <sstream>
#include <chrono>
#include <regex>
#include <stdexcept>
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

/*SMT*/
    constexpr char SMT::comment[];
    constexpr char SMT::and_op[];
    constexpr char SMT::or_op[];
    constexpr char SMT::not_op[];
    constexpr char SMT::eq_op[];
    constexpr char SMT::declare[];
    constexpr char SMT::cond_expr[];
    constexpr char SMT::assume[];
    constexpr char SMT::assert[];
    constexpr char SMT::check[];
    constexpr char SMT::nondet_str[];
    constexpr char SMT::int_ty_str[];
    constexpr char SMT::bool_ty_str[];
    constexpr char SMT::true_str[];
    constexpr char SMT::false_str[];

    string SMT::bv_ty_str(int bv_size) {
        std::stringstream fmt;
        fmt << "(_ BitVec " << bv_size << ")";
        return fmt.str();
    }

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

    Expr Assignment::getAssignmentEq() {
        return createEqExpr(this->variable, this->value);
    }

    int Assignment::redundant() {
        return this->variable->_inline;
    }

    string Assignment::print() {
        std::stringstream fmt;

        string var = this->variable->print();
        string expr = this->value->print();
        if (this->redundant()) {
            fmt << "/* " << var << Defs::assign_op << expr << Defs::line_end << " */";
            return fmt.str();
        }
        else {
            fmt << var << Defs::assign_op << expr << Defs::line_end;
            return fmt.str();
        }
    }

    void Assignment::toFile(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "%s", "/* ");
        }

        this->variable->toFile(outputFile);
        fprintf(outputFile, "%s", Defs::assign_op);
        this->value->toFile(outputFile);
        
        if (this->redundant()) {
             fprintf(outputFile, "%s", " */");
        }
        fprintf(outputFile, "%s", Defs::line_end);
    }

    void Assignment::toSMT(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "%s ", SMT::comment);
        }

        if (this->value->type != Exprv::NONDET_EXPR) {
            fprintf(outputFile, "(%s (%s ", SMT::assert, SMT::eq_op);


            this->variable->toSMT(outputFile);
            fprintf(outputFile, " ");
            

            this->value->toSMT(outputFile);

            fprintf(outputFile, "))");
        }
        else {
            fprintf(outputFile, "%s %s is a nondet variable, so leave it unassigned...", SMT::comment, this->variable->print().c_str());
        }
        
    }

/*ASSERTION OPS*/
    Assertion::Assertion(Expr cond) :
        Stmtv(Stmtv::ASSERT), 
        assertion(cond) { }

    int Assertion::redundant() {
        if (this->assertion->type == Exprv::CONSTANT) {
            shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(this->assertion);
            if (c->value) {
                return true;
            }
            //FIXME: add here check for early termination
        }
        return false;
    }
    string Assertion::print() {
        std::stringstream fmt;
        if (this->redundant()) {
            string asserted = this->assertion->print();
            fmt << "/*" << Defs::assert_str << "(" << asserted << ")" << "*/" << Defs::line_end;
            return fmt.str();
        }
        string asserted = this->assertion->print();
        fmt << Defs::assert_str << "(" << asserted << ")" << Defs::line_end;
        return fmt.str();
    }
    void Assertion::toFile(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "/* " );
        }
        
        fprintf(outputFile, "%s(", Defs::assert_str );
        this->assertion->toFile(outputFile);
        fprintf(outputFile, ")");
        
        if (this->redundant()) {
             fprintf(outputFile, " */");
        }
        fprintf(outputFile, Defs::line_end);
    }

    void Assertion::toSMT(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "%s ", SMT::comment );
        }
        
        fprintf(outputFile, "(%s ", SMT::assert);
        this->assertion->toSMT(outputFile);
        fprintf(outputFile, ")");
    }
    
/*ASSUMPTION OPS*/
    Assumption::Assumption(Expr cond) :
        Stmtv(Stmtv::ASSUME), 
        assumption(cond) { }

    int Assumption::redundant() {
        if (this->assumption->type == Exprv::CONSTANT) {
            shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(this->assumption);
            if (c->value) {
                return true;
            }
            //FIXME: add here check for early termination
        }
        return false;
    }    
    string Assumption::print() {
        std::stringstream fmt;
        if (this->redundant()) {
            string assumed = this->assumption->print();
            fmt << "/*" << Defs::assume_str << "(" << assumed << ")" << "*/" << Defs::line_end;
            return fmt.str();
        }
        string assumed = this->assumption->print();
        fmt << Defs::assume_str << "(" << assumed << ")" << Defs::line_end;
        return fmt.str();
    }
    void Assumption::toFile(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "/* " );
        }
        
        fprintf(outputFile, "%s(", Defs::assume_str );
        this->assumption->toFile(outputFile);
        fprintf(outputFile, ")");
        
        if (this->redundant()) {
             fprintf(outputFile, " */");
        }
        fprintf(outputFile, Defs::line_end);
    }

    void Assumption::toSMT(FILE* outputFile) {
        if (this->redundant()) {
            fprintf(outputFile, "%s ", SMT::comment );
        }
        
        fprintf(outputFile, "(%s ", SMT::assert );
        this->assumption->toSMT(outputFile);
        fprintf(outputFile, ")");
        
    }

/*COMMENT OPS*/
    Comment::Comment(const string _comment) :
        Stmtv(Stmtv::COMMENT), comment(_comment) { }

    int Comment::redundant() {
        return true;
    }
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
    void Comment::toFile(FILE* outputFile) {
        if (this->comment.length() > 0) {
            fprintf(outputFile, "/* %s */", this->comment.c_str());
        }
    }
    void Comment::toSMT(FILE* outputFile) {
        if (this->comment.length() > 0) {
            string n_line = string("\n") + string(SMT::comment) + string(" ");
            string n_comment = std::regex_replace(this->comment, std::regex("\\n"), n_line);
            fprintf(outputFile, "%s %s", SMT::comment, n_comment.c_str());
        }
    }
    
/*EXPR OPS*/
    Exprv::Exprv(ExprType ty) : type(ty) { } 
    
/*VARIABLE OPS*/
    Variable::Variable(const string _name, int _idx, Expr _value, int _bv_size, int do_not_inline):
        Exprv(Exprv::VARIABLE), 
        name(_name), idx(_idx), value(_value), _inline(!do_not_inline), no_inline(do_not_inline), bv_size(_bv_size) {
            this->type = (bv_size > 1) ? INT : BOOL;
         }

    string Variable::print() {
        std::stringstream fmt;
        fmt << "|" << this->name << "_" << this->idx << "|";
        return fmt.str();
    }
    void Variable::toFile(FILE* outputFile) {
        fprintf(outputFile, "%s", this->print().c_str());
    }
    void Variable::toSMT(FILE* outputFile) {
        fprintf(outputFile, "%s", this->print().c_str());
    }

    void Variable::writeSMTDeclaration(FILE* outputFile) {
        string name = this->print();
        string type = (this->type == BOOL) ? SMT::bool_ty_str : SMT::bv_ty_str(this->bv_size);
        fprintf(outputFile, "(%s %s () %s)", SMT::declare, name.c_str(), type.c_str());
    }
         
/*CONSTANT OPS*/
    Constant::Constant(int _value, int _bv_size) :
        Exprv(Exprv::CONSTANT),
        value(_value), bv_size(_bv_size) { 
            if (_bv_size == 1) {
                var_type = BOOL;
            }
            else {
                var_type = INT;
            }
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
    
    void Constant::toFile(FILE* outputFile) {
        if (this->var_type == VarType::BOOL) {
            if (this->value) {
                fprintf(outputFile, Defs::true_str);
            }
            else {
                fprintf(outputFile, Defs::false_str);
            }
        }
        else {
            fprintf(outputFile, "%d", this->value);
        }
    }

    void Constant::toSMT(FILE* outputFile) {
        if (this->var_type == VarType::BOOL) {
            if (this->value) {
                fprintf(outputFile, SMT::true_str);
            }
            else {
                fprintf(outputFile, SMT::false_str);
            }
        }
        else {
            fprintf(outputFile, "(_ bv%d %d)", this->value, this->bv_size);
            // fprintf(outputFile, "%d", this->value);
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

    void OrExpr::toFile(FILE* outputFile) {
        fprintf(outputFile, "(");
        this->lhs->toFile(outputFile);
        fprintf(outputFile, Defs::or_op);
        this->rhs->toFile(outputFile);
        fprintf(outputFile, ")");
    }

    void OrExpr::toSMT(FILE* outputFile) {
        fprintf(outputFile, "(%s ", SMT::or_op);
        this->lhs->toSMT(outputFile);
        fprintf(outputFile, " ");
        this->rhs->toSMT(outputFile);
        fprintf(outputFile, ")");
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

    void AndExpr::toFile(FILE* outputFile) {
        fprintf(outputFile, "(");
        this->lhs->toFile(outputFile);
        fprintf(outputFile, Defs::and_op);
        this->rhs->toFile(outputFile);
        fprintf(outputFile, ")");
    }

    void AndExpr::toSMT(FILE* outputFile) {
        fprintf(outputFile, "(%s ", SMT::and_op);
        this->lhs->toSMT(outputFile);
        fprintf(outputFile, " ");
        this->rhs->toSMT(outputFile);
        fprintf(outputFile, ")");
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

    void EqExpr::toFile(FILE* outputFile) {
        fprintf(outputFile, "(");
        this->lhs->toFile(outputFile);
        fprintf(outputFile, "%s", Defs::eq_op);
        this->rhs->toFile(outputFile);
        fprintf(outputFile, ")");
    }

    void EqExpr::toSMT(FILE* outputFile) {
        fprintf(outputFile, "(%s ", SMT::eq_op);
        this->lhs->toSMT(outputFile);
        fprintf(outputFile, " ");
        this->rhs->toSMT(outputFile);
        fprintf(outputFile, ")");
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
    void NotExpr::toFile(FILE* outputFile) {
        fprintf(outputFile, "%s(", Defs::not_op);
        this->expr->toFile(outputFile);
        fprintf(outputFile, ")");
    }
    void NotExpr::toSMT(FILE* outputFile) {
        fprintf(outputFile, "(%s ", SMT::not_op);
        this->expr->toSMT(outputFile);
        fprintf(outputFile, ")");
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

    void CondExpr::toFile(FILE* outputFile) {
        fprintf(outputFile, "(");
        this->cond->toFile(outputFile);
        fprintf(outputFile, ") ? (");
        this->choice1->toFile(outputFile);
        fprintf(outputFile, ") : (");
        this->choice2->toFile(outputFile);
        fprintf(outputFile, "))");
    }

    void CondExpr::toSMT(FILE* outputFile) {
        fprintf(outputFile, "(%s ", SMT::cond_expr);
        this->cond->toSMT(outputFile);
        fprintf(outputFile, " ");
        this->choice1->toSMT(outputFile);
        fprintf(outputFile, " ");
        this->choice2->toSMT(outputFile);
        fprintf(outputFile, ")");
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

    void NondetExpr::toFile(FILE* outputFile) {
        const char* ty_name = this->nondet_type == INT ? Defs::int_ty_str : Defs::bool_ty_str;
        fprintf(outputFile, "%s%s()", Defs::nondet_str, ty_name);
    }

    void NondetExpr::toSMT(FILE* outputFile) {
        throw std::runtime_error("CANNOT PRINT A NONDET EXPRESSION IN SMT");
        const char* ty_name = this->nondet_type == INT ? Defs::int_ty_str : Defs::bool_ty_str;
        fprintf(outputFile, "%s%s()", Defs::nondet_str, ty_name);
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

    int Simplifier::canInline(Expr expr) {
        switch (this->level) {
            //WARNING: Switch without break to fall in previous cases
            case ALL:
                return true;
            case EQUALITY:
                if (expr->type == Exprv::EQ_EXPR) {
                    return true;
                }
            case LBIN_OPS:
                if (expr->type == Exprv::OR_EXPR || expr->type == Exprv::AND_EXPR) {
                    return true;
                }
            case UN_OPS:
                if (expr->type == Exprv::NOT_EXPR) {
                    return true;
                }
            case CONST_VARS:
                if (expr->type == Exprv::CONSTANT || expr->type == Exprv::VARIABLE) {
                    return true;
                }
            case NOTHING:
                return false;
        }
        return false;
    }
    void Simplifier::simplifyAssignment(shared_ptr<Assignment> assignment) {
        //TODO: put here redundancy after simplification check
        Expr nval = this->simplifyExpr(assignment->variable->value);

        assignment->value = nval;
        assignment->variable->value = nval;
        assignment->variable->_inline = assignment->variable->_inline && canInline(nval);

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
        if (!var->_inline) {
            return var;
        }
        Expr res = var->value;
        while (res->type == Exprv::VARIABLE && std::dynamic_pointer_cast<Variable>(res)->_inline) {
            res = std::dynamic_pointer_cast<Variable>(res)->value;
        }
        return res;
    }
    Expr Simplifier::simplifyConstant(shared_ptr<Constant> expr) {
        //TODO: could be removed
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
            return createConstantExpr(1, 1);
        }

        if (nlhs->type == Exprv::CONSTANT && nrhs->type == Exprv::CONSTANT) {
            shared_ptr<Constant> nl = std::dynamic_pointer_cast<Constant>(nlhs);
            shared_ptr<Constant> nr = std::dynamic_pointer_cast<Constant>(nrhs);
            return createConstantExpr(nl->value == nr->value, 1);
        }

        return createEqExpr(nlhs, nrhs);
            
    }
    Expr Simplifier::simplifyNotExpr(shared_ptr<NotExpr> not_expr) {
        Expr nexpr = simplifyExpr(not_expr->expr);
        if (nexpr->type == Exprv::CONSTANT) {
            return createConstantExpr(!(std::dynamic_pointer_cast<Constant>(nexpr))->value, 1);
        }
        if (nexpr->type == Exprv::NOT_EXPR) {
            return std::dynamic_pointer_cast<NotExpr>(nexpr)->expr;
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

/*SSAPROGRAM*/
    SSAProgram::SSAProgram() { }

    void SSAProgram::addAssignment(shared_ptr<Assignment> assignment) {
        this->statements.push_back(assignment);
        this->variables.push_back(assignment->variable);
    }
    void SSAProgram::addAssumption(shared_ptr<Assumption> assumption) {
        this->statements.push_back(assumption);
    }
    void SSAProgram::addAssertion(shared_ptr<Assertion> assertion) {
        this->statements.push_back(assertion);        
        this->assertions_body.push_back(assertion->assertion);
    }
    void SSAProgram::addComment(shared_ptr<Comment> comment) {
        this->statements.push_back(comment);
    }
    void SSAProgram::printStats(int skip_redundant) {
        int assignments = 0, assertions = 0, assumptions = 0, comments = 0;
        auto ite = this->statements.begin();
        for ( ; ite != this->statements.end(); ++ite) {
            Stmt s = *ite;
            if (!skip_redundant || !s->redundant()) {
                switch (s->type) {
                    case Stmtv::ASSIGNMENT: 
                        assignments++;
                        break;
                    case Stmtv::ASSERT: 
                        assertions++;
                        break;
                    case Stmtv::ASSUME: 
                        assumptions++;
                        break;
                    case Stmtv::COMMENT:
                        comments++;
                        break;
                    default:
                        break;
                }
            }
        }
        std::cout << "SSA Program:\n";
        std::cout << "    assignments:  " << assignments << "\n";
        std::cout << "    assertions:   " << assertions << "\n";
        std::cout << "    assumptions:  " << assumptions << "\n";
        std::cout << "    comments:     " << comments << "\n";
        std::cout << "    total stmts:  " << assignments + assertions + assumptions << "\n";
    }

    void SSAProgram::simplify(Simplifier::SimplLevel level, int visualize_progress) {
        // float progress = 0.0;
        // while (progress < 1.0) {
        //     int barWidth = 70;

        //     std::cout << "[";
        //     int pos = barWidth * progress;
        //     for (int i = 0; i < barWidth; ++i) {
        //         if (i < pos) std::cout << "=";
        //         else if (i == pos) std::cout << ">";
        //         else std::cout << " ";
        //     }
        //     std::cout << "] " << int(progress * 100.0) << " %\r";
        //     std::cout.flush();

        //     progress += 0.16; // for demonstration only
        // }
        // std::cout << std::endl;
        //FIXME: if !visualize_progress cout = fmt
        std::cout << "------------ STARTING SIMPLIFICATION ------------\n";
        int i = 0;
        int last = 0;
        unsigned long l = this->statements.size();
        std::cout <<  "[";
        auto start = std::chrono::high_resolution_clock::now();
        Simplifier simpl(level); // CONST_VARS
        auto ite = this->statements.begin();
        for ( ; ite != this->statements.end(); ++ite) {
            i++;
            Stmt elem = *ite;
            simpl.simplifyStmt(elem);
            int perc = (i * 50) / l;
            if (perc != last) {
                last = perc;
                std::cout << "#";
                std::cout.flush();
            }
        }
        auto end = std::chrono::high_resolution_clock::now();
        std::cout << "]\n";
        auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
        std::cout << "------------ SIMPLIFICATION DONE IN " << milliseconds.count() << " ms ------------\n";
    }

    void SSAProgram::write(FILE* outputFile, int skip_redundant) {
        unsigned long i = 0;
        std::vector<Stmt>::iterator ite = this->statements.begin();
        for ( ; ite != this->statements.end(); ++ite) {
            Stmt elem = *ite;
            if (!skip_redundant || !elem->redundant() || elem->type == Stmtv::COMMENT) {
                elem->toFile(outputFile);
                fprintf(outputFile, "\n");
                i++;
            }
        }
        fprintf(stderr, "------------ GENERATED %lu STATEMENTS ------------\n", i);
    }

    void SSAProgram::writeSMTDeclarations(FILE* outputFile, int skip_redundant) {
        unsigned long i = 0;
        std::vector<Variablep>::iterator ite = this->variables.begin();
        fprintf(outputFile, "(set-logic QF_UFBV)\n");
        for ( ; ite != this->variables.end(); ++ite) {
            Variablep v = *ite;
            if (!skip_redundant || !v->_inline) {
                v->writeSMTDeclaration(outputFile);
                fprintf(outputFile, "\n");
                i++;
            }
        }
        fprintf(stderr, "------------ GENERATED %lu VARIABLES ------------\n", i);
    }

    void SSAProgram::writeSMT(FILE* outputFile, int skip_redundant, Simplifier::SimplLevel level) {
        unsigned long i = 0;
        std::vector<Stmt>::iterator ite = this->statements.begin();
        for ( ; ite != this->statements.end(); ++ite) {
            Stmt elem = *ite;
            if (elem->type == Stmtv::ASSERT)
                continue;
            if (!skip_redundant || !elem->redundant() || elem->type == Stmtv::COMMENT) {
                elem->toSMT(outputFile);
                fprintf(outputFile, "\n");
                i++;
            }
        }

        Simplifier simpl(level); // CONST_VARS
        
        auto aite = this->assertions_body.begin();
        Expr assert_body = createNotExpr((*aite));
        for ( ; aite != this->assertions_body.end(); ++aite) {
            assert_body = createOrExpr(assert_body, createNotExpr((*aite)));
        }
        Stmt final_assert = createAssertion(simpl.simplifyExpr(assert_body));
        final_assert->toSMT(outputFile);
        fprintf(outputFile, "\n");
        fprintf(outputFile, "(%s)", SMT::check);
        fprintf(stderr, "------------ GENERATED %lu STATEMENTS ------------\n", i);
    }

    void SSAProgram::loadSMTSolver(std::shared_ptr<SMTSolver> solver, Simplifier::SimplLevel level, int join_assignments) {
        unsigned long i = 0;
        std::vector<Variablep>::iterator ite = this->variables.begin();
        for ( ; ite != this->variables.end(); ++ite) {
            Variablep v = *ite;
            if (!v->_inline) {
                solver->declareVariable(v, false);
                i++;
            }
        }
        fprintf(stderr, "------------ GENERATED %lu VARIABLES ------------\n", i);
        std::vector<Expr> assignments;
        std::vector<Stmt>::iterator site = this->statements.begin();
        for ( ; site != this->statements.end(); ++site) {
            Stmt elem = *site;
            if (elem->type == Stmtv::ASSERT)
                continue;
            if (!elem->redundant() && elem->type != Stmtv::COMMENT) {
                Expr body;
                if (elem->type == Stmtv::ASSUME) {
                    body = std::dynamic_pointer_cast<Assumption>(elem)->assumption;
                }
                if (elem->type == Stmtv::ASSIGNMENT) {
                    body = std::dynamic_pointer_cast<Assignment>(elem)->getAssignmentEq();
                    if (std::dynamic_pointer_cast<EqExpr>(body)->rhs->type == Exprv::NONDET_EXPR) 
                        continue;
                }
                if (!join_assignments) {
                    solver->addAssertion(body);
                }
                else {
                    assignments.push_back(body);
                }
                i++;
            }
        }

        if (join_assignments) {
            Expr joined_ass = createConstantExpr(true, 1);
            for (auto aite = assignments.begin(); aite != assignments.end(); ++aite) {
                joined_ass = createAndExpr(joined_ass, *aite);
            }
            solver->addAssertion(joined_ass);
        }

        Simplifier simpl(level); // CONST_VARS
        
        auto aite = this->assertions_body.begin();
        Expr assert_body = createNotExpr((*aite));
        for ( ; aite != this->assertions_body.end(); ++aite) {
            assert_body = createOrExpr(assert_body, createNotExpr((*aite)));
        }
        Expr final_assert = simpl.simplifyExpr(assert_body);
        solver->addAssertion(final_assert);
        fprintf(stderr, "------------ GENERATED %lu STATEMENTS ------------\n", i);
    }

    void SSAProgram::clear() {
        this->statements.clear();
    }



/*OTHER OPS*/
    Variablep createVariablep(string name, int idx, Expr value, int bv_size, bool no_simplify) {
        return shared_ptr<Variable>(new Variable(name, idx, value, bv_size, no_simplify));
    }

    shared_ptr<Assignment> createAssignment(Variablep var, Expr val) {
        return std::shared_ptr<Assignment>(new Assignment(var, val));
    }
    shared_ptr<Assignment> createAssignment(Variablep var) {
        return std::shared_ptr<Assignment>(new Assignment(var));
    }
    shared_ptr<Assertion> createAssertion(Expr cond) {
        return std::shared_ptr<Assertion>(new Assertion(cond));
    }
    shared_ptr<Assumption> createAssumption(Expr cond) {
        return std::shared_ptr<Assumption>(new Assumption(cond));
    }
    shared_ptr<Comment> createComment(const string comment) {
        return std::shared_ptr<Comment>(new Comment(comment));
    }
    Expr createVariableExpr(const string name, int idx, Expr value, int bv_size, int no_simplify) {
        return std::shared_ptr<Exprv>(new Variable(name, idx, value, bv_size, no_simplify));
    }
    Expr createConstantExpr(int value, int bv_size) {
        return std::shared_ptr<Exprv>(new Constant(value, bv_size));
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
