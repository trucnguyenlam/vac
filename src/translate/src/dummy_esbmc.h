/*
 * dummy_esbmc.h
 *
 *  Created on: 2 Feb 2017
 *      Author: esteffin
 */

#ifndef SRC_DUMMY_ESBMC_H_
#define SRC_DUMMY_ESBMC_H_

#include <string>
#include <memory>
#include <vector>

using std::string;
using std::shared_ptr;

class Instrumentation {
public:
    static string line_end = ";";
    static string and_op = " && ";
    static string or_op = " || ";
    static string assign_op = " = ";
    static string open_comment = "// ";
    static string assume_str = "assume";
    static string assert_str = "assert";
    static string nondet_str = "nondet_bool()";
};

class Stmt;
class Expr;

typedef shared_ptr<Stmt> Stmtc;
typedef shared_ptr<Expr> Exprc;

class Stmt {
public:

    enum StmtType {
        ASSERT,
        ASSUME,
        ASSIGNMENT,
        OUTPUT
    };

    virtual string print();
    
    StmtType type;
};

class Assignment : public Stmt {
public:
    Assignment(shared_ptr<Variable> var, Exprc val) : type(StmtType::ASSIGNMENT), 
            variable(var), value(val) {
        auto nval = val->simplify();
        if (nval->type != ExprType::COND_EXPR) {
            var->value = nval;
        }
        useless = true;
    }
    
    ~Assignment() {
        delete variable;
        delete value;
    }
    
    string print() override {
        string str = "";
        if (useless)
            str += open_comment;
        str += variable->print() + assign_op + value->print() + line_end;
        return str;
    }
    
//private:
    shared_ptr<Variable> variable;
    Exprc value;
    bool useless = false;
};

class Assert : Stmt {
public:
    Assert(Exprc cond) : type(StmtType::ASSERT),
        assertion(cond) {
    }
    Assert(const Assert& orig);
    virtual ~Assert();
    
    string print() override{
        return Instrumentation::assert_str + "(" + assertion->print() + ")" + ;
    }

//private:
    Exprc assertion;
};

class Assume : Stmt {
public:
    Assume(Exprc cond) : type(StmtType::ASSERT),
        assertion(cond) {
    }
    Assume(const Assert& orig);
    virtual ~Assume();
    
    string print() override{
        return Instrumentation::assert_str + "(" + assertion->print() + ")" + ;
    }

//private:
    Exprc assertion;
};


enum ExprType {
    CONSTANT,
    VARIABLE,
    OR_EXPR,
    AND_EXPR,
    COND_EXPR,
    NONDET_EXPR
};

class Expr {
public:
    virtual Exprc simplify();
    virtual string print();
    ExprType type;
};

class Variable : Expr {
public:

    Variable(const string _name) : Expr::type(ExprType::VARIABLE),
    name(_name), id(0) {
    }

    Variable(const string _name, int _id) : Expr::type(ExprType::VARIABLE),
    name(_name), id(_id) {
    }

    Variable(const string _name, int _id, Exprc val) : Expr::type(ExprType::VARIABLE),
    name(_name), id(_id), value(val->simplify()) {
    }

    ~Variable() {
        //delete name;
    }

    string print(FILE *outFile) override {
        return name + "_" + id;
    }
    //private:
    string name;
    int id;
    Exprc value = NULL;
};

class Constant : Expr {
public:

    Constant(int val) : Expr::type(ExprType::CONSTANT),
        value(val) {
    }
    Constant(const Constant& orig);

    ~Constant() {
    }

    Expr simplify() override {
        return this;
    }

    string print() override {
        return "" + value;
    }
    //private:
    int value;
};

class OrExpr : Expr {
public:

    OrExpr(Exprc _lhs, Exprc _rhs) : Expr::type(ExprType::OR_EXPR),
    lhs(_lhs), rhs(_rhs) {
    }
    OrExpr(const OrExpr& orig);

    virtual ~OrExpr() {
        delete lhs;
        delete rhs;
    }

    Exprc simplify() override {
        Expr nlhs, nrhs;
        nlhs = lhs->simplify();
        if (nlhs.type == ExprType::CONSTANT) {
            if (((shared_ptr<Constant>) nlhs)->value) {
                return (Constant) nlhs;
            }
            else {
                return rhs->simplify();
            }
        }
        nrhs = rhs->simplify();
        if (nrhs.type == ExprType::CONSTANT) {
            if (((Constant) nrhs).value) {
                return (Constant) nrhs;
            }
            else {
                return nlhs;
            }
        }
        return new OrExpr(nlhs, nrhs);
    }
    
    string print() override {
        return "(" + lhs->print() + Instrumentation::or_op + rhs->print() + ")";
    }

    //private:
    Exprc lhs = NULL, rhs = NULL;
};

class AndExpr : Expr {
public:

    AndExpr(Expr _lhs, Expr _rhs) : Expr::type(ExprType::AND_EXPR),
        lhs(_lhs), rhs(_rhs) {
    }
    AndExpr(const AndExpr& orig);

    virtual ~AndExpr() {
        delete lhs;
        delete rhs;
    }

    Exprc simplify() override {
        Expr nlhs, nrhs;
        nlhs = lhs->simplify();
        if (nlhs.type == ExprType::CONSTANT) {
            if (!((Constant) nlhs).value) {
                return (Constant) nlhs;
            }
            else {
                return rhs->simplify();
            }
        }
        nrhs = rhs->simplify();
        if (nrhs.type == ExprType::CONSTANT) {
            if (!((Constant) nrhs).value) {
                return (Constant) nrhs;
            }
            else {
                return nlhs;
            }
        }
        return new AndExpr(nlhs, nrhs);
    }
    
    string print() override {
        return "(" + lhs->print() + Instrumentation::and_op + rhs->print() + ")";
    }

    //private:
    Exprc lhs = NULL, rhs = NULL;
};

class CondExpr : Expr {
public:
    CondExpr(Exprc _cond, Exprc _choice1, Exprc _choice2) : Expr::type(ExprType::COND_EXPR),
        cond(_cond), choice1(_choice1), choice2(_choice2) {
    }
    CondExpr(const CondExpr& orig);
    virtual ~CondExpr() {
        delete cond;
        delete choice1;
        delete choice2;
    }

    Exprc simplify() override {
        Exprc ncond = cond->simplify();
        if (ncond->type == ExprType::CONSTANT) {
            if (((shared_ptr<Constant>) ncond)->value) {
                return choice1->simplify();
            }
            else {
                return choice2->simplify();
            }
        }
        
        return new CondExpr(ncond, choice1->simplify(), choice2->simplify());
    }
    
    string print() override {
        return "((" + cond->print() + ") ? (" + choice1->print() + ") : (" +choice2->print() + "))";
    }
    
//private:
    Exprc cond = NULL, choice1 = NULL, choice2 = NULL;

};

class NondetExpr : Expr {
public:
    static Exprc value = shared_ptr<NondetExpr>(NondetExpr()) ;
    virtual ~NondetExpr() { }
    
    Exprc simplify() override {
        return this;
    }
    
    string print() override {
        return Stmt::nondet_str + "()" + Stmt::line_end;
    }
    
private:
    NondetExpr() : Expr::type(ExprType::NONDET_EXPR) {
    }
    NondetExpr(const NondetExpr& orig);
};

#endif /* SRC_DUMMY_ESBMC_H_ */
