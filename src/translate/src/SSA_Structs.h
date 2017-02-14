/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   SSA_Structs.h
 * Author: esteffin
 *
 * Created on 07 February 2017, 13:12
 */

#ifndef SSA_STRUCTS_H
#define SSA_STRUCTS_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

//#include "ARBACExact.h"

extern "C" {
        
    static const char* line_end = ";";
    static const char* and_op = " && ";
    static const char* or_op = " || ";
    static const char* not_op = "!";
    static const char* assign_op = " = ";
    static const char* eq_op = " == ";
    static const char* open_comment = "// ";
    static const char* assume_str = "__VERIFIER_assume";
    static const char* assert_str = "assert";
    static const char* nondet_str = "nondet_%s";

    enum Type {
        INT,
        BOOL
    };

    enum StmtType {
        ASSERT,
        ASSUME,
        ASSIGNMENT,
        COMMENT,
        OUTPUT
    };
    enum ExprType {
        CONSTANT,
        VARIABLE,
        EQ_EXPR,
        NOT_EXPR,
        OR_EXPR,
        AND_EXPR,
        COND_EXPR,
        NONDET_EXPR
    };

    struct _Stmt {
        StmtType type;
        void *value;
    };
    typedef _Stmt *Stmt;
    
    struct _Expr {
        ExprType type;
        void *value;
    };
    typedef _Expr *Expr;
    
    struct Variable;
    
    struct Assignment {
        Variable* variable;
        Expr value;
        bool useless;
    };    
    struct Assertion {
        Expr assertion;
    };
    struct Assumption {
        Expr assume;
    };
    struct Comment {
        char* comment;
    };

    struct Variable{
        char* name;
        int idx;
        int no_simplify;
        Expr value;
    };
    struct Constant {
        int value;
    };
    struct OrExpr {
        Expr lhs;
        Expr rhs;
    };
    struct AndExpr {
        Expr lhs;
        Expr rhs;
    };
    struct NotExpr {
        Expr expr;
    };
    struct CondExpr {
        Expr cond;
        Expr choice1;
        Expr choice2;
    };
    struct NondetExpr {
        Type nondet_type;
     };
    struct EqExpr {
        Expr lhs;
        Expr rhs;
    };
    
    void freeStmt(Stmt stmt);
    void freeAssignment(Assignment *assign);
    void freeAssertion(Assertion *assert);
    void freeAssumption(Assumption *assumption);
    void freeComment(Comment *comment);
    void freeExpr(Expr expr);
    void freeVariable(Variable *var);
    void freeConstant(Constant *constant);
    void freeOrExpr(OrExpr* or_expr);
    void freeAndExpr(AndExpr* and_expr);
    void freeNotExpr(NotExpr* not_expr);
    void freeCondExpr(CondExpr* cond_expr);
    void freeNondetExpr(NondetExpr* nondet_expr);
    void freeEqExpr(EqExpr* eq_expr);

    char* printStmt(Stmt stmt);
    char* printAssignment(Assignment *assign);
    char* printAssertion(Assertion *assert);
    char* printAssumption(Assumption *assumption);
    char* printComment(Comment *comment);
    char* printExpr(Expr expr);
    char* printVariable(Variable *var);
    char* printConstant(Constant *constant);
    char* printOrExpr(OrExpr* or_expr);
    char* printAndExpr(AndExpr* and_expr);
    char* printNotExpr(NotExpr* not_expr);
    char* printCondExpr(CondExpr* cond_expr);
    char* printNondetExpr(NondetExpr* nondet_expr);
    char* printEqExpr(EqExpr* eq_expr);

    Stmt createAssignment(Variable *var, Expr val);
    Stmt createAssertion(Expr cond);
    Stmt createAssumption(Expr cond);
    Stmt createComment(const char* comment);
    Variable* createVariable(const char* name, int idx, Expr value, int no_simplify);
    Expr createVariableExpr(const char* name, int idx, Expr value, int no_simplify);
    Constant* createConstant(int value);
    Expr createConstantExpr(int value);
    Expr createOrExpr(Expr lhs, Expr rhs);
    Expr createAndExpr(Expr lhs, Expr rhs);
    Expr createNotExpr(Expr expr);
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2);
    Expr createNondetExpr(Type type);
    Expr createEqExpr(Expr lhs, Expr rhs);
    
    Expr simplifyExpr(Expr expr);
    Expr simplifyVariable(Expr var);
    Expr simplifyConstant(Expr constant);
    Expr simplifyOrExpr(Expr* or_expr);
    Expr simplifyAndExpr(Expr* and_expr);
    Expr simplifyNotExpr(Expr* not_expr);
    Expr simplifyCondExpr(CondExpr* cond_expr);
    Expr simplifyNondetExpr(Expr nondet_expr);
    Expr simplifyEqExpr(Expr nondet_expr);

    Stmt generateAssignment(Variable* var);
    Expr exprFromVar(Variable* var);

    // Stmt createAssign(const char* var_name, int occ, Expr value);
    // Variable createConstVar(const char* var_name, int occ, int value);

}
#endif /* SSA_STRUCTS_H */

