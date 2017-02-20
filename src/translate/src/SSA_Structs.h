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
#include <memory>
#include <string>

using std::shared_ptr;
using std::string;

//#include "ARBACExact.h"

namespace SSA {
    
    class Defs {
        public:
            static constexpr char line_end[] = ";";
            static constexpr char and_op[] = " && ";
            static constexpr char or_op[] = " || ";
            static constexpr char not_op[] = "!";
            static constexpr char assign_op[] = " = ";
            static constexpr char eq_op[] = " == ";
            static constexpr char open_comment[] = "// ";
            static constexpr char assume_str[] = "__VERIFIER_assume";
            static constexpr char assert_str[] = "assert";
            static constexpr char nondet_str[] = "nondet_";
            static constexpr char int_ty_str[] = "int";
            static constexpr char bool_ty_str[] = "_Bool";
            static constexpr char true_str[] = "1";
            static constexpr char false_str[] = "0";
            // static constexpr char true_str[] = "TRUE";
            // static constexpr char false_str[] = "FALSE";
    };    

    enum VarType {
        INT,
        BOOL
    };

    class Exprv;
    class Stmtv;
    
    typedef shared_ptr<Stmtv> Stmt;        
    typedef shared_ptr<Exprv> Expr;

    class Stmtv {
        public:
            enum StmtType {
                ASSERT,
                ASSUME,
                ASSIGNMENT,
                COMMENT,
                OUTPUT
            };

            Stmtv(StmtType ty);

            virtual string print() = 0;

            StmtType type;
    };

    class Exprv {
        public:
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

        Exprv(ExprType ty);

        virtual string print() = 0;

        ExprType type;
    };

    class Variable;

    typedef shared_ptr<Variable> Variablep;

    class Assignment : public Stmtv {
        public:
            Assignment(shared_ptr<Variable> var, Expr val);
            Assignment(shared_ptr<Variable> var);

            string print() override;
        
            shared_ptr<Variable> variable;
            Expr value;
            bool useless;
    };
    class Assertion : public Stmtv {
        public:
            Assertion(Expr cond);

            string print() override;
        
            Expr assertion;
    };
    class Assumption : public Stmtv {
        public:
            Assumption(Expr cond);

            string print() override;
        
            Expr assumption;
    };
    class Comment : public Stmtv {
        public:
            Comment(string _comment);

            string print() override;
        
            string comment;
    };

    class Variable : public Exprv {
        public:
            Variable(const string _name, int _idx, Expr _value, int _no_simplify);
            
            string print() override;
        
            string name;
            int idx;
            Expr value;
            int no_simplify;
    };
    class Constant : public Exprv  {
        public:
            Constant(int val, VarType _var_type = VarType::BOOL);

            string print() override;

            int value;
            VarType var_type;
    };
    class OrExpr : public Exprv  {
        public:
            OrExpr(Expr _lhs, Expr _rhs);

            string print() override;

            Expr lhs;
            Expr rhs;
    };
    class AndExpr : public Exprv  {
        public:
            AndExpr(Expr _lhs, Expr _rhs);

            string print() override;

            Expr lhs;
            Expr rhs;
    };
    class EqExpr : public Exprv  {
        public:
            EqExpr(Expr _lhs, Expr _rhs);

            string print() override;

            Expr lhs;
            Expr rhs;
    };
    class NotExpr : public Exprv  {
        public:
            NotExpr(Expr _expr);

            string print() override;

            Expr expr;
    };
    class CondExpr : public Exprv  {
        public:
            CondExpr(Expr _cond, Expr _choice1, Expr _choice2);

            string print() override;

            Expr cond;
            Expr choice1;
            Expr choice2;
    };
    class NondetExpr : public Exprv  {
        public:
            NondetExpr(VarType _nondet_type);

            string print() override;

            VarType nondet_type;
     };

    Variablep createVariablep(string name, int idx, Expr value, bool no_simplify = 0) ;

    Stmt createAssignment(Variablep var, Expr val);
    Stmt createAssignment(Variablep var);
    Stmt createAssertion(Expr cond);
    Stmt createAssumption(Expr cond);
    Stmt createComment(const string comment);
    Expr createVariableExpr(const string name, int idx, Expr value, int no_simplify);
    Expr createConstantExpr(int value, VarType _var_type = VarType::BOOL);
    Expr createOrExpr(Expr lhs, Expr rhs);
    Expr createAndExpr(Expr lhs, Expr rhs);
    Expr createNotExpr(Expr expr);
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2);
    Expr createNondetExpr(VarType type);
    Expr createEqExpr(Expr lhs, Expr rhs);

    class Simplifier {
        public:
            enum SimplLevel {
                NOTHING,
                CONST_VARS,
                UN_OPS,
                LBIN_OPS,
                EQUALITY,
                ALL
            };
            Simplifier(SimplLevel _level);
            void simplifyStmt(Stmt stmt);
            Expr simplifyExpr(Expr expr);
        private:
            SimplLevel level;
            void simplifyAssignment(shared_ptr<Assignment> stmt);
            void simplifyAssertion(shared_ptr<Assertion> stmt);
            void simplifyAssumption(shared_ptr<Assumption> stmt);
            Expr simplifyVariable(shared_ptr<Variable> expr);
            Expr simplifyConstant(shared_ptr<Constant> expr);
            Expr simplifyOrExpr(shared_ptr<OrExpr> expr);
            Expr simplifyAndExpr(shared_ptr<AndExpr> expr);
            Expr simplifyEqExpr(shared_ptr<EqExpr> expr);
            Expr simplifyNotExpr(shared_ptr<NotExpr> expr);
            Expr simplifyCondExpr(shared_ptr<CondExpr> expr);
            // Expr simplifyNondetExpr(NondetExpr expr);
    };

}

// extern "C" {
        


    
    


    
//     void freeStmt(Stmt stmt);
//     void freeAssignment(Assignment *assign);
//     void freeAssertion(Assertion *assert);
//     void freeAssumption(Assumption *assumption);
//     void freeComment(Comment *comment);
//     void freeExpr(Expr expr);
//     void freeVariable(Variable *var);
//     void freeConstant(Constant *constant);
//     void freeOrExpr(OrExpr* or_expr);
//     void freeAndExpr(AndExpr* and_expr);
//     void freeNotExpr(NotExpr* not_expr);
//     void freeCondExpr(CondExpr* cond_expr);
//     void freeNondetExpr(NondetExpr* nondet_expr);
//     void freeEqExpr(EqExpr* eq_expr);

//     string printStmt(Stmt stmt);
//     string printAssignment(Assignment *assign);
//     string printAssertion(Assertion *assert);
//     string printAssumption(Assumption *assumption);
//     string printComment(Comment *comment);
//     string printExpr(Expr expr);
//     string printVariable(Variable *var);
//     string printConstant(Constant *constant);
//     string printOrExpr(OrExpr* or_expr);
//     string printAndExpr(AndExpr* and_expr);
//     string printNotExpr(NotExpr* not_expr);
//     string printCondExpr(CondExpr* cond_expr);
//     string printNondetExpr(NondetExpr* nondet_expr);
//     string printEqExpr(EqExpr* eq_expr);

//     Stmt createAssignment(Variable *var, Expr val);
//     Stmt createAssertion(Expr cond);
//     Stmt createAssumption(Expr cond);
//     Stmt createComment(const string comment);
//     Variable* createVariable(const string name, int idx, Expr value, int no_simplify);
//     Expr createVariableExpr(const string name, int idx, Expr value, int no_simplify);
//     Constant* createConstant(int value);
//     Expr createConstantExpr(int value);
//     Expr createOrExpr(Expr lhs, Expr rhs);
//     Expr createAndExpr(Expr lhs, Expr rhs);
//     Expr createNotExpr(Expr expr);
//     Expr createCondExpr(Expr cond, Expr choice1, Expr choice2);
//     Expr createNondetExpr(Type type);
//     Expr createEqExpr(Expr lhs, Expr rhs);
    
//     Expr simplifyExpr(Expr expr);
//     Expr simplifyVariable(Expr var);
//     Expr simplifyConstant(Expr constant);
//     Expr simplifyOrExpr(Expr* or_expr);
//     Expr simplifyAndExpr(Expr* and_expr);
//     Expr simplifyNotExpr(Expr* not_expr);
//     Expr simplifyCondExpr(CondExpr* cond_expr);
//     Expr simplifyNondetExpr(Expr nondet_expr);
//     Expr simplifyEqExpr(Expr nondet_expr);

//     Stmt generateAssignment(Variable* var);
//     Expr exprFromVar(Variable* var);

//     // Stmt createAssign(const string var_name, int occ, Expr value);
//     // Variable createConstVar(const string var_name, int occ, int value);

// }
#endif /* SSA_STRUCTS_H */

