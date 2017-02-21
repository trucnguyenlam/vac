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
#include <vector>
#include <iostream>

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
            // virtual void toStream(std::iostream fmt) = 0;
            virtual int redundant() = 0;

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
        // virtual void toStream(std::iostream fmt) = 0;

        ExprType type;
    };

    class Variable;

    typedef shared_ptr<Variable> Variablep;

    class Assignment : public Stmtv {
        public:
            Assignment(shared_ptr<Variable> var, Expr val);
            Assignment(shared_ptr<Variable> var);

            string print() override;
            // void toStream(std::iostream fmt) override;
            int redundant() override;
        
            shared_ptr<Variable> variable;
            Expr value;
            bool useless;
    };
    class Assertion : public Stmtv {
        public:
            Assertion(Expr cond);

            string print() override;
            // void toStream(std::iostream fmt) override;
            int redundant() override;
        
            Expr assertion;
    };
    class Assumption : public Stmtv {
        public:
            Assumption(Expr cond);

            string print() override;
            // void toStream(std::iostream fmt) override;
            int redundant() override;
        
            Expr assumption;
    };
    class Comment : public Stmtv {
        public:
            Comment(string _comment);

            string print() override;
            // void toStream(std::iostream fmt) override;
            int redundant() override;
        
            string comment;
    };

    class Variable : public Exprv {
        public:
            Variable(const string _name, int _idx, Expr _value, int do_not_inline);
            
            string print() override;
            // void toStream(std::iostream fmt) override;
        
            string name;
            int idx;
            Expr value;
            int no_inline;
            int _inline;
    };
    class Constant : public Exprv  {
        public:
            Constant(int val, VarType _var_type = VarType::BOOL);

            string print() override;
            // void toStream(std::iostream fmt) override;

            int value;
            VarType var_type;
    };
    class OrExpr : public Exprv  {
        public:
            OrExpr(Expr _lhs, Expr _rhs);

            string print() override;
            // void toStream(std::iostream fmt) override;

            Expr lhs;
            Expr rhs;
    };
    class AndExpr : public Exprv  {
        public:
            AndExpr(Expr _lhs, Expr _rhs);

            string print() override;
            // void toStream(std::iostream fmt) override;

            Expr lhs;
            Expr rhs;
    };
    class EqExpr : public Exprv  {
        public:
            EqExpr(Expr _lhs, Expr _rhs);

            string print() override;
            // void toStream(std::iostream fmt) override;

            Expr lhs;
            Expr rhs;
    };
    class NotExpr : public Exprv  {
        public:
            NotExpr(Expr _expr);

            string print() override;
            // void toStream(std::iostream fmt) override;

            Expr expr;
    };
    class CondExpr : public Exprv  {
        public:
            CondExpr(Expr _cond, Expr _choice1, Expr _choice2);

            string print() override;
            // void toStream(std::iostream fmt) override;

            Expr cond;
            Expr choice1;
            Expr choice2;
    };
    class NondetExpr : public Exprv  {
        public:
            NondetExpr(VarType _nondet_type);

            string print() override;
            // void toStream(std::iostream fmt) override;

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
            int canInline(Expr expr);
            // Expr simplifyNondetExpr(NondetExpr expr);
    };

    class SSAProgram {
        public:
            SSAProgram();
            void simplify(Simplifier::SimplLevel level, int visualize_progress = 0);
            void write(FILE* outputFile, int skip_redundant);
            void printStats(int skip_redundant);
            void addStmt(Stmt stmt);
            void clear();
        private:
            // int assignments, assertions, assumptions;
            std::vector<Stmt> statements;
    };

}


#endif /* SSA_STRUCTS_H */

