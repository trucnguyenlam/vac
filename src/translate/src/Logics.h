#pragma once

#include <set>
#include <map>
#include <memory>

#include <SMT.h>

namespace SMT {
    class Defs {
        public:
            static constexpr char line_end[] = ";";
            static constexpr char and_op[] = " && ";
            static constexpr char or_op[] = " || ";
            static constexpr char not_op[] = "!";
            static constexpr char assign_op[] = " = ";
            static constexpr char eq_op[] = " == ";
            static constexpr char impl_op[] = " => ";
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

    class SMTKeyword {
        public:
            static constexpr char comment[] = ";";
            static constexpr char and_op[] = "and";
            static constexpr char or_op[] = "or";
            static constexpr char not_op[] = "not";
            static constexpr char eq_op[] = "=";
            static constexpr char declare[] = "declare-fun";
            static constexpr char cond_expr[] = "ite";
            static constexpr char assume[] = "assume";
            static constexpr char assert[] = "assert";
            static constexpr char check[] = "check-sat";
            static constexpr char nondet_str[] = "nondet_";
            static constexpr char int_ty_str[] = "Int";
            static constexpr char bool_ty_str[] = "Bool";
            static constexpr char true_str[] = "true";
            static constexpr char false_str[] = "false";
            static std::string bv_ty_str(int bv_size);
    };

    class Exprv;
    
    typedef std::shared_ptr<Exprv> Expr;

    class Literal;
    typedef std::shared_ptr<Literal> Literalp;
    
    class Constant;
    typedef std::shared_ptr<Constant> Constantp;

    class Exprv {
        public:
            enum VarType {
                    INT,
                    BOOL
                };
            enum ExprType {
                CONSTANT,
                LITERAL,
                EQ_EXPR,
                NOT_EXPR,
                OR_EXPR,
                AND_EXPR,
                COND_EXPR,
                IMPL_EXPR,
            };

        Exprv(ExprType ty, std::set<Literalp> literals);
        
        void setSuffix(int idx);
        void setSuffix(std::string suffix);
        void resetSuffix();
        void setLiteralValue(std::string lit_name, Expr value);
        void resetValue(std::string lit_name = "");
        
        virtual std::string print() = 0;
        // virtual void toFile(FILE* outputFile) = 0;
        // virtual void toSMT(FILE* outputFile) = 0;

        std::set<std::shared_ptr<Literal>> literals();

        // template <typename TType, typename TVar, typename TExpr>
        // virtual TExpr generateSMTFormula(SMTFactory<TType, TVar, TExpr>) = 0;

        ExprType type;

    protected:
        std::set<Literalp> _literals;
    };

    class Literal : public Exprv {
        public:
            Literal(const std::string _name, int bv_size, Expr _value = nullptr);

            std::string getSMTName();
            std::string fullName();

            void setLiterals(Literalp &self);
            void setSuffix(std::string suffix);
            void setSuffix(int idx);
            void resetSuffix();
            void setValue(Expr  value);
            void resetValue();
            
            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;
            // void writeSMTDeclaration(FILE* outputFile);

            // std::set<std::shared_ptr<Literal>> literals() override;
        
            std::string name;
            // VarType type;
            int bv_size;
            Expr value;
            std::string suffix;
    };
    class Constant : public Exprv  {
        public:
            Constant(int val, int bv_size);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;
            
            // std::set<std::shared_ptr<Literal>> literals() override;

            int value;
            int bv_size;
            ExprType expr_type;
    };
    class OrExpr : public Exprv  {
        public:
            OrExpr(Expr _lhs, Expr _rhs);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr lhs;
            Expr rhs;
        // private:
        //     std::set<Literalp> _literals;
    };
    class AndExpr : public Exprv  {
        public:
            AndExpr(Expr _lhs, Expr _rhs);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr lhs;
            Expr rhs;
        // private:
        //     std::set<Literalp> _literals;            
    };
    class EqExpr : public Exprv  {
        public:
            EqExpr(Expr _lhs, Expr _rhs);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr lhs;
            Expr rhs;
        // private:
        //     std::set<Literalp> _literals;
    };
    class ImplExpr : public Exprv  {
        public:
            ImplExpr(Expr _lhs, Expr _rhs);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr lhs;
            Expr rhs;
        // private:
        //     std::set<Literalp> _literals;
    };
    class NotExpr : public Exprv  {
        public:
            NotExpr(Expr _expr);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr expr;
        // private:
        //     std::set<Literalp> _literals;
    };
    class CondExpr : public Exprv  {
        public:
            CondExpr(Expr _cond, Expr _choice1, Expr _choice2);

            std::string print() override;
            // void toFile(FILE* outputFile) override;
            // void toSMT(FILE* outputFile) override;

            // std::set<std::shared_ptr<Literal>> literals() override;

            Expr cond;
            Expr choice1;
            Expr choice2;

        // private:
        //     std::set<Literalp> _literals;
    };
    // class NondetExpr : public Exprv  {
    //     public:
    //         NondetExpr(VarType _nondet_type);

    //         std::string print() override;
    //         void toFile(FILE* outputFile) override;
    //         void toSMT(FILE* outputFile) override;

    //         VarType nondet_type;
    //  };

    Literalp createLiteralp(const std::string name, int bv_size, Expr value = nullptr);

    Expr createLiteralExpr(const std::string name, int bv_size, Expr value = nullptr);
    Expr createConstantExpr(int value, int bv_size);
    Expr createOrExpr(Expr lhs, Expr rhs);
    Expr createAndExpr(Expr lhs, Expr rhs);
    Expr createImplExpr(Expr lhs, Expr rhs);
    Expr createNotExpr(Expr expr);
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2);
    // Expr createNondetExpr(Exprv::ExprType type);
    Expr createEqExpr(Expr lhs, Expr rhs);

    template <typename TVar, typename TExpr>
    TExpr generateSMTFunction(std::shared_ptr<SMTFactory<TVar, TExpr>> solver, Expr expr, std::map<std::string, TVar>& var_map) {
        switch (expr->type) {
                case Exprv::CONSTANT: {
                    std::shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(expr);
                    if (c->bv_size == 1) {
                        return solver->createBoolConst(c->value);
                    }
                    else {
                        return solver->createBVConst(c->value, c->bv_size);
                    } 
                }
                case Exprv::LITERAL: {
                    Literalp lit = std::dynamic_pointer_cast<Literal>(expr);
                    if (lit->value == nullptr) {
                        std::string name = lit->fullName();
                        if(var_map.find(name) != var_map.end()) {
                            return var_map[name];
                        }
                        else {
                            TVar var = solver->createVar2(name, lit->bv_size);
                            var_map[name] = var;
                            // printf("%s not found. Creating it: %d\n", name.c_str(), var);
                            return var;
                        }
                    }
                    else {
                        return generateSMTFunction(solver, lit->value, var_map);
                    }
                    
                }
                case Exprv::AND_EXPR: {
                    std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                    TExpr slhs = generateSMTFunction(solver, andExpr->lhs, var_map);
                    TExpr srhs = generateSMTFunction(solver, andExpr->rhs, var_map);
                    return solver->createAndExpr(slhs, srhs);
                }
                case Exprv::OR_EXPR: {
                    std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                    TExpr slhs = generateSMTFunction(solver, orExpr->lhs, var_map);
                    TExpr srhs = generateSMTFunction(solver, orExpr->rhs, var_map);
                    return solver->createOrExpr(slhs, srhs);
                }
                case Exprv::IMPL_EXPR: {
                    std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
                    TExpr slhs = generateSMTFunction(solver, implExpr->lhs, var_map);
                    TExpr srhs = generateSMTFunction(solver, implExpr->rhs, var_map);
                    return solver->createImplExpr(slhs, srhs);
                }
                case Exprv::COND_EXPR: {
                    std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
                    TExpr scond = generateSMTFunction(solver, condExpr->cond, var_map);
                    TExpr schoice1 = generateSMTFunction(solver, condExpr->choice1, var_map);
                    TExpr schoice2 = generateSMTFunction(solver, condExpr->choice2, var_map);                    
                    return solver->createCondExpr(scond, schoice1, schoice2);
                }
                case Exprv::EQ_EXPR: {
                    std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
                    TExpr slhs = generateSMTFunction(solver, eqExpr->lhs, var_map);
                    TExpr srhs = generateSMTFunction(solver, eqExpr->rhs, var_map);
                    return solver->createEqExpr(slhs, srhs);
                }
                case Exprv::NOT_EXPR:{
                    std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                    TExpr sexpr = generateSMTFunction(solver, notExpr->expr, var_map);
                    return solver->createNotExpr(sexpr);
                }
                default:
                    break;
            }
            throw new std::runtime_error("Cannot translate expression to SMT");
            fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->print().c_str());
    }

    // class Simplifier {
    //     public:
    //         enum SimplLevel {
    //             NOTHING,
    //             CONST_VARS,
    //             UN_OPS,
    //             LBIN_OPS,
    //             EQUALITY,
    //             ALL
    //         };
    //         Simplifier(SimplLevel _level);
    //         void simplifyStmt(Stmt stmt);
    //         Expr simplifyExpr(Expr expr);
    //     private:
    //         SimplLevel level;
    //         void simplifyAssignment(shared_ptr<Assignment> stmt);
    //         void simplifyAssertion(shared_ptr<Assertion> stmt);
    //         void simplifyAssumption(shared_ptr<Assumption> stmt);
    //         Expr simplifyVariable(shared_ptr<Variable> expr);
    //         Expr simplifyConstant(shared_ptr<Constant> expr);
    //         Expr simplifyOrExpr(shared_ptr<OrExpr> expr);
    //         Expr simplifyAndExpr(shared_ptr<AndExpr> expr);
    //         Expr simplifyEqExpr(shared_ptr<EqExpr> expr);
    //         Expr simplifyNotExpr(shared_ptr<NotExpr> expr);
    //         Expr simplifyCondExpr(shared_ptr<CondExpr> expr);
    //         int canInline(Expr expr);
    //         // Expr simplifyNondetExpr(NondetExpr expr);
    // };
 
 
}