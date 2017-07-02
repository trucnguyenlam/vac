//
// Created by esteffin on 25/04/17.
//

#ifndef VACSAT_LOGICS_H
#define VACSAT_LOGICS_H

#include <set>
#include <map>
#include <memory>
#include <vector>
#include <sstream>
#include <iostream>

#include "prelude.h"
#include "config.h"
#include "SMT.h"

namespace SMT {
    class Defs {
        public:
            static constexpr char line_end[] = ";";
            static constexpr char and_op[] = " & ";
            static constexpr char or_op[] = " | ";
            static constexpr char not_op[] = "!";
            static constexpr char assign_op[] = " = ";
            static constexpr char eq_op[] = "=";
            static constexpr char impl_op[] = " => ";
            static constexpr char open_comment[] = "// ";
            static constexpr char assume_str[] = "__VERIFIER_assume";
            static constexpr char assert_str[] = "assert";
            static constexpr char nondet_str[] = "nondet_";
            static constexpr char int_ty_str[] = "int";
            static constexpr char bool_ty_str[] = "_Bool";
            static constexpr char true_str[] = "TRUE";
            static constexpr char false_str[] = "FALSE";
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

    class Simplifier;

    class Atom;

    typedef std::shared_ptr<Atom> Atomp;

    class Literal;
    typedef std::shared_ptr<Literal> Literalp;
//    typedef std::weak_ptr<Literal> Literalw;
//    typedef Literalp Atom;

    class Constant;
    typedef std::shared_ptr<Constant> Constantp;

    class OrExpr;
    typedef std::shared_ptr<OrExpr> OrExprp;

    class AndExpr;
    typedef std::shared_ptr<AndExpr> AndExprp;

    class ImplExpr;
    typedef std::shared_ptr<ImplExpr> ImplExprp;

    class EqExpr;
    typedef std::shared_ptr<EqExpr> EqExprp;

    class NotExpr;
    typedef std::shared_ptr<NotExpr> NotExprp;

    class CondExpr;
    typedef std::shared_ptr<CondExpr> CondExprp;

    class Atom : public std::enable_shared_from_this<Atom> {
    public:

        Atom(const std::string _name, int _role_array_index, int bv_size, Expr value = nullptr);
        bool equals(const Atomp& other) const;

        const std::string getSMTName() const;
        const std::string fullName() const;
        const std::string nameWithSuffix(std::string suffix) const;

        void setValue(Expr  value);
        void resetValue();

        std::string to_string() const;
        std::string to_arbac_string() const;
        std::string to_new_string(std::string& uname) const;
        friend std::ostream & operator<<(std::ostream & out, Atom const & atom);

        inline Expr get_value() const {
            return value;
        }


        std::string name;
        // Index in the role_array
        int role_array_index;
        // VarType type;
        int bv_size;
        std::string suffix;

    private:
        Expr value;
    };

    class Exprv {
        public:
        friend Simplifier;
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

        Exprv(ExprType ty, std::set<Atomp> literals);

        virtual bool equals(const Expr& other) const = 0;


//        bool containsLiteral(std::string full_name);
//        bool containsLiteral(Literalp lit);
//        virtual void setSuffix(int idx);
//        virtual void setSuffix(std::string suffix);
//        virtual void resetSuffix();
//        void setLiteralValue(Literalp lit, Expr value);
//        void setLiteralValue(std::string lit_name, Expr value);
//        void resetValue(std::string lit_name = "");

        void set_value(Expr value);
        Expr& get_value();
        friend std::ostream & operator<<(std::ostream & out, Exprv const & expr);
        virtual std::string to_string() const = 0;
        virtual std::string to_arbac_string() const = 0;
        virtual std::string to_new_string(std::string& uname) const = 0;

        //FIXME: update otherwise could be not valid
        virtual const std::set<Atomp>& atoms();

        ExprType type;
        ulong64 node_idx;

        static ulong64 counter;


    protected:
        Expr value;
        std::set<Atomp> _atoms;
    };

    class Literal : public Exprv {
    public:
        friend Simplifier;

        Literal(Atomp _inner);
        bool equals(const Expr& other) const override;

        const std::string getSMTName() const;
        const std::string fullName() const;
        const std::string nameWithSuffix(std::string suffix) const;

//        void setValue(Expr  value);
//        void resetValue();

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        inline Expr get_value() const {
            return atom->get_value();
        }

        const Atomp atom;
    };
    class Constant : public Exprv  {
    public:
        friend Simplifier;
        Constant(int val, int bv_size);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        int value;
        int bv_size;
        ExprType expr_type;
    };
    class OrExpr : public Exprv  {
    public:
        friend Simplifier;
        OrExpr(Expr _lhs, Expr _rhs);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr lhs;
        Expr rhs;
    };
    class AndExpr : public Exprv  {
    public:
        friend Simplifier;
        AndExpr(Expr _lhs, Expr _rhs);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr lhs;
        Expr rhs;
    };
    class EqExpr : public Exprv  {
    public:
        friend Simplifier;
        EqExpr(Expr _lhs, Expr _rhs);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr lhs;
        Expr rhs;
    };
    class ImplExpr : public Exprv  {
    public:
        friend Simplifier;
        ImplExpr(Expr _lhs, Expr _rhs);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr lhs;
        Expr rhs;
    };
    class NotExpr : public Exprv  {
    public:
        friend Simplifier;
        NotExpr(Expr _expr);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr expr;
    };
    class CondExpr : public Exprv  {
    public:
        friend Simplifier;
        CondExpr(Expr _cond, Expr _choice1, Expr _choice2);
        bool equals(const Expr& other) const override;

        std::string to_string() const override;
        std::string to_arbac_string() const override;
        std::string to_new_string(std::string& uname) const override;

        Expr cond;
        Expr choice1;
        Expr choice2;
    };

    Atomp createAtomp(const std::string _name, int _role_array_index, int _bv_size, Expr _value = nullptr);

    Literalp createLiteralp(Atomp atom);
//    Expr createLiteralExpr(Atomp atom);
    Expr createConstantExpr(int value, int bv_size);
    Expr createConstantTrue();
    Expr createConstantFalse();
    Expr createOrExpr(Expr lhs, Expr rhs);
    Expr createAndExpr(Expr lhs, Expr rhs);
    Expr createImplExpr(Expr lhs, Expr rhs);
    Expr createNotExpr(Expr expr);
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2);
    // Expr createNondetExpr(Exprv::ExprType type);
    Expr createEqExpr(Expr lhs, Expr rhs);

    Expr joinBigAnd(const std::list<Expr>& exprs);

    bool is_constant_true(const Expr& expr);
    bool is_constant_false(const Expr& expr);

    Expr normalize_expr(Expr expr);
    Expr or_to_xor(Expr expr);

    Expr delete_atom(Expr expr, Atomp atom);

    Expr guard_atom(Expr expr, const Literalp& lit, const Expr& guard);

    std::list<Expr> get_toplevel_or(const Expr& expr);

    Expr clone_but_lits(const Expr& expr);

    Expr clone_substitute(const Expr& expr, const Expr& substitute, const Expr& with);

    std::list<std::pair<int, OrExprp>> get_or_expressions(const Expr& expr, int level);

    // THIS FUNCTION DIFFERS FROM THE PREVIOUS BECAUSE THE FIRST RETURNS ALL THE OR (E.G. FALSE | A), WHILE THIS ONLY THE VALID ONES
    std::list<std::pair<int, OrExprp>> get_proper_or_expressions_sorted(const Expr& expr, int max_level, int level);
//    std::list<std::pair<int, Expr>> get_internal_or_expressions(const Expr& expr, int max_level, int level);

    // Expr - Solver expr funtions
    template<typename TVar>
    struct TVarWrapper {
    public:
        TVarWrapper(std::shared_ptr<TVar> _solver_varp) : solver_varp(_solver_varp) { }

        inline TVar get_solver_var() const {
            if (solver_varp == nullptr)
                throw std::runtime_error("Null variable");
            else {
                return *solver_varp;
            }
        }

        std::shared_ptr<TVar> solver_varp;
    };

    template <typename TVar, typename TLookup>
    TLookup update_tlookup(const TLookup& base_lookup, const TLookup& new_lookup);

    template <typename TVar>
    std::map<std::string, TVar> update_tlookup(const std::map<std::string, TVar>& base_lookup,
                                               const std::map<std::string, TVar>& new_lookup) {
        std::map<std::string, TVar> res(base_lookup);

        for (auto ite = new_lookup.begin(); ite != new_lookup.end(); ++ite) {
            res[ite->first] = ite->second;
        }
        return res;
    };

    template <typename TVar>
    std::vector<std::shared_ptr<TVar>> update_tlookup(const std::vector<std::shared_ptr<TVar>>& base_lookup,
                                                      const std::vector<std::shared_ptr<TVar>>& new_lookup) {
        if (base_lookup.size() != new_lookup.size()) {
            log->error("Cannot update vector of different size.");
            throw std::runtime_error("Cannot update vector of different size.");
        }
        std::vector<std::shared_ptr<TVar>> res(base_lookup);

        for (int i = 0; i < new_lookup.size(); ++i) {
            if (new_lookup[i] != nullptr) {
                res[i] = new_lookup[i];
            }
        }
        return res;
    };

    template <typename TVar, typename TExpr, typename TLookup>
    TExpr generateSMTFunction(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, const Expr& expr, TLookup& lookup,
                               const std::string suffix);



    template <typename TVar, typename TExpr, typename TLookup>
    TExpr atomToSMT(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                    const Atomp& atom,
                    TLookup& lookup,
                    const std::string suffix);

    template <typename TVar, typename TExpr>
    TExpr atomToSMT(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                    const Atomp& atom,
                    std::vector<std::shared_ptr<TExpr>>& var_vector,
                    const std::string suffix) {
        if (atom->get_value() == nullptr) {
            std::string name = atom->nameWithSuffix(suffix);
            if (var_vector[atom->role_array_index] != nullptr) {
                return *var_vector[atom->role_array_index];
            }
            else {
                TVar var = solver->createVar2(name, atom->bv_size);
                var_vector[atom->role_array_index] = std::make_shared<TVar>(var);
                // printf("%s not found. Creating it: %d\n", name.c_str(), var);
                return var;
            }
        }
        else {
            return generateSMTFunction(solver, atom->get_value(), var_vector, suffix);
        }
    }

    template <typename TVar, typename TExpr>
    TExpr atomToSMT(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                    const Atomp& atom,
                    std::map<std::string, TVar>& var_map,
                    const std::string suffix) {
        if (atom->get_value() == nullptr) {
            std::string name = atom->nameWithSuffix(suffix);
            if (var_map.find(name) != var_map.end()) {
                return var_map[name];
            }
            else {
                TVar var = solver->createVar2(name, atom->bv_size);
                var_map[name] = var;
                // printf("%s not found. Creating it: %d\n", name.c_str(), var);
                return var;
            }
        }
        else {
            return generateSMTFunction(solver, atom->get_value(), var_map, suffix);
        }
    }

    template <typename TVar, typename TExpr, typename TWrapper>
    TExpr atomToSMT(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                    const Atomp& atom,
                    std::vector<TWrapper>& var_vector,
                    const std::string suffix) {
        static_assert(std::is_base_of<TVarWrapper<TVar>, TWrapper>::value, "TWrapper not derived from TWrapper<TVar>");

        if (atom->get_value() == nullptr) {
            std::string name = atom->nameWithSuffix(suffix);
            if (var_vector[atom->role_array_index].solver_varp != nullptr) {
                return *var_vector[atom->role_array_index].solver_varp;
            } else {
                std::stringstream fmt;
                fmt << "Error in literalToSMT with vector<TWrapper>." << std::endl;
                fmt << "Lookup table does not contain item with index " << atom->role_array_index
                    << " and could not be instantiated.";
                throw std::runtime_error(fmt.str());
            }
        } else {
            return generateSMTFunction(solver, atom->get_value(), var_vector, suffix);
        }

    }


    /*template <typename TVar, typename TExpr>
    TExpr literalToSMT<std::map<std::string, TVar>>(std::shared_ptr<SMTFactory<TVar, TExpr>> solver, Literalp lit, std::map<std::string, TVar>& var_map, std::string suffix) {
        if (lit->value == nullptr) {
            std::string name = lit->nameWithSuffix(suffix);
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
            return generateSMTFunction(solver, lit->value, var_map, suffix);
        }
    };*/

    template <typename TVar, typename TExpr, typename TLookup>
    TExpr generateSMTFunction(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver, const Expr& expr, TLookup& lookup,
                               const std::string suffix) {
        if (expr->get_value() != nullptr) {
            return generateSMTFunction(solver, expr->get_value(), lookup, suffix);
        }
        switch (expr->type) {
            case Exprv::CONSTANT: {
                std::shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(expr);
                if (c->bv_size == 1) {
                    return solver->createBoolConst(c->value);
                } else {
                    return solver->createBVConst(c->value, c->bv_size);
                }
            }
            case Exprv::LITERAL: {
                Literalp lit = std::dynamic_pointer_cast<Literal>(expr);
                return atomToSMT(solver, lit->atom, lookup, suffix);

            }
            case Exprv::AND_EXPR: {
                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                TExpr slhs = generateSMTFunction(solver, andExpr->lhs, lookup, suffix);
                TExpr srhs = generateSMTFunction(solver, andExpr->rhs, lookup, suffix);
                return solver->createAndExpr(slhs, srhs);
            }
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                TExpr slhs = generateSMTFunction(solver, orExpr->lhs, lookup, suffix);
                TExpr srhs = generateSMTFunction(solver, orExpr->rhs, lookup, suffix);
                return solver->createOrExpr(slhs, srhs);
            }
            case Exprv::IMPL_EXPR: {
                std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
                TExpr slhs = generateSMTFunction(solver, implExpr->lhs, lookup, suffix);
                TExpr srhs = generateSMTFunction(solver, implExpr->rhs, lookup, suffix);
                return solver->createImplExpr(slhs, srhs);
            }
            case Exprv::COND_EXPR: {
                std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
                TExpr scond = generateSMTFunction(solver, condExpr->cond, lookup, suffix);
                TExpr schoice1 = generateSMTFunction(solver, condExpr->choice1, lookup, suffix);
                TExpr schoice2 = generateSMTFunction(solver, condExpr->choice2, lookup, suffix);
                return solver->createCondExpr(scond, schoice1, schoice2);
            }
            case Exprv::EQ_EXPR: {
                std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
                TExpr slhs = generateSMTFunction(solver, eqExpr->lhs, lookup, suffix);
                TExpr srhs = generateSMTFunction(solver, eqExpr->rhs, lookup, suffix);
                return solver->createEqExpr(slhs, srhs);
            }
            case Exprv::NOT_EXPR: {
                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                TExpr sexpr = generateSMTFunction(solver, notExpr->expr, lookup, suffix);
                return solver->createNotExpr(sexpr);
            }
            default:
                break;
        }
        throw std::runtime_error("Cannot translate expression to SMT");
        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    }


    template <typename TVar, typename TExpr, typename TLookup>
    TExpr generateSMTFunction2(const std::shared_ptr<SMTFactory<TVar, TExpr>>& solver,
                               const Expr& expr,
                               const std::set<Expr>& lookup2_exprs,
                               TLookup& lookup1,
                               TLookup& lookup2,
                               const std::string& suffix1,
                               const std::string& suffix2) {
        if (expr->get_value() != nullptr) {
            return generateSMTFunction2(solver, expr->get_value(), lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
        }
//        log->trace("Translating: {}", *expr);
        if (contains(lookup2_exprs, expr)) {
//            log->trace("Found {} for translation with {}", *expr, suffix2);
            return generateSMTFunction(solver, expr, lookup2, suffix2);
        }
        switch (expr->type) {
            case Exprv::CONSTANT: {
                std::shared_ptr<Constant> c = std::dynamic_pointer_cast<Constant>(expr);
                if (c->bv_size == 1) {
                    return solver->createBoolConst(c->value);
                } else {
                    return solver->createBVConst(c->value, c->bv_size);
                }
            }
            case Exprv::LITERAL: {
                Literalp lit = std::dynamic_pointer_cast<Literal>(expr);
                return atomToSMT(solver, lit->atom, lookup1, suffix1);

            }
            case Exprv::AND_EXPR: {
                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                TExpr slhs = generateSMTFunction2(solver, andExpr->lhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr srhs = generateSMTFunction2(solver, andExpr->rhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createAndExpr(slhs, srhs);
            }
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                TExpr slhs = generateSMTFunction2(solver, orExpr->lhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr srhs = generateSMTFunction2(solver, orExpr->rhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createOrExpr(slhs, srhs);
            }
            case Exprv::IMPL_EXPR: {
                std::shared_ptr<ImplExpr> implExpr = std::dynamic_pointer_cast<ImplExpr>(expr);
                TExpr slhs = generateSMTFunction2(solver, implExpr->lhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr srhs = generateSMTFunction2(solver, implExpr->rhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createImplExpr(slhs, srhs);
            }
            case Exprv::COND_EXPR: {
                std::shared_ptr<CondExpr> condExpr = std::dynamic_pointer_cast<CondExpr>(expr);
                TExpr scond = generateSMTFunction2(solver, condExpr->cond, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr schoice1 = generateSMTFunction2(solver, condExpr->choice1, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr schoice2 = generateSMTFunction2(solver, condExpr->choice2, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createCondExpr(scond, schoice1, schoice2);
            }
            case Exprv::EQ_EXPR: {
                std::shared_ptr<EqExpr> eqExpr = std::dynamic_pointer_cast<EqExpr>(expr);
                TExpr slhs = generateSMTFunction2(solver, eqExpr->lhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                TExpr srhs = generateSMTFunction2(solver, eqExpr->rhs, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createEqExpr(slhs, srhs);
            }
            case Exprv::NOT_EXPR: {
                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                TExpr sexpr = generateSMTFunction2(solver, notExpr->expr, lookup2_exprs, lookup1, lookup2, suffix1, suffix2);
                return solver->createNotExpr(sexpr);
            }
            default:
                break;
        }
        throw std::runtime_error("Cannot translate expression to SMT");
    };

    class Simplifier {
         public:
             enum SimplLevel {
                 NOTHING,
                 INLINE_KNOWN
             };
             Simplifier(SimplLevel _level);
             Expr simplifyExpr(Expr expr) const;
         private:
             SimplLevel level;

            Expr simplifyLiteral(std::shared_ptr<Literal> expr) const;
            Expr simplifyConstant(std::shared_ptr<Constant> expr) const;
            Expr simplifyOrExpr(std::shared_ptr<OrExpr> expr) const;
            Expr simplifyAndExpr(std::shared_ptr<AndExpr> expr) const;
            Expr simplifyEqExpr(std::shared_ptr<EqExpr> expr) const;
            Expr simplifyImplExpr(std::shared_ptr<ImplExpr> expr) const;
            Expr simplifyNotExpr(std::shared_ptr<NotExpr> expr) const;
            Expr simplifyCondExpr(std::shared_ptr<CondExpr> expr) const;
     };

    inline Expr simplifyExpr(Expr expr) {
        return Simplifier(Simplifier::NOTHING).simplifyExpr(expr);
    }

    // EXPR COMPARER
    struct deepCmpExprs {
        int operator()(const Expr& e1, const Expr& e2) const;
    };


}

#endif //VACSAT_LOGICS_H
