#include "Logics.h"

#include <iostream>
#include <sstream>
#include <chrono>
#include <regex>
#include <stdexcept>
#include <assert.h>
#include <algorithm>
#include <utility>


namespace SMT {

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
    ulong64 Exprv::counter = 0;
    Exprv::Exprv(ExprType ty, std::set<Literalw, std::owner_less<Literalw>> literals) : type(ty), node_idx(counter++), _literals(literals) { }
    /*
     * bool Exprv::containsLiteral(std::string full_name) {
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
    }*/

    const std::set<Literalw, std::owner_less<Literalw>>& Exprv::literals() {
        return this->_literals;
     }

    std::ostream & operator<<(std::ostream& out, Exprv const & expr) {
        out << expr.to_string();

        return out;
    }
    
/*LITERAL OPS*/
    Literal::Literal(const std::string _name, int _role_array_index, int _bv_size, Expr _value):
        Exprv(Exprv::LITERAL, std::set<Literalw, std::owner_less<Literalw>>()),
        name(_name), role_array_index(_role_array_index), bv_size(_bv_size), value(_value) { }

    bool Literal::equals(const Expr &other) const {
        if (other->type != Exprv::LITERAL)
            return false;
        Literalp other_lit = std::dynamic_pointer_cast<Literal>(other);

        return  this->role_array_index == other_lit->role_array_index &&
                this->name == other_lit->name &&
                this->bv_size == other_lit->bv_size;
    }

    /*
     * void Literal::setLiterals(Literalp &self) {
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
    }*/
    void Literal::setValue(Expr value) {
        this->value = value;
    }
    void Literal::resetValue() {
        this->value = nullptr;
    }
    const std::set<Literalw, std::owner_less<Literalw>>& Literal::literals() {
        if (this->_literals.size() < 1) {
            _literals.insert(get_ptr());
        }
        return _literals;
    }

    const std::string Literal::getSMTName() const {
        return this->fullName();
    }

    const std::string Literal::fullName() const {
        if (this->suffix == "") {
            return this->name;
        }
        else {
            std::stringstream fmt;
            fmt << this->name + "_" + this->suffix;
            return fmt.str();
        }
    }

    std::shared_ptr<Literal> Literal::get_ptr() {
        return shared_from_this();
    }

    const std::string Literal::nameWithSuffix(std::string suffix) const {
//        if (this->suffix == "") {
            return this->fullName() + "_" + suffix;
//        }
//        else {
//            std::stringstream fmt;
//            fmt << this->name + "_" + this->suffix;
//            return fmt.str();
//        }
    }

    std::string Literal::to_string() const {
        std::stringstream fmt;
        // fmt << "|" << this->fullName() << "|";
        fmt << this->fullName();
        return fmt.str();
    }
    std::string Literal::to_arbac_string() const {
        std::stringstream fmt;
        fmt << this->name;
        return fmt.str();
    }
    std::string Literal::to_new_string(std::string& uname) const {
        return uname + "." + this->name + "=1";
    }

/*CONSTANT OPS*/
    Constant::Constant(int _value, int _bv_size) :
        Exprv(Exprv::CONSTANT, std::set<Literalw, std::owner_less<Literalw>>()),
        value(_value), bv_size(_bv_size) { }

    bool Constant::equals(const Expr &other) const {
        if (other->type != Exprv::CONSTANT)
            return false;
        Constantp other_lit = std::dynamic_pointer_cast<Constant>(other);

        return  this->bv_size == other_lit->bv_size &&
                this->value == other_lit->value;
    }

    std::string Constant::to_string() const {
        if (this->bv_size == 1) {
            if (this->value) {
                return Defs::true_str + std::string(":Bool");
            }
            else {
                return Defs::false_str + std::string(":Bool");
            }
        }
        else {
            std::stringstream fmt;
            fmt << this->value;
            fmt << ":BV[" << this->bv_size << "]";
            return fmt.str();
        }
    }
    std::string Constant::to_arbac_string() const {
        if (this->bv_size == 1) {
            if (this->value) {
                return Defs::true_str;
            }
            else {
                log->error("Could not print a false constant in ARBAC style: {}", *this);
                throw std::runtime_error("Could not print a false constant in ARBAC style");
            }
        }
        else {
            log->error("Could not print a bitvector constant in ARBAC style: {}", *this);
            throw std::runtime_error("Could not print a bitvector constant in ARBAC style");
        }
    }
    std::string Constant::to_new_string(std::string& uname) const {
        if (bv_size == 1) {
            return this->value ? "1" : "0";
        }
        return std::to_string(value);
    }
    
/*OR OPS*/
    OrExpr::OrExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::OR_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }
    bool OrExpr::equals(const Expr &other) const {
        if (other->type != Exprv::OR_EXPR)
            return false;
        std::shared_ptr<OrExpr> other_expr = std::dynamic_pointer_cast<OrExpr>(other);

        return  (this->lhs->equals(other_expr->lhs) && this->rhs->equals(other_expr->rhs)) ||
                (this->lhs->equals(other_expr->rhs) && this->rhs->equals(other_expr->lhs));
    }
    
    std::string OrExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::or_op << rhsv << ")";
        return fmt.str();
    }
    std::string OrExpr::to_arbac_string() const {
        log->error("Cannot print in ARBAC grammar OR_EXPR: {}", *this);
        throw std::runtime_error("UNSUPPORTED ARBAC STYLE PRINT: OR_EXPR");
    }
    std::string OrExpr::to_new_string(std::string& uname) const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_new_string(uname);
        std::string rhsv = this->rhs->to_new_string(uname);
        fmt << "(" << lhsv << Defs::or_op << rhsv << ")";
        return fmt.str();
    }

/*AND OPS*/
    AndExpr::AndExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::AND_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }
    bool AndExpr::equals(const Expr &other) const {
        if (other->type != Exprv::AND_EXPR)
            return false;
        std::shared_ptr<AndExpr> other_expr = std::dynamic_pointer_cast<AndExpr>(other);

        return  (this->lhs->equals(other_expr->lhs) && this->rhs->equals(other_expr->rhs)) ||
                (this->lhs->equals(other_expr->rhs) && this->rhs->equals(other_expr->lhs)) ;
    }

    std::string AndExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::and_op << rhsv << ")";
        return fmt.str();
    }
    std::string AndExpr::to_arbac_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_arbac_string();
        std::string rhsv = this->rhs->to_arbac_string();
        fmt << lhsv << Defs::and_op << rhsv;
        return fmt.str();
    }
    std::string AndExpr::to_new_string(std::string& uname) const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_new_string(uname);
        std::string rhsv = this->rhs->to_new_string(uname);
        fmt << "(" << lhsv << Defs::and_op << rhsv << ")";
        return fmt.str();
    }

/*EQ OPS*/
    EqExpr::EqExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::EQ_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }
    bool EqExpr::equals(const Expr &other) const {
        if (other->type != Exprv::EQ_EXPR)
            return false;
        std::shared_ptr<EqExpr> other_expr = std::dynamic_pointer_cast<EqExpr>(other);

        return  (this->lhs->equals(other_expr->lhs) && this->rhs->equals(other_expr->rhs)) ||
                (this->lhs->equals(other_expr->rhs) && this->rhs->equals(other_expr->lhs));
    }
    
    std::string EqExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::eq_op << rhsv << ")";
        return fmt.str();
    }
    std::string EqExpr::to_arbac_string() const {
        log->error("Cannot print in ARBAC grammar EQ_EXPR: {}", *this);
        throw std::runtime_error("UNSUPPORTED ARBAC STYLE PRINT: EQ_EXPR");
    }
    std::string EqExpr::to_new_string(std::string& uname) const {
        std::stringstream fmt;
        std::string slhsv = lhs->type == LITERAL ? uname + "." + (std::dynamic_pointer_cast<Literal>(lhs))->name : lhs->to_new_string(uname);
        std::string srhsv = rhs->type == LITERAL ? uname + "." + (std::dynamic_pointer_cast<Literal>(rhs))->name : rhs->to_new_string(uname);
        if ((lhs->type == LITERAL && rhs->type == CONSTANT) ||
            (lhs->type == CONSTANT && rhs->type == LITERAL)) {
            fmt << slhsv << Defs::eq_op << srhsv;
        }
        else {
            fmt << "(" << slhsv << Defs::eq_op << srhsv << ")";
        }
        return fmt.str();
    }

/*IMPLICATION OPS*/
    ImplExpr::ImplExpr(Expr _lhs, Expr _rhs) :
        Exprv(Exprv::IMPL_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
        lhs(_lhs), rhs(_rhs) { }
    bool ImplExpr::equals(const Expr &other) const {
        if (other->type != Exprv::IMPL_EXPR)
            return false;
        std::shared_ptr<ImplExpr> other_expr = std::dynamic_pointer_cast<ImplExpr>(other);

        return  this->lhs->equals(other_expr->lhs) &&
                this->rhs->equals(other_expr->rhs);
    }
    
    std::string ImplExpr::to_string() const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_string();
        std::string rhsv = this->rhs->to_string();
        fmt << "(" << lhsv << Defs::impl_op << rhsv << ")";
        return fmt.str();
    }
    std::string ImplExpr::to_arbac_string() const {
        log->error("Cannot print in ARBAC grammar IMPL_EXPR: {}", *this);
        throw std::runtime_error("UNSUPPORTED ARBAC STYLE PRINT: IMPL_EXPR");
    }
    std::string ImplExpr::to_new_string(std::string& uname) const {
        std::stringstream fmt;
        std::string lhsv = this->lhs->to_new_string(uname);
        std::string rhsv = this->rhs->to_new_string(uname);
        fmt << "(" << lhsv << Defs::impl_op << rhsv << ")";
        return fmt.str();
    }

/*NOT OPS*/
    NotExpr::NotExpr(Expr _expr) :
        Exprv(Exprv::NOT_EXPR, _expr->literals()),
        expr(_expr) { }
    bool NotExpr::equals(const Expr &other) const {
        if (other->type != Exprv::NOT_EXPR)
            return false;
        std::shared_ptr<NotExpr> other_expr = std::dynamic_pointer_cast<NotExpr>(other);

        return  this->expr->equals(other_expr->expr);
    }
    
    std::string NotExpr::to_string() const {
        std::stringstream fmt;
        std::string exprv = this->expr->to_string();
        fmt << Defs::not_op << "(" << exprv << ")";
        return fmt.str();
    }
    std::string NotExpr::to_arbac_string() const {
        std::stringstream fmt;
        fmt << "-" << expr->to_arbac_string();
        return fmt.str();
    }
    std::string NotExpr::to_new_string(std::string& uname) const {
        std::stringstream fmt;
        std::string sexpr = this->expr->to_new_string(uname);
        fmt << Defs::not_op << "(" << sexpr << ")";
        return fmt.str();
    }

/*COND OPS*/
    CondExpr::CondExpr(Expr _cond, Expr _choice1, Expr _choice2) :
        Exprv(Exprv::COND_EXPR, 
              setUnion(_cond->literals(), setUnion(_choice1->literals(), _choice2->literals()))),
        cond(_cond), choice1(_choice1), choice2(_choice2) { }
    bool CondExpr::equals(const Expr &other) const {
        if (other->type != Exprv::COND_EXPR)
            return false;
        std::shared_ptr<CondExpr> other_expr = std::dynamic_pointer_cast<CondExpr>(other);

        return  this->cond->equals(other_expr->cond) &&
                this->choice1->equals(other_expr->choice1) &&
                this->choice2->equals(other_expr->choice2);
    }

    std::string CondExpr::to_string() const {
        std::stringstream fmt;
        std::string cond = this->cond->to_string();
        std::string ch1 = this->choice1->to_string();
        std::string ch2 = this->choice2->to_string();
        fmt << "((" << cond << ") ? (" << ch1 << ") : (" << ch2 << "))";
        return fmt.str();
    }
    std::string CondExpr::to_arbac_string() const {
        log->error("Cannot print in ARBAC grammar COND_EXPR: {}", *this);
        throw std::runtime_error("UNSUPPORTED ARBAC STYLE PRINT: COND_EXPR");
    }
    std::string CondExpr::to_new_string(std::string &uname) const {
        std::stringstream fmt;
        std::string cond = this->cond->to_new_string(uname);
        std::string ch1 = this->choice1->to_new_string(uname);
        std::string ch2 = this->choice2->to_new_string(uname);
        fmt << "((" << cond << ") ? (" << ch1 << ") : (" << ch2 << "))";
        return fmt.str();
    }

/*SIMPLIFICATION OPS */
    Simplifier::Simplifier(SimplLevel _level) : level(_level) { }

    Expr Simplifier::simplifyExpr(Expr expr) const {
         switch (expr->type) {
             case Exprv::LITERAL:
                 return simplifyLiteral(std::dynamic_pointer_cast<Literal>(expr));
             case Exprv::CONSTANT:
                 // CAN BE REMOVED SINCE IS ID
                 return simplifyConstant(std::dynamic_pointer_cast<Constant>(expr));
             case Exprv::OR_EXPR:
                 return simplifyOrExpr(std::dynamic_pointer_cast<OrExpr>(expr));
             case Exprv::AND_EXPR:
                 return simplifyAndExpr(std::dynamic_pointer_cast<AndExpr>(expr));
             case Exprv::EQ_EXPR:
                 return simplifyEqExpr(std::dynamic_pointer_cast<EqExpr>(expr));
             case Exprv::IMPL_EXPR:
                 return simplifyImplExpr(std::dynamic_pointer_cast<ImplExpr>(expr));
             case Exprv::NOT_EXPR:
                 return simplifyNotExpr(std::dynamic_pointer_cast<NotExpr>(expr));
             case Exprv::COND_EXPR:
                 return simplifyCondExpr(std::dynamic_pointer_cast<CondExpr>(expr));
             default:
                 throw std::runtime_error("Unknown expression to simplify...");
         }
         // return expr;
     }

    Expr Simplifier::simplifyLiteral(std::shared_ptr<Literal> lit) const {
     if (level == Simplifier::INLINE_KNOWN) {
         return lit->get_value();
     }
     return lit;
    }
    Expr Simplifier::simplifyConstant(std::shared_ptr<Constant> expr) const {
     //TODO: could be removed
     return expr;
    }
    Expr Simplifier::simplifyOrExpr(std::shared_ptr<OrExpr> or_expr) const {
     Expr nlhs, nrhs;
     nlhs = this->simplifyExpr(or_expr->lhs);
     if (nlhs->type == Exprv::CONSTANT) {
         auto lv = (std::dynamic_pointer_cast<Constant>(nlhs));
         if (lv->bv_size > 1) {
             log->error("Cannot simplify something of the form (bitvector_literal || e): ({} {} {})", *nlhs, Defs::or_op, *or_expr->rhs);
             throw std::runtime_error("Cannot simplify something of the form (bitvector_literal || e)");
         }

         if (is_constant_true(nlhs)) {
             return nlhs;
         }
         else {
             return this->simplifyExpr(or_expr->rhs);
         }
     }
     nrhs = this->simplifyExpr(or_expr->rhs);
     if (nrhs->type == Exprv::CONSTANT) {
         auto rv = (std::dynamic_pointer_cast<Constant>(nrhs));
         if (rv->bv_size > 1) {
             log->error("Cannot simplify something of the form (e || bitvector_literal): ({} {} {})", *nlhs, Defs::or_op, *nlhs);
             throw std::runtime_error("Cannot simplify something of the form (e || bitvector_literal)");
         }
         if (is_constant_true(nrhs)) {
             return nrhs;
         }
         else {
             return nlhs;
         }
     }
     return createOrExpr(nlhs, nrhs);
    }
    Expr Simplifier::simplifyAndExpr(std::shared_ptr<AndExpr> and_expr) const {
     Expr nlhs, nrhs;
     nlhs = this->simplifyExpr(and_expr->lhs);
     if (nlhs->type == Exprv::CONSTANT) {
         auto lv = (std::dynamic_pointer_cast<Constant>(nlhs));
         if (lv->bv_size > 1) {
             log->error("Cannot simplify something of the form (bitvector_literal && e): ({} {} {})", *nlhs, Defs::and_op, *and_expr->rhs);
             throw std::runtime_error("Cannot simplify something of the form (bitvector_literal && e)");
         }
         if (is_constant_false(nlhs)) {
             return nlhs;
         }
         else {
             return this->simplifyExpr(and_expr->rhs);
         }
     }
     nrhs = this->simplifyExpr(and_expr->rhs);
     if (nrhs->type == Exprv::CONSTANT) {
         auto rv = (std::dynamic_pointer_cast<Constant>(nrhs));
         if (rv->bv_size > 1) {
             log->error("Cannot simplify something of the form (e && bitvector_literal): ({} {} {})", *nlhs, Defs::and_op, *nrhs);
             throw std::runtime_error("Cannot simplify something of the form (bitvector_literal && e)");
         }
         if (is_constant_false(nrhs)) {
             return nrhs;
         }
         else {
             return nlhs;
         }
     }
     return createAndExpr(nlhs, nrhs);
    }
    Expr Simplifier::simplifyEqExpr(std::shared_ptr<EqExpr> expr) const {
         //TODO: COULD BE IMPROVED
         Expr nlhs = this->simplifyExpr(expr->lhs);
         Expr nrhs = this->simplifyExpr(expr->rhs);

//         if (nlhs->equals(nrhs)) {
         if (nlhs == nrhs) {
             return createConstantExpr(1, 1);
         }

         if (nlhs->type == Exprv::CONSTANT && nrhs->type == Exprv::CONSTANT) {
             std::shared_ptr<Constant> nl = std::dynamic_pointer_cast<Constant>(nlhs);
             std::shared_ptr<Constant> nr = std::dynamic_pointer_cast<Constant>(nrhs);
             return createConstantExpr(nl->value == nr->value, 1);
         }

         return createEqExpr(nlhs, nrhs);
            
     }
    Expr Simplifier::simplifyImplExpr(std::shared_ptr<ImplExpr> impl_expr) const {
        Expr nlhs, nrhs;
        nlhs = this->simplifyExpr(impl_expr->lhs);
        if (nlhs->type == Exprv::CONSTANT) {
            auto lv = (std::dynamic_pointer_cast<Constant>(nlhs));
            if (lv->bv_size > 1) {
                log->error("Cannot simplify something of the form (bitvector_literal ==> e): ({} {} {})", *nlhs, Defs::impl_op, *impl_expr->rhs);
                throw std::runtime_error("Cannot simplify something of the form (bitvector_literal ==> e)");
            }
            if (is_constant_false(nlhs)) {
                return createConstantTrue();
            }
            else {
                return this->simplifyExpr(impl_expr->rhs);
            }
        }
        nrhs = this->simplifyExpr(impl_expr->rhs);
        if (nrhs->type == Exprv::CONSTANT) {
            auto rv = (std::dynamic_pointer_cast<Constant>(nrhs));
            if (rv->bv_size > 1) {
                log->error("Cannot simplify something of the form (e ==> bitvector_literal): ({} {} {})", *nlhs, Defs::impl_op, *nrhs);
                throw std::runtime_error("Cannot simplify something of the form (bitvector_literal ==> e)");
            }
            if (is_constant_true(nrhs)) {
                return createConstantTrue();
            }
            else {
                return createNotExpr(nlhs);
            }
        }
        return createImplExpr(nlhs, nrhs);
    }
    Expr Simplifier::simplifyNotExpr(std::shared_ptr<NotExpr> not_expr) const {
         Expr nexpr = this->simplifyExpr(not_expr->expr);
         if (nexpr->type == Exprv::CONSTANT) {
             auto v = std::dynamic_pointer_cast<Constant>(nexpr);
             if (v->bv_size > 1) {
                 log->error("Cannot simplify something of the form (! bitvector_literal): ({} {})", Defs::not_op, *v);
                 throw std::runtime_error("Cannot simplify something of the form (!bitvector_literal)");
             }
             return createConstantExpr(!(std::dynamic_pointer_cast<Constant>(nexpr))->value, 1);
         }
         if (nexpr->type == Exprv::NOT_EXPR) {
             return std::dynamic_pointer_cast<NotExpr>(nexpr)->expr;
         }
         return createNotExpr(nexpr);
     }
    Expr Simplifier::simplifyCondExpr(std::shared_ptr<CondExpr> cond_expr) const {
         Expr ncond = this->simplifyExpr(cond_expr->cond);
         // If condition is true or false return the selected branch simplified...
         if (ncond->type == Exprv::CONSTANT) {
             auto nv = std::dynamic_pointer_cast<Constant>(ncond);
             if (nv->bv_size > 1) {
                 log->error("Cannot simplify something of the form (bitvector_literal ? e : e): ({} ? {} : {})", *nv, cond_expr->choice1, cond_expr->choice2);
                 throw std::runtime_error("Cannot simplify something of the form (bitvector_literal ? e : e)");
             }
             if (is_constant_true(ncond)) {
                 return this->simplifyExpr(cond_expr->choice1);
             }
             else {
                 return this->simplifyExpr(cond_expr->choice2);
             }
         }

         Expr nch1 = this->simplifyExpr(cond_expr->choice1);
         Expr nch2 = this->simplifyExpr(cond_expr->choice2);
         // If simplified branches are equals simplify removing conditional expression and return it
//         if (nch1->equals(nch2)) {
         if (nch1 == nch2) {
             return nch1;
         }

         // If branches are 1, 0 or 0, 1 replace conditional expression with guard or negation of it respectively
         if (nch1->type == Exprv::CONSTANT && nch2->type == Exprv::CONSTANT) {
             std::shared_ptr<Constant> nc2 = std::dynamic_pointer_cast<Constant>(nch2);
             std::shared_ptr<Constant> nc1 = std::dynamic_pointer_cast<Constant>(nch1);
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

/*EXPR CREATION AND CHECK OPS*/
    Literalp createLiteralp(const std::string name, int role_array_index, int bv_size, Expr value) {
        std::shared_ptr<Literal> res(new Literal(name, role_array_index, bv_size, value));
        return res;
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

    bool is_constant_true(const Expr& expr) {
        switch (expr->type) {
            case Exprv::CONSTANT: {
                Constantp cexpr = std::dynamic_pointer_cast<Constant>(expr);
                return cexpr->bv_size == 1 && cexpr->value != 0;
            }
                break;
            default:
                return false;
        }
    }
    bool is_constant_false(const Expr& expr) {
        switch (expr->type) {
            case Exprv::CONSTANT: {
                Constantp cexpr = std::dynamic_pointer_cast<Constant>(expr);
                return cexpr->bv_size == 1 && cexpr->value == 0;
            }
                break;
            default:
                return false;
        }
    }

/*Other operations on Expressions: normalization and atom removal*/
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
                throw std::runtime_error("Could not normalize this expression");
                return expr;
        }
        throw std::runtime_error("Cannot translate expression to SMT");
        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    }

    bool is_lit_const_eq(const std::shared_ptr<EqExpr>& eq_expr) {
        return (eq_expr->lhs->type == Exprv::LITERAL && eq_expr->rhs->type == Exprv::CONSTANT) ||
               (eq_expr->lhs->type == Exprv::CONSTANT && eq_expr->rhs->type == Exprv::LITERAL);
    }
    std::pair<Literalp, std::shared_ptr<Constant>> eq_to_lit_const(const std::shared_ptr<EqExpr>& eq_expr) {
        if (!is_lit_const_eq(eq_expr)) {
            log->error("Cannot extract literal and constant from a formula not of the (lit = const) form: {}", *eq_expr);
            throw std::runtime_error("Cannot extract literal and constant from a formula not of the (lit = const) form: " + eq_expr->to_string());
        }
        Literalp r1;
        std::shared_ptr<Constant> r2;

        if (eq_expr->lhs->type == Exprv::LITERAL) {
            r1 = std::dynamic_pointer_cast<Literal>(eq_expr->lhs);
            r2 = std::dynamic_pointer_cast<Constant>(eq_expr->rhs);
        } else {
            r2 = std::dynamic_pointer_cast<Constant>(eq_expr->lhs);
            r1 = std::dynamic_pointer_cast<Literal>(eq_expr->rhs);
        }
        return std::pair<Literalp, std::shared_ptr<Constant>>(r1, r2);
    }

    Expr delete_atom(Expr expr, Literalp lit) {
        switch (expr->type) {
            case Exprv::CONSTANT: {
                return expr;
            }
            case Exprv::LITERAL: {
                if (expr == lit) {
                    return createConstantTrue();
                }
                else {
                    return expr;
                }
            }
            case Exprv::AND_EXPR: {
                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                Expr nlhs = delete_atom(andExpr->lhs, lit);
                Expr nrhs = delete_atom(andExpr->rhs, lit);
                return createAndExpr(nlhs, nrhs);
            }
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                Expr nlhs = delete_atom(orExpr->lhs, lit);
                Expr nrhs = delete_atom(orExpr->rhs, lit);
                return createOrExpr(nlhs, nrhs);
            }
            case Exprv::NOT_EXPR: {
                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                Expr inner = notExpr->expr;
                switch (inner->type) {
                    case Exprv::CONSTANT:
                        return expr;
                    case Exprv::LITERAL:
                        if (inner == lit) {
                            return createConstantTrue();
                        }
                        else {
                            return expr;
                        }
                    case Exprv::EQ_EXPR: {
                        std::shared_ptr<EqExpr> inner_eq = std::dynamic_pointer_cast<EqExpr>(inner);
                        if (is_lit_const_eq(inner_eq)) {
                            auto pair = eq_to_lit_const(inner_eq);
                            if (pair.first == lit) {
                                return createConstantTrue();
                            } else {
                                return expr;
                            }
                        }
                        else {
                            log->error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                            log->error("\tExpr is {}", expr->to_string());
                            throw std::runtime_error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        }
                        break;
                    }
                    default:
                        log->error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        log->error("\tExpr is {}", expr->to_string());
                        throw std::runtime_error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        return nullptr;
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
            case Exprv::EQ_EXPR: {
                std::shared_ptr<EqExpr> eq_expr = std::dynamic_pointer_cast<EqExpr>(expr);
                if (is_lit_const_eq(eq_expr)) {
                    auto lit_cons = eq_to_lit_const(eq_expr);
                    if (lit_cons.first == lit) {
                        return createConstantTrue();
                    }
                    else {
                        return expr;
                    }
                }
                else {
                    log->error("EQ expression MUST be between an ATOM (LITERAL) and a CONSTANT");
                    log->error("\tExpr is {}", expr->to_string());
                    throw std::runtime_error("EQ expression MUST be between an ATOM (LITERAL) and a CONSTANT");
                    return nullptr;
                }
            }
            default:
            log->error("Could not simplify an expression that is not an OR, AND, NOT, CONSTANT, LITERAL.");
            log->error("\tExpr is {}", expr->to_string());
                throw std::runtime_error("Could not normalize this expression");
                return expr;
        }
        throw std::runtime_error("Cannot translate expression to SMT");
        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    }

    Expr guard_atom(Expr expr, const Literalp& lit, const Expr& guard) {
        switch (expr->type) {
            case Exprv::CONSTANT: {
                return expr;
            }
            case Exprv::LITERAL: {
                if (expr == lit) {
                    return createAndExpr(guard, lit);
                }
                else {
                    return expr;
                }
            }
            case Exprv::AND_EXPR: {
                std::shared_ptr<AndExpr> andExpr = std::dynamic_pointer_cast<AndExpr>(expr);
                Expr nlhs = guard_atom(andExpr->lhs, lit, guard);
                Expr nrhs = guard_atom(andExpr->rhs, lit, guard);
                return createAndExpr(nlhs, nrhs);
            }
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> orExpr = std::dynamic_pointer_cast<OrExpr>(expr);
                Expr nlhs = guard_atom(orExpr->lhs, lit, guard);
                Expr nrhs = guard_atom(orExpr->rhs, lit, guard);
                return createOrExpr(nlhs, nrhs);
            }
            case Exprv::NOT_EXPR: {
                std::shared_ptr<NotExpr> notExpr = std::dynamic_pointer_cast<NotExpr>(expr);
                Expr inner = notExpr->expr;
                switch (inner->type) {
                    case Exprv::CONSTANT:
                        return expr;
                    case Exprv::LITERAL:
                        if (inner == lit) {
                            return createAndExpr(guard, notExpr);
                        }
                        else {
                            return expr;
                        }
                    case Exprv::EQ_EXPR: {
                        std::shared_ptr<EqExpr> inner_eq = std::dynamic_pointer_cast<EqExpr>(inner);
                        if (is_lit_const_eq(inner_eq)) {
                            auto pair = eq_to_lit_const(inner_eq);
                            if (pair.first == lit) {
                                return createAndExpr(guard, notExpr);
                            } else {
                                return expr;
                            }
                        }
                        else {
                            log->error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                            log->error("\tExpr is {}", expr->to_string());
                            throw std::runtime_error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        }
                        break;
                    }
                    default:
                        log->error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        log->error("\tExpr is {}", expr->to_string());
                        throw std::runtime_error("NOT expression MUST be located close to atoms (LITERAL, CONSTANT or EQ_EXPR)");
                        return nullptr;
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
            case Exprv::EQ_EXPR: {
                std::shared_ptr<EqExpr> eq_expr = std::dynamic_pointer_cast<EqExpr>(expr);
                if (is_lit_const_eq(eq_expr)) {
                    auto lit_cons = eq_to_lit_const(eq_expr);
                    if (lit_cons.first == lit) {
                        return createAndExpr(guard, expr);
                    }
                    else {
                        return expr;
                    }
                }
                else {
                    log->error("EQ expression MUST be between an ATOM (LITERAL) and a CONSTANT");
                    log->error("\tExpr is {}", expr->to_string());
                    throw std::runtime_error("EQ expression MUST be between an ATOM (LITERAL) and a CONSTANT");
                    return nullptr;
                }
            }
            default:
                log->error("Could not simplify an expression that is not an OR, AND, NOT, CONSTANT, LITERAL.");
                log->error("\tExpr is {}", expr->to_string());
                throw std::runtime_error("Could not normalize this expression");
                return expr;
        }
        throw std::runtime_error("Cannot translate expression to SMT");
        fprintf(stderr, "Cannot translate expression to SMT:\n    %s\n", expr->to_string().c_str());
    }

    std::list<Expr> get_toplevel_or(const Expr& expr) {
        switch (expr->type) {
            case Exprv::OR_EXPR: {
                std::shared_ptr<OrExpr> self = std::dynamic_pointer_cast<OrExpr>(expr);
                std::list<Expr> lexprs = get_toplevel_or(self->lhs);
                std::list<Expr> rexprs = get_toplevel_or(self->rhs);
                lexprs.insert(lexprs.end(), rexprs.begin(), rexprs.end());
                return lexprs;
            }
            default: {
                std::list<Expr> result;
                result.push_back(expr);
                return result;
            }
        }
    }

    Expr clone_but_lits(const Expr& expr) {
        switch (expr->type) {
            case Exprv::LITERAL:
            case Exprv::CONSTANT:
                return expr;
            case Exprv::EQ_EXPR: {
                EqExprp eq_expr = std::dynamic_pointer_cast<EqExpr>(expr);
                Expr res = createEqExpr(clone_but_lits(eq_expr->lhs), clone_but_lits(eq_expr->rhs));
                res->node_idx = expr->node_idx;
                return res;
            }
            case Exprv::NOT_EXPR: {
                NotExprp not_expr = std::dynamic_pointer_cast<NotExpr>(expr);
                Expr res = createNotExpr(clone_but_lits(not_expr->expr));
                res->node_idx = expr->node_idx;
                return res;
            }
            case Exprv::AND_EXPR: {
                AndExprp and_expr = std::dynamic_pointer_cast<AndExpr>(expr);
                Expr res = createAndExpr(clone_but_lits(and_expr->lhs), clone_but_lits(and_expr->rhs));
                res->node_idx = expr->node_idx;
                return res;
            }
            case Exprv::OR_EXPR: {
                OrExprp or_expr = std::dynamic_pointer_cast<OrExpr>(expr);
                Expr res = createOrExpr(clone_but_lits(or_expr->lhs), clone_but_lits(or_expr->rhs));
                res->node_idx = expr->node_idx;
                return res;
            }
            case Exprv::IMPL_EXPR: {
                ImplExprp impl_expr = std::dynamic_pointer_cast<ImplExpr>(expr);
                Expr res = createImplExpr(clone_but_lits(impl_expr->lhs), clone_but_lits(impl_expr->rhs));
                res->node_idx = expr->node_idx;
                return res;
            }
            case Exprv::COND_EXPR: {
                CondExprp cond_expr = std::dynamic_pointer_cast<CondExpr>(expr);
                Expr res =  createCondExpr(clone_but_lits(cond_expr->cond),
                                           clone_but_lits(cond_expr->choice1),
                                           clone_but_lits(cond_expr->choice2));
                res->node_idx = expr->node_idx;
                return res;
            }
            default:
                log->critical("Should not be here...");
                throw unexpected_error("Should not be here...");
        }

    }

    std::list<std::pair<int, OrExprp>> get_or_expressions(const Expr& expr, int level) {
        switch (expr->type) {
            case Exprv::LITERAL:
            case Exprv::CONSTANT:
                return std::list<std::pair<int, OrExprp>>();
            case Exprv::OR_EXPR: {
                OrExprp or_expr = std::dynamic_pointer_cast<OrExpr>(expr);
                std::list<std::pair<int, OrExprp>> lhs_or = get_or_expressions(or_expr->lhs, level);
                std::list<std::pair<int, OrExprp>> rhs_or = get_or_expressions(or_expr->rhs, level);
                lhs_or.push_front(std::pair<int, OrExprp>(level, or_expr));
                lhs_or.insert(lhs_or.end(), rhs_or.begin(), rhs_or.end());
                return lhs_or;
            }
            case Exprv::AND_EXPR: {
                AndExprp and_expr = std::dynamic_pointer_cast<AndExpr>(expr);
                std::list<std::pair<int, OrExprp>> lhs_or = get_or_expressions(and_expr->lhs, level + 1);
                std::list<std::pair<int, OrExprp>> rhs_or = get_or_expressions(and_expr->rhs, level + 1);
                lhs_or.insert(lhs_or.end(), rhs_or.begin(), rhs_or.end());
                return lhs_or;
            }
            case Exprv::EQ_EXPR: {
                EqExprp eq_expr = std::dynamic_pointer_cast<EqExpr>(expr);
                std::list<std::pair<int, OrExprp>> lhs_or = get_or_expressions(eq_expr->lhs, level + 1);
                std::list<std::pair<int, OrExprp>> rhs_or = get_or_expressions(eq_expr->rhs, level + 1);
                lhs_or.insert(lhs_or.end(), rhs_or.begin(), rhs_or.end());
                return lhs_or;
            }
            case Exprv::NOT_EXPR: {
                NotExprp not_expr = std::dynamic_pointer_cast<NotExpr>(expr);
                return get_or_expressions(not_expr->expr, level + 1);
            }
            case Exprv::IMPL_EXPR: {
                log->critical("IMPL_EXPR not supported here");
                throw unexpected_error("IMPL_EXPR not supported here");
            }
            case Exprv::COND_EXPR: {
                log->critical("COND_EXPR not supported here");
                throw unexpected_error("COND_EXPR not supported here");
            }
            default:
                log->critical("Should not be here");
                throw unexpected_error("Should not be here");
        }
    }

//    Expr select_or_expressions(Expr expr, OrExprp _or, OrExpr::or_position pos) {
//        //FIXME: continue here
//        throw unexpected_error("NOT IMPLEMENTED YET");
//        return nullptr;
//    }
//    void set_or_expressions_sub(Expr expr, const OrExprp& _or, OrExpr::or_position pos, const Expr& new_value) {
//        if (expr->node_idx == _or->node_idx) {
//            OrExprp self = std::dynamic_pointer_cast<OrExpr>(expr);
//            switch (pos) {
//                case OrExpr::LEFT:
//                    self->lhs = new_value;
//                break;
//                case OrExpr::RIGHT:
//                    self->rhs = new_value;
//                break;
//                default:
//                    throw unexpected_error("Uh?");
//                    break;
//            }
//            return;
//        }
//        else {
//            switch (expr->type) {
//                case Exprv::LITERAL:
//                case Exprv::CONSTANT:
//                    return;
//                case Exprv::OR_EXPR: {
//                    OrExprp or_expr = std::dynamic_pointer_cast<OrExpr>(expr);
//                    set_or_expressions_sub(or_expr->lhs, _or, pos, new_value);
//                    set_or_expressions_sub(or_expr->rhs, _or, pos, new_value);
//                    return;
//                }
//                case Exprv::AND_EXPR: {
//                    AndExprp and_expr = std::dynamic_pointer_cast<AndExpr>(expr);
//                    set_or_expressions_sub(and_expr->lhs, _or, pos, new_value);
//                    set_or_expressions_sub(and_expr->rhs, _or, pos, new_value);
//                    return;
//                }
//                case Exprv::EQ_EXPR: {
//                    EqExprp eq_expr = std::dynamic_pointer_cast<EqExpr>(expr);
//                    set_or_expressions_sub(eq_expr->lhs, _or, pos, new_value);
//                    set_or_expressions_sub(eq_expr->rhs, _or, pos, new_value);
//                    return;
//                }
//                case Exprv::NOT_EXPR: {
//                    NotExprp not_expr = std::dynamic_pointer_cast<NotExpr>(expr);
//                    set_or_expressions_sub(not_expr->expr, _or, pos, new_value);
//                    return;
//                }
//                case Exprv::IMPL_EXPR: {
//                    log->critical("IMPL_EXPR not supported here");
//                    throw unexpected_error("IMPL_EXPR not supported here");
//                }
//                case Exprv::COND_EXPR: {
//                    log->critical("COND_EXPR not supported here");
//                    throw unexpected_error("COND_EXPR not supported here");
//                }
//                default:
//                    log->critical("Should not be here");
//                    throw unexpected_error("Should not be here");
//            }
//        }
//    }

/*EXPR COMPARER FOR STD COLLECTIONS*/
    int deepCmpExprs::operator()(const Expr &e1, const Expr &e2) const {
        //FIXME: use semantics equivalence and not structural one
        int res = e1->equals(e2) ? 0 : (e1 < e2);
        return res;
    }

}
