#include "Logics.h"

#include <iostream>
#include <sstream>
#include <chrono>
#include <regex>
#include <stdexcept>
#include <assert.h>
#include <algorithm>
#include <utility>


using namespace Parser;

template <typename T>
std::set<T> setUnion(const std::set<T>& a, const std::set<T>& b) {
    std::set<T> result = a;
    result.insert(b.begin(), b.end());
    return result;
}

/*EXPR OPS*/
Exprv::Exprv(ExprType ty, std::set<Literalp> literals) : type(ty), _literals(literals) { }

bool Exprv::containsLiteral(std::string full_name) {
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
}

std::ostream & operator<<(std::ostream & out, Exprv const & expr) {
    out << expr.to_string();

    return out;
}

std::set<Literalp> Exprv::literals() {
    return this->_literals;
}

/*LITERAL OPS*/
Literal::Literal(const std::string _name, int _role_array_index, int _bv_size, Expr _value):
    Exprv(Exprv::LITERAL, std::set<Literalp>()),
    name(_name), role_array_index(_role_array_index), bv_size(_bv_size), value(_value) { }

void Literal::setLiterals(Literalp &self) {
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
}
void Literal::setValue(Expr value) {
    this->value = value;
}
void Literal::resetValue() {
    this->value = nullptr;
}
std::string Literal::getSMTName() const {
    return this->fullName();
}

std::string Literal::fullName() const {
    if (this->suffix == "") {
        return this->name;
    } else {
        std::stringstream fmt;
        fmt << this->name + "_" + this->suffix;
        return fmt.str();
    }
}

std::string Literal::nameWithSuffix(std::string suffix) const {
    if (this->suffix == "") {
        return this->fullName() + "_" + suffix;
    } else {
        std::stringstream fmt;
        fmt << this->name + "_" + this->suffix;
        return fmt.str();
    }
}

std::string Literal::to_string() const {
    std::stringstream fmt;
    // fmt << "|" << this->fullName() << "|";
    fmt << this->fullName();
    return fmt.str();
}

/*CONSTANT OPS*/
Constant::Constant(int _value, int _bv_size) :
    Exprv(Exprv::CONSTANT, std::set<Literalp>()),
    value(_value), bv_size(_bv_size) { }

std::string Constant::to_string() const {
    if (this->bv_size == 1) {
        if (this->value) {
            return "1";
        } else {
            return "0";
        }
    } else {
        std::stringstream fmt;
        fmt << this->value;
        return fmt.str();
    }
}

/*OR OPS*/
OrExpr::OrExpr(Expr _lhs, Expr _rhs) :
    Exprv(Exprv::OR_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
    lhs(_lhs), rhs(_rhs) { }

std::string OrExpr::to_string() const {
    std::stringstream fmt;
    std::string lhsv = this->lhs->to_string();
    std::string rhsv = this->rhs->to_string();
    fmt << "(" << lhsv << "||" << rhsv << ")";
    return fmt.str();
}

/*AND OPS*/
AndExpr::AndExpr(Expr _lhs, Expr _rhs) :
    Exprv(Exprv::AND_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
    lhs(_lhs), rhs(_rhs) { }

std::string AndExpr::to_string() const {
    std::stringstream fmt;
    std::string lhsv = this->lhs->to_string();
    std::string rhsv = this->rhs->to_string();
    fmt << "(" << lhsv << "&&" << rhsv << ")";
    return fmt.str();
}

/*EQ OPS*/
EqExpr::EqExpr(Expr _lhs, Expr _rhs) :
    Exprv(Exprv::EQ_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
    lhs(_lhs), rhs(_rhs) { }

std::string EqExpr::to_string() const {
    std::stringstream fmt;
    std::string lhsv = this->lhs->to_string();
    std::string rhsv = this->rhs->to_string();
    fmt << "(" << lhsv << "=" << rhsv << ")";
    return fmt.str();
}

/*IMPLICATION OPS*/
ImplExpr::ImplExpr(Expr _lhs, Expr _rhs) :
    Exprv(Exprv::IMPL_EXPR, setUnion(_lhs->literals(), _rhs->literals())),
    lhs(_lhs), rhs(_rhs) { }

std::string ImplExpr::to_string() const {
    std::stringstream fmt;
    std::string lhsv = this->lhs->to_string();
    std::string rhsv = this->rhs->to_string();
    fmt << "(" << lhsv << "=>" << rhsv << ")";
    return fmt.str();
}

/*NOT OPS*/
NotExpr::NotExpr(Expr _expr) :
    Exprv(Exprv::NOT_EXPR, _expr->literals()),
    expr(_expr) { }

std::string NotExpr::to_string() const {
    std::stringstream fmt;
    std::string exprv = this->expr->to_string();
    fmt << "!" << "(" << exprv << ")";
    return fmt.str();
}

/*COND OPS*/
CondExpr::CondExpr(Expr _cond, Expr _choice1, Expr _choice2) :
    Exprv(Exprv::COND_EXPR,
          setUnion(_cond->literals(), setUnion(_choice1->literals(), _choice2->literals()))),
    cond(_cond), choice1(_choice1), choice2(_choice2) { }

std::string CondExpr::to_string() const {
    std::stringstream fmt;
    std::string cond = this->cond->to_string();
    std::string ch1 = this->choice1->to_string();
    std::string ch2 = this->choice2->to_string();
    fmt << "((" << cond << ") ? (" << ch1 << ") : (" << ch2 << "))";
    return fmt.str();
}

// Entity class
int Entity::getLocalID(void) const {
    return local_ID;
}

int Entity::getAttributeID(void) const {
    return attr_ID;
}

std::string Entity::getUserName(void) const {
    return user_name;
}

std::string Entity::getAttributeName(void) const {
    return attr_name;
}

std::string Entity::to_string(void) const {
    return name;
}
