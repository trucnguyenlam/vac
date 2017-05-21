//
// Created by esteffin on 25/04/17.
//

#ifndef PARSER_LOGICS_H
#define PARSER_LOGICS_H

#include <set>
#include <map>
#include <memory>
#include <vector>

namespace Parser {

class Exprv;

typedef std::shared_ptr<Exprv> Expr;

class Literal;
typedef std::shared_ptr<Literal> Literalp;
typedef Literalp Atom;

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
        ENTITY,
        EQ_EXPR,
        NOT_EXPR,
        OR_EXPR,
        AND_EXPR,
        COND_EXPR,
        IMPL_EXPR,
    };

    Exprv(void) {}
    Exprv(ExprType ty, std::set<Literalp> literals);

    bool containsLiteral(std::string full_name);
    bool containsLiteral(Literalp lit);
    virtual void setSuffix(int idx);
    virtual void setSuffix(std::string suffix);
    virtual void resetSuffix();
    void setLiteralValue(Literalp lit, Expr value);
    void setLiteralValue(std::string lit_name, Expr value);
    void resetValue(std::string lit_name = "");

    friend std::ostream & operator<<(std::ostream & out, Exprv const & expr);

    virtual std::string to_string() const = 0;
    std::set<std::shared_ptr<Literal>> literals();

    ExprType type;

  protected:
    std::set<Literalp> _literals;
};

class Literal : public Exprv {
  public:
    Literal(void) {}
    Literal(const std::string _name, int _role_array_index, int bv_size, Expr _value = nullptr);

    std::string getSMTName() const;
    std::string fullName() const;
    std::string nameWithSuffix(std::string suffix) const;

    void setLiterals(Literalp &self);
    void setSuffix(std::string suffix);
    void setSuffix(int idx);
    void resetSuffix();
    void setValue(Expr  value);
    void resetValue();

    std::string to_string() const override;

    std::string name;
    // Index in the role_array
    int role_array_index;
    // VarType type;
    int bv_size;
    Expr value;
    std::string suffix;
};


// AttributeRef in Expression
class Entity: public Literal {
  public:
    Entity(std::string _name, std::string _user_name, int _local_id,
           std::string _attr_name, int _attr_ID):
        type(Exprv::ENTITY), name(_name), user_name(_user_name), local_ID(_local_id),
        attr_name(_attr_name), attr_ID(_attr_ID)
    {}
    ~Entity() {}

    int getLocalID(void) const;
    int getAttributeID(void) const;
    std::string getAttributeName(void) const;
    std::string getUserName(void) const;
    std::string to_string(void) const;

    ExprType type;

  private:
    std::string name;  // full name
    int local_ID; // local ID of user
    std::string user_name; // Attribute name
    int attr_ID; // Attribute ID
    std::string attr_name; // Attribute name
};

typedef std::shared_ptr<Entity> Entityp;

class Constant : public Exprv  {
  public:
    Constant(int val, int bv_size);

    std::string to_string() const override;

    int value;
    int bv_size;
    ExprType expr_type;
};

class OrExpr : public Exprv  {
  public:
    OrExpr(Expr _lhs, Expr _rhs);

    std::string to_string() const override;

    Expr lhs;
    Expr rhs;
};
class AndExpr : public Exprv  {
  public:
    AndExpr(Expr _lhs, Expr _rhs);

    std::string to_string() const override;
    Expr lhs;
    Expr rhs;
};
class EqExpr : public Exprv  {
  public:
    EqExpr(Expr _lhs, Expr _rhs);

    std::string to_string() const override;

    Expr lhs;
    Expr rhs;
};

class ImplExpr : public Exprv  {
  public:
    ImplExpr(Expr _lhs, Expr _rhs);

    std::string to_string() const override;

    Expr lhs;
    Expr rhs;
};
class NotExpr : public Exprv  {
  public:
    NotExpr(Expr _expr);

    std::string to_string() const override;

    Expr expr;
};
class CondExpr : public Exprv  {
  public:
    CondExpr(Expr _cond, Expr _choice1, Expr _choice2);

    std::string to_string() const override;

    Expr cond;
    Expr choice1;
    Expr choice2;
};
}

#endif //PARSER_LOGICS_H