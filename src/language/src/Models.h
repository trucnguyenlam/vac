// Author: trucnguyenlam@gmail.com
// Description:
//    This is ...
//
// TODO:
//
// ChangeLog:
//    2017.04.28   Initial version


#ifndef VACSAT_MODEL_H
#define VACSAT_MODEL_H

#include <string>
#include <vector>
#include <memory>

#include "Logics.h"

namespace SMT {

class Attribute {
  public:
    Attribute(int _ID, std::string _name, int _size, Expr _default = nullptr):
        ID(_ID), name(_name), size(_size), value(_default) {}
    ~Attribute();

    int getID(void) const { return ID;}
    std::string getName(void) const { return name;}
    int getSize(void) const { return size;}
    Expr getValue(void) const { return value;}
    void setValue(Expr _value)  { value=_value;}

  private:
    int ID;
    std::string name;
    int size;
    Expr value;  // value of this attribute
};
typedef std::shared_ptr<Attribute> AttributePtr;

// A variable name in Expression
class Entity: public Literal {
  public:
    Entity(const std::string _name, int _id, int _attr_ID):
        name(_name), local_ID(_id), attr_ID(_attr_ID)
    {};
    ~Entity();

    std::string to_string() override;

    int getLocalID(void) const {return local_ID;}
    // AttributePtr getAttribute(void) const {return attr;}
    int getAttributeID(void) const {return attr_ID;}

  private:
    int local_ID;
    // AttributePtr attr; // Attribute, too complicated
    int attr_ID; // Attribute ID
};

class User {
  public:
    User(int ID, std::string name):
        ID(ID), name(name) {}

    void getAttribute(std::string name) const;
    void getAttribute(int ID) const;

    void setAttribute(std::string name, Expr expr);
    void setAttribute(int ID, Expr expr);

    int getID(void) const { return ID;}

    bool hasAttribute(std::string name) const;
    bool hasAttribute(int ID) const;

    std::vector<AttributePtr> getInitConfiguration(void) const {return init_attrs;}
    std::vector<AttributePtr> getCurrentConfiguration(void) const {return attrs;}

  private:
    int ID; //
    std::string name;
    bool isNew;   // If this user if a new user (unlimited)
    std::vector<AttributePtr> init_attrs;
    std::vector<AttributePtr> attrs;
};

typedef std::shared_ptr<User> UserPtr;

class Rule {
    Rule(Expr _precondition){}

    void addTargetExpr(EqExpr expr);


    ExpressionPtr getPrecondition(void) const {return precondition;}
    std::vector<std::shared_ptr<EqExpr>> getApplyTarget(void) const {return apply_target;}

  private:
    Expr precondition;
    std::vector<std::shared_ptr<EqExpr>> apply_target;

};

typedef std::shared_ptr<Rule> RulePtr;


class Model {
public:
    int getUserIDFromName(std::string _username);
    int getAttributeIDFromName(std::string _attributename);

  private:
    std::vector<UserPtr> users;
    std::vector<AttributePtr> attrs;
}


typedef std::unique_ptr<Model> ModelPtr;


} // SMT



#endif //VACSAT_MODEL_H
