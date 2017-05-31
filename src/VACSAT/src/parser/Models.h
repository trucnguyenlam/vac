// @author: trucnguyenlam@gmail.com
// @description:
//    This is the model of VAC general language for
//         access control policies
//    This model can encode easily ARBAC, ABAC
//
// TODO:
//
// @changeLog:
//    2017.04.28   Initial version

#ifndef PARSER_MODEL_H
#define PARSER_MODEL_H

#include "Logics.h"

#include <string>
#include <vector>
#include <map>
#include <memory>
#include <iostream>
#include <csignal>


namespace Parser {

class Attribute {
  public:
    Attribute(int _ID, std::string _name, int _size, Expr _default = nullptr):
        ID(_ID), name(_name), size(_size), value(_default)
    {}
    ~Attribute() {}

    int getID(void) const;
    std::string getName(void) const;
    int getSize(void) const;
    Expr getValue(void) const;
    void setValue(Expr _value);

    std::string to_string(void) const;

  private:
    int ID;
    std::string name;
    int size;
    Expr value;  // value of this attribute
};
using AttributePtr = std::shared_ptr<Attribute>;

class User {
  public:
    User(int ID, std::string name, bool isNew = false):
        ID(ID), name(name), isNew(isNew)
    {}
    ~User() {}

    // Set attribute for user, if this user does not have
    // this attribute, insert new one, otherwise, update
    // the existing one.
    void setAttribute(AttributePtr attr) ;
    bool hasAttribute(std::string name) const;
    AttributePtr getAttribute(std::string name) const;

    std::string getName(void) const;
    int getID(void) const;
    std::vector<AttributePtr> getCopyConfiguration(void) const;
    std::string to_string(void) const;
    bool isInfinite(void) const;

  private:
    int ID; //
    std::string name;
    bool isNew;   // If this user if a new user (unlimited)
    std::vector<AttributePtr> attrs;
    std::map<std::string, int> attr_map;
};

using UserPtr = std::shared_ptr<User>;

class Rule {
  public:
    Rule(Expr _precondition): precondition(_precondition) {}
    ~Rule() {}

    void addTargetExpr(EqExpr expr);
    Expr getPrecondition(void) const;
    std::vector<std::shared_ptr<EqExpr>> getCopyApplyTarget(void) const;
    std::string to_string(void) const;

  private:
    Expr precondition;
    std::vector<std::shared_ptr<EqExpr>> apply_target;

};

using RulePtr = std::shared_ptr<Rule>;


class Model {
  public:
    Model(): query(nullptr) {}
    ~Model() {}

    void insertNewUser(UserPtr u, int id);
    void insertNewAttribute(AttributePtr a, int id);
    void insertNewRule(RulePtr);

    int getUserID(std::string _username) const;
    UserPtr getUser(std::string _username) const;

    int getAttributeID(std::string _attributename) const;
    std::string getAttributeName(int _id) const;
    AttributePtr getAttribute(std::string _attributename) const;
    std::vector<UserPtr> getCopyOfUsers(void) const;
    int getCurrentUserSize(void) const;
    std::vector<AttributePtr> getCopyOfAttributes(void) const;
    int getCurrentAttributeSize(void) const;
    std::vector<RulePtr> getCopyOfRules(void) const;
    Expr getQuery(void) const;
    void setQuery(Expr);

    std::string to_string(void) const;
  private:
    std::vector<UserPtr> users;
    std::vector<AttributePtr> attrs;
    std::vector<RulePtr> rules;
    Expr query;

    std::map<std::string, int> user_map;
    std::map<std::string, int> attr_map;
};

using ModelPtr = std::shared_ptr<Model>;

}

#endif //PARSER_MODEL_H
