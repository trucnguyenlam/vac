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
#include <map>
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

    int getLocalID(void) const {return local_ID;}
    // AttributePtr getAttribute(void) const {return attr;}
    int getAttributeID(void) const {return attr_ID;}

  private:
    int local_ID;
    // AttributePtr attr; // Attribute, too complicated
    int attr_ID; // Attribute ID
    std::string name;
};

class User {
  public:
    User(int ID, std::string name, bool isNew=false):
        ID(ID), name(name), isNew(isNew) {}

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


    Expr getPrecondition(void) const {return precondition;}
    std::vector<std::shared_ptr<EqExpr>> getApplyTarget(void) const {return apply_target;}

  private:
    Expr precondition;
    std::vector<std::shared_ptr<EqExpr>> apply_target;

};

typedef std::shared_ptr<Rule> RulePtr;


class Model {
public:
    Model():query(nullptr){

    }
    ~Model(){
        users.clear();
        attrs.clear();
        rules.clear();
        user_map.clear();
        attr_map.clear();
    }

    void insertNewUser(UserPtr u, int id) {
        users.push_back(u);
        user_map.insert(std::pair<UserPtr, int>(u, id));
    }
    void insertNewAttribute(AttributePtr);
    void insertNewRule(RulePtr);

    int getUserIDFromName(std::string _username);
    int getAttributeIDFromName(std::string _attributename);

    std::vector<UserPtr> getCopyOfUsers(void){ return users;}
    int getCurrentUserSize(void){ return users.size();}
    std::vector<AttributePtr> getCopyOfAttributes(void) {return attrs;}
    std::vector<RulePtr> getCopyOfRules(void) {return rules;}

    Expr getQuery(void);
    void setQuery(Expr);

  private:
    std::vector<UserPtr> users;
    std::vector<AttributePtr> attrs;
    std::vector<RulePtr> rules;
    Expr query;

    std::map<UserPtr, int> user_map;
    std::map<AttributePtr, int> attr_map;
};


typedef std::shared_ptr<Model> ModelPtr;


} // SMT



#endif //VACSAT_MODEL_H
