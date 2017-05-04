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
    ~Attribute() {}

    int getID(void) const { return ID;}
    std::string getName(void) const { return name;}
    int getSize(void) const { return size;}
    Expr getValue(void) const { return value;}
    void setValue(Expr _value)  { value = _value;}

    std::string to_string(void) const {
        std::string ret = "{";
        ret += "name:" + name + ",";
        ret += "id:" + std::to_string(ID) + ",";
        ret += "size:" + std::to_string(size) + ",";
        ret += "value:" + value->to_string();
        ret += "}";
        return ret;
    }

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
    ~Entity() {}

    int getLocalID(void) const {return local_ID;}
    // AttributePtr getAttribute(void) const {return attr;}
    int getAttributeID(void) const {return attr_ID;}

    std::string to_string(void) const {
        return name;
    }

  private:
    int local_ID; // local ID of user e.g. x
    // AttributePtr attr; // Attribute, too complicated
    int attr_ID; // Attribute ID
    std::string name;
};

class User {
  public:
    User(int ID, std::string name, bool isNew = false):
        ID(ID), name(name), isNew(isNew) {}
    ~User() {}

    AttributePtr getAttribute(std::string name) const;
    void setAttribute(std::string name, Expr expr) {
        attr_value_map.at(name) = expr; // TODO: Dangerous
    }

    void setAttribute(AttributePtr attr) {
        attrs.push_back(attr);
        attr_value_map.insert(std::pair<std::string, Expr>(attr->getName(), attr->getValue()));
    }

    std::string getName(void) const { return name;}

    int getID(void) const { return ID;}

    bool hasAttribute(std::string name) const;

    std::vector<AttributePtr> getCopyConfiguration(void) const {return attrs;}

    std::string to_string(void) const {
        std::string ret = "{";
        ret += "name:" + name + ",";
        ret += "id:" + std::to_string(ID) + ",";
        ret += "isNew:" + std::to_string(isNew) + ",";
        ret += "attributes:[";
        for (const auto & a: attrs) {
            ret += a->to_string() + ",";
        }
        ret += "]}";
        return ret;
    }

  private:
    int ID; //
    std::string name;
    bool isNew;   // If this user if a new user (unlimited)
    std::vector<AttributePtr> attrs;
    std::map<std::string, Expr> attr_value_map;
};

typedef std::shared_ptr<User> UserPtr;

class Rule {
    Rule(Expr _precondition) {}

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
    Model(): query(nullptr) {

    }
    ~Model() {
        users.clear();
        attrs.clear();
        rules.clear();
        user_map.clear();
        attr_map.clear();
    }

    void insertNewUser(UserPtr u, int id) {
        users.push_back(u);
        user_map.insert(std::pair<std::string, int>(u->getName(), id));
    }
    void insertNewAttribute(AttributePtr a, int id) {
        attrs.push_back(a);
        attr_map.insert(std::pair<std::string, int>(a->getName(), id));
    }

    void insertNewRule(RulePtr);

    int getUserID(std::string _username);
    UserPtr getUser(std::string _username) const {
        auto user_pos = user_map.find(_username);
        if (user_pos != user_map.end()) {
            int user_id = user_pos->second;
            return users[user_id];
        } else {
            return nullptr;
        }
    }

    int getAttributeID(std::string _attributename) const {
        auto attr_pos = attr_map.find(_attributename);
        if (attr_pos != attr_map.end()) {
            return attr_pos->second;
        } else {
            return -1;
        }
    }

    std::string getAttributeName(int _id) const {
        if (_id < 0 || _id > attrs.size()){
            std::cerr << "Out of bound attribute index: " << _id << std::endl;
        }
        else{
            return attrs[_id]->getName();
        }
    }


    AttributePtr getAttribute(std::string _attributename) const {
        auto attr_pos = attr_map.find(_attributename);
        if (attr_pos != attr_map.end()) {
            int attr_id = attr_pos->second;
            return attrs[attr_id];
        } else {
            return nullptr;
        }
    }

    std::vector<UserPtr> getCopyOfUsers(void) { return users;}
    int getCurrentUserSize(void) const { return users.size();}
    std::vector<AttributePtr> getCopyOfAttributes(void) const {return attrs;}
    int getCurrentAttributeSize(void) const {return attrs.size();}
    std::vector<RulePtr> getCopyOfRules(void) const {return rules;}

    Expr getQuery(void);
    void setQuery(Expr);

  private:
    std::vector<UserPtr> users;
    std::vector<AttributePtr> attrs;
    std::vector<RulePtr> rules;
    Expr query;

    std::map<std::string, int> user_map;
    std::map<std::string, int> attr_map;
};


typedef std::shared_ptr<Model> ModelPtr;


} // SMT



#endif //VACSAT_MODEL_H
