#pragma once

// @author: trucnguyenlam@gmail.com
// @description:
//    This is the model of rGURA policy
//
// TODO:
//
// @changeLog:
//    2017.05.09   Initial version

#include <map>
#include <string>
#include <vector>
#include <set>
#include <memory>
#include <iostream>

namespace VAC {

class Value {
  public:
    Value(std::string valstr, int id):
        valstr(valstr), ID(id) {}
    ~Value() {}

    int getID(void) const;
    std::string getVal(void) const;

    std::string to_string(void) const;

  private:
    int ID;
    std::string valstr;
};

typedef std::shared_ptr<Value> ValuePtr;

class Domain {
  public:
    Domain() {}
    ~Domain() {}
    void addValueToSet(std::string v);
    int getValueID(std::string v) const;
    bool belongToDomain(std::string v) const;

    std::string to_string(void) const;
  private:
    std::vector<std::string> values;
    std::map<std::string, int> valuemap;
};

typedef std::shared_ptr<Domain> DomainPtr;

class Scope {
  public:
    Scope() {}
    ~Scope() {}

    void addDomain(std::string, DomainPtr d);

    DomainPtr getDomain(std::string attrname) const;

    bool inScope(std::string name) const;

    std::string to_string(void) const;
  private:
    std::map<std::string, DomainPtr> domains;
};

typedef std::shared_ptr<Scope> ScopePtr;

class Attribute {
  public:
    Attribute(int _ID, std::string _name, bool isSingle):
        ID(_ID), name(_name), single(isSingle)
    {}
    ~Attribute() {}

    int getID(void) const;
    std::string getName(void) const;
    bool isSingle(void) const;

    void setValue(Value v);
    const std::vector<ValuePtr> &getValue(void) const;

    std::string to_string(void) const;

  private:
    int ID;
    std::string name;
    bool single;
    std::vector<ValuePtr> values;
};

typedef std::shared_ptr<Attribute> AttributePtr;

class User {
  public:
    User(int ID, std::string name):
        ID(ID), name(name)
    {}
    ~User() {}

    void setAttribute(AttributePtr attr);
    bool hasAttribute(std::string name) const;
    AttributePtr getAttribute(std::string name) const;

    std::string getName(void) const;
    int getID(void) const;
    const std::vector<AttributePtr>& getConfiguration(void) const;
    std::string to_string(void) const;

  private:
    int ID;
    std::string name;
    std::vector<AttributePtr> attrs;
    std::map<std::string, int> attr_map;
};

typedef std::shared_ptr<User> UserPtr;

class EqualExpression {
  public:
    EqualExpression(std::string attr, std::string val):
        attribute(attr), value(val)
    {}
    ~EqualExpression() {}

    std::string getAttribute(void) const;
    std::string getValue(void) const;
    std::string to_string(void) const;
  private:
    std::string attribute;
    std::string value;
};

typedef std::shared_ptr<EqualExpression> TargetPtr;

class Precondition {
  public:
    Precondition(): isTrue(false) {}
    ~Precondition() {}

    std::string to_string(void) const;

    // Too lazy to put this in private
    bool isTrue;
    std::vector<TargetPtr> Pt;
    std::vector<TargetPtr> Nt;
};

typedef std::shared_ptr<Precondition> PreconditionPtr;

class AssignRule {
  public:
    AssignRule(std::string admin, PreconditionPtr precondition, TargetPtr target):
        admin(admin), precondition(precondition), target(target) {}
    ~AssignRule() {}

    std::string getAdmin(void) const;
    PreconditionPtr getPrecondition(void) const;
    TargetPtr getTarget(void) const;
    std::string to_string(void) const;

  private:
    std::string admin;
    PreconditionPtr precondition;
    TargetPtr target;
};

typedef std::shared_ptr<AssignRule> AssignRulePtr;

class AddRule {
  public:
    AddRule(std::string admin, PreconditionPtr precondition, TargetPtr target):
        admin(admin), precondition(precondition), target(target) {}
    ~AddRule() {}

    std::string getAdmin(void) const;
    PreconditionPtr getPrecondition(void) const;
    TargetPtr getTarget(void) const;
    std::string to_string(void) const;

  private:
    std::string admin;
    PreconditionPtr precondition;
    TargetPtr target;
};

typedef std::shared_ptr<AddRule> AddRulePtr;

class DeleteRule {
  public:
    DeleteRule(std::string admin, TargetPtr target):
        admin(admin), target(target) {}
    ~DeleteRule() {}

    std::string getAdmin(void) const;
    TargetPtr getTarget(void) const;
    std::string to_string(void) const;

  private:
    std::string admin;
    TargetPtr target;
};

typedef std::shared_ptr<DeleteRule> DeleteRulePtr;


class rGURA {
  public:
    rGURA() {
        scope = std::make_shared<Scope>(Scope());
        query = std::make_shared<EqualExpression>(EqualExpression("", ""));
        }
    ~rGURA() {}

    void insertNewUser(UserPtr u, int id);
    void insertNewAttribute(AttributePtr a, int id);
    void setScope(Scope s);
    ScopePtr getScope(void) const;
    void insertAdminRole(std::string a);
    void insertNewAssignRule(AssignRulePtr);
    void insertNewAddRule(AddRulePtr);
    void insertNewDeleteRule(DeleteRulePtr);

    UserPtr getUser(std::string _username) const;
    AttributePtr getAttribute(std::string _attributename) const;
    bool hasAdminRole(std::string name) const;

    int getCurrentUserSize(void) const;
    int getCurrentAttributeSize(void) const;
    TargetPtr getQuery(void) const;
    void setQuery(TargetPtr t);

    std::string to_string(void) const;
  private:
    std::vector<UserPtr> users;
    std::vector<AttributePtr> attrs;
    std::vector<std::string> admin_roles;
    std::vector<AssignRulePtr> assign_rules;
    std::vector<AddRulePtr> add_rules;
    std::vector<DeleteRulePtr> delete_rules;
    ScopePtr scope;
    TargetPtr query;

    std::map<std::string, int> user_map;
    std::map<std::string, int> attr_map;
    std::map<std::string, int> adminrole_map;
};


typedef std::shared_ptr<rGURA> rGURAPtr;

} // VAC