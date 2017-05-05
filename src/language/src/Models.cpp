// Author: trucnguyenlam@gmail.com
// Description:
//    This is ...
//
// TODO:
//
// ChangeLog:
//    2017.05.05   Initial version

#include <csignal>
#include <iostream>
#include "Models.h"

using namespace SMT;

// Attribute class
int Attribute::getID(void) const {
    return ID;
}

std::string Attribute::getName(void) const {
    return name;
}

int Attribute::getSize(void) const {
    return size;
}

Expr Attribute::getValue(void) const {
    return value;
}

void Attribute::setValue(Expr _value)  {
    value = _value;
}

std::string Attribute::to_string(void) const {
    std::string ret = "{";
    ret += "name:" + name + ",";
    ret += "id:" + std::to_string(ID) + ",";
    ret += "size:" + std::to_string(size) + ",";
    ret += "value:" + (value == nullptr) ? "EMPTY" : value->to_string();
    ret += "}";
    return ret;
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

// User class

void User::setAttribute(AttributePtr attr) {
    auto pos = attr_map.find(attr->getName());
    if (pos != attr_map.end()) { // This attribute already available
        attrs[pos->second] = attr; // Update attribute
    } else {
        attrs.push_back(attr);
        attr_map.insert(std::pair<std::string, int>(attr->getName(), attrs.size() - 1));
    }
}

std::string User::getName(void) const {
    return name;
}

int User::getID(void) const {
    return ID;
}

bool User::hasAttribute(std::string name) const {
    return (attr_map.find(name) != attr_map.end());
}

AttributePtr User::getAttribute(std::string name) const {
    auto pos = attr_map.find(name);
    if (pos != attr_map.end()) { // This attribute already available
        return attrs[pos->second];
    } else {
        return nullptr;
    }
}

std::vector<AttributePtr> User::getCopyConfiguration(void) const {
    return attrs;
}

std::string User::to_string(void) const {
    std::string ret = "{";
    ret += "name:" + name + ",";
    ret += "id:" + std::to_string(ID) + ",";
    ret += "isNew:" + std::to_string(isNew) + ",";
    ret += "attributes:[";
    for (const auto & a : attrs) {
        ret += a->to_string() + ",";
    }
    ret += "]}";
    return ret;
}

// Class Rule
void Rule::addTargetExpr(EqExpr expr) {
    apply_target.push_back(std::make_shared<EqExpr>(expr));
}

Expr Rule::getPrecondition(void) const {
    return precondition;
}
std::vector<std::shared_ptr<EqExpr>> Rule::getCopyApplyTarget(void) const {
    return apply_target;
}

std::string Rule::to_string(void) const {
    std::string ret = "<";
    ret +=  precondition->to_string();
    for (const auto & t : apply_target) {
        ret += "," + t->to_string();
    }
    ret += ">";
    return ret;
}


// Class model
void Model::insertNewUser(UserPtr u, int id) {
    users.push_back(u);
    user_map.insert(std::pair<std::string, int>(u->getName(), id));
}
void Model::insertNewAttribute(AttributePtr a, int id) {
    attrs.push_back(a);
    attr_map.insert(std::pair<std::string, int>(a->getName(), id));
}

void Model::insertNewRule(RulePtr r) {
    rules.push_back(r);
}

int Model::getUserID(std::string _username) const {
    auto user_pos = user_map.find(_username);
    if (user_pos != user_map.end()) {
        return user_pos->second;
    } else {
        return -1;
    }
}

UserPtr Model::getUser(std::string _username) const {
    auto user_pos = user_map.find(_username);
    if (user_pos != user_map.end()) {
        int user_id = user_pos->second;
        return users[user_id];
    } else {
        return nullptr;
    }
}

int Model::getAttributeID(std::string _attributename) const {
    auto attr_pos = attr_map.find(_attributename);
    if (attr_pos != attr_map.end()) {
        return attr_pos->second;
    } else {
        return -1;
    }
}

std::string Model::getAttributeName(int _id) const {
    if (_id < 0 || _id > attrs.size()) {
        std::cerr << "Out of bound attribute index: " << _id << std::endl;
        std::_Exit(EXIT_FAILURE);
    } else {
        return attrs[_id]->getName();
    }
}

AttributePtr Model::getAttribute(std::string _attributename) const {
    auto attr_pos = attr_map.find(_attributename);
    if (attr_pos != attr_map.end()) {
        int attr_id = attr_pos->second;
        return attrs[attr_id];
    } else {
        return nullptr;
    }
}

std::vector<UserPtr> Model::getCopyOfUsers(void) const {
    return users;
}
int Model::getCurrentUserSize(void) const {
    return users.size();
}
std::vector<AttributePtr> Model::getCopyOfAttributes(void) const {
    return attrs;
}
int Model::getCurrentAttributeSize(void) const {
    return attrs.size();
}
std::vector<RulePtr> Model::getCopyOfRules(void) const {
    return rules;
}

Expr Model::getQuery(void) const {
    return query;
}

void Model::setQuery(Expr q) {
    query = q;
}

std::string Model::to_string(void) const {
    std::string ret = "Model:\n";
    // User
    ret += "  users:\n";
    for (const auto & u : users) {
        ret += "    " + u->to_string() + "\n";
    }
    // Attribute
    ret += "  attributes:\n";
    for (const auto & a : attrs) {
        ret += "    " + a->to_string() + "\n";
    }
    // Rules
    ret += "  rules:\n";
    for (const auto & r : rules) {
        ret += "    " + r->to_string() + "\n";
    }
    // Query
    ret += "  query: " + query->to_string() + "\n";

    return ret;
}
