#include "rGURAModel.h"

using namespace VAC;


// class Domain
void Domain::addValueToSet(std::string v) {
    valuemap.insert(std::pair<std::string, int>(v, values.size()));
    values.push_back(v);
}

int Domain::getValueID(std::string v) const {
    auto pos = valuemap.find(v);
    if (pos != valuemap.end()) {
        return pos->second;
    } else {
        return -1;
    }
}


//class Scope
void Scope::addDomain(std::string name, DomainPtr d) {
    domains.insert(std::pair<std::string, DomainPtr>(name, d));
}

DomainPtr Scope::getDomain(std::string attrname) const {
    auto pos = domains.find(attrname);
    if (pos != domains.end()) {
        return pos->second;
    } else {
        return nullptr;
    }
}


//class Attribute
int Attribute::getID(void) const {
    return ID;
}

std::string Attribute::getName(void) const {
    return name;
}
bool Attribute::isSingle(void) const {
    return single;
}

void Attribute::setValue(Value v) {
    if (single) {
        if (values.size() > 0) {
            values[0] = std::make_shared<Value>(v);
        } else {
            values.push_back(std::make_shared<Value>(v));
        }
    } else {
        values.push_back(std::make_shared<Value>(v));
    }
}

const std::vector<ValuePtr> & Attribute::getValue(void) const {
    return values;
}



//class User
std::string User::getName(void) const {
    return name;
}

void User::setAttribute(AttributePtr attr) {
    // Check if this attribute is already there
    auto pos = attr_map.find(attr->getName());
    if (pos != attr_map.end()) {
        attrs[pos->second] = attr; // Only update
    } else {
        attr_map.insert(std::pair<std::string, int>(attr->getName(), attrs.size()));
        attrs.push_back(attr);
    }
}

bool User::hasAttribute(std::string name) const {
    auto pos = attr_map.find(name);
    if (pos != attr_map.end()) {
        return true;
    } else {
        return false;
    }
}



//class rGURA
void rGURA::insertNewUser(UserPtr u, int id) {
    users.push_back(u);
    user_map.insert(std::pair<std::string, int>(u->getName(), id));
}

void rGURA::insertNewAttribute(AttributePtr a, int id) {
    attrs.push_back(a);
    attr_map.insert(std::pair<std::string, int>(a->getName(), id));
}

void rGURA::setScope(Scope s) {
    scope = std::make_shared<Scope>(s);
}

ScopePtr rGURA::getScope(void) const {
    return scope;
}


void rGURA::insertAdminRole(std::string a) {
    adminrole_map.insert(std::pair<std::string, int>(a, admin_roles.size()));
    admin_roles.push_back(a);
}


void rGURA::insertNewAssignRule(AssignRulePtr r) {
    assign_rules.push_back(r);

}
void rGURA::insertNewAddRule(AddRulePtr r) {
    add_rules.push_back(r);


}
void rGURA::insertNewDeleteRule(DeleteRulePtr r) {
    delete_rules.push_back(r);
}


UserPtr rGURA::getUser(std::string _username) const {
    auto user_pos = user_map.find(_username);
    if (user_pos != user_map.end()) {
        int user_id = user_pos->second;
        return users[user_id];
    } else {
        return nullptr;
    }
}


AttributePtr rGURA::getAttribute(std::string _attributename) const {
    auto attr_pos = attr_map.find(_attributename);
    if (attr_pos != attr_map.end()) {
        int attr_id = attr_pos->second;
        return attrs[attr_id];
    } else {
        return nullptr;
    }
}


bool rGURA::hasAdminRole(std::string name) const {
    auto pos = adminrole_map.find(name);
    if (pos != adminrole_map.end()) {
        return true;
    } else {
        return false;
    }
}

int rGURA::getCurrentUserSize(void) const {
    return users.size();
}


int rGURA::getCurrentAttributeSize(void) const {
    return attrs.size();
}

void rGURA::setQuery(TargetPtr t) {
    query = t;
}
