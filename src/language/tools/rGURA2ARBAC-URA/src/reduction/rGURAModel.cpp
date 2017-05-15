#include "rGURAModel.h"

using namespace VAC;

// class Value
int Value::getID(void) const {
    return ID;
}
std::string Value::getVal(void) const {
    return valstr;
}

std::string Value::to_string(void) const {
    return valstr;
}


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

bool Domain::belongToDomain(std::string v) const {
    auto pos = valuemap.find(v);
    if (pos != valuemap.end()) {
        return true;
    } else {
        return false;
    }
}


const std::vector<std::string>& Domain::getValues(void) const {
    return values;
}


std::string Domain::to_string(void) const {
    std::string ret = "{";
    for (const auto& s : values) {
        ret += " " + s;
    }
    ret += "}";
    return ret;
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

bool Scope::inScope(std::string name) const {
    auto pos = domains.find(name);
    if (pos != domains.end()) {
        return true;
    } else {
        for (auto it = domains.begin(); it != domains.end(); it++) {
            if (it->second->belongToDomain(name)) {
                return true;
            }
        }
        return false;
    }
}

const std::map<std::string, DomainPtr>& Scope::getDomains(void) const {
    return domains;
}

std::string Scope::to_string(void) const {
    std::string ret = "";
    for (auto it = domains.begin(); it != domains.end(); ++it) {
        ret += it->first + " : " + it->second->to_string() + "\n";
    }
    return ret;
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
    ValuePtr vptr = std::make_shared<Value>(v);
    if (single) {
        if (values.size() > 0) {
            values[0] = vptr;
        } else {
            values.push_back(vptr);
        }
    } else {
        values.push_back(vptr);
    }
}

const std::vector<ValuePtr> & Attribute::getValue(void) const {
    return values;
}

std::string Attribute::to_string(void) const {
    std::string ret = "{";
    ret += "name:" + name + ",";
    ret += "ID:" + std::to_string(ID) + ",";
    ret += "values:";
    for (const auto& r : values) {
        ret += " " + r->to_string();
    }
    ret += "}";
    return ret;
}


//class User
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

std::string User::getName(void) const {
    return name;
}

int User::getID(void) const {
    return ID;
}

const std::vector<AttributePtr>& User::getConfiguration(void) const {
    return attrs;
}

std::string User::to_string(void) const {
    std::string ret = "{";
    ret += "name:" + name + ",";
    ret += "ID:" + std::to_string(ID) + ",";
    ret += "attrs:[";
    for (const auto& a : attrs) {
        ret += " " + a->to_string();
    }
    ret += "]}";
    return ret;
}

//class EqualExpression
std::string EqualExpression::getAttribute(void) const {
    return attribute;
}
std::string EqualExpression::getValue(void) const {
    return value;
}
std::string EqualExpression::to_string(void) const {
    return attribute + "=" + value;
}

//class Precondition
void Precondition::insertPositive(TargetPtr t) {
    Pt.push_back(t);
}
void Precondition::insertNegative(TargetPtr t) {
    Nt.push_back(t);
}
const std::vector<TargetPtr>& Precondition::getPt(void) const {
    return Pt;
}
const std::vector<TargetPtr>& Precondition::getNt(void) const {
    return Nt;
}


std::string Precondition::to_string(void) const {
    if (isTrue) {
        return "TRUE";
    } else {
        std::string ret = "Pt:[";
        for (const auto& t : Pt) {
            ret += " " + t->to_string();
        }
        ret += "] Nt:[";
        for (const auto& t : Nt) {
            ret += " " + t->to_string();
        }
        ret += "]";
        return ret;
    }
}

//class AssignRule
std::string AssignRule::getAdmin(void) const {
    return admin;
}

PreconditionPtr AssignRule::getPrecondition(void) const {
    return precondition;
}

TargetPtr AssignRule::getTarget(void) const {
    return target;
}

std::string AssignRule::to_string(void) const {
    std::string ret = "<";
    ret += admin + ",";
    ret += precondition->to_string() + ",";
    ret += target->to_string();
    ret += ">";
    return ret;
}


//class AddRule
std::string AddRule::getAdmin(void) const {
    return admin;
}

PreconditionPtr AddRule::getPrecondition(void) const {
    return precondition;
}

TargetPtr AddRule::getTarget(void) const {
    return target;
}

std::string AddRule::to_string(void) const {
    std::string ret = "<";
    ret += admin + ",";
    ret += precondition->to_string() + ",";
    ret += target->to_string();
    ret += ">";
    return ret;
}

// class DeleteRule
std::string DeleteRule::getAdmin(void) const {
    return admin;
}

TargetPtr DeleteRule::getTarget(void) const {
    return target;
}

std::string DeleteRule::to_string(void) const {
    std::string ret = "<";
    ret += admin + ",";
    ret += target->to_string();
    ret += ">";
    return ret;
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
        return attrs[attr_pos->second];
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

TargetPtr rGURA::getQuery(void) const {
    return query;
}

void rGURA::setQuery(TargetPtr t) {
    query = t;
}


const std::vector<UserPtr> & rGURA::getUsers(void) const {
    return users;
}
const std::vector<AttributePtr> &  rGURA::getAttrs(void) const {
    return attrs;
}
const std::vector<std::string> &  rGURA::getAdmin_roles(void) const {
    return admin_roles;
}
const std::vector<AssignRulePtr> &  rGURA::getAssign_rules(void) const {
    return assign_rules;
}
const std::vector<AddRulePtr> &  rGURA::getAdd_rules(void) const {
    return add_rules;
}
const std::vector<DeleteRulePtr> &  rGURA::getDelete_rules(void) const {
    return delete_rules;
}

std::string rGURA::to_string(void) const {
    std::string ret = "Users:\n";
    for (const auto& u : users) {
        ret += u->to_string() + '\n';
    }
    ret += "Attributes:\n";
    for (const auto& a : attrs) {
        ret += a->to_string() + '\n';
    }
    ret += "Scope:\n";
    ret += scope->to_string();
    ret += "AdminRoles:\n";
    for (const auto& a : admin_roles) {
        ret += a + '\n';
    }
    ret += "Rules:\n";
    for (const auto& r : assign_rules) {
        ret += r->to_string() + '\n';
    }
    for (const auto& r : add_rules) {
        ret += r->to_string() + '\n';
    }
    for (const auto& r : delete_rules) {
        ret += r->to_string() + '\n';
    }
    ret += "Spec:" + query->to_string() + "\n";
    return ret;
}



