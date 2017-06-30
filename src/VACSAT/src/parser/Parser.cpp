#include "Parser.h"
#include <algorithm>
/**
 * TODO: improve ParserError
 */

using namespace Parser;

namespace {
void my_delete(Token *p) {
    delete p;
}
}

ParserError::ParserError(const std::string &msg) : std::exception(), _message(msg) {
}

const char* ParserError::what() const noexcept {
    return ("ParserError: " + _message).c_str();
}

HandParser::HandParser(std::vector<Token *> tokens):
    tokens(tokens) {
    current = 0;
    vac_model = std::make_shared<Model>(Model());
}
HandParser::~HandParser() {
    std::for_each(tokens.begin(), tokens.end(), my_delete);
    tokens.clear();
}

// Public method
void HandParser::parse(void) {
    // std::cout << "DEBUG: token size is: " << tokens.size() << std::endl;
    while (!isAtEnd()) {
        r_start();
    }
}

ModelPtr HandParser::getPolicy(void) const {
    return vac_model;
}

// Private method
void HandParser::r_start(void) {
    try {
        // std::cout << "DEBUG: first token is " << peek()->ToString() << std::endl;
        if (match(USER)) {
            // std::cout << "DEBUG: go into r_user()" << std::endl;
            r_user();
        } else if (match(ATTR)) {
            r_attr();
        } else if (match(INIT)) {
            r_init();
        } else if (match(RULE)) {
            r_rules();
        } else if (match(QUERY)) {
            r_query();
        } else {
            throw ParserError("Line " + std::to_string(peek()->getLine()) + \
                              ": undefined: " + peek()->ToString());
        }
    } catch (ParserError error) {
        std::cerr << error.what() << std::endl;
        std::_Exit(EXIT_FAILURE);
    }
}

void HandParser::r_user(void) {
    // std::cout << "DEBUG: go r_user()" << std::endl;
    do {
        user_element();
    } while (check(IDENTIFIER));
    checkConsume(SEMI, "Line " + std::to_string(peek()->getLine()) + ": expect ;.");
}


void HandParser::user_element(void) {
    Token * userTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect user name.");
    // std::cout << "DEBUG: got user " << userTk->getLexeme() << std::endl;
    bool isNew = match(STAR) ? true : false;
    int user_id = this->vac_model->getCurrentUserSize();
    UserPtr newuser = std::make_shared<User>(User(user_id, userTk->getLexeme(), isNew));
    this->vac_model->insertNewUser(newuser, user_id); // Insert user into model
}

void HandParser::r_attr(void) {
    do {
        attr_element();
    } while (check(IDENTIFIER));
    checkConsume(SEMI, "Line " + std::to_string(peek()->getLine()) + ": expect ;.");
}


void HandParser::attr_element(void) {
    Token * attrTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect attribute name.");
    if (match(LEFTBRACKET)) {
        Token * sizeTk = consume(CONSTANT, "Line " + std::to_string(peek()->getLine()) + ": expect attribute size.");
        int attr_id = this->vac_model->getCurrentAttributeSize();
        int attr_size = sizeTk->getLiteral();
        std::string attr_name = attrTk->getLexeme();
        if (attr_size <= 0) {
            throw ParserError("Line " + std::to_string(sizeTk->getLine()) + \
                              ": attribute size is negative: " + attr_name);
        }
        AttributePtr newAttr = std::make_shared<Attribute>(Attribute(attr_id, attr_name, attr_size ) );
        this->vac_model->insertNewAttribute(newAttr, attr_id);
        if (!match(RIGHTBRACKET)) {
            throw ParserError("Line " + std::to_string(attrTk->getLine()) + \
                              ": attribute " + attrTk->getLexeme() + " is defined wrongly.");
        }
    } else {
        throw ParserError("Line " + std::to_string(attrTk->getLine()) + \
                          ": attribute " + attrTk->getLexeme() + " is defined wrongly.");
    }
}

void HandParser::r_init(void) {
    do {
        init_element();
    } while (check(LEFTTUPLE));
    checkConsume(SEMI, "Line " + std::to_string(peek()->getLine()) + ": expect ;.");
}



void HandParser::init_element(void) {
    checkConsume(LEFTTUPLE, "Line " + std::to_string(peek()->getLine()) + ": expect <.");
    Token * uTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect user name.");
    std::string user_name = uTk->getLexeme();
    UserPtr user = this->vac_model->getUser(user_name);
    if (user) {
        checkConsume(COLON, "Line " + std::to_string(peek()->getLine()) + ": expect :.");
        init_assignment(user);
        while (match(COMMA)) {
            init_assignment(user);
        }
        checkConsume(RIGHTTUPLE, "Line " + std::to_string(peek()->getLine()) + ": expect >.");
    } else {
        throw ParserError("Line " + std::to_string(uTk->getLine()) + \
                          ": user " + user_name + " is undefined!");
    }
}

void HandParser::init_assignment(UserPtr user) {
    Token * aTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect attribute name.");
    std::string attr_name = aTk->getLexeme();
    auto attrptr = this->vac_model->getAttribute(attr_name);
    if (attrptr) { // this attribute is available
        // Create an attribute and attach to user
        AttributePtr attr = std::make_shared<Attribute>(Attribute(
                                attrptr->getID(), attr_name, attrptr->getSize()));
        // Set value
        checkConsume(EQUAL, "Line " + std::to_string(peek()->getLine()) + ": expect =.");
        Token * vTk = consume(CONSTANT, "Line " + std::to_string(peek()->getLine()) + ": expect a constant.");
        int value = vTk->getLiteral();
        Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));
        attr->setValue(valptr);
        // Add to user
        user->setAttribute(attr);
    } else {
        throw ParserError("Line " + std::to_string(aTk->getLine()) + \
                          ": attribute " + attr_name + " is undefined!");
    }
}


void HandParser::r_rules(void) {
    while (check(LEFTTUPLE)) {
        rule_element();
    }
    checkConsume(SEMI, "Line " + std::to_string(peek()->getLine()) + ": expect ;.");
}


void HandParser::rule_element(void) {
    checkConsume(LEFTTUPLE, "Line " + std::to_string(peek()->getLine()) + ": expect <.");
    std::map<std::string, int> luser_map;
    int const_size = 1;
    Expr admin = expression(luser_map, const_size);
    checkConsume(COMMA, "Line " + std::to_string(peek()->getLine()) + ": expect ,.");
    Expr precondition = expression(luser_map, const_size);
    checkConsume(COLON, "Line " + std::to_string(peek()->getLine()) + ": expect :.");
    RulePtr ruleptr = std::make_shared<Rule>(Rule(admin, precondition));

    std::string tmp_user = "";
    normal_assignment(ruleptr, luser_map, tmp_user);
    while (match(COMMA)) {
        normal_assignment(ruleptr, luser_map, tmp_user);
    }
    checkConsume(RIGHTTUPLE, "Line " + std::to_string(peek()->getLine()) + ": expect >.");
    // Add to model
    this->vac_model->insertNewRule(ruleptr);
}

Expr HandParser::primaryExpression(std::map<std::string, int>& luser_map, int& const_size) {
    if (check(CONSTANT)) { // A constant
        Token * vTk = advance();
        int value = vTk->getLiteral();
        return std::make_shared<Constant>(Constant(value, const_size));
    } else if (check(IDENTIFIER)) {
        Token * uTk = advance();
        std::string u_name = uTk->getLexeme();
        auto pos = luser_map.find(u_name);
        int luser_id;
        if (pos != luser_map.end()) {
            luser_id = pos->second;
        } else {
            luser_id = luser_map.size();
            luser_map.insert(std::pair<std::string, int>(u_name, luser_id));
        }
        checkConsume(DOT, "Line " + std::to_string(peek()->getLine()) + ": expect DOT token.");
        Token *aTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect attribute name");
        std::string attr_name = aTk->getLexeme();
        AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
        if (attrptr) {
            Entityp e = std::make_shared<Entity>(
                            Entity(u_name + "." + attr_name,
                                   u_name,
                                   luser_id,
                                   attr_name,
                                   attrptr->getID()));
            const_size = attrptr->getSize();
            return e;
        } else {
            throw ParserError("Line " + std::to_string(aTk->getLine()) + \
                              ":attribute " + attr_name + " is undefined!");
        }
    } else if (check(LEFTPAREN)) {
        // std::cout << "DEBUG: got primaryExpression" << std::endl;
        advance();
        Expr e = expression(luser_map, const_size);
        checkConsume(RIGHTPAREN, "Line " + std::to_string(peek()->getLine()) + ": expect ).");
        return e;
    } else {
        throw ParserError("Line " + std::to_string(peek()->getLine()) + \
                          ": unknown expression!");
    }

}

Expr HandParser::unaryExpression(std::map<std::string, int>& luser_map, int& const_size) {
    if (match(NOT)) {
        return std::make_shared<NotExpr>(NotExpr(primaryExpression(luser_map, const_size)));
    } else {
        return primaryExpression(luser_map, const_size);
    }
}

Expr HandParser::equalityExpression(std::map<std::string, int>& luser_map, int& const_size) {
    Expr _lhs = unaryExpression(luser_map, const_size);
    if (match(EQUAL)) {
        Expr _rhs = equalityExpression(luser_map, const_size);
        return std::make_shared<EqExpr>(EqExpr(_lhs, _rhs));
    } else {
        return _lhs;
    }
}

Expr HandParser::andExpression(std::map<std::string, int>& luser_map, int& const_size) {
    Expr _lhs = equalityExpression(luser_map, const_size);
    while (match(AND) || match(ANDAND)) {
        // std::cout << "DEBUG: got andExpression" << std::endl;
        Expr _rhs = equalityExpression(luser_map, const_size);
        _lhs = std::make_shared<AndExpr>(AndExpr(_lhs, _rhs));
    }
    return _lhs;
}

Expr HandParser::orExpression(std::map<std::string, int>& luser_map, int& const_size) {
    Expr _lhs = andExpression(luser_map, const_size);
    while (match(OR) || match(OROR)) {
        // std::cout << "DEBUG: got orExpression" << std::endl;
        Expr _rhs = andExpression(luser_map, const_size);
        _lhs = std::make_shared<OrExpr>(OrExpr(_lhs, _rhs));
    }
    return _lhs;
}

Expr HandParser::implyExpression(std::map<std::string, int>& luser_map, int& const_size) {
    Expr _lhs = orExpression(luser_map, const_size);
    if (match(IMPLY)) {
        // std::cout << "DEBUG: got implyExpression" << std::endl;
        Expr _rhs = implyExpression(luser_map, const_size);
        return std::make_shared<ImplExpr>(ImplExpr(_lhs, _rhs));
    } else {
        return _lhs;
    }
}



Expr HandParser::conditionalExpression(std::map<std::string, int>& luser_map, int& const_size) {
    Expr _cond = implyExpression(luser_map, const_size);
    if (match(QUESTION)) {
        // std::cout << "DEBUG: got conditionalExpression" << std::endl;

        Expr _choice1 = expression(luser_map, const_size);
        checkConsume(COLON, "Line " + std::to_string(peek()->getLine()) + ": expect :.");
        Expr _choice2 = expression(luser_map, const_size);
        return std::make_shared<CondExpr>(CondExpr(_cond, _choice1, _choice2));
    } else {
        return _cond;
    }
}

Expr HandParser::expression(std::map<std::string, int>& luser_map, int& const_size) {
    if (match(VTRUE)) {
        Constantp valptr = std::make_shared<Constant>(Constant(1, 1));
        return valptr;
    } else {
        // std::cout << "DEBUG: got expression" << std::endl;
        return conditionalExpression(luser_map, const_size);
    }
}


void HandParser::normal_assignment(RulePtr ruleptr,  std::map<std::string, int>& luser_map, std::string & tmp_user) {
    // Apply target
    Token * uTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect user name.");
    std::string target_user_name = uTk->getLexeme();
    if (tmp_user == "") tmp_user = target_user_name;
    if (tmp_user != "" && target_user_name != tmp_user) {
        throw ParserError("Line " + std::to_string(uTk->getLine()) + \
                          ": target user must be the same!");
    }
    auto id_pos = luser_map.find(target_user_name);
    int luser_id = (id_pos != luser_map.end()) ? id_pos->second : luser_map.size();
    checkConsume(DOT, "Line " + std::to_string(peek()->getLine()) + ": expect DOT token.");
    Token * aTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect attribute name.");
    std::string attr_name = aTk->getLexeme();
    AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
    if (attrptr) {
        Entityp e = std::make_shared<Entity>(
                        Entity(target_user_name + "." + attr_name,
                               target_user_name,
                               luser_id,
                               attr_name,
                               attrptr->getID()));
        checkConsume(EQUAL, "Line " + std::to_string(peek()->getLine()) + ": expect =.");
        Token * vTk = consume(CONSTANT, "Line " + std::to_string(peek()->getLine()) + ": expect constant.");
        int value = vTk->getLiteral();
        Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));
        // add to rule
        ruleptr->addTargetExpr(EqExpr(e, valptr));
    } else {
        throw ParserError("Line " + std::to_string(aTk->getLine()) + \
                          ": attribute " + attr_name + " is undefined!");
    }
}


void HandParser::r_query(void) {
    // Collecting query
    query_normal_assignment();
    checkConsume(SEMI, "Line " + std::to_string(peek()->getLine()) + ": expect ;.");
}

void HandParser::query_normal_assignment(void) {
    // Create lhs
    Token * uTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect user name.");
    std::string user_name = uTk->getLexeme();
    int user_id = this->vac_model->getUserID(user_name);
    checkConsume(DOT, "Line " + std::to_string(peek()->getLine()) + ": expect DOT token.");
    Token * aTk = consume(IDENTIFIER, "Line " + std::to_string(peek()->getLine()) + ": expect attribute name.");
    std::string attr_name = aTk->getLexeme();
    AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
    if (!attrptr) {
        throw ParserError("Line " + std::to_string(aTk->getLine()) + \
                          ": attribute " + attr_name + " is undefined!");
    }
    Entityp e = std::make_shared<Entity>(
                    Entity(user_name + "." + attr_name,
                           user_name, user_id, attr_name, attrptr->getID()));
    // Create rhs
    checkConsume(EQUAL, "Line " + std::to_string(peek()->getLine()) + ": expect =.");
    Token * vTk = consume(CONSTANT, "Line " + std::to_string(peek()->getLine()) + ": expect constant.");
    int value = vTk->getLiteral();
    Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));

    std::shared_ptr<EqExpr> query =  std::make_shared<EqExpr>(EqExpr(e, valptr));
    // add to model
    this->vac_model->setQuery(query);
}


bool HandParser::match(TokenType type) {
    if (check(type)) {
        advance();
        return true;
    } else {
        return false;
    }
}

// template <typename... Args>
// bool HandParser::matchOneOf(Args... types) {
//     for (auto & t : types) {
//         if (check(t)) {
//             advance();
//             return true;
//         }
//     }
//     return false;
// }


Token* HandParser::consume(TokenType type, std::string message) {
    if (check(type)) return advance();
    throw ParserError(message);
}

void HandParser::checkConsume(TokenType type, std::string message) {
    if (check(type)) {advance(); return;}
    throw ParserError(message);
}


bool HandParser::check(TokenType type) {
    if (isAtEnd()) return false;
    return peek()->getType() == type;
}


bool HandParser::isAtEnd(void) {
    return peek()->getType() == ENDOFFILE;
}


Token * HandParser::previous(void) const {
    return tokens.at(current - 1);
}


Token * HandParser::advance(void) {
    if (!isAtEnd()) current++;
    return previous();
}


Token * HandParser::peek(void) const {
    return tokens.at(current);

}


