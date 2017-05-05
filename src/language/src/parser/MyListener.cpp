// Author: trucnguyenlam@gmail.com
// Description:
//    This is for the parser.
//
// TODO:
//  - More professional way of hanlding error
// ChangeLog:
//    2017.05.04   Initial version


#include <csignal>
#include <typeinfo>
#include "MyListener.h"

using namespace SMT;

void MyListener::enterFile(vacgrammarParser::FileContext * ctx) {}

void MyListener::exitFile(vacgrammarParser::FileContext * ctx) {}



void MyListener::enterR_user(vacgrammarParser::R_userContext * ctx) {}
void MyListener::exitR_user(vacgrammarParser::R_userContext * ctx) {}

void MyListener::enterUser_element(vacgrammarParser::User_elementContext * ctx) {
    bool isNew = ctx->STAR() ? true : false; // Check if this user is new user
    int user_id = this->vac_model->getCurrentUserSize();
    UserPtr newuser = std::make_shared<User>(User(user_id, ctx->Identifier()->getText(), isNew));
    this->vac_model->insertNewUser(newuser, user_id); // Insert user into model
}

void MyListener::exitUser_element(vacgrammarParser::User_elementContext * ctx) {}


void MyListener::enterR_attr(vacgrammarParser::R_attrContext * ctx) {}

void MyListener::exitR_attr(vacgrammarParser::R_attrContext * ctx) {}

void MyListener::enterAttr_element(vacgrammarParser::Attr_elementContext * ctx) {
    int attr_id = this->vac_model->getCurrentAttributeSize();
    int attr_size = std::stoi(ctx->Constant()->getText(), nullptr);
    std::string attr_name = ctx->Identifier()->getText();
    if (attr_size <= 0) {
        std::cerr << "Error in Attribute: " << attr_name << " with size negative" << std::endl;
        std::_Exit(EXIT_FAILURE);

    }
    AttributePtr newAttr  = std::make_shared<Attribute>(Attribute(attr_id, attr_name, attr_size ) );

    this->vac_model->insertNewAttribute(newAttr, attr_id);
}


void MyListener::exitAttr_element(vacgrammarParser::Attr_elementContext * ctx) {}


void MyListener::enterR_init(vacgrammarParser::R_initContext * ctx) {}

void MyListener::exitR_init(vacgrammarParser::R_initContext * ctx) {}

void MyListener::enterInit_element(vacgrammarParser::Init_elementContext * ctx) {
    std::string user_name = ctx->Identifier()->getText();
    UserPtr user = this->vac_model->getUser(user_name);
    if (user) {
        for (const auto& e : ctx->init_assignment()) {
            std::string attr_name = e->Identifier()->getText();

            auto attrptr = this->vac_model->getAttribute(attr_name);
            if (attrptr) { // this attribute is available
                // Create an attribute and attach to user
                AttributePtr attr = std::make_shared<Attribute>(Attribute(
                                        attrptr->getID(), attr_name, attrptr->getSize()));

                // Set value
                int value = std::stoi(e->Constant()->getText(), nullptr);
                Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));
                attr->setValue(valptr);

                // Add to user
                user->setAttribute(attr);
            } else {
                std::cerr << "Error in Init: attribute " << attr_name << " is undefined!" << std::endl;
                std::_Exit(EXIT_FAILURE);

            }
        }
    } else {
        std::cerr << "Error in Init: user " << user_name << " is undefined!" << std::endl;
        std::_Exit(EXIT_FAILURE);

    }
}


void MyListener::exitInit_element(vacgrammarParser::Init_elementContext * ctx) {}

void MyListener::enterInit_assignment(vacgrammarParser::Init_assignmentContext * ctx) {}

void MyListener::exitInit_assignment(vacgrammarParser::Init_assignmentContext * ctx) {}

void  MyListener::enterRule_element(vacgrammarParser::Rule_elementContext * ctx) {
    // Precondition
    std::map<std::string, int> luser_map;
    Expr precondition = buildPrecondition(ctx->precondition(), luser_map);

    RulePtr ruleptr = std::make_shared<Rule>(Rule(precondition));

    // Apply target
    std::string tmp_user = "";
    for (const auto & t : ctx->normal_assignment()) {
        std::string target_user_name = t->u->getText();
        if (tmp_user == "") tmp_user = target_user_name;
        if (tmp_user != "" && target_user_name != tmp_user) {
            std::cerr   << "Error in Rule: target user must be the same, "
                        << tmp_user << " != " << target_user_name
                        << std::endl;
            std::_Exit(EXIT_FAILURE);
        }

        auto id_pos = luser_map.find(target_user_name);
        int luser_id = (id_pos != luser_map.end()) ? id_pos->second : luser_map.size();
        std::string attr_name = t->a->getText();
        AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
        Entityp e = std::make_shared<Entity>(
                        Entity(target_user_name + "." + attr_name,
                               target_user_name,
                               luser_id,
                               attr_name,
                               attrptr->getID()));
        int value = std::stoi(t->Constant()->getText(), nullptr);
        Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));
        // add to rule
        ruleptr->addTargetExpr(EqExpr(e, valptr));
    }
    // Add to model
    this->vac_model->insertNewRule(ruleptr);

}
void  MyListener::exitRule_element(vacgrammarParser::Rule_elementContext * ctx) {
}

void MyListener::enterR_query(vacgrammarParser::R_queryContext * ctx) {
    // Create lhs
    std::string user_name = ctx->normal_assignment()->u->getText();
    int user_id = this->vac_model->getUserID(user_name);
    std::string attr_name = ctx->normal_assignment()->a->getText();
    AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
    if (attrptr == nullptr) {
        std::cerr << "Error in Query: attribute " << attr_name << " is undefined!" << std::endl;
        std::_Exit(EXIT_FAILURE);

    }
    Entityp e = std::make_shared<Entity>(
                    Entity(user_name + "." + attr_name, user_name, user_id, attr_name, attrptr->getID()));

    // Create rhs
    int value = std::stoi(ctx->normal_assignment()->Constant()->getText(), nullptr);
    Constantp valptr = std::make_shared<Constant>(Constant(value, attrptr->getSize()));

    std::shared_ptr<EqExpr> query =  std::make_shared<EqExpr>(EqExpr(e, valptr));

    // add to model
    this->vac_model->setQuery(query);
}


void MyListener::exitR_query(vacgrammarParser::R_queryContext * ctx) {}


ModelPtr MyListener::getPolicy(void) const {
    return vac_model;
}

// Private helper methods
Expr MyListener::buildPrimaryExpression(
    vacgrammarParser::PrimaryExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) {
        if (ctx->DOT()) {
            std::string u_name = ctx->u->getText();
            auto pos = luser_map.find(u_name);
            int luser_id;
            if (pos != luser_map.end()) {
                luser_id = pos->second;
            } else {
                luser_id = luser_map.size();
                luser_map.insert(std::pair<std::string, int>(u_name, luser_id));
            }
            std::string attr_name = ctx->a->getText();
            AttributePtr attrptr = this->vac_model->getAttribute(attr_name);
            if (attrptr) {
                Entityp e = std::make_shared<Entity>(
                                Entity(u_name + "." + attr_name,
                                       u_name,
                                       luser_id,
                                       attr_name,
                                       attrptr->getID()));
                return e;
            }            else {
                std::cerr << "Error in Rule: attribute " << attr_name << " is undefined!" << std::endl;
                std::_Exit(EXIT_FAILURE);
            }
        } else {
            return buildExpression(ctx->expression(), luser_map);
        }
    } else {
        if (ctx->Constant()) {
            int value = std::stoi(ctx->Constant()->getText(), nullptr);
            Constantp valptr = std::make_shared<Constant>(Constant(value, 0));
            return valptr;
        }
    }
}

Expr MyListener::buildUnaryExpression(
    vacgrammarParser::UnaryExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) { // Primary expression
        return std::make_shared<NotExpr>(NotExpr(buildUnaryExpression(ctx->unaryExpression(), luser_map)));
    } else {
        return buildPrimaryExpression(ctx->primaryExpression(), luser_map);
    }
}

Expr MyListener::buildEqualityExpression(
    vacgrammarParser::EqualityExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) {
        Expr _lhs = buildEqualityExpression(ctx->equalityExpression(), luser_map);
        Expr _rhs = buildUnaryExpression(ctx->unaryExpression(), luser_map);
        return std::make_shared<EqExpr>(EqExpr(_lhs, _rhs));
    } else {
        return buildUnaryExpression(ctx->unaryExpression(), luser_map);
    }

}

Expr MyListener::buildAndExpression(
    vacgrammarParser::AndExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) {
        Expr  _lhs = buildAndExpression(ctx->andExpression(), luser_map);
        Expr  _rhs = buildEqualityExpression(ctx->equalityExpression(), luser_map);
        return std::make_shared<AndExpr>(AndExpr(_lhs, _rhs));
    } else {
        return buildEqualityExpression(ctx->equalityExpression(), luser_map);
    }
}


Expr MyListener::buildOrExpression(
    vacgrammarParser::OrExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) {
        Expr _lhs = buildOrExpression(ctx->orExpression(), luser_map);
        Expr _rhs = buildAndExpression(ctx->andExpression(), luser_map);
        return std::make_shared<OrExpr>(OrExpr(_lhs, _rhs));
    } else {
        return buildAndExpression(ctx->andExpression(), luser_map);
    }

}

Expr MyListener::buildImplyExpression(
    vacgrammarParser::ImplyExpressionContext * ctx,
    std::map<std::string, int> & luser_map) const {
    if (ctx->children.size() > 1) {
        Expr _lhs = buildImplyExpression(ctx->implyExpression(), luser_map);
        Expr _rhs = buildOrExpression(ctx->orExpression(), luser_map);
        return std::make_shared<ImplExpr>(ImplExpr(_lhs, _rhs));
    } else {
        return buildOrExpression(ctx->orExpression(), luser_map);
    }

}

Expr MyListener::buildConditionalExpression(
    vacgrammarParser::ConditionalExpressionContext * ctx,
    std::map<std::string, int> & luser_map
) const {
    if (ctx->QUESTION()) {
        Expr _cond = buildImplyExpression(ctx->implyExpression(), luser_map);
        Expr _choice1 = buildExpression(ctx->expression(), luser_map);
        Expr _choice2 = buildConditionalExpression(ctx->conditionalExpression(), luser_map);
        return std::make_shared<CondExpr>(CondExpr(_cond, _choice1, _choice2));
    } else {
        return buildImplyExpression(ctx->implyExpression(), luser_map);
    }
}

Expr MyListener::buildExpression(
    vacgrammarParser::ExpressionContext * ctx,
    std::map<std::string, int> & luser_map
) const {
    return buildConditionalExpression(ctx->conditionalExpression(), luser_map);
}

Expr MyListener::buildPrecondition(
    vacgrammarParser::PreconditionContext * ctx,
    std::map<std::string, int> & luser_map
) const {
    if (ctx->TRUE()) {
        Constantp valptr = std::make_shared<Constant>(Constant(1, 1));
        return valptr;
    } else {
        if (dynamic_cast<vacgrammarParser::ExpressionContext*>(ctx->expression())) {
            return buildExpression(ctx->expression(), luser_map);
        } else {
            std::cerr << "Error in Rule: precondition " << ctx->getText() << " is not valid!" << std::endl;
            std::_Exit(EXIT_FAILURE);
        }
    }
}

