#include "myrGURAListener.h"

using namespace VAC;


void myrGURAListener::enterR_user(rGURAParser::R_userContext * ctx) {
    int i = 0;
    for (const auto& c : ctx->Identifier()) {
        UserPtr newuser = std::make_shared<User>(User(i, c->getText()));
        this->policy->insertNewUser(newuser, i);
        i++;
    }
}

void myrGURAListener::enterR_attr_s(rGURAParser::R_attr_sContext * ctx) {
    for (const auto& c : ctx->Identifier()) {
        int attr_id = this->policy->getCurrentAttributeSize();
        AttributePtr newattr = std::make_shared<Attribute>(Attribute(attr_id, c->getText(), true));
        this->policy->insertNewAttribute(newattr, attr_id);
    }
}

void myrGURAListener::enterR_attr_m(rGURAParser::R_attr_mContext * ctx) {
    for (const auto& c : ctx->Identifier()) {
        int attr_id = this->policy->getCurrentAttributeSize();
        AttributePtr newattr = std::make_shared<Attribute>(Attribute(attr_id, c->getText(), false));
        this->policy->insertNewAttribute(newattr, attr_id);
    }
}

void myrGURAListener::enterR_scope(rGURAParser::R_scopeContext * ctx) {
    Scope scope;
    for (const auto & c : ctx->scope_element()) {
        std::string attrname = c->Identifier()[0]->getText();
        AttributePtr attr = this->policy->getAttribute(attrname);
        if (!attr) {
            throw ParserException(
                "Error in line  " + getTokenLocation(c->Identifier()[0]->getSymbol()) + ": attribute " + attrname + " is undefined!");

        }
        DomainPtr d = std::make_shared<Domain>(Domain());
        for (int i = 1; i < c->Identifier().size(); i++) {
            d->addValueToSet(c->Identifier()[i]->getText());
        }
        scope.addDomain(attrname, d);
    }
    this->policy->setScope(scope);
}

void myrGURAListener::enterR_admin(rGURAParser::R_adminContext * ctx) {
    for (const auto & c : ctx->Identifier()) {

        this->policy->insertAdminRole(c->getText());
    }

}

void myrGURAListener::enterUas_element(rGURAParser::Uas_elementContext * ctx) {
    // Find user
    std::string username = ctx->Identifier()->getText();
    UserPtr user = this->policy->getUser(username);
    if (user) {
        // Add attribute to user
        for (const auto& c : ctx->attr_val()) {
            // Get attribute name
            std::string attrname = c->a->getText();
            AttributePtr attr = this->policy->getAttribute(attrname);
            if (attr) {
                if (!attr->isSingle()) throw ParserException(
                        "Error in line  " + getTokenLocation(c->a) + ": attribute " + attrname + " is multiple!");

                AttributePtr newattr = std::make_shared<Attribute>(
                                           Attribute(attr->getID(), attr->getName(), attr->isSingle()));
                // Get value
                std::string valuename = c->v->getText();
                DomainPtr d = this->policy->getScope()->getDomain(attrname);
                if (d) {
                    int value_id = d->getValueID(valuename);
                    if (value_id < 0) {
                        throw ParserException(
                            "Error in line  " + getTokenLocation(c->v) + ": value " + valuename + " is undefined!");
                    }
                    // add value to attribute
                    newattr->setValue(Value(valuename, value_id));
                    // add attribute to user
                    user->setAttribute(newattr);
                } else {
                    throw ParserException(
                        "Error in line  " + getTokenLocation(c->a) + ": attribute " + attrname + " is undefined!");
                }
            } else {
                throw ParserException(
                    "Error in line  " + getTokenLocation(c->a) + ": attribute " + attrname + " is undefined!");
            }
        }
    } else {
        throw ParserException(
            "Error in line  " + getTokenLocation(ctx->Identifier()->getSymbol()) + ": user " + username + " is undefined!");
    }
}


void myrGURAListener::enterUam_element(rGURAParser::Uam_elementContext * ctx) {
    // Find user
    std::string username = ctx->Identifier()[0]->getText();
    UserPtr user = this->policy->getUser(username);
    if (user) {
        // Get attribute name
        std::string attrname = ctx->Identifier()[1]->getText();
        AttributePtr attr = this->policy->getAttribute(attrname);
        if (attr) {
            if (attr->isSingle()) throw ParserException(
                    "Error in line  " + getTokenLocation(ctx->Identifier()[1]->getSymbol()) + ": attribute " + attrname + " is single!");

            AttributePtr newattr = std::make_shared<Attribute>(
                                       Attribute(attr->getID(), attr->getName(), attr->isSingle()));
            for (auto it = ctx->Identifier().begin() + 2; it != ctx->Identifier().end(); ++it) {
                // Get value
                std::string valuename = (*it)->getText();
                DomainPtr d = this->policy->getScope()->getDomain(attrname);
                if (d) {
                    int value_id = d->getValueID(valuename);
                    if (value_id < 0) {
                        throw ParserException(
                            "Error in line  " + getTokenLocation((*it)->getSymbol()) + ": value " + valuename + " is undefined!");
                    }
                    // add value to attribute
                    newattr->setValue(Value(valuename, value_id));
                } else {
                    throw ParserException(
                        "Error in line  " + getTokenLocation(ctx->Identifier()[1]->getSymbol()) + ": attribute " + attrname + " is undefined!");
                }
            }
            // add attribute to user
            user->setAttribute(newattr);
        } else {
            throw ParserException(
                "Error in line  " + getTokenLocation(ctx->Identifier()[1]->getSymbol()) + ": attribute " + attrname + " is undefined!");
        }

    } else {
        throw ParserException(
            "Error in line  " + getTokenLocation(ctx->Identifier()[0]->getSymbol()) + ": user " + username + " is undefined!");
    }

}


void myrGURAListener::enterAdd_rule(rGURAParser::Add_ruleContext * ctx) {
    std::string adminrole = ctx->admin->getText();
    if (this->policy->hasAdminRole(adminrole)) {
        std::string attrname = ctx->attr->getText();
        AttributePtr attr = this->policy->getAttribute(attrname);
        if (attr) {
            std::string valuename = ctx->value->getText();
            DomainPtr d = this->policy->getScope()->getDomain(attrname);
            if (!d) {
                throw ParserException(
                    "Error in line  " + getTokenLocation(ctx->attr) + ": attribute " + attrname + " is undefined!");
            }
            int value_id = d->getValueID(valuename);
            if (value_id < 0) {
                throw ParserException(
                    "Error in line  " + getTokenLocation(ctx->value) + ": value " + valuename + " is undefined!");
            }
            TargetPtr t = std::make_shared<EqualExpression>(EqualExpression(attrname, valuename));

            PreconditionPtr precond = buildPrecondition(ctx->precondition());

            if (attr->isSingle()) {
                AssignRulePtr newrule = std::make_shared<AssignRule>(AssignRule(adminrole, precond, t));
                this->policy->insertNewAssignRule(newrule);
            } else {
                AddRulePtr newrule = std::make_shared<AddRule>(AddRule(adminrole, precond, t));
                this->policy->insertNewAddRule(newrule);
            }
        } else {
            throw ParserException(
                "Error in line  " + getTokenLocation(ctx->attr) + ": attribute " + attrname + " is undefined!");
        }
    } else {
        throw ParserException(
            "Error in line  " + getTokenLocation(ctx->admin) + ": admin role " + adminrole + " is undefined!");
    }
}

void myrGURAListener::enterDelete_rule(rGURAParser::Delete_ruleContext * ctx) {
    std::string adminrole = ctx->admin->getText();
    if (this->policy->hasAdminRole(adminrole)) {
        std::string attrname = ctx->attr->getText();
        AttributePtr attr = this->policy->getAttribute(attrname);
        if (attr) {
            std::string valuename = ctx->value->getText();
            DomainPtr d = this->policy->getScope()->getDomain(attrname);
            if (!d) {
                throw ParserException(
                    "Error in line  " + getTokenLocation(ctx->attr) + ": attribute " + attrname + " is undefined!");
            }
            int value_id = d->getValueID(valuename);
            if (value_id < 0) {
                throw ParserException(
                    "Error in line  " + getTokenLocation(ctx->value) + ": value " + valuename + " is undefined!");
            }
            TargetPtr t = std::make_shared<EqualExpression>(EqualExpression(attrname, valuename));
            DeleteRulePtr newrule = std::make_shared<DeleteRule>(DeleteRule(adminrole, t));
            this->policy->insertNewDeleteRule(newrule);
        } else {
            throw ParserException(
                "Error in line  " + getTokenLocation(ctx->attr) + ": attribute " + attrname + " is undefined!");
        }
    } else {
        throw ParserException(
            "Error in line  " + getTokenLocation(ctx->admin) + ": admin role " + adminrole + " is undefined!");
    }
}


void myrGURAListener::enterR_spec(rGURAParser::R_specContext * ctx) {
    std::string attrname = ctx->attr->getText();
    AttributePtr attr = this->policy->getAttribute(attrname);
    if (attr) {
        std::string valuename = ctx->value->getText();
        DomainPtr d = this->policy->getScope()->getDomain(attrname);
        if (!d) {
            throw ParserException(
                "Error in line  " + getTokenLocation(ctx->attr) + ": undefined domain for attribute " + attrname);
        }
        int value_id = d->getValueID(valuename);
        if (value_id < 0) {
            throw ParserException(
                "Error in line  " + getTokenLocation(ctx->value) + ": value " + valuename + " is undefined!");
        }
        TargetPtr t = std::make_shared<EqualExpression>(EqualExpression(attrname, valuename));
        this->policy->setQuery(t);
    } else {
        throw ParserException(
            "Error in line  " + getTokenLocation(ctx->attr) + ": attribute " + attrname + " is undefined!");
    }
}

// Private stub
PreconditionPtr myrGURAListener::buildPrecondition(rGURAParser::PreconditionContext * ctx) {
    PreconditionPtr precond = std::make_shared<Precondition>(Precondition());
    if (ctx->TRUE()) {
        precond->isTrue = true;
        return precond;
    } else {
        for (const auto& a : ctx->atom()) {
            std::string attrname = a->attr->getText();
            AttributePtr attr = this->policy->getAttribute(attrname);
            if (attr) {
                std::string valuename = a->value->getText();
                DomainPtr d = this->policy->getScope()->getDomain(attrname);
                if (!d) {
                    throw ParserException(
                        "Error in line  " + getTokenLocation(a->attr) + ": attribute " + attrname + " is undefined!");
                }
                int value_id = d->getValueID(valuename);
                if (value_id < 0) {
                    throw ParserException(
                        "Error in line  " + getTokenLocation(a->value) + ": value " + valuename + " is undefined!");
                }
                TargetPtr t = std::make_shared<EqualExpression>(EqualExpression(attrname, valuename));
                if (a->NOT()) { // negative set Nt
                    precond->insertNegative(t);
                } else { // positive set Pt
                    precond->insertPositive(t);
                }
            } else {
                throw ParserException(
                    "Error in line  " + getTokenLocation(a->attr) + ": attribute " + attrname + " is undefined!");
            }
        }
        return precond;
    }
}

std::string myrGURAListener::getTokenLocation(antlr4::Token * t) const {
    return std::to_string(t->getLine()) + ":" + std::to_string(t->getCharPositionInLine());
}

