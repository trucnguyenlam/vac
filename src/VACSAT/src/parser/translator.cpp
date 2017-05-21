#include "translator.h"

namespace { // Use unnamed namespace for private functions

bool hasSameUser(Parser::Expr e) {
    // TODO
    return true;
}

SMT::Expr buildExpression(Parser::Expr e, const Parser::ModelPtr policy, const std::vector<SMT::atom> & atoms) {
    switch (e->type) {
    case Parser::Exprv::CONSTANT:
        return std::make_shared<SMT::Constant>(SMT::Constant(std::dynamic_pointer_cast<Parser::Constant>(e)->value,
                                               std::dynamic_pointer_cast<Parser::Constant>(e)->bv_size));
    case Parser::Exprv::LITERAL:
        throw Parser::TranslatorException("Expression " + e->to_string() + " is not valid in precondition!");
    case Parser::Exprv::ENTITY:
        return atoms[std::dynamic_pointer_cast<Parser::Entity>(e)->getAttributeID()];
        break;
    case Parser::Exprv::EQ_EXPR:
        return std::make_shared<SMT::EqExpr>(SMT::EqExpr(
                buildExpression(std::dynamic_pointer_cast<Parser::EqExpr>(e)->lhs, policy, atoms),
                buildExpression(std::dynamic_pointer_cast<Parser::EqExpr>(e)->rhs, policy, atoms)));
    case Parser::Exprv::NOT_EXPR:
        return std::make_shared<SMT::NotExpr>(SMT::NotExpr(
                buildExpression(std::dynamic_pointer_cast<Parser::NotExpr>(e)->expr, policy, atoms)
                                              ));
    case Parser::Exprv::OR_EXPR:
        return std::make_shared<SMT::OrExpr>(SMT::OrExpr(
                buildExpression(std::dynamic_pointer_cast<Parser::OrExpr>(e)->lhs, policy, atoms),
                buildExpression(std::dynamic_pointer_cast<Parser::OrExpr>(e)->rhs, policy, atoms)
                                             ));
    case Parser::Exprv::AND_EXPR:
        return std::make_shared<SMT::AndExpr>(SMT::AndExpr(
                buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(e)->lhs, policy, atoms),
                buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(e)->rhs, policy, atoms)
                                              ));
    case Parser::Exprv::COND_EXPR:
    case Parser::Exprv::IMPL_EXPR:
    default:
        throw Parser::TranslatorException("Expression " + e->to_string() + " is not valid in precondition!");
    }
}

std::shared_ptr<SMT::arbac_policy> toSMT_arbac_policy(Parser::ModelPtr policy) {
    std::shared_ptr<SMT::arbac_policy> newpolicy = std::make_shared<SMT::arbac_policy>(SMT::arbac_policy());
    std::vector<SMT::atom> atoms;
    // Created attribute, vector of UNIQUE attributes
    for (const auto & a : policy->getCopyOfAttributes()) {
        if (a->getSize() == 1) {
            SMT::atom role(new SMT::Literal(a->getName(), a->getID(), a->getSize()));
            atoms.push_back(role);
        } else {
            throw Parser::TranslatorException("Attribute " + a->getName() + " does not have size 1!");
        }
    }
    // TODO(truc): add atom to SMT::arbac_policy _atoms

    // Add user
    for (const auto & u : policy->getCopyOfUsers()) {
        SMT::userp user = std::make_shared<SMT::user>(SMT::user(u->getName(), u->getID(), u->isInfinite()));
        // Add attribute for each user
        for (const auto & ua : u->getCopyConfiguration()) {
            if (ua->getValue() != nullptr && ua->getValue()->to_string() == "1") {
                user->add_atom(atoms[ua->getID()]);
            } else {
                throw Parser::TranslatorException(
                    "Attribute " + ua->getName() + " of user " + u->getName() + " has invalid value!");
            }
        }
        newpolicy->add_user(user);
    }

    // Add rule
    int cr_counter = 0;
    int ca_counter = 0;
    for (const auto & r : policy->getCopyOfRules()) {
        // Check target expression
        if (r->getCopyApplyTarget().size() == 1) {
            SMT::Expr admin;
            SMT::Expr prec;
            SMT::atom tar;
            if (std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())) {
                // Extract admin
                if (hasSameUser(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->lhs)) {
                    admin = buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->lhs, policy, atoms);
                } else {
                    throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported!");
                }
                // Extract precondition
                if (hasSameUser(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->rhs)) {
                    prec = buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->rhs, policy, atoms);
                } else {
                    throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported!");
                }
            } else { // There is no precondition (limitation)
                if (hasSameUser(r->getPrecondition())) {
                    admin = buildExpression(r->getPrecondition(), policy, atoms);
                    prec = std::make_shared<SMT::Constant>(SMT::Constant(1, 1));
                } else {
                    throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported!");
                }
            }
            // Extract target
            std::shared_ptr<Parser::EqExpr> target = r->getCopyApplyTarget()[0];
            if (std::dynamic_pointer_cast<Parser::Entity>(target->lhs)) {
                tar = atoms[std::dynamic_pointer_cast<Parser::Entity>(target->lhs)->getAttributeID()];
            } else {
                throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported, invalid target!");
            }

            if (std::dynamic_pointer_cast<Parser::Constant>(target->rhs)) {
                if (std::dynamic_pointer_cast<Parser::Constant>(target->rhs)->value == 0) { // Can revoke rule
                    SMT::rulep nr(new SMT::rule(false, admin, prec, tar, cr_counter));
                    newpolicy->add_rule(nr);
                    cr_counter++;
                } else {
                    SMT::rulep nr(new SMT::rule(true, admin, prec, tar, ca_counter));
                    newpolicy->add_rule(nr);
                    ca_counter++;
                }
            } else {
                throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported, invalid target!");
            }

        } else {
            throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported, multiple targets!");
        }
    }

    // Query
    std::shared_ptr<Parser::EqExpr> query = std::dynamic_pointer_cast<Parser::EqExpr>(policy->getQuery());
    newpolicy->goal_role = atoms[std::dynamic_pointer_cast<Parser::Entity>(query->lhs)->getAttributeID()];

    return newpolicy;
}

}

std::shared_ptr<SMT::arbac_policy> Parser::parse_new_ac(std::string inputfile) {
    std::ifstream stream;
    stream.open(inputfile);

    antlr4::ANTLRInputStream input(stream);
    Parser::vacgrammarLexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);

    // Create parser
    Parser::vacgrammarParser parser(&tokens);
    antlr4::tree::ParseTree * program = parser.file();

    // Work through parser tree to produce the model
    Parser::MyListener listener;
    antlr4::tree::ParseTreeWalker::DEFAULT.walk(&listener, program);

    // Retrieve policy
    Parser::ModelPtr policy = listener.getPolicy();

    // Close file stream
    stream.close();

    // Print policy
    std::cout << policy->to_string();
    std::shared_ptr<SMT::arbac_policy> newpolicy = toSMT_arbac_policy(policy);
    std::cout << newpolicy->to_string();
    return newpolicy;
}

