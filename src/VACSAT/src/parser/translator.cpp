#include "translator.h"

namespace { // Use unnamed namespace for private functions

bool hasSameUser(Parser::Expr e) {
    // TODO
    return true;
}

SMT::Expr buildExpression(Parser::Expr e, const Parser::ModelPtr policy, const std::vector<SMT::atom> & atoms) {
    // std::cout << "DEBUG: " << e->to_string() << ":" << std::to_string(e->type) << std::endl;
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

    // std::cout << "DEBUG: process atoms" << std::endl;
    std::vector<SMT::atom> atoms;
    // Created attribute, vector of UNIQUE attributes
    for (const auto & a : policy->getCopyOfAttributes()) {
        if (a->getSize() == 1) {
            SMT::atom role(new SMT::Literal(a->getName(), a->getID(), a->getSize()));
            // std::cout << "DEBUG:   " << role->to_string() << std::endl;
            atoms.push_back(role);
            newpolicy->add_atom(role);
        } else {
            throw Parser::TranslatorException("Attribute " + a->getName() + " does not have size 1!");
        }
    }

    // std::cout << "DEBUG: process users" << std::endl;
    // Add user
    for (const auto & u : policy->getCopyOfUsers()) {
        SMT::userp user = std::make_shared<SMT::user>(SMT::user(u->getName(), u->getID(), u->isInfinite()));
        // Add attribute for each user
        for (const auto & ua : u->getCopyConfiguration()) {
            if (ua->getValue() != nullptr && ua->getValue()->to_string() == "1") {
                user->add_atom(atoms[ua->getID()]);
            } else if (ua->getValue() != nullptr && ua->getValue()->to_string() == "0") {
            } else {
                throw Parser::TranslatorException(
                    "Attribute " + ua->getName() + " of " + u->getName() + " has invalid value!");
            }
        }
        // std::cout << "DEBUG:    " << user->to_string() << std::endl;
        newpolicy->add_user(user);
    }

    // Add rule
    int cr_counter = 0;
    int ca_counter = 0;

    // std::cout << "DEBUG: process rules" << std::endl;
    for (const auto & r : policy->getCopyOfRules()) {
        // Check target expression
        if (r->getCopyApplyTarget().size() == 1) {
            // std::cout << "DEBUG: adding rule: " << r->to_string() << std::endl;
            SMT::Expr admin;
            SMT::Expr prec;
            SMT::atom tar;
            if (std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())) {
                // std::cout << "DEBUG:    type 1 rule\n";
                // Extract admin
                if (hasSameUser(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->lhs)) {
                    admin = buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->lhs, policy, atoms);
                    // std::cout << "DEBUG:    admin:" << admin->to_string() << std::endl;
                } else {
                    throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported!");
                }
                // Extract precondition
                if (hasSameUser(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->rhs)) {
                    prec = buildExpression(std::dynamic_pointer_cast<Parser::AndExpr>(r->getPrecondition())->rhs, policy, atoms);
                    // std::cout << "DEBUG:    prec:" << prec->to_string() << std::endl;
                } else {
                    throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported!");
                }
            } else { // There is no precondition (limitation)
                // std::cout << "DEBUG:     type 2 rule\n";
                if (hasSameUser(r->getPrecondition())) {
                    admin = buildExpression(r->getPrecondition(), policy, atoms);
                    // std::cout << "DEBUG:    admin:" << admin->to_string() << std::endl;
                    prec = std::make_shared<SMT::Constant>(SMT::Constant(1, 1));
                    // std::cout << "DEBUG:    prec:" << prec->to_string() << std::endl;
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

            // std::cout << "DEBUG:    target:" << tar->to_string() << std::endl;

            if (target->rhs->to_string() == "0") { // Can revoke rule
                // std::cout << "DEBUG: cr rule\n";
                SMT::rulep cr = std::make_shared<SMT::rule>(SMT::rule(false, admin, prec, tar, cr_counter));
                newpolicy->add_can_revoke_no_update(cr);
                cr_counter++;
            } else if (target->rhs->to_string() == "1") { // Can assign rule
                // std::cout << "DEBUG: ca rule\n";
                SMT::rulep ca = std::make_shared<SMT::rule>(SMT::rule(true, admin, prec, tar, ca_counter));
                newpolicy->add_can_assign_no_update(ca);
                ca_counter++;
            } else {
                throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported, invalid target!");
            }
            // std::cout << "DEBUG: ...done\n";
        } else {
            throw Parser::TranslatorException("Rule:" + r->to_string() + " is not supported, multiple targets!");
        }
    }

    // Query
    std::shared_ptr<Parser::EqExpr> query =
        std::dynamic_pointer_cast<Parser::EqExpr>(policy->getQuery());
    newpolicy->update_query (
        atoms[std::dynamic_pointer_cast<Parser::Entity>(query->lhs)->getAttributeID()]);
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
    // std::cout << policy->to_string();
    std::shared_ptr<SMT::arbac_policy> newpolicy = toSMT_arbac_policy(policy);
    // std::cout << newpolicy->to_string();
    return newpolicy;
}

