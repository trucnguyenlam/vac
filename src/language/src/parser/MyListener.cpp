#include "MyListener.h"

using namespace SMT;


void MyListener::enterR_user(vacgrammarParser::R_userContext * ctx) {
    std::cout   << "initial size of users is: "
                << this->vac_model->getCurrentUserSize()
                << std::endl;
}
void MyListener::exitR_user(vacgrammarParser::R_userContext * ctx) {
    std::cout   << "size of users is: "
                << this->vac_model->getCurrentUserSize()
                << std::endl;
}

void MyListener::enterUser_element(vacgrammarParser::User_elementContext * ctx) {
    bool isNew = ctx->STAR() ? true : false; // Check if this user is new user
    int user_id = this->vac_model->getCurrentUserSize();
    UserPtr newuser = std::make_shared<User>(User(user_id, ctx->Identifier()->getText(), isNew));
    this->vac_model->insertNewUser(newuser, user_id); // Insert user into model
}

void MyListener::exitUser_element(vacgrammarParser::User_elementContext * ctx) {
    // Not implement
}


void MyListener::enterR_attr(vacgrammarParser::R_attrContext * ctx) {
    std::cout   << "Initial size of attributes is: "
                << this->vac_model->getCurrentAttributeSize()
                << std::endl;

}
void MyListener::exitR_attr(vacgrammarParser::R_attrContext * ctx) {
    std::cout   << "size of attributes is: "
                << this->vac_model->getCurrentAttributeSize()
                << std::endl;
}

void MyListener::enterAttr_element(vacgrammarParser::Attr_elementContext * ctx) {
    int attr_id = this->vac_model->getCurrentAttributeSize();
    int attr_size = std::stoi(ctx->Constant()->getText(), nullptr);
    std::string attr_name = ctx->Identifier()->getText();
    if (attr_size <= 0) {
        std::cerr << "Attribute " << attr_name << " with size negative" << std::endl;
    }
    AttributePtr newAttr  = std::make_shared<Attribute>(Attribute(attr_id, attr_name, attr_size ) );

    this->vac_model->insertNewAttribute(newAttr, attr_id);
}


void MyListener::exitAttr_element(vacgrammarParser::Attr_elementContext * ctx) {
    // Not implement
}


void MyListener::enterR_init(vacgrammarParser::R_initContext * ctx) {

}
void MyListener::exitR_init(vacgrammarParser::R_initContext * ctx) {
    for (const auto & u : this->vac_model->getCopyOfUsers()) {
        std::cout << u->to_string() << std::endl;
    }
}

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
                std::cerr << "Attribute: " << attr_name << " is undefined!" << std::endl;
            }
        }
    } else {
        std::cerr << "User: " << user_name << " is undefined!" << std::endl;
    }
}


void MyListener::exitInit_element(vacgrammarParser::Init_elementContext * ctx) {
}


void MyListener::enterInit_assignment(vacgrammarParser::Init_assignmentContext * ctx) {

}

void MyListener::exitInit_assignment(vacgrammarParser::Init_assignmentContext * ctx) {

}




