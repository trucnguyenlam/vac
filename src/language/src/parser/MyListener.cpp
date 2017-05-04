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
    UserPtr newuser = std::make_shared<User>(User(user_id, ctx->Identifier()->getText(), isNew));
    int user_id = this->vac_model->getCurrentUserSize();
    this->vac_model->insertNewUser(newuser, user_id); // Insert user into model
}

void MyListener::exitUser_element(vacgrammarParser::User_elementContext * ctx) {
    //
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


}


void MyListener::exitAttr_element(vacgrammarParser::Attr_elementContext * ctx) {


}




