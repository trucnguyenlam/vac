
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "Models.h"
#include "vacgrammarBaseListener.h"


namespace SMT {

/**
 * This class provides an empty implementation of vacgrammarListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  MyListener : public vacgrammarBaseListener {
 public:
  MyListener(){ vac_model = std::make_shared<Model>(Model());}
  ~MyListener() {}

  virtual void enterR_user(vacgrammarParser::R_userContext * /*ctx*/) override;
  virtual void exitR_user(vacgrammarParser::R_userContext * /*ctx*/) override;

  virtual void enterUser_element(vacgrammarParser::User_elementContext * /*ctx*/) override;
  virtual void exitUser_element(vacgrammarParser::User_elementContext * /*ctx*/) override;

  virtual void enterR_attr(vacgrammarParser::R_attrContext * /*ctx*/) override;
  virtual void exitR_attr(vacgrammarParser::R_attrContext * /*ctx*/) override;

  virtual void enterAttr_element(vacgrammarParser::Attr_elementContext * /*ctx*/) override;
  virtual void exitAttr_element(vacgrammarParser::Attr_elementContext * /*ctx*/) override;

  virtual void enterR_init(vacgrammarParser::R_initContext * /*ctx*/) override;
  virtual void exitR_init(vacgrammarParser::R_initContext * /*ctx*/) override;

  virtual void enterInit_element(vacgrammarParser::Init_elementContext * /*ctx*/) override;
  virtual void exitInit_element(vacgrammarParser::Init_elementContext * /*ctx*/) override;

  virtual void enterInit_assignment(vacgrammarParser::Init_assignmentContext * /*ctx*/) override;
  virtual void exitInit_assignment(vacgrammarParser::Init_assignmentContext * /*ctx*/) override;


 private:
  ModelPtr vac_model;

};

}  // namespace SMT
