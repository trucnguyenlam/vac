
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "vacgrammarBaseListener.h"
#include "Models.h"


namespace Parser {

/**
 * This class provides an empty implementation of vacgrammarListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  MyListener : public vacgrammarBaseListener {
 public:
  MyListener(){ vac_model = std::make_shared<Model>(Model());}
  ~MyListener() {}

  virtual void enterFile(vacgrammarParser::FileContext * /*ctx*/) override;
  virtual void exitFile(vacgrammarParser::FileContext * /*ctx*/) override;

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

  virtual void enterRule_element(vacgrammarParser::Rule_elementContext * /*ctx*/) override;
  virtual void exitRule_element(vacgrammarParser::Rule_elementContext * /*ctx*/) override;

  virtual void enterR_query(vacgrammarParser::R_queryContext * /*ctx*/) override;
  virtual void exitR_query(vacgrammarParser::R_queryContext * /*ctx*/) override;


  ModelPtr getPolicy(void) const;

 private:

  Expr buildPrimaryExpression(vacgrammarParser::PrimaryExpressionContext *, std::map<std::string, int> &) const;
  Expr buildUnaryExpression(vacgrammarParser::UnaryExpressionContext *, std::map<std::string, int> &) const;
  Expr buildEqualityExpression(vacgrammarParser::EqualityExpressionContext *, std::map<std::string, int> &) const;
  Expr buildAndExpression(vacgrammarParser::AndExpressionContext *, std::map<std::string, int> &) const;
  Expr buildOrExpression(vacgrammarParser::OrExpressionContext *, std::map<std::string, int> &) const;
  Expr buildImplyExpression(vacgrammarParser::ImplyExpressionContext *, std::map<std::string, int> &) const;
  Expr buildConditionalExpression(vacgrammarParser::ConditionalExpressionContext *, std::map<std::string, int> &) const;
  Expr buildExpression(vacgrammarParser::ExpressionContext *, std::map<std::string, int> &) const;
  Expr buildPrecondition(vacgrammarParser::PreconditionContext *, std::map<std::string, int> &) const;

  // attibute
  ModelPtr vac_model;

};

}  // namespace Parser
