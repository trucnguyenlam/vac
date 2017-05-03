
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "vacgrammarParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by vacgrammarParser.
 */
class  vacgrammarListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterR_start(vacgrammarParser::R_startContext *ctx) = 0;
  virtual void exitR_start(vacgrammarParser::R_startContext *ctx) = 0;

  virtual void enterR_user(vacgrammarParser::R_userContext *ctx) = 0;
  virtual void exitR_user(vacgrammarParser::R_userContext *ctx) = 0;

  virtual void enterUser_element(vacgrammarParser::User_elementContext *ctx) = 0;
  virtual void exitUser_element(vacgrammarParser::User_elementContext *ctx) = 0;

  virtual void enterR_attr(vacgrammarParser::R_attrContext *ctx) = 0;
  virtual void exitR_attr(vacgrammarParser::R_attrContext *ctx) = 0;

  virtual void enterAttr_element(vacgrammarParser::Attr_elementContext *ctx) = 0;
  virtual void exitAttr_element(vacgrammarParser::Attr_elementContext *ctx) = 0;

  virtual void enterR_init(vacgrammarParser::R_initContext *ctx) = 0;
  virtual void exitR_init(vacgrammarParser::R_initContext *ctx) = 0;

  virtual void enterInit_element(vacgrammarParser::Init_elementContext *ctx) = 0;
  virtual void exitInit_element(vacgrammarParser::Init_elementContext *ctx) = 0;

  virtual void enterInit_assignment(vacgrammarParser::Init_assignmentContext *ctx) = 0;
  virtual void exitInit_assignment(vacgrammarParser::Init_assignmentContext *ctx) = 0;

  virtual void enterPrimaryExpression(vacgrammarParser::PrimaryExpressionContext *ctx) = 0;
  virtual void exitPrimaryExpression(vacgrammarParser::PrimaryExpressionContext *ctx) = 0;

  virtual void enterUnaryExpression(vacgrammarParser::UnaryExpressionContext *ctx) = 0;
  virtual void exitUnaryExpression(vacgrammarParser::UnaryExpressionContext *ctx) = 0;

  virtual void enterEqualityExpression(vacgrammarParser::EqualityExpressionContext *ctx) = 0;
  virtual void exitEqualityExpression(vacgrammarParser::EqualityExpressionContext *ctx) = 0;

  virtual void enterAndExpression(vacgrammarParser::AndExpressionContext *ctx) = 0;
  virtual void exitAndExpression(vacgrammarParser::AndExpressionContext *ctx) = 0;

  virtual void enterOrExpression(vacgrammarParser::OrExpressionContext *ctx) = 0;
  virtual void exitOrExpression(vacgrammarParser::OrExpressionContext *ctx) = 0;

  virtual void enterImplyExpression(vacgrammarParser::ImplyExpressionContext *ctx) = 0;
  virtual void exitImplyExpression(vacgrammarParser::ImplyExpressionContext *ctx) = 0;

  virtual void enterConditionalExpression(vacgrammarParser::ConditionalExpressionContext *ctx) = 0;
  virtual void exitConditionalExpression(vacgrammarParser::ConditionalExpressionContext *ctx) = 0;

  virtual void enterExpression(vacgrammarParser::ExpressionContext *ctx) = 0;
  virtual void exitExpression(vacgrammarParser::ExpressionContext *ctx) = 0;

  virtual void enterR_rules(vacgrammarParser::R_rulesContext *ctx) = 0;
  virtual void exitR_rules(vacgrammarParser::R_rulesContext *ctx) = 0;

  virtual void enterRule_element(vacgrammarParser::Rule_elementContext *ctx) = 0;
  virtual void exitRule_element(vacgrammarParser::Rule_elementContext *ctx) = 0;

  virtual void enterNormal_assignment(vacgrammarParser::Normal_assignmentContext *ctx) = 0;
  virtual void exitNormal_assignment(vacgrammarParser::Normal_assignmentContext *ctx) = 0;

  virtual void enterPrecondition(vacgrammarParser::PreconditionContext *ctx) = 0;
  virtual void exitPrecondition(vacgrammarParser::PreconditionContext *ctx) = 0;

  virtual void enterR_query(vacgrammarParser::R_queryContext *ctx) = 0;
  virtual void exitR_query(vacgrammarParser::R_queryContext *ctx) = 0;


};

