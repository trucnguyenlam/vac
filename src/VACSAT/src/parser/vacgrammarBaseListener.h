
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "vacgrammarListener.h"


namespace Parser {

/**
 * This class provides an empty implementation of vacgrammarListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  vacgrammarBaseListener : public vacgrammarListener {
public:

  virtual void enterFile(vacgrammarParser::FileContext * /*ctx*/) override { }
  virtual void exitFile(vacgrammarParser::FileContext * /*ctx*/) override { }

  virtual void enterR_start(vacgrammarParser::R_startContext * /*ctx*/) override { }
  virtual void exitR_start(vacgrammarParser::R_startContext * /*ctx*/) override { }

  virtual void enterR_user(vacgrammarParser::R_userContext * /*ctx*/) override { }
  virtual void exitR_user(vacgrammarParser::R_userContext * /*ctx*/) override { }

  virtual void enterUser_element(vacgrammarParser::User_elementContext * /*ctx*/) override { }
  virtual void exitUser_element(vacgrammarParser::User_elementContext * /*ctx*/) override { }

  virtual void enterR_attr(vacgrammarParser::R_attrContext * /*ctx*/) override { }
  virtual void exitR_attr(vacgrammarParser::R_attrContext * /*ctx*/) override { }

  virtual void enterAttr_element(vacgrammarParser::Attr_elementContext * /*ctx*/) override { }
  virtual void exitAttr_element(vacgrammarParser::Attr_elementContext * /*ctx*/) override { }

  virtual void enterR_init(vacgrammarParser::R_initContext * /*ctx*/) override { }
  virtual void exitR_init(vacgrammarParser::R_initContext * /*ctx*/) override { }

  virtual void enterInit_element(vacgrammarParser::Init_elementContext * /*ctx*/) override { }
  virtual void exitInit_element(vacgrammarParser::Init_elementContext * /*ctx*/) override { }

  virtual void enterInit_assignment(vacgrammarParser::Init_assignmentContext * /*ctx*/) override { }
  virtual void exitInit_assignment(vacgrammarParser::Init_assignmentContext * /*ctx*/) override { }

  virtual void enterPrimaryExpression(vacgrammarParser::PrimaryExpressionContext * /*ctx*/) override { }
  virtual void exitPrimaryExpression(vacgrammarParser::PrimaryExpressionContext * /*ctx*/) override { }

  virtual void enterUnaryExpression(vacgrammarParser::UnaryExpressionContext * /*ctx*/) override { }
  virtual void exitUnaryExpression(vacgrammarParser::UnaryExpressionContext * /*ctx*/) override { }

  virtual void enterEqualityExpression(vacgrammarParser::EqualityExpressionContext * /*ctx*/) override { }
  virtual void exitEqualityExpression(vacgrammarParser::EqualityExpressionContext * /*ctx*/) override { }

  virtual void enterAndExpression(vacgrammarParser::AndExpressionContext * /*ctx*/) override { }
  virtual void exitAndExpression(vacgrammarParser::AndExpressionContext * /*ctx*/) override { }

  virtual void enterOrExpression(vacgrammarParser::OrExpressionContext * /*ctx*/) override { }
  virtual void exitOrExpression(vacgrammarParser::OrExpressionContext * /*ctx*/) override { }

  virtual void enterImplyExpression(vacgrammarParser::ImplyExpressionContext * /*ctx*/) override { }
  virtual void exitImplyExpression(vacgrammarParser::ImplyExpressionContext * /*ctx*/) override { }

  virtual void enterConditionalExpression(vacgrammarParser::ConditionalExpressionContext * /*ctx*/) override { }
  virtual void exitConditionalExpression(vacgrammarParser::ConditionalExpressionContext * /*ctx*/) override { }

  virtual void enterExpression(vacgrammarParser::ExpressionContext * /*ctx*/) override { }
  virtual void exitExpression(vacgrammarParser::ExpressionContext * /*ctx*/) override { }

  virtual void enterR_rules(vacgrammarParser::R_rulesContext * /*ctx*/) override { }
  virtual void exitR_rules(vacgrammarParser::R_rulesContext * /*ctx*/) override { }

  virtual void enterRule_element(vacgrammarParser::Rule_elementContext * /*ctx*/) override { }
  virtual void exitRule_element(vacgrammarParser::Rule_elementContext * /*ctx*/) override { }

  virtual void enterNormal_assignment(vacgrammarParser::Normal_assignmentContext * /*ctx*/) override { }
  virtual void exitNormal_assignment(vacgrammarParser::Normal_assignmentContext * /*ctx*/) override { }

  virtual void enterPrecondition(vacgrammarParser::PreconditionContext * /*ctx*/) override { }
  virtual void exitPrecondition(vacgrammarParser::PreconditionContext * /*ctx*/) override { }

  virtual void enterAdmincondition(vacgrammarParser::AdminconditionContext * /*ctx*/) override { }
  virtual void exitAdmincondition(vacgrammarParser::AdminconditionContext * /*ctx*/) override { }

  virtual void enterR_query(vacgrammarParser::R_queryContext * /*ctx*/) override { }
  virtual void exitR_query(vacgrammarParser::R_queryContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

}  // namespace Parser
