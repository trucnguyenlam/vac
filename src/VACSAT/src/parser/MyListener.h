
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "vacgrammarBaseListener.h"
#include "Models.h"


namespace Parser {

class TranslatorException: public antlr4::RuntimeException {
 public:
  TranslatorException(const std::string &msg = "") : RuntimeException(msg) {};
};

class ParserException: public antlr4::RuntimeException {
 public:
  ParserException(const std::string &msg = "") : RuntimeException(msg) {};
};

/**
 * This class provides an empty implementation of vacgrammarListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  MyListener : public vacgrammarBaseListener {
 public:
  MyListener() { vac_model = std::make_shared<Model>(Model());}
  ~MyListener() {}

  virtual void enterUser_element(vacgrammarParser::User_elementContext * /*ctx*/) override;
  virtual void enterAttr_element(vacgrammarParser::Attr_elementContext * /*ctx*/) override;
  virtual void enterInit_element(vacgrammarParser::Init_elementContext * /*ctx*/) override;
  virtual void enterRule_element(vacgrammarParser::Rule_elementContext * /*ctx*/) override;
  virtual void enterR_query(vacgrammarParser::R_queryContext * /*ctx*/) override;
  ModelPtr getPolicy(void) const;

 private:
  Expr buildPrimaryExpression(vacgrammarParser::PrimaryExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildUnaryExpression(vacgrammarParser::UnaryExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildEqualityExpression(vacgrammarParser::EqualityExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildAndExpression(vacgrammarParser::AndExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildOrExpression(vacgrammarParser::OrExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildImplyExpression(vacgrammarParser::ImplyExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildConditionalExpression(vacgrammarParser::ConditionalExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildExpression(vacgrammarParser::ExpressionContext *, std::map<std::string, int> &, int &) const;
  Expr buildPrecondition(vacgrammarParser::PreconditionContext *, std::map<std::string, int> &, int &) const;
  Expr buildAdmincondition(vacgrammarParser::AdminconditionContext *, std::map<std::string, int> &, int &) const;

  std::string getTokenLocation(antlr4::Token * ) const;

  // attibute
  ModelPtr vac_model;

};

}  // namespace Parser
