
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"


namespace SMT {


class  vacgrammarParser : public antlr4::Parser {
public:
  enum {
    USER = 1, ATTR = 2, INIT = 3, RULE = 4, QUERY = 5, TRUE = 6, LEFTPAREN = 7, 
    SEMI = 8, STAR = 9, COMMA = 10, DOT = 11, COLON = 12, AND = 13, ANDAND = 14, 
    OR = 15, OROR = 16, EQUAL = 17, IMPLY = 18, QUESTION = 19, RIGHTPAREN = 20, 
    LEFTBRACKET = 21, RIGHTBRACKET = 22, NOT = 23, LEFTTUPLE = 24, RIGHTTUPLE = 25, 
    Identifier = 26, Constant = 27, Whitespace = 28, Newline = 29, BlockComment = 30, 
    LineComment = 31
  };

  enum {
    RuleFile = 0, RuleR_start = 1, RuleR_user = 2, RuleUser_element = 3, 
    RuleR_attr = 4, RuleAttr_element = 5, RuleR_init = 6, RuleInit_element = 7, 
    RuleInit_assignment = 8, RulePrimaryExpression = 9, RuleUnaryExpression = 10, 
    RuleEqualityExpression = 11, RuleAndExpression = 12, RuleOrExpression = 13, 
    RuleImplyExpression = 14, RuleConditionalExpression = 15, RuleExpression = 16, 
    RuleR_rules = 17, RuleRule_element = 18, RuleNormal_assignment = 19, 
    RulePrecondition = 20, RuleR_query = 21
  };

  vacgrammarParser(antlr4::TokenStream *input);
  ~vacgrammarParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class FileContext;
  class R_startContext;
  class R_userContext;
  class User_elementContext;
  class R_attrContext;
  class Attr_elementContext;
  class R_initContext;
  class Init_elementContext;
  class Init_assignmentContext;
  class PrimaryExpressionContext;
  class UnaryExpressionContext;
  class EqualityExpressionContext;
  class AndExpressionContext;
  class OrExpressionContext;
  class ImplyExpressionContext;
  class ConditionalExpressionContext;
  class ExpressionContext;
  class R_rulesContext;
  class Rule_elementContext;
  class Normal_assignmentContext;
  class PreconditionContext;
  class R_queryContext; 

  class  FileContext : public antlr4::ParserRuleContext {
  public:
    FileContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<R_startContext *> r_start();
    R_startContext* r_start(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  FileContext* file();

  class  R_startContext : public antlr4::ParserRuleContext {
  public:
    R_startContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    R_userContext *r_user();
    R_attrContext *r_attr();
    R_initContext *r_init();
    R_rulesContext *r_rules();
    R_queryContext *r_query();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_startContext* r_start();

  class  R_userContext : public antlr4::ParserRuleContext {
  public:
    R_userContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *USER();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<User_elementContext *> user_element();
    User_elementContext* user_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_userContext* r_user();

  class  User_elementContext : public antlr4::ParserRuleContext {
  public:
    User_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *STAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  User_elementContext* user_element();

  class  R_attrContext : public antlr4::ParserRuleContext {
  public:
    R_attrContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ATTR();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Attr_elementContext *> attr_element();
    Attr_elementContext* attr_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_attrContext* r_attr();

  class  Attr_elementContext : public antlr4::ParserRuleContext {
  public:
    Attr_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *LEFTBRACKET();
    antlr4::tree::TerminalNode *Constant();
    antlr4::tree::TerminalNode *RIGHTBRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Attr_elementContext* attr_element();

  class  R_initContext : public antlr4::ParserRuleContext {
  public:
    R_initContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INIT();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Init_elementContext *> init_element();
    Init_elementContext* init_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_initContext* r_init();

  class  Init_elementContext : public antlr4::ParserRuleContext {
  public:
    Init_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Init_assignmentContext *> init_assignment();
    Init_assignmentContext* init_assignment(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Init_elementContext* init_element();

  class  Init_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Init_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Identifier();
    antlr4::tree::TerminalNode *EQUAL();
    antlr4::tree::TerminalNode *Constant();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Init_assignmentContext* init_assignment();

  class  PrimaryExpressionContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *u = nullptr;;
    antlr4::Token *a = nullptr;;
    PrimaryExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Constant();
    antlr4::tree::TerminalNode *DOT();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *LEFTPAREN();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *RIGHTPAREN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PrimaryExpressionContext* primaryExpression();

  class  UnaryExpressionContext : public antlr4::ParserRuleContext {
  public:
    UnaryExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PrimaryExpressionContext *primaryExpression();
    antlr4::tree::TerminalNode *NOT();
    UnaryExpressionContext *unaryExpression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  UnaryExpressionContext* unaryExpression();

  class  EqualityExpressionContext : public antlr4::ParserRuleContext {
  public:
    EqualityExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    UnaryExpressionContext *unaryExpression();
    EqualityExpressionContext *equalityExpression();
    antlr4::tree::TerminalNode *EQUAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EqualityExpressionContext* equalityExpression();
  EqualityExpressionContext* equalityExpression(int precedence);
  class  AndExpressionContext : public antlr4::ParserRuleContext {
  public:
    AndExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    EqualityExpressionContext *equalityExpression();
    AndExpressionContext *andExpression();
    antlr4::tree::TerminalNode *AND();
    antlr4::tree::TerminalNode *ANDAND();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  AndExpressionContext* andExpression();
  AndExpressionContext* andExpression(int precedence);
  class  OrExpressionContext : public antlr4::ParserRuleContext {
  public:
    OrExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    AndExpressionContext *andExpression();
    OrExpressionContext *orExpression();
    antlr4::tree::TerminalNode *OR();
    antlr4::tree::TerminalNode *OROR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  OrExpressionContext* orExpression();
  OrExpressionContext* orExpression(int precedence);
  class  ImplyExpressionContext : public antlr4::ParserRuleContext {
  public:
    ImplyExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    OrExpressionContext *orExpression();
    ImplyExpressionContext *implyExpression();
    antlr4::tree::TerminalNode *IMPLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ImplyExpressionContext* implyExpression();
  ImplyExpressionContext* implyExpression(int precedence);
  class  ConditionalExpressionContext : public antlr4::ParserRuleContext {
  public:
    ConditionalExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ImplyExpressionContext *implyExpression();
    antlr4::tree::TerminalNode *QUESTION();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *COLON();
    ConditionalExpressionContext *conditionalExpression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ConditionalExpressionContext* conditionalExpression();

  class  ExpressionContext : public antlr4::ParserRuleContext {
  public:
    ExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ConditionalExpressionContext *conditionalExpression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ExpressionContext* expression();

  class  R_rulesContext : public antlr4::ParserRuleContext {
  public:
    R_rulesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RULE();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Rule_elementContext *> rule_element();
    Rule_elementContext* rule_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_rulesContext* r_rules();

  class  Rule_elementContext : public antlr4::ParserRuleContext {
  public:
    Rule_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    PreconditionContext *precondition();
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Normal_assignmentContext *> normal_assignment();
    Normal_assignmentContext* normal_assignment(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rule_elementContext* rule_element();

  class  Normal_assignmentContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *u = nullptr;;
    antlr4::Token *a = nullptr;;
    Normal_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *EQUAL();
    antlr4::tree::TerminalNode *Constant();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Normal_assignmentContext* normal_assignment();

  class  PreconditionContext : public antlr4::ParserRuleContext {
  public:
    PreconditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TRUE();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PreconditionContext* precondition();

  class  R_queryContext : public antlr4::ParserRuleContext {
  public:
    R_queryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *QUERY();
    Normal_assignmentContext *normal_assignment();
    antlr4::tree::TerminalNode *SEMI();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_queryContext* r_query();


  virtual bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;
  bool equalityExpressionSempred(EqualityExpressionContext *_localctx, size_t predicateIndex);
  bool andExpressionSempred(AndExpressionContext *_localctx, size_t predicateIndex);
  bool orExpressionSempred(OrExpressionContext *_localctx, size_t predicateIndex);
  bool implyExpressionSempred(ImplyExpressionContext *_localctx, size_t predicateIndex);

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

}  // namespace SMT
