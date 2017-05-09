
// Generated from rGURA.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"


namespace VAC {


class  rGURAParser : public antlr4::Parser {
public:
  enum {
    USER = 1, ATTR_S = 2, ATTR_M = 3, SCOPE = 4, AR = 5, UAS = 6, UAM = 7, 
    RULE = 8, SPEC = 9, TRUE = 10, NOT = 11, LEFTPAREN = 12, SEMI = 13, 
    STAR = 14, COMMA = 15, DOT = 16, COLON = 17, AND = 18, OR = 19, EQUAL = 20, 
    IMPLY = 21, QUESTION = 22, RIGHTPAREN = 23, LEFTBRACKET = 24, RIGHTBRACKET = 25, 
    LEFTTUPLE = 26, RIGHTTUPLE = 27, Identifier = 28, Constant = 29, Whitespace = 30, 
    Newline = 31, BlockComment = 32, LineComment = 33
  };

  enum {
    RuleFile = 0, RuleR_start = 1, RuleR_user = 2, RuleR_attr_s = 3, RuleR_attr_m = 4, 
    RuleR_scope = 5, RuleScope_element = 6, RuleSep = 7, RuleR_admin = 8, 
    RuleR_ua_s = 9, RuleUas_element = 10, RuleAttr_val = 11, RuleR_ua_m = 12, 
    RuleUam_element = 13, RuleR_rules = 14, RuleRule_element = 15, RuleAdd_rule = 16, 
    RuleDelete_rule = 17, RulePrecondition = 18, RuleAtom = 19, RuleR_spec = 20
  };

  rGURAParser(antlr4::TokenStream *input);
  ~rGURAParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class FileContext;
  class R_startContext;
  class R_userContext;
  class R_attr_sContext;
  class R_attr_mContext;
  class R_scopeContext;
  class Scope_elementContext;
  class SepContext;
  class R_adminContext;
  class R_ua_sContext;
  class Uas_elementContext;
  class Attr_valContext;
  class R_ua_mContext;
  class Uam_elementContext;
  class R_rulesContext;
  class Rule_elementContext;
  class Add_ruleContext;
  class Delete_ruleContext;
  class PreconditionContext;
  class AtomContext;
  class R_specContext; 

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
    R_attr_sContext *r_attr_s();
    R_attr_mContext *r_attr_m();
    R_scopeContext *r_scope();
    R_adminContext *r_admin();
    R_ua_sContext *r_ua_s();
    R_ua_mContext *r_ua_m();
    R_rulesContext *r_rules();
    R_specContext *r_spec();

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
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_userContext* r_user();

  class  R_attr_sContext : public antlr4::ParserRuleContext {
  public:
    R_attr_sContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ATTR_S();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_attr_sContext* r_attr_s();

  class  R_attr_mContext : public antlr4::ParserRuleContext {
  public:
    R_attr_mContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ATTR_M();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_attr_mContext* r_attr_m();

  class  R_scopeContext : public antlr4::ParserRuleContext {
  public:
    R_scopeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SCOPE();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Scope_elementContext *> scope_element();
    Scope_elementContext* scope_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_scopeContext* r_scope();

  class  Scope_elementContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *v = nullptr;;
    Scope_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    SepContext *sep();
    antlr4::tree::TerminalNode *RIGHTTUPLE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Scope_elementContext* scope_element();

  class  SepContext : public antlr4::ParserRuleContext {
  public:
    SepContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *COLON();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  SepContext* sep();

  class  R_adminContext : public antlr4::ParserRuleContext {
  public:
    R_adminContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *AR();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_adminContext* r_admin();

  class  R_ua_sContext : public antlr4::ParserRuleContext {
  public:
    R_ua_sContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UAS();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Uas_elementContext *> uas_element();
    Uas_elementContext* uas_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_ua_sContext* r_ua_s();

  class  Uas_elementContext : public antlr4::ParserRuleContext {
  public:
    Uas_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Identifier();
    std::vector<Attr_valContext *> attr_val();
    Attr_valContext* attr_val(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Uas_elementContext* uas_element();

  class  Attr_valContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *a = nullptr;;
    antlr4::Token *v = nullptr;;
    Attr_valContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Attr_valContext* attr_val();

  class  R_ua_mContext : public antlr4::ParserRuleContext {
  public:
    R_ua_mContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UAM();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<Uam_elementContext *> uam_element();
    Uam_elementContext* uam_element(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_ua_mContext* r_ua_m();

  class  Uam_elementContext : public antlr4::ParserRuleContext {
  public:
    Uam_elementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *LEFTTUPLE();
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Uam_elementContext* uam_element();

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
    Add_ruleContext *add_rule();
    Delete_ruleContext *delete_rule();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rule_elementContext* rule_element();

  class  Add_ruleContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *admin = nullptr;;
    antlr4::Token *attr = nullptr;;
    antlr4::Token *value = nullptr;;
    Add_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    PreconditionContext *precondition();
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Add_ruleContext* add_rule();

  class  Delete_ruleContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *admin = nullptr;;
    antlr4::Token *attr = nullptr;;
    antlr4::Token *value = nullptr;;
    Delete_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LEFTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *RIGHTTUPLE();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delete_ruleContext* delete_rule();

  class  PreconditionContext : public antlr4::ParserRuleContext {
  public:
    PreconditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TRUE();
    std::vector<AtomContext *> atom();
    AtomContext* atom(size_t i);
    std::vector<antlr4::tree::TerminalNode *> AND();
    antlr4::tree::TerminalNode* AND(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PreconditionContext* precondition();

  class  AtomContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *attr = nullptr;;
    antlr4::Token *value = nullptr;;
    AtomContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EQUAL();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);
    antlr4::tree::TerminalNode *NOT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  AtomContext* atom();

  class  R_specContext : public antlr4::ParserRuleContext {
  public:
    antlr4::Token *attr = nullptr;;
    antlr4::Token *value = nullptr;;
    R_specContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SPEC();
    antlr4::tree::TerminalNode *SEMI();
    std::vector<antlr4::tree::TerminalNode *> Identifier();
    antlr4::tree::TerminalNode* Identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  R_specContext* r_spec();


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

}  // namespace VAC
