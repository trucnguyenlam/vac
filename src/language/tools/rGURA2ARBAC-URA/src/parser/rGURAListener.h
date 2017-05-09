
// Generated from rGURA.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "rGURAParser.h"


namespace VAC {

/**
 * This interface defines an abstract listener for a parse tree produced by rGURAParser.
 */
class  rGURAListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterFile(rGURAParser::FileContext *ctx) = 0;
  virtual void exitFile(rGURAParser::FileContext *ctx) = 0;

  virtual void enterR_start(rGURAParser::R_startContext *ctx) = 0;
  virtual void exitR_start(rGURAParser::R_startContext *ctx) = 0;

  virtual void enterR_user(rGURAParser::R_userContext *ctx) = 0;
  virtual void exitR_user(rGURAParser::R_userContext *ctx) = 0;

  virtual void enterR_attr_s(rGURAParser::R_attr_sContext *ctx) = 0;
  virtual void exitR_attr_s(rGURAParser::R_attr_sContext *ctx) = 0;

  virtual void enterR_attr_m(rGURAParser::R_attr_mContext *ctx) = 0;
  virtual void exitR_attr_m(rGURAParser::R_attr_mContext *ctx) = 0;

  virtual void enterR_scope(rGURAParser::R_scopeContext *ctx) = 0;
  virtual void exitR_scope(rGURAParser::R_scopeContext *ctx) = 0;

  virtual void enterScope_element(rGURAParser::Scope_elementContext *ctx) = 0;
  virtual void exitScope_element(rGURAParser::Scope_elementContext *ctx) = 0;

  virtual void enterSep(rGURAParser::SepContext *ctx) = 0;
  virtual void exitSep(rGURAParser::SepContext *ctx) = 0;

  virtual void enterR_admin(rGURAParser::R_adminContext *ctx) = 0;
  virtual void exitR_admin(rGURAParser::R_adminContext *ctx) = 0;

  virtual void enterR_ua_s(rGURAParser::R_ua_sContext *ctx) = 0;
  virtual void exitR_ua_s(rGURAParser::R_ua_sContext *ctx) = 0;

  virtual void enterUas_element(rGURAParser::Uas_elementContext *ctx) = 0;
  virtual void exitUas_element(rGURAParser::Uas_elementContext *ctx) = 0;

  virtual void enterAttr_val(rGURAParser::Attr_valContext *ctx) = 0;
  virtual void exitAttr_val(rGURAParser::Attr_valContext *ctx) = 0;

  virtual void enterR_ua_m(rGURAParser::R_ua_mContext *ctx) = 0;
  virtual void exitR_ua_m(rGURAParser::R_ua_mContext *ctx) = 0;

  virtual void enterUam_element(rGURAParser::Uam_elementContext *ctx) = 0;
  virtual void exitUam_element(rGURAParser::Uam_elementContext *ctx) = 0;

  virtual void enterR_rules(rGURAParser::R_rulesContext *ctx) = 0;
  virtual void exitR_rules(rGURAParser::R_rulesContext *ctx) = 0;

  virtual void enterRule_element(rGURAParser::Rule_elementContext *ctx) = 0;
  virtual void exitRule_element(rGURAParser::Rule_elementContext *ctx) = 0;

  virtual void enterAdd_rule(rGURAParser::Add_ruleContext *ctx) = 0;
  virtual void exitAdd_rule(rGURAParser::Add_ruleContext *ctx) = 0;

  virtual void enterDelete_rule(rGURAParser::Delete_ruleContext *ctx) = 0;
  virtual void exitDelete_rule(rGURAParser::Delete_ruleContext *ctx) = 0;

  virtual void enterPrecondition(rGURAParser::PreconditionContext *ctx) = 0;
  virtual void exitPrecondition(rGURAParser::PreconditionContext *ctx) = 0;

  virtual void enterAtom(rGURAParser::AtomContext *ctx) = 0;
  virtual void exitAtom(rGURAParser::AtomContext *ctx) = 0;

  virtual void enterR_spec(rGURAParser::R_specContext *ctx) = 0;
  virtual void exitR_spec(rGURAParser::R_specContext *ctx) = 0;


};

}  // namespace VAC
