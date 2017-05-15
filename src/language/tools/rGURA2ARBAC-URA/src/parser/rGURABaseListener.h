
// Generated from rGURA.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "rGURAListener.h"


namespace VAC {

/**
 * This class provides an empty implementation of rGURAListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  rGURABaseListener : public rGURAListener {
public:

  virtual void enterFile(rGURAParser::FileContext * /*ctx*/) override { }
  virtual void exitFile(rGURAParser::FileContext * /*ctx*/) override { }

  virtual void enterR_start(rGURAParser::R_startContext * /*ctx*/) override { }
  virtual void exitR_start(rGURAParser::R_startContext * /*ctx*/) override { }

  virtual void enterR_user(rGURAParser::R_userContext * /*ctx*/) override { }
  virtual void exitR_user(rGURAParser::R_userContext * /*ctx*/) override { }

  virtual void enterR_attr_s(rGURAParser::R_attr_sContext * /*ctx*/) override { }
  virtual void exitR_attr_s(rGURAParser::R_attr_sContext * /*ctx*/) override { }

  virtual void enterR_attr_m(rGURAParser::R_attr_mContext * /*ctx*/) override { }
  virtual void exitR_attr_m(rGURAParser::R_attr_mContext * /*ctx*/) override { }

  virtual void enterR_scope(rGURAParser::R_scopeContext * /*ctx*/) override { }
  virtual void exitR_scope(rGURAParser::R_scopeContext * /*ctx*/) override { }

  virtual void enterScope_element(rGURAParser::Scope_elementContext * /*ctx*/) override { }
  virtual void exitScope_element(rGURAParser::Scope_elementContext * /*ctx*/) override { }

  virtual void enterSep(rGURAParser::SepContext * /*ctx*/) override { }
  virtual void exitSep(rGURAParser::SepContext * /*ctx*/) override { }

  virtual void enterR_admin(rGURAParser::R_adminContext * /*ctx*/) override { }
  virtual void exitR_admin(rGURAParser::R_adminContext * /*ctx*/) override { }

  virtual void enterR_ua_s(rGURAParser::R_ua_sContext * /*ctx*/) override { }
  virtual void exitR_ua_s(rGURAParser::R_ua_sContext * /*ctx*/) override { }

  virtual void enterUas_element(rGURAParser::Uas_elementContext * /*ctx*/) override { }
  virtual void exitUas_element(rGURAParser::Uas_elementContext * /*ctx*/) override { }

  virtual void enterAttr_val(rGURAParser::Attr_valContext * /*ctx*/) override { }
  virtual void exitAttr_val(rGURAParser::Attr_valContext * /*ctx*/) override { }

  virtual void enterR_ua_m(rGURAParser::R_ua_mContext * /*ctx*/) override { }
  virtual void exitR_ua_m(rGURAParser::R_ua_mContext * /*ctx*/) override { }

  virtual void enterUam_element(rGURAParser::Uam_elementContext * /*ctx*/) override { }
  virtual void exitUam_element(rGURAParser::Uam_elementContext * /*ctx*/) override { }

  virtual void enterAttr_mval(rGURAParser::Attr_mvalContext * /*ctx*/) override { }
  virtual void exitAttr_mval(rGURAParser::Attr_mvalContext * /*ctx*/) override { }

  virtual void enterR_rules(rGURAParser::R_rulesContext * /*ctx*/) override { }
  virtual void exitR_rules(rGURAParser::R_rulesContext * /*ctx*/) override { }

  virtual void enterRule_element(rGURAParser::Rule_elementContext * /*ctx*/) override { }
  virtual void exitRule_element(rGURAParser::Rule_elementContext * /*ctx*/) override { }

  virtual void enterAdd_rule(rGURAParser::Add_ruleContext * /*ctx*/) override { }
  virtual void exitAdd_rule(rGURAParser::Add_ruleContext * /*ctx*/) override { }

  virtual void enterDelete_rule(rGURAParser::Delete_ruleContext * /*ctx*/) override { }
  virtual void exitDelete_rule(rGURAParser::Delete_ruleContext * /*ctx*/) override { }

  virtual void enterPrecondition(rGURAParser::PreconditionContext * /*ctx*/) override { }
  virtual void exitPrecondition(rGURAParser::PreconditionContext * /*ctx*/) override { }

  virtual void enterAtom(rGURAParser::AtomContext * /*ctx*/) override { }
  virtual void exitAtom(rGURAParser::AtomContext * /*ctx*/) override { }

  virtual void enterR_spec(rGURAParser::R_specContext * /*ctx*/) override { }
  virtual void exitR_spec(rGURAParser::R_specContext * /*ctx*/) override { }


  virtual void enterEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void exitEveryRule(antlr4::ParserRuleContext * /*ctx*/) override { }
  virtual void visitTerminal(antlr4::tree::TerminalNode * /*node*/) override { }
  virtual void visitErrorNode(antlr4::tree::ErrorNode * /*node*/) override { }

};

}  // namespace VAC
