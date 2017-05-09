
// Generated from rGURA.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"
#include "rGURABaseListener.h"
#include "rGURAModel.h"

namespace VAC {

/**
 * This class provides an empty implementation of rGURAListener,
 * which can be extended to create a listener which only needs to handle a subset
 * of the available methods.
 */
class  myrGURAListener : public rGURABaseListener {
 public:
  myrGURAListener() { policy = std::make_shared<rGURA>(rGURA());}
  ~myrGURAListener() {}

  rGURAPtr getPolicy(void) const {return policy;}

  virtual void enterR_user(rGURAParser::R_userContext * /*ctx*/) override;
  virtual void enterR_attr_s(rGURAParser::R_attr_sContext * /*ctx*/) override;
  virtual void enterR_attr_m(rGURAParser::R_attr_mContext * /*ctx*/) override;
  virtual void enterR_scope(rGURAParser::R_scopeContext * /*ctx*/) override;
  virtual void enterR_admin(rGURAParser::R_adminContext * /*ctx*/) override;
  virtual void enterUas_element(rGURAParser::Uas_elementContext * /*ctx*/) override;
  virtual void enterUam_element(rGURAParser::Uam_elementContext * /*ctx*/) override;
  virtual void enterAdd_rule(rGURAParser::Add_ruleContext * /*ctx*/) override;
  virtual void enterDelete_rule(rGURAParser::Delete_ruleContext * /*ctx*/) override;
  virtual void enterR_spec(rGURAParser::R_specContext * /*ctx*/) override;

 private:
  PreconditionPtr buildPrecondition(rGURAParser::PreconditionContext * ctx);
  std::string getTokenLocation(antlr4::Token * ) const;
  rGURAPtr policy;

};

}  // namespace VAC
