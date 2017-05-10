
// Generated from rGURA.g4 by ANTLR 4.7


#include "rGURAListener.h"

#include "rGURAParser.h"


using namespace antlrcpp;
using namespace VAC;
using namespace antlr4;

rGURAParser::rGURAParser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

rGURAParser::~rGURAParser() {
  delete _interpreter;
}

std::string rGURAParser::getGrammarFileName() const {
  return "rGURA.g4";
}

const std::vector<std::string>& rGURAParser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& rGURAParser::getVocabulary() const {
  return _vocabulary;
}


//----------------- FileContext ------------------------------------------------------------------

rGURAParser::FileContext::FileContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<rGURAParser::R_startContext *> rGURAParser::FileContext::r_start() {
  return getRuleContexts<rGURAParser::R_startContext>();
}

rGURAParser::R_startContext* rGURAParser::FileContext::r_start(size_t i) {
  return getRuleContext<rGURAParser::R_startContext>(i);
}


size_t rGURAParser::FileContext::getRuleIndex() const {
  return rGURAParser::RuleFile;
}

void rGURAParser::FileContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterFile(this);
}

void rGURAParser::FileContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitFile(this);
}

rGURAParser::FileContext* rGURAParser::file() {
  FileContext *_localctx = _tracker.createInstance<FileContext>(_ctx, getState());
  enterRule(_localctx, 0, rGURAParser::RuleFile);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(43); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(42);
      r_start();
      setState(45); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << rGURAParser::USER)
      | (1ULL << rGURAParser::ATTR_S)
      | (1ULL << rGURAParser::ATTR_M)
      | (1ULL << rGURAParser::SCOPE)
      | (1ULL << rGURAParser::AR)
      | (1ULL << rGURAParser::UAS)
      | (1ULL << rGURAParser::UAM)
      | (1ULL << rGURAParser::RULE)
      | (1ULL << rGURAParser::SPEC))) != 0));
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_startContext ------------------------------------------------------------------

rGURAParser::R_startContext::R_startContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

rGURAParser::R_userContext* rGURAParser::R_startContext::r_user() {
  return getRuleContext<rGURAParser::R_userContext>(0);
}

rGURAParser::R_attr_sContext* rGURAParser::R_startContext::r_attr_s() {
  return getRuleContext<rGURAParser::R_attr_sContext>(0);
}

rGURAParser::R_attr_mContext* rGURAParser::R_startContext::r_attr_m() {
  return getRuleContext<rGURAParser::R_attr_mContext>(0);
}

rGURAParser::R_scopeContext* rGURAParser::R_startContext::r_scope() {
  return getRuleContext<rGURAParser::R_scopeContext>(0);
}

rGURAParser::R_adminContext* rGURAParser::R_startContext::r_admin() {
  return getRuleContext<rGURAParser::R_adminContext>(0);
}

rGURAParser::R_ua_sContext* rGURAParser::R_startContext::r_ua_s() {
  return getRuleContext<rGURAParser::R_ua_sContext>(0);
}

rGURAParser::R_ua_mContext* rGURAParser::R_startContext::r_ua_m() {
  return getRuleContext<rGURAParser::R_ua_mContext>(0);
}

rGURAParser::R_rulesContext* rGURAParser::R_startContext::r_rules() {
  return getRuleContext<rGURAParser::R_rulesContext>(0);
}

rGURAParser::R_specContext* rGURAParser::R_startContext::r_spec() {
  return getRuleContext<rGURAParser::R_specContext>(0);
}


size_t rGURAParser::R_startContext::getRuleIndex() const {
  return rGURAParser::RuleR_start;
}

void rGURAParser::R_startContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_start(this);
}

void rGURAParser::R_startContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_start(this);
}

rGURAParser::R_startContext* rGURAParser::r_start() {
  R_startContext *_localctx = _tracker.createInstance<R_startContext>(_ctx, getState());
  enterRule(_localctx, 2, rGURAParser::RuleR_start);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(56);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case rGURAParser::USER: {
        enterOuterAlt(_localctx, 1);
        setState(47);
        r_user();
        break;
      }

      case rGURAParser::ATTR_S: {
        enterOuterAlt(_localctx, 2);
        setState(48);
        r_attr_s();
        break;
      }

      case rGURAParser::ATTR_M: {
        enterOuterAlt(_localctx, 3);
        setState(49);
        r_attr_m();
        break;
      }

      case rGURAParser::SCOPE: {
        enterOuterAlt(_localctx, 4);
        setState(50);
        r_scope();
        break;
      }

      case rGURAParser::AR: {
        enterOuterAlt(_localctx, 5);
        setState(51);
        r_admin();
        break;
      }

      case rGURAParser::UAS: {
        enterOuterAlt(_localctx, 6);
        setState(52);
        r_ua_s();
        break;
      }

      case rGURAParser::UAM: {
        enterOuterAlt(_localctx, 7);
        setState(53);
        r_ua_m();
        break;
      }

      case rGURAParser::RULE: {
        enterOuterAlt(_localctx, 8);
        setState(54);
        r_rules();
        break;
      }

      case rGURAParser::SPEC: {
        enterOuterAlt(_localctx, 9);
        setState(55);
        r_spec();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_userContext ------------------------------------------------------------------

rGURAParser::R_userContext::R_userContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_userContext::USER() {
  return getToken(rGURAParser::USER, 0);
}

tree::TerminalNode* rGURAParser::R_userContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::R_userContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::R_userContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::R_userContext::getRuleIndex() const {
  return rGURAParser::RuleR_user;
}

void rGURAParser::R_userContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_user(this);
}

void rGURAParser::R_userContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_user(this);
}

rGURAParser::R_userContext* rGURAParser::r_user() {
  R_userContext *_localctx = _tracker.createInstance<R_userContext>(_ctx, getState());
  enterRule(_localctx, 4, rGURAParser::RuleR_user);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(58);
    match(rGURAParser::USER);
    setState(62);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(59);
      match(rGURAParser::Identifier);
      setState(64);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(65);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_attr_sContext ------------------------------------------------------------------

rGURAParser::R_attr_sContext::R_attr_sContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_attr_sContext::ATTR_S() {
  return getToken(rGURAParser::ATTR_S, 0);
}

tree::TerminalNode* rGURAParser::R_attr_sContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::R_attr_sContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::R_attr_sContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::R_attr_sContext::getRuleIndex() const {
  return rGURAParser::RuleR_attr_s;
}

void rGURAParser::R_attr_sContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_attr_s(this);
}

void rGURAParser::R_attr_sContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_attr_s(this);
}

rGURAParser::R_attr_sContext* rGURAParser::r_attr_s() {
  R_attr_sContext *_localctx = _tracker.createInstance<R_attr_sContext>(_ctx, getState());
  enterRule(_localctx, 6, rGURAParser::RuleR_attr_s);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(67);
    match(rGURAParser::ATTR_S);
    setState(71);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(68);
      match(rGURAParser::Identifier);
      setState(73);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(74);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_attr_mContext ------------------------------------------------------------------

rGURAParser::R_attr_mContext::R_attr_mContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_attr_mContext::ATTR_M() {
  return getToken(rGURAParser::ATTR_M, 0);
}

tree::TerminalNode* rGURAParser::R_attr_mContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::R_attr_mContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::R_attr_mContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::R_attr_mContext::getRuleIndex() const {
  return rGURAParser::RuleR_attr_m;
}

void rGURAParser::R_attr_mContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_attr_m(this);
}

void rGURAParser::R_attr_mContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_attr_m(this);
}

rGURAParser::R_attr_mContext* rGURAParser::r_attr_m() {
  R_attr_mContext *_localctx = _tracker.createInstance<R_attr_mContext>(_ctx, getState());
  enterRule(_localctx, 8, rGURAParser::RuleR_attr_m);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(76);
    match(rGURAParser::ATTR_M);
    setState(80);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(77);
      match(rGURAParser::Identifier);
      setState(82);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(83);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_scopeContext ------------------------------------------------------------------

rGURAParser::R_scopeContext::R_scopeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_scopeContext::SCOPE() {
  return getToken(rGURAParser::SCOPE, 0);
}

tree::TerminalNode* rGURAParser::R_scopeContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<rGURAParser::Scope_elementContext *> rGURAParser::R_scopeContext::scope_element() {
  return getRuleContexts<rGURAParser::Scope_elementContext>();
}

rGURAParser::Scope_elementContext* rGURAParser::R_scopeContext::scope_element(size_t i) {
  return getRuleContext<rGURAParser::Scope_elementContext>(i);
}


size_t rGURAParser::R_scopeContext::getRuleIndex() const {
  return rGURAParser::RuleR_scope;
}

void rGURAParser::R_scopeContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_scope(this);
}

void rGURAParser::R_scopeContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_scope(this);
}

rGURAParser::R_scopeContext* rGURAParser::r_scope() {
  R_scopeContext *_localctx = _tracker.createInstance<R_scopeContext>(_ctx, getState());
  enterRule(_localctx, 10, rGURAParser::RuleR_scope);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(85);
    match(rGURAParser::SCOPE);
    setState(89);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::LEFTTUPLE) {
      setState(86);
      scope_element();
      setState(91);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(92);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Scope_elementContext ------------------------------------------------------------------

rGURAParser::Scope_elementContext::Scope_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::Scope_elementContext::LEFTTUPLE() {
  return getToken(rGURAParser::LEFTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Scope_elementContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::Scope_elementContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}

rGURAParser::SepContext* rGURAParser::Scope_elementContext::sep() {
  return getRuleContext<rGURAParser::SepContext>(0);
}

tree::TerminalNode* rGURAParser::Scope_elementContext::RIGHTTUPLE() {
  return getToken(rGURAParser::RIGHTTUPLE, 0);
}


size_t rGURAParser::Scope_elementContext::getRuleIndex() const {
  return rGURAParser::RuleScope_element;
}

void rGURAParser::Scope_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterScope_element(this);
}

void rGURAParser::Scope_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitScope_element(this);
}

rGURAParser::Scope_elementContext* rGURAParser::scope_element() {
  Scope_elementContext *_localctx = _tracker.createInstance<Scope_elementContext>(_ctx, getState());
  enterRule(_localctx, 12, rGURAParser::RuleScope_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(94);
    match(rGURAParser::LEFTTUPLE);
    setState(95);
    match(rGURAParser::Identifier);
    setState(96);
    sep();
    setState(98); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(97);
      match(rGURAParser::Identifier);
      setState(100); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == rGURAParser::Identifier);
    setState(102);
    match(rGURAParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- SepContext ------------------------------------------------------------------

rGURAParser::SepContext::SepContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::SepContext::COMMA() {
  return getToken(rGURAParser::COMMA, 0);
}

tree::TerminalNode* rGURAParser::SepContext::COLON() {
  return getToken(rGURAParser::COLON, 0);
}


size_t rGURAParser::SepContext::getRuleIndex() const {
  return rGURAParser::RuleSep;
}

void rGURAParser::SepContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterSep(this);
}

void rGURAParser::SepContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitSep(this);
}

rGURAParser::SepContext* rGURAParser::sep() {
  SepContext *_localctx = _tracker.createInstance<SepContext>(_ctx, getState());
  enterRule(_localctx, 14, rGURAParser::RuleSep);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(104);
    _la = _input->LA(1);
    if (!(_la == rGURAParser::COMMA

    || _la == rGURAParser::COLON)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_adminContext ------------------------------------------------------------------

rGURAParser::R_adminContext::R_adminContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_adminContext::AR() {
  return getToken(rGURAParser::AR, 0);
}

tree::TerminalNode* rGURAParser::R_adminContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::R_adminContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::R_adminContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::R_adminContext::getRuleIndex() const {
  return rGURAParser::RuleR_admin;
}

void rGURAParser::R_adminContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_admin(this);
}

void rGURAParser::R_adminContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_admin(this);
}

rGURAParser::R_adminContext* rGURAParser::r_admin() {
  R_adminContext *_localctx = _tracker.createInstance<R_adminContext>(_ctx, getState());
  enterRule(_localctx, 16, rGURAParser::RuleR_admin);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(106);
    match(rGURAParser::AR);
    setState(110);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(107);
      match(rGURAParser::Identifier);
      setState(112);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(113);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_ua_sContext ------------------------------------------------------------------

rGURAParser::R_ua_sContext::R_ua_sContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_ua_sContext::UAS() {
  return getToken(rGURAParser::UAS, 0);
}

tree::TerminalNode* rGURAParser::R_ua_sContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<rGURAParser::Uas_elementContext *> rGURAParser::R_ua_sContext::uas_element() {
  return getRuleContexts<rGURAParser::Uas_elementContext>();
}

rGURAParser::Uas_elementContext* rGURAParser::R_ua_sContext::uas_element(size_t i) {
  return getRuleContext<rGURAParser::Uas_elementContext>(i);
}


size_t rGURAParser::R_ua_sContext::getRuleIndex() const {
  return rGURAParser::RuleR_ua_s;
}

void rGURAParser::R_ua_sContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_ua_s(this);
}

void rGURAParser::R_ua_sContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_ua_s(this);
}

rGURAParser::R_ua_sContext* rGURAParser::r_ua_s() {
  R_ua_sContext *_localctx = _tracker.createInstance<R_ua_sContext>(_ctx, getState());
  enterRule(_localctx, 18, rGURAParser::RuleR_ua_s);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(115);
    match(rGURAParser::UAS);
    setState(119);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(116);
      uas_element();
      setState(121);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(122);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Uas_elementContext ------------------------------------------------------------------

rGURAParser::Uas_elementContext::Uas_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::Uas_elementContext::Identifier() {
  return getToken(rGURAParser::Identifier, 0);
}

std::vector<rGURAParser::Attr_valContext *> rGURAParser::Uas_elementContext::attr_val() {
  return getRuleContexts<rGURAParser::Attr_valContext>();
}

rGURAParser::Attr_valContext* rGURAParser::Uas_elementContext::attr_val(size_t i) {
  return getRuleContext<rGURAParser::Attr_valContext>(i);
}


size_t rGURAParser::Uas_elementContext::getRuleIndex() const {
  return rGURAParser::RuleUas_element;
}

void rGURAParser::Uas_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUas_element(this);
}

void rGURAParser::Uas_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUas_element(this);
}

rGURAParser::Uas_elementContext* rGURAParser::uas_element() {
  Uas_elementContext *_localctx = _tracker.createInstance<Uas_elementContext>(_ctx, getState());
  enterRule(_localctx, 20, rGURAParser::RuleUas_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(124);
    match(rGURAParser::Identifier);
    setState(126); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(125);
      attr_val();
      setState(128); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == rGURAParser::LEFTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Attr_valContext ------------------------------------------------------------------

rGURAParser::Attr_valContext::Attr_valContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::Attr_valContext::LEFTTUPLE() {
  return getToken(rGURAParser::LEFTTUPLE, 0);
}

tree::TerminalNode* rGURAParser::Attr_valContext::COMMA() {
  return getToken(rGURAParser::COMMA, 0);
}

tree::TerminalNode* rGURAParser::Attr_valContext::RIGHTTUPLE() {
  return getToken(rGURAParser::RIGHTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Attr_valContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::Attr_valContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::Attr_valContext::getRuleIndex() const {
  return rGURAParser::RuleAttr_val;
}

void rGURAParser::Attr_valContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAttr_val(this);
}

void rGURAParser::Attr_valContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAttr_val(this);
}

rGURAParser::Attr_valContext* rGURAParser::attr_val() {
  Attr_valContext *_localctx = _tracker.createInstance<Attr_valContext>(_ctx, getState());
  enterRule(_localctx, 22, rGURAParser::RuleAttr_val);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(130);
    match(rGURAParser::LEFTTUPLE);
    setState(131);
    dynamic_cast<Attr_valContext *>(_localctx)->a = match(rGURAParser::Identifier);
    setState(132);
    match(rGURAParser::COMMA);
    setState(133);
    dynamic_cast<Attr_valContext *>(_localctx)->v = match(rGURAParser::Identifier);
    setState(134);
    match(rGURAParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_ua_mContext ------------------------------------------------------------------

rGURAParser::R_ua_mContext::R_ua_mContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_ua_mContext::UAM() {
  return getToken(rGURAParser::UAM, 0);
}

tree::TerminalNode* rGURAParser::R_ua_mContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<rGURAParser::Uam_elementContext *> rGURAParser::R_ua_mContext::uam_element() {
  return getRuleContexts<rGURAParser::Uam_elementContext>();
}

rGURAParser::Uam_elementContext* rGURAParser::R_ua_mContext::uam_element(size_t i) {
  return getRuleContext<rGURAParser::Uam_elementContext>(i);
}


size_t rGURAParser::R_ua_mContext::getRuleIndex() const {
  return rGURAParser::RuleR_ua_m;
}

void rGURAParser::R_ua_mContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_ua_m(this);
}

void rGURAParser::R_ua_mContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_ua_m(this);
}

rGURAParser::R_ua_mContext* rGURAParser::r_ua_m() {
  R_ua_mContext *_localctx = _tracker.createInstance<R_ua_mContext>(_ctx, getState());
  enterRule(_localctx, 24, rGURAParser::RuleR_ua_m);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(136);
    match(rGURAParser::UAM);
    setState(140);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::Identifier) {
      setState(137);
      uam_element();
      setState(142);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(143);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Uam_elementContext ------------------------------------------------------------------

rGURAParser::Uam_elementContext::Uam_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> rGURAParser::Uam_elementContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::Uam_elementContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}

tree::TerminalNode* rGURAParser::Uam_elementContext::LEFTTUPLE() {
  return getToken(rGURAParser::LEFTTUPLE, 0);
}

tree::TerminalNode* rGURAParser::Uam_elementContext::RIGHTTUPLE() {
  return getToken(rGURAParser::RIGHTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Uam_elementContext::COMMA() {
  return getTokens(rGURAParser::COMMA);
}

tree::TerminalNode* rGURAParser::Uam_elementContext::COMMA(size_t i) {
  return getToken(rGURAParser::COMMA, i);
}


size_t rGURAParser::Uam_elementContext::getRuleIndex() const {
  return rGURAParser::RuleUam_element;
}

void rGURAParser::Uam_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUam_element(this);
}

void rGURAParser::Uam_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUam_element(this);
}

rGURAParser::Uam_elementContext* rGURAParser::uam_element() {
  Uam_elementContext *_localctx = _tracker.createInstance<Uam_elementContext>(_ctx, getState());
  enterRule(_localctx, 26, rGURAParser::RuleUam_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(145);
    match(rGURAParser::Identifier);
    setState(146);
    match(rGURAParser::LEFTTUPLE);
    setState(147);
    match(rGURAParser::Identifier);
    setState(150); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(148);
      match(rGURAParser::COMMA);
      setState(149);
      match(rGURAParser::Identifier);
      setState(152); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == rGURAParser::COMMA);
    setState(154);
    match(rGURAParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_rulesContext ------------------------------------------------------------------

rGURAParser::R_rulesContext::R_rulesContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_rulesContext::RULE() {
  return getToken(rGURAParser::RULE, 0);
}

tree::TerminalNode* rGURAParser::R_rulesContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<rGURAParser::Rule_elementContext *> rGURAParser::R_rulesContext::rule_element() {
  return getRuleContexts<rGURAParser::Rule_elementContext>();
}

rGURAParser::Rule_elementContext* rGURAParser::R_rulesContext::rule_element(size_t i) {
  return getRuleContext<rGURAParser::Rule_elementContext>(i);
}


size_t rGURAParser::R_rulesContext::getRuleIndex() const {
  return rGURAParser::RuleR_rules;
}

void rGURAParser::R_rulesContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_rules(this);
}

void rGURAParser::R_rulesContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_rules(this);
}

rGURAParser::R_rulesContext* rGURAParser::r_rules() {
  R_rulesContext *_localctx = _tracker.createInstance<R_rulesContext>(_ctx, getState());
  enterRule(_localctx, 28, rGURAParser::RuleR_rules);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(156);
    match(rGURAParser::RULE);
    setState(160);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == rGURAParser::LEFTTUPLE) {
      setState(157);
      rule_element();
      setState(162);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(163);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Rule_elementContext ------------------------------------------------------------------

rGURAParser::Rule_elementContext::Rule_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

rGURAParser::Add_ruleContext* rGURAParser::Rule_elementContext::add_rule() {
  return getRuleContext<rGURAParser::Add_ruleContext>(0);
}

rGURAParser::Delete_ruleContext* rGURAParser::Rule_elementContext::delete_rule() {
  return getRuleContext<rGURAParser::Delete_ruleContext>(0);
}


size_t rGURAParser::Rule_elementContext::getRuleIndex() const {
  return rGURAParser::RuleRule_element;
}

void rGURAParser::Rule_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterRule_element(this);
}

void rGURAParser::Rule_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitRule_element(this);
}

rGURAParser::Rule_elementContext* rGURAParser::rule_element() {
  Rule_elementContext *_localctx = _tracker.createInstance<Rule_elementContext>(_ctx, getState());
  enterRule(_localctx, 30, rGURAParser::RuleRule_element);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(167);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(165);
      add_rule();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(166);
      delete_rule();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Add_ruleContext ------------------------------------------------------------------

rGURAParser::Add_ruleContext::Add_ruleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::Add_ruleContext::LEFTTUPLE() {
  return getToken(rGURAParser::LEFTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Add_ruleContext::COMMA() {
  return getTokens(rGURAParser::COMMA);
}

tree::TerminalNode* rGURAParser::Add_ruleContext::COMMA(size_t i) {
  return getToken(rGURAParser::COMMA, i);
}

rGURAParser::PreconditionContext* rGURAParser::Add_ruleContext::precondition() {
  return getRuleContext<rGURAParser::PreconditionContext>(0);
}

tree::TerminalNode* rGURAParser::Add_ruleContext::RIGHTTUPLE() {
  return getToken(rGURAParser::RIGHTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Add_ruleContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::Add_ruleContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::Add_ruleContext::getRuleIndex() const {
  return rGURAParser::RuleAdd_rule;
}

void rGURAParser::Add_ruleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAdd_rule(this);
}

void rGURAParser::Add_ruleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAdd_rule(this);
}

rGURAParser::Add_ruleContext* rGURAParser::add_rule() {
  Add_ruleContext *_localctx = _tracker.createInstance<Add_ruleContext>(_ctx, getState());
  enterRule(_localctx, 32, rGURAParser::RuleAdd_rule);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(169);
    match(rGURAParser::LEFTTUPLE);
    setState(170);
    dynamic_cast<Add_ruleContext *>(_localctx)->admin = match(rGURAParser::Identifier);
    setState(171);
    match(rGURAParser::COMMA);
    setState(172);
    precondition();
    setState(173);
    match(rGURAParser::COMMA);
    setState(174);
    dynamic_cast<Add_ruleContext *>(_localctx)->attr = match(rGURAParser::Identifier);
    setState(175);
    match(rGURAParser::COMMA);
    setState(176);
    dynamic_cast<Add_ruleContext *>(_localctx)->value = match(rGURAParser::Identifier);
    setState(177);
    match(rGURAParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Delete_ruleContext ------------------------------------------------------------------

rGURAParser::Delete_ruleContext::Delete_ruleContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::Delete_ruleContext::LEFTTUPLE() {
  return getToken(rGURAParser::LEFTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Delete_ruleContext::COMMA() {
  return getTokens(rGURAParser::COMMA);
}

tree::TerminalNode* rGURAParser::Delete_ruleContext::COMMA(size_t i) {
  return getToken(rGURAParser::COMMA, i);
}

tree::TerminalNode* rGURAParser::Delete_ruleContext::RIGHTTUPLE() {
  return getToken(rGURAParser::RIGHTTUPLE, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::Delete_ruleContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::Delete_ruleContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::Delete_ruleContext::getRuleIndex() const {
  return rGURAParser::RuleDelete_rule;
}

void rGURAParser::Delete_ruleContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterDelete_rule(this);
}

void rGURAParser::Delete_ruleContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitDelete_rule(this);
}

rGURAParser::Delete_ruleContext* rGURAParser::delete_rule() {
  Delete_ruleContext *_localctx = _tracker.createInstance<Delete_ruleContext>(_ctx, getState());
  enterRule(_localctx, 34, rGURAParser::RuleDelete_rule);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(179);
    match(rGURAParser::LEFTTUPLE);
    setState(180);
    dynamic_cast<Delete_ruleContext *>(_localctx)->admin = match(rGURAParser::Identifier);
    setState(181);
    match(rGURAParser::COMMA);
    setState(182);
    dynamic_cast<Delete_ruleContext *>(_localctx)->attr = match(rGURAParser::Identifier);
    setState(183);
    match(rGURAParser::COMMA);
    setState(184);
    dynamic_cast<Delete_ruleContext *>(_localctx)->value = match(rGURAParser::Identifier);
    setState(185);
    match(rGURAParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PreconditionContext ------------------------------------------------------------------

rGURAParser::PreconditionContext::PreconditionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::PreconditionContext::TRUE() {
  return getToken(rGURAParser::TRUE, 0);
}

std::vector<rGURAParser::AtomContext *> rGURAParser::PreconditionContext::atom() {
  return getRuleContexts<rGURAParser::AtomContext>();
}

rGURAParser::AtomContext* rGURAParser::PreconditionContext::atom(size_t i) {
  return getRuleContext<rGURAParser::AtomContext>(i);
}

std::vector<tree::TerminalNode *> rGURAParser::PreconditionContext::AND() {
  return getTokens(rGURAParser::AND);
}

tree::TerminalNode* rGURAParser::PreconditionContext::AND(size_t i) {
  return getToken(rGURAParser::AND, i);
}


size_t rGURAParser::PreconditionContext::getRuleIndex() const {
  return rGURAParser::RulePrecondition;
}

void rGURAParser::PreconditionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPrecondition(this);
}

void rGURAParser::PreconditionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPrecondition(this);
}

rGURAParser::PreconditionContext* rGURAParser::precondition() {
  PreconditionContext *_localctx = _tracker.createInstance<PreconditionContext>(_ctx, getState());
  enterRule(_localctx, 36, rGURAParser::RulePrecondition);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(196);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case rGURAParser::TRUE: {
        enterOuterAlt(_localctx, 1);
        setState(187);
        match(rGURAParser::TRUE);
        break;
      }

      case rGURAParser::NOT:
      case rGURAParser::Identifier: {
        enterOuterAlt(_localctx, 2);
        setState(188);
        atom();
        setState(193);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while (_la == rGURAParser::AND) {
          setState(189);
          match(rGURAParser::AND);
          setState(190);
          atom();
          setState(195);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AtomContext ------------------------------------------------------------------

rGURAParser::AtomContext::AtomContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::AtomContext::EQUAL() {
  return getToken(rGURAParser::EQUAL, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::AtomContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::AtomContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}

tree::TerminalNode* rGURAParser::AtomContext::NOT() {
  return getToken(rGURAParser::NOT, 0);
}


size_t rGURAParser::AtomContext::getRuleIndex() const {
  return rGURAParser::RuleAtom;
}

void rGURAParser::AtomContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAtom(this);
}

void rGURAParser::AtomContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAtom(this);
}

rGURAParser::AtomContext* rGURAParser::atom() {
  AtomContext *_localctx = _tracker.createInstance<AtomContext>(_ctx, getState());
  enterRule(_localctx, 38, rGURAParser::RuleAtom);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(199);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == rGURAParser::NOT) {
      setState(198);
      match(rGURAParser::NOT);
    }
    setState(201);
    dynamic_cast<AtomContext *>(_localctx)->attr = match(rGURAParser::Identifier);
    setState(202);
    match(rGURAParser::EQUAL);
    setState(203);
    dynamic_cast<AtomContext *>(_localctx)->value = match(rGURAParser::Identifier);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_specContext ------------------------------------------------------------------

rGURAParser::R_specContext::R_specContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* rGURAParser::R_specContext::SPEC() {
  return getToken(rGURAParser::SPEC, 0);
}

tree::TerminalNode* rGURAParser::R_specContext::SEMI() {
  return getToken(rGURAParser::SEMI, 0);
}

std::vector<tree::TerminalNode *> rGURAParser::R_specContext::Identifier() {
  return getTokens(rGURAParser::Identifier);
}

tree::TerminalNode* rGURAParser::R_specContext::Identifier(size_t i) {
  return getToken(rGURAParser::Identifier, i);
}


size_t rGURAParser::R_specContext::getRuleIndex() const {
  return rGURAParser::RuleR_spec;
}

void rGURAParser::R_specContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_spec(this);
}

void rGURAParser::R_specContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<rGURAListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_spec(this);
}

rGURAParser::R_specContext* rGURAParser::r_spec() {
  R_specContext *_localctx = _tracker.createInstance<R_specContext>(_ctx, getState());
  enterRule(_localctx, 40, rGURAParser::RuleR_spec);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(205);
    match(rGURAParser::SPEC);

    setState(206);
    dynamic_cast<R_specContext *>(_localctx)->attr = match(rGURAParser::Identifier);

    setState(207);
    dynamic_cast<R_specContext *>(_localctx)->value = match(rGURAParser::Identifier);
    setState(208);
    match(rGURAParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

// Static vars and initialization.
std::vector<dfa::DFA> rGURAParser::_decisionToDFA;
atn::PredictionContextCache rGURAParser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN rGURAParser::_atn;
std::vector<uint16_t> rGURAParser::_serializedATN;

std::vector<std::string> rGURAParser::_ruleNames = {
  "file", "r_start", "r_user", "r_attr_s", "r_attr_m", "r_scope", "scope_element", 
  "sep", "r_admin", "r_ua_s", "uas_element", "attr_val", "r_ua_m", "uam_element", 
  "r_rules", "rule_element", "add_rule", "delete_rule", "precondition", 
  "atom", "r_spec"
};

std::vector<std::string> rGURAParser::_literalNames = {
  "", "", "", "", "'SCOPE'", "'ADMINROLES'", "", "", "", "'SPEC'", "'TRUE'", 
  "'not'", "'('", "';'", "'*'", "','", "'.'", "':'", "'&'", "'|'", "'='", 
  "'=>'", "'?'", "')'", "'['", "']'", "'<'", "'>'"
};

std::vector<std::string> rGURAParser::_symbolicNames = {
  "", "USER", "ATTR_S", "ATTR_M", "SCOPE", "AR", "UAS", "UAM", "RULE", "SPEC", 
  "TRUE", "NOT", "LEFTPAREN", "SEMI", "STAR", "COMMA", "DOT", "COLON", "AND", 
  "OR", "EQUAL", "IMPLY", "QUESTION", "RIGHTPAREN", "LEFTBRACKET", "RIGHTBRACKET", 
  "LEFTTUPLE", "RIGHTTUPLE", "Identifier", "Constant", "Whitespace", "Newline", 
  "BlockComment", "LineComment"
};

dfa::Vocabulary rGURAParser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> rGURAParser::_tokenNames;

rGURAParser::Initializer::Initializer() {
	for (size_t i = 0; i < _symbolicNames.size(); ++i) {
		std::string name = _vocabulary.getLiteralName(i);
		if (name.empty()) {
			name = _vocabulary.getSymbolicName(i);
		}

		if (name.empty()) {
			_tokenNames.push_back("<INVALID>");
		} else {
      _tokenNames.push_back(name);
    }
	}

  _serializedATN = {
    0x3, 0x608b, 0xa72a, 0x8133, 0xb9ed, 0x417c, 0x3be7, 0x7786, 0x5964, 
    0x3, 0x23, 0xd5, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 0x9, 
    0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 0x4, 
    0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 0x9, 
    0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 0x4, 
    0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 0x12, 
    0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 0x15, 0x9, 
    0x15, 0x4, 0x16, 0x9, 0x16, 0x3, 0x2, 0x6, 0x2, 0x2e, 0xa, 0x2, 0xd, 
    0x2, 0xe, 0x2, 0x2f, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 
    0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x5, 0x3, 0x3b, 0xa, 0x3, 0x3, 
    0x4, 0x3, 0x4, 0x7, 0x4, 0x3f, 0xa, 0x4, 0xc, 0x4, 0xe, 0x4, 0x42, 0xb, 
    0x4, 0x3, 0x4, 0x3, 0x4, 0x3, 0x5, 0x3, 0x5, 0x7, 0x5, 0x48, 0xa, 0x5, 
    0xc, 0x5, 0xe, 0x5, 0x4b, 0xb, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x6, 0x3, 
    0x6, 0x7, 0x6, 0x51, 0xa, 0x6, 0xc, 0x6, 0xe, 0x6, 0x54, 0xb, 0x6, 0x3, 
    0x6, 0x3, 0x6, 0x3, 0x7, 0x3, 0x7, 0x7, 0x7, 0x5a, 0xa, 0x7, 0xc, 0x7, 
    0xe, 0x7, 0x5d, 0xb, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x8, 0x3, 0x8, 0x3, 
    0x8, 0x3, 0x8, 0x6, 0x8, 0x65, 0xa, 0x8, 0xd, 0x8, 0xe, 0x8, 0x66, 0x3, 
    0x8, 0x3, 0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0xa, 0x3, 0xa, 0x7, 0xa, 0x6f, 
    0xa, 0xa, 0xc, 0xa, 0xe, 0xa, 0x72, 0xb, 0xa, 0x3, 0xa, 0x3, 0xa, 0x3, 
    0xb, 0x3, 0xb, 0x7, 0xb, 0x78, 0xa, 0xb, 0xc, 0xb, 0xe, 0xb, 0x7b, 0xb, 
    0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xc, 0x3, 0xc, 0x6, 0xc, 0x81, 0xa, 0xc, 
    0xd, 0xc, 0xe, 0xc, 0x82, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 
    0xd, 0x3, 0xd, 0x3, 0xe, 0x3, 0xe, 0x7, 0xe, 0x8d, 0xa, 0xe, 0xc, 0xe, 
    0xe, 0xe, 0x90, 0xb, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xf, 0x3, 0xf, 0x3, 
    0xf, 0x3, 0xf, 0x3, 0xf, 0x6, 0xf, 0x99, 0xa, 0xf, 0xd, 0xf, 0xe, 0xf, 
    0x9a, 0x3, 0xf, 0x3, 0xf, 0x3, 0x10, 0x3, 0x10, 0x7, 0x10, 0xa1, 0xa, 
    0x10, 0xc, 0x10, 0xe, 0x10, 0xa4, 0xb, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 
    0x11, 0x3, 0x11, 0x5, 0x11, 0xaa, 0xa, 0x11, 0x3, 0x12, 0x3, 0x12, 0x3, 
    0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 0x3, 0x12, 
    0x3, 0x12, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 
    0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 
    0x7, 0x14, 0xc2, 0xa, 0x14, 0xc, 0x14, 0xe, 0x14, 0xc5, 0xb, 0x14, 0x5, 
    0x14, 0xc7, 0xa, 0x14, 0x3, 0x15, 0x5, 0x15, 0xca, 0xa, 0x15, 0x3, 0x15, 
    0x3, 0x15, 0x3, 0x15, 0x3, 0x15, 0x3, 0x16, 0x3, 0x16, 0x3, 0x16, 0x3, 
    0x16, 0x3, 0x16, 0x3, 0x16, 0x2, 0x2, 0x17, 0x2, 0x4, 0x6, 0x8, 0xa, 
    0xc, 0xe, 0x10, 0x12, 0x14, 0x16, 0x18, 0x1a, 0x1c, 0x1e, 0x20, 0x22, 
    0x24, 0x26, 0x28, 0x2a, 0x2, 0x3, 0x4, 0x2, 0x11, 0x11, 0x13, 0x13, 
    0x2, 0xd7, 0x2, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x4, 0x3a, 0x3, 0x2, 0x2, 
    0x2, 0x6, 0x3c, 0x3, 0x2, 0x2, 0x2, 0x8, 0x45, 0x3, 0x2, 0x2, 0x2, 0xa, 
    0x4e, 0x3, 0x2, 0x2, 0x2, 0xc, 0x57, 0x3, 0x2, 0x2, 0x2, 0xe, 0x60, 
    0x3, 0x2, 0x2, 0x2, 0x10, 0x6a, 0x3, 0x2, 0x2, 0x2, 0x12, 0x6c, 0x3, 
    0x2, 0x2, 0x2, 0x14, 0x75, 0x3, 0x2, 0x2, 0x2, 0x16, 0x7e, 0x3, 0x2, 
    0x2, 0x2, 0x18, 0x84, 0x3, 0x2, 0x2, 0x2, 0x1a, 0x8a, 0x3, 0x2, 0x2, 
    0x2, 0x1c, 0x93, 0x3, 0x2, 0x2, 0x2, 0x1e, 0x9e, 0x3, 0x2, 0x2, 0x2, 
    0x20, 0xa9, 0x3, 0x2, 0x2, 0x2, 0x22, 0xab, 0x3, 0x2, 0x2, 0x2, 0x24, 
    0xb5, 0x3, 0x2, 0x2, 0x2, 0x26, 0xc6, 0x3, 0x2, 0x2, 0x2, 0x28, 0xc9, 
    0x3, 0x2, 0x2, 0x2, 0x2a, 0xcf, 0x3, 0x2, 0x2, 0x2, 0x2c, 0x2e, 0x5, 
    0x4, 0x3, 0x2, 0x2d, 0x2c, 0x3, 0x2, 0x2, 0x2, 0x2e, 0x2f, 0x3, 0x2, 
    0x2, 0x2, 0x2f, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x2f, 0x30, 0x3, 0x2, 0x2, 
    0x2, 0x30, 0x3, 0x3, 0x2, 0x2, 0x2, 0x31, 0x3b, 0x5, 0x6, 0x4, 0x2, 
    0x32, 0x3b, 0x5, 0x8, 0x5, 0x2, 0x33, 0x3b, 0x5, 0xa, 0x6, 0x2, 0x34, 
    0x3b, 0x5, 0xc, 0x7, 0x2, 0x35, 0x3b, 0x5, 0x12, 0xa, 0x2, 0x36, 0x3b, 
    0x5, 0x14, 0xb, 0x2, 0x37, 0x3b, 0x5, 0x1a, 0xe, 0x2, 0x38, 0x3b, 0x5, 
    0x1e, 0x10, 0x2, 0x39, 0x3b, 0x5, 0x2a, 0x16, 0x2, 0x3a, 0x31, 0x3, 
    0x2, 0x2, 0x2, 0x3a, 0x32, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x33, 0x3, 0x2, 
    0x2, 0x2, 0x3a, 0x34, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x35, 0x3, 0x2, 0x2, 
    0x2, 0x3a, 0x36, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x37, 0x3, 0x2, 0x2, 0x2, 
    0x3a, 0x38, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x39, 0x3, 0x2, 0x2, 0x2, 0x3b, 
    0x5, 0x3, 0x2, 0x2, 0x2, 0x3c, 0x40, 0x7, 0x3, 0x2, 0x2, 0x3d, 0x3f, 
    0x7, 0x1e, 0x2, 0x2, 0x3e, 0x3d, 0x3, 0x2, 0x2, 0x2, 0x3f, 0x42, 0x3, 
    0x2, 0x2, 0x2, 0x40, 0x3e, 0x3, 0x2, 0x2, 0x2, 0x40, 0x41, 0x3, 0x2, 
    0x2, 0x2, 0x41, 0x43, 0x3, 0x2, 0x2, 0x2, 0x42, 0x40, 0x3, 0x2, 0x2, 
    0x2, 0x43, 0x44, 0x7, 0xf, 0x2, 0x2, 0x44, 0x7, 0x3, 0x2, 0x2, 0x2, 
    0x45, 0x49, 0x7, 0x4, 0x2, 0x2, 0x46, 0x48, 0x7, 0x1e, 0x2, 0x2, 0x47, 
    0x46, 0x3, 0x2, 0x2, 0x2, 0x48, 0x4b, 0x3, 0x2, 0x2, 0x2, 0x49, 0x47, 
    0x3, 0x2, 0x2, 0x2, 0x49, 0x4a, 0x3, 0x2, 0x2, 0x2, 0x4a, 0x4c, 0x3, 
    0x2, 0x2, 0x2, 0x4b, 0x49, 0x3, 0x2, 0x2, 0x2, 0x4c, 0x4d, 0x7, 0xf, 
    0x2, 0x2, 0x4d, 0x9, 0x3, 0x2, 0x2, 0x2, 0x4e, 0x52, 0x7, 0x5, 0x2, 
    0x2, 0x4f, 0x51, 0x7, 0x1e, 0x2, 0x2, 0x50, 0x4f, 0x3, 0x2, 0x2, 0x2, 
    0x51, 0x54, 0x3, 0x2, 0x2, 0x2, 0x52, 0x50, 0x3, 0x2, 0x2, 0x2, 0x52, 
    0x53, 0x3, 0x2, 0x2, 0x2, 0x53, 0x55, 0x3, 0x2, 0x2, 0x2, 0x54, 0x52, 
    0x3, 0x2, 0x2, 0x2, 0x55, 0x56, 0x7, 0xf, 0x2, 0x2, 0x56, 0xb, 0x3, 
    0x2, 0x2, 0x2, 0x57, 0x5b, 0x7, 0x6, 0x2, 0x2, 0x58, 0x5a, 0x5, 0xe, 
    0x8, 0x2, 0x59, 0x58, 0x3, 0x2, 0x2, 0x2, 0x5a, 0x5d, 0x3, 0x2, 0x2, 
    0x2, 0x5b, 0x59, 0x3, 0x2, 0x2, 0x2, 0x5b, 0x5c, 0x3, 0x2, 0x2, 0x2, 
    0x5c, 0x5e, 0x3, 0x2, 0x2, 0x2, 0x5d, 0x5b, 0x3, 0x2, 0x2, 0x2, 0x5e, 
    0x5f, 0x7, 0xf, 0x2, 0x2, 0x5f, 0xd, 0x3, 0x2, 0x2, 0x2, 0x60, 0x61, 
    0x7, 0x1c, 0x2, 0x2, 0x61, 0x62, 0x7, 0x1e, 0x2, 0x2, 0x62, 0x64, 0x5, 
    0x10, 0x9, 0x2, 0x63, 0x65, 0x7, 0x1e, 0x2, 0x2, 0x64, 0x63, 0x3, 0x2, 
    0x2, 0x2, 0x65, 0x66, 0x3, 0x2, 0x2, 0x2, 0x66, 0x64, 0x3, 0x2, 0x2, 
    0x2, 0x66, 0x67, 0x3, 0x2, 0x2, 0x2, 0x67, 0x68, 0x3, 0x2, 0x2, 0x2, 
    0x68, 0x69, 0x7, 0x1d, 0x2, 0x2, 0x69, 0xf, 0x3, 0x2, 0x2, 0x2, 0x6a, 
    0x6b, 0x9, 0x2, 0x2, 0x2, 0x6b, 0x11, 0x3, 0x2, 0x2, 0x2, 0x6c, 0x70, 
    0x7, 0x7, 0x2, 0x2, 0x6d, 0x6f, 0x7, 0x1e, 0x2, 0x2, 0x6e, 0x6d, 0x3, 
    0x2, 0x2, 0x2, 0x6f, 0x72, 0x3, 0x2, 0x2, 0x2, 0x70, 0x6e, 0x3, 0x2, 
    0x2, 0x2, 0x70, 0x71, 0x3, 0x2, 0x2, 0x2, 0x71, 0x73, 0x3, 0x2, 0x2, 
    0x2, 0x72, 0x70, 0x3, 0x2, 0x2, 0x2, 0x73, 0x74, 0x7, 0xf, 0x2, 0x2, 
    0x74, 0x13, 0x3, 0x2, 0x2, 0x2, 0x75, 0x79, 0x7, 0x8, 0x2, 0x2, 0x76, 
    0x78, 0x5, 0x16, 0xc, 0x2, 0x77, 0x76, 0x3, 0x2, 0x2, 0x2, 0x78, 0x7b, 
    0x3, 0x2, 0x2, 0x2, 0x79, 0x77, 0x3, 0x2, 0x2, 0x2, 0x79, 0x7a, 0x3, 
    0x2, 0x2, 0x2, 0x7a, 0x7c, 0x3, 0x2, 0x2, 0x2, 0x7b, 0x79, 0x3, 0x2, 
    0x2, 0x2, 0x7c, 0x7d, 0x7, 0xf, 0x2, 0x2, 0x7d, 0x15, 0x3, 0x2, 0x2, 
    0x2, 0x7e, 0x80, 0x7, 0x1e, 0x2, 0x2, 0x7f, 0x81, 0x5, 0x18, 0xd, 0x2, 
    0x80, 0x7f, 0x3, 0x2, 0x2, 0x2, 0x81, 0x82, 0x3, 0x2, 0x2, 0x2, 0x82, 
    0x80, 0x3, 0x2, 0x2, 0x2, 0x82, 0x83, 0x3, 0x2, 0x2, 0x2, 0x83, 0x17, 
    0x3, 0x2, 0x2, 0x2, 0x84, 0x85, 0x7, 0x1c, 0x2, 0x2, 0x85, 0x86, 0x7, 
    0x1e, 0x2, 0x2, 0x86, 0x87, 0x7, 0x11, 0x2, 0x2, 0x87, 0x88, 0x7, 0x1e, 
    0x2, 0x2, 0x88, 0x89, 0x7, 0x1d, 0x2, 0x2, 0x89, 0x19, 0x3, 0x2, 0x2, 
    0x2, 0x8a, 0x8e, 0x7, 0x9, 0x2, 0x2, 0x8b, 0x8d, 0x5, 0x1c, 0xf, 0x2, 
    0x8c, 0x8b, 0x3, 0x2, 0x2, 0x2, 0x8d, 0x90, 0x3, 0x2, 0x2, 0x2, 0x8e, 
    0x8c, 0x3, 0x2, 0x2, 0x2, 0x8e, 0x8f, 0x3, 0x2, 0x2, 0x2, 0x8f, 0x91, 
    0x3, 0x2, 0x2, 0x2, 0x90, 0x8e, 0x3, 0x2, 0x2, 0x2, 0x91, 0x92, 0x7, 
    0xf, 0x2, 0x2, 0x92, 0x1b, 0x3, 0x2, 0x2, 0x2, 0x93, 0x94, 0x7, 0x1e, 
    0x2, 0x2, 0x94, 0x95, 0x7, 0x1c, 0x2, 0x2, 0x95, 0x98, 0x7, 0x1e, 0x2, 
    0x2, 0x96, 0x97, 0x7, 0x11, 0x2, 0x2, 0x97, 0x99, 0x7, 0x1e, 0x2, 0x2, 
    0x98, 0x96, 0x3, 0x2, 0x2, 0x2, 0x99, 0x9a, 0x3, 0x2, 0x2, 0x2, 0x9a, 
    0x98, 0x3, 0x2, 0x2, 0x2, 0x9a, 0x9b, 0x3, 0x2, 0x2, 0x2, 0x9b, 0x9c, 
    0x3, 0x2, 0x2, 0x2, 0x9c, 0x9d, 0x7, 0x1d, 0x2, 0x2, 0x9d, 0x1d, 0x3, 
    0x2, 0x2, 0x2, 0x9e, 0xa2, 0x7, 0xa, 0x2, 0x2, 0x9f, 0xa1, 0x5, 0x20, 
    0x11, 0x2, 0xa0, 0x9f, 0x3, 0x2, 0x2, 0x2, 0xa1, 0xa4, 0x3, 0x2, 0x2, 
    0x2, 0xa2, 0xa0, 0x3, 0x2, 0x2, 0x2, 0xa2, 0xa3, 0x3, 0x2, 0x2, 0x2, 
    0xa3, 0xa5, 0x3, 0x2, 0x2, 0x2, 0xa4, 0xa2, 0x3, 0x2, 0x2, 0x2, 0xa5, 
    0xa6, 0x7, 0xf, 0x2, 0x2, 0xa6, 0x1f, 0x3, 0x2, 0x2, 0x2, 0xa7, 0xaa, 
    0x5, 0x22, 0x12, 0x2, 0xa8, 0xaa, 0x5, 0x24, 0x13, 0x2, 0xa9, 0xa7, 
    0x3, 0x2, 0x2, 0x2, 0xa9, 0xa8, 0x3, 0x2, 0x2, 0x2, 0xaa, 0x21, 0x3, 
    0x2, 0x2, 0x2, 0xab, 0xac, 0x7, 0x1c, 0x2, 0x2, 0xac, 0xad, 0x7, 0x1e, 
    0x2, 0x2, 0xad, 0xae, 0x7, 0x11, 0x2, 0x2, 0xae, 0xaf, 0x5, 0x26, 0x14, 
    0x2, 0xaf, 0xb0, 0x7, 0x11, 0x2, 0x2, 0xb0, 0xb1, 0x7, 0x1e, 0x2, 0x2, 
    0xb1, 0xb2, 0x7, 0x11, 0x2, 0x2, 0xb2, 0xb3, 0x7, 0x1e, 0x2, 0x2, 0xb3, 
    0xb4, 0x7, 0x1d, 0x2, 0x2, 0xb4, 0x23, 0x3, 0x2, 0x2, 0x2, 0xb5, 0xb6, 
    0x7, 0x1c, 0x2, 0x2, 0xb6, 0xb7, 0x7, 0x1e, 0x2, 0x2, 0xb7, 0xb8, 0x7, 
    0x11, 0x2, 0x2, 0xb8, 0xb9, 0x7, 0x1e, 0x2, 0x2, 0xb9, 0xba, 0x7, 0x11, 
    0x2, 0x2, 0xba, 0xbb, 0x7, 0x1e, 0x2, 0x2, 0xbb, 0xbc, 0x7, 0x1d, 0x2, 
    0x2, 0xbc, 0x25, 0x3, 0x2, 0x2, 0x2, 0xbd, 0xc7, 0x7, 0xc, 0x2, 0x2, 
    0xbe, 0xc3, 0x5, 0x28, 0x15, 0x2, 0xbf, 0xc0, 0x7, 0x14, 0x2, 0x2, 0xc0, 
    0xc2, 0x5, 0x28, 0x15, 0x2, 0xc1, 0xbf, 0x3, 0x2, 0x2, 0x2, 0xc2, 0xc5, 
    0x3, 0x2, 0x2, 0x2, 0xc3, 0xc1, 0x3, 0x2, 0x2, 0x2, 0xc3, 0xc4, 0x3, 
    0x2, 0x2, 0x2, 0xc4, 0xc7, 0x3, 0x2, 0x2, 0x2, 0xc5, 0xc3, 0x3, 0x2, 
    0x2, 0x2, 0xc6, 0xbd, 0x3, 0x2, 0x2, 0x2, 0xc6, 0xbe, 0x3, 0x2, 0x2, 
    0x2, 0xc7, 0x27, 0x3, 0x2, 0x2, 0x2, 0xc8, 0xca, 0x7, 0xd, 0x2, 0x2, 
    0xc9, 0xc8, 0x3, 0x2, 0x2, 0x2, 0xc9, 0xca, 0x3, 0x2, 0x2, 0x2, 0xca, 
    0xcb, 0x3, 0x2, 0x2, 0x2, 0xcb, 0xcc, 0x7, 0x1e, 0x2, 0x2, 0xcc, 0xcd, 
    0x7, 0x16, 0x2, 0x2, 0xcd, 0xce, 0x7, 0x1e, 0x2, 0x2, 0xce, 0x29, 0x3, 
    0x2, 0x2, 0x2, 0xcf, 0xd0, 0x7, 0xb, 0x2, 0x2, 0xd0, 0xd1, 0x7, 0x1e, 
    0x2, 0x2, 0xd1, 0xd2, 0x7, 0x1e, 0x2, 0x2, 0xd2, 0xd3, 0x7, 0xf, 0x2, 
    0x2, 0xd3, 0x2b, 0x3, 0x2, 0x2, 0x2, 0x13, 0x2f, 0x3a, 0x40, 0x49, 0x52, 
    0x5b, 0x66, 0x70, 0x79, 0x82, 0x8e, 0x9a, 0xa2, 0xa9, 0xc3, 0xc6, 0xc9, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

rGURAParser::Initializer rGURAParser::_init;
