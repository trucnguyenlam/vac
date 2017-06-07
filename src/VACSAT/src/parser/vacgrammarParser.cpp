
// Generated from vacgrammar.g4 by ANTLR 4.7


#include "vacgrammarListener.h"

#include "vacgrammarParser.h"


using namespace antlrcpp;
using namespace Parser;
using namespace antlr4;

vacgrammarParser::vacgrammarParser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

vacgrammarParser::~vacgrammarParser() {
  delete _interpreter;
}

std::string vacgrammarParser::getGrammarFileName() const {
  return "vacgrammar.g4";
}

const std::vector<std::string>& vacgrammarParser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& vacgrammarParser::getVocabulary() const {
  return _vocabulary;
}


//----------------- FileContext ------------------------------------------------------------------

vacgrammarParser::FileContext::FileContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<vacgrammarParser::R_startContext *> vacgrammarParser::FileContext::r_start() {
  return getRuleContexts<vacgrammarParser::R_startContext>();
}

vacgrammarParser::R_startContext* vacgrammarParser::FileContext::r_start(size_t i) {
  return getRuleContext<vacgrammarParser::R_startContext>(i);
}


size_t vacgrammarParser::FileContext::getRuleIndex() const {
  return vacgrammarParser::RuleFile;
}

void vacgrammarParser::FileContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterFile(this);
}

void vacgrammarParser::FileContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitFile(this);
}

vacgrammarParser::FileContext* vacgrammarParser::file() {
  FileContext *_localctx = _tracker.createInstance<FileContext>(_ctx, getState());
  enterRule(_localctx, 0, vacgrammarParser::RuleFile);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(47); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(46);
      r_start();
      setState(49); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << vacgrammarParser::USER)
      | (1ULL << vacgrammarParser::ATTR)
      | (1ULL << vacgrammarParser::INIT)
      | (1ULL << vacgrammarParser::RULE)
      | (1ULL << vacgrammarParser::QUERY))) != 0));
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_startContext ------------------------------------------------------------------

vacgrammarParser::R_startContext::R_startContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::R_userContext* vacgrammarParser::R_startContext::r_user() {
  return getRuleContext<vacgrammarParser::R_userContext>(0);
}

vacgrammarParser::R_attrContext* vacgrammarParser::R_startContext::r_attr() {
  return getRuleContext<vacgrammarParser::R_attrContext>(0);
}

vacgrammarParser::R_initContext* vacgrammarParser::R_startContext::r_init() {
  return getRuleContext<vacgrammarParser::R_initContext>(0);
}

vacgrammarParser::R_rulesContext* vacgrammarParser::R_startContext::r_rules() {
  return getRuleContext<vacgrammarParser::R_rulesContext>(0);
}

vacgrammarParser::R_queryContext* vacgrammarParser::R_startContext::r_query() {
  return getRuleContext<vacgrammarParser::R_queryContext>(0);
}


size_t vacgrammarParser::R_startContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_start;
}

void vacgrammarParser::R_startContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_start(this);
}

void vacgrammarParser::R_startContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_start(this);
}

vacgrammarParser::R_startContext* vacgrammarParser::r_start() {
  R_startContext *_localctx = _tracker.createInstance<R_startContext>(_ctx, getState());
  enterRule(_localctx, 2, vacgrammarParser::RuleR_start);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(56);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case vacgrammarParser::USER: {
        enterOuterAlt(_localctx, 1);
        setState(51);
        r_user();
        break;
      }

      case vacgrammarParser::ATTR: {
        enterOuterAlt(_localctx, 2);
        setState(52);
        r_attr();
        break;
      }

      case vacgrammarParser::INIT: {
        enterOuterAlt(_localctx, 3);
        setState(53);
        r_init();
        break;
      }

      case vacgrammarParser::RULE: {
        enterOuterAlt(_localctx, 4);
        setState(54);
        r_rules();
        break;
      }

      case vacgrammarParser::QUERY: {
        enterOuterAlt(_localctx, 5);
        setState(55);
        r_query();
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

vacgrammarParser::R_userContext::R_userContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::R_userContext::USER() {
  return getToken(vacgrammarParser::USER, 0);
}

tree::TerminalNode* vacgrammarParser::R_userContext::SEMI() {
  return getToken(vacgrammarParser::SEMI, 0);
}

std::vector<vacgrammarParser::User_elementContext *> vacgrammarParser::R_userContext::user_element() {
  return getRuleContexts<vacgrammarParser::User_elementContext>();
}

vacgrammarParser::User_elementContext* vacgrammarParser::R_userContext::user_element(size_t i) {
  return getRuleContext<vacgrammarParser::User_elementContext>(i);
}


size_t vacgrammarParser::R_userContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_user;
}

void vacgrammarParser::R_userContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_user(this);
}

void vacgrammarParser::R_userContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_user(this);
}

vacgrammarParser::R_userContext* vacgrammarParser::r_user() {
  R_userContext *_localctx = _tracker.createInstance<R_userContext>(_ctx, getState());
  enterRule(_localctx, 4, vacgrammarParser::RuleR_user);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(58);
    match(vacgrammarParser::USER);
    setState(60); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(59);
      user_element();
      setState(62); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == vacgrammarParser::Identifier);
    setState(64);
    match(vacgrammarParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- User_elementContext ------------------------------------------------------------------

vacgrammarParser::User_elementContext::User_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::User_elementContext::Identifier() {
  return getToken(vacgrammarParser::Identifier, 0);
}

tree::TerminalNode* vacgrammarParser::User_elementContext::STAR() {
  return getToken(vacgrammarParser::STAR, 0);
}


size_t vacgrammarParser::User_elementContext::getRuleIndex() const {
  return vacgrammarParser::RuleUser_element;
}

void vacgrammarParser::User_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUser_element(this);
}

void vacgrammarParser::User_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUser_element(this);
}

vacgrammarParser::User_elementContext* vacgrammarParser::user_element() {
  User_elementContext *_localctx = _tracker.createInstance<User_elementContext>(_ctx, getState());
  enterRule(_localctx, 6, vacgrammarParser::RuleUser_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(66);
    match(vacgrammarParser::Identifier);
    setState(68);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == vacgrammarParser::STAR) {
      setState(67);
      match(vacgrammarParser::STAR);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_attrContext ------------------------------------------------------------------

vacgrammarParser::R_attrContext::R_attrContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::R_attrContext::ATTR() {
  return getToken(vacgrammarParser::ATTR, 0);
}

tree::TerminalNode* vacgrammarParser::R_attrContext::SEMI() {
  return getToken(vacgrammarParser::SEMI, 0);
}

std::vector<vacgrammarParser::Attr_elementContext *> vacgrammarParser::R_attrContext::attr_element() {
  return getRuleContexts<vacgrammarParser::Attr_elementContext>();
}

vacgrammarParser::Attr_elementContext* vacgrammarParser::R_attrContext::attr_element(size_t i) {
  return getRuleContext<vacgrammarParser::Attr_elementContext>(i);
}


size_t vacgrammarParser::R_attrContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_attr;
}

void vacgrammarParser::R_attrContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_attr(this);
}

void vacgrammarParser::R_attrContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_attr(this);
}

vacgrammarParser::R_attrContext* vacgrammarParser::r_attr() {
  R_attrContext *_localctx = _tracker.createInstance<R_attrContext>(_ctx, getState());
  enterRule(_localctx, 8, vacgrammarParser::RuleR_attr);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(70);
    match(vacgrammarParser::ATTR);
    setState(72); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(71);
      attr_element();
      setState(74); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == vacgrammarParser::Identifier);
    setState(76);
    match(vacgrammarParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Attr_elementContext ------------------------------------------------------------------

vacgrammarParser::Attr_elementContext::Attr_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::Attr_elementContext::Identifier() {
  return getToken(vacgrammarParser::Identifier, 0);
}

tree::TerminalNode* vacgrammarParser::Attr_elementContext::LEFTBRACKET() {
  return getToken(vacgrammarParser::LEFTBRACKET, 0);
}

tree::TerminalNode* vacgrammarParser::Attr_elementContext::Constant() {
  return getToken(vacgrammarParser::Constant, 0);
}

tree::TerminalNode* vacgrammarParser::Attr_elementContext::RIGHTBRACKET() {
  return getToken(vacgrammarParser::RIGHTBRACKET, 0);
}


size_t vacgrammarParser::Attr_elementContext::getRuleIndex() const {
  return vacgrammarParser::RuleAttr_element;
}

void vacgrammarParser::Attr_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAttr_element(this);
}

void vacgrammarParser::Attr_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAttr_element(this);
}

vacgrammarParser::Attr_elementContext* vacgrammarParser::attr_element() {
  Attr_elementContext *_localctx = _tracker.createInstance<Attr_elementContext>(_ctx, getState());
  enterRule(_localctx, 10, vacgrammarParser::RuleAttr_element);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(78);
    match(vacgrammarParser::Identifier);
    setState(79);
    match(vacgrammarParser::LEFTBRACKET);
    setState(80);
    match(vacgrammarParser::Constant);
    setState(81);
    match(vacgrammarParser::RIGHTBRACKET);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_initContext ------------------------------------------------------------------

vacgrammarParser::R_initContext::R_initContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::R_initContext::INIT() {
  return getToken(vacgrammarParser::INIT, 0);
}

tree::TerminalNode* vacgrammarParser::R_initContext::SEMI() {
  return getToken(vacgrammarParser::SEMI, 0);
}

std::vector<vacgrammarParser::Init_elementContext *> vacgrammarParser::R_initContext::init_element() {
  return getRuleContexts<vacgrammarParser::Init_elementContext>();
}

vacgrammarParser::Init_elementContext* vacgrammarParser::R_initContext::init_element(size_t i) {
  return getRuleContext<vacgrammarParser::Init_elementContext>(i);
}


size_t vacgrammarParser::R_initContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_init;
}

void vacgrammarParser::R_initContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_init(this);
}

void vacgrammarParser::R_initContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_init(this);
}

vacgrammarParser::R_initContext* vacgrammarParser::r_init() {
  R_initContext *_localctx = _tracker.createInstance<R_initContext>(_ctx, getState());
  enterRule(_localctx, 12, vacgrammarParser::RuleR_init);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(83);
    match(vacgrammarParser::INIT);
    setState(85); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(84);
      init_element();
      setState(87); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == vacgrammarParser::LEFTTUPLE);
    setState(89);
    match(vacgrammarParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Init_elementContext ------------------------------------------------------------------

vacgrammarParser::Init_elementContext::Init_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::Init_elementContext::LEFTTUPLE() {
  return getToken(vacgrammarParser::LEFTTUPLE, 0);
}

tree::TerminalNode* vacgrammarParser::Init_elementContext::Identifier() {
  return getToken(vacgrammarParser::Identifier, 0);
}

tree::TerminalNode* vacgrammarParser::Init_elementContext::COLON() {
  return getToken(vacgrammarParser::COLON, 0);
}

std::vector<vacgrammarParser::Init_assignmentContext *> vacgrammarParser::Init_elementContext::init_assignment() {
  return getRuleContexts<vacgrammarParser::Init_assignmentContext>();
}

vacgrammarParser::Init_assignmentContext* vacgrammarParser::Init_elementContext::init_assignment(size_t i) {
  return getRuleContext<vacgrammarParser::Init_assignmentContext>(i);
}

tree::TerminalNode* vacgrammarParser::Init_elementContext::RIGHTTUPLE() {
  return getToken(vacgrammarParser::RIGHTTUPLE, 0);
}

std::vector<tree::TerminalNode *> vacgrammarParser::Init_elementContext::COMMA() {
  return getTokens(vacgrammarParser::COMMA);
}

tree::TerminalNode* vacgrammarParser::Init_elementContext::COMMA(size_t i) {
  return getToken(vacgrammarParser::COMMA, i);
}


size_t vacgrammarParser::Init_elementContext::getRuleIndex() const {
  return vacgrammarParser::RuleInit_element;
}

void vacgrammarParser::Init_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterInit_element(this);
}

void vacgrammarParser::Init_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitInit_element(this);
}

vacgrammarParser::Init_elementContext* vacgrammarParser::init_element() {
  Init_elementContext *_localctx = _tracker.createInstance<Init_elementContext>(_ctx, getState());
  enterRule(_localctx, 14, vacgrammarParser::RuleInit_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(91);
    match(vacgrammarParser::LEFTTUPLE);
    setState(92);
    match(vacgrammarParser::Identifier);
    setState(93);
    match(vacgrammarParser::COLON);
    setState(94);
    init_assignment();
    setState(99);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == vacgrammarParser::COMMA) {
      setState(95);
      match(vacgrammarParser::COMMA);
      setState(96);
      init_assignment();
      setState(101);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(102);
    match(vacgrammarParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Init_assignmentContext ------------------------------------------------------------------

vacgrammarParser::Init_assignmentContext::Init_assignmentContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::Init_assignmentContext::Identifier() {
  return getToken(vacgrammarParser::Identifier, 0);
}

tree::TerminalNode* vacgrammarParser::Init_assignmentContext::EQUAL() {
  return getToken(vacgrammarParser::EQUAL, 0);
}

tree::TerminalNode* vacgrammarParser::Init_assignmentContext::Constant() {
  return getToken(vacgrammarParser::Constant, 0);
}


size_t vacgrammarParser::Init_assignmentContext::getRuleIndex() const {
  return vacgrammarParser::RuleInit_assignment;
}

void vacgrammarParser::Init_assignmentContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterInit_assignment(this);
}

void vacgrammarParser::Init_assignmentContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitInit_assignment(this);
}

vacgrammarParser::Init_assignmentContext* vacgrammarParser::init_assignment() {
  Init_assignmentContext *_localctx = _tracker.createInstance<Init_assignmentContext>(_ctx, getState());
  enterRule(_localctx, 16, vacgrammarParser::RuleInit_assignment);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(104);
    match(vacgrammarParser::Identifier);
    setState(105);
    match(vacgrammarParser::EQUAL);
    setState(106);
    match(vacgrammarParser::Constant);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PrimaryExpressionContext ------------------------------------------------------------------

vacgrammarParser::PrimaryExpressionContext::PrimaryExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::PrimaryExpressionContext::Constant() {
  return getToken(vacgrammarParser::Constant, 0);
}

tree::TerminalNode* vacgrammarParser::PrimaryExpressionContext::DOT() {
  return getToken(vacgrammarParser::DOT, 0);
}

std::vector<tree::TerminalNode *> vacgrammarParser::PrimaryExpressionContext::Identifier() {
  return getTokens(vacgrammarParser::Identifier);
}

tree::TerminalNode* vacgrammarParser::PrimaryExpressionContext::Identifier(size_t i) {
  return getToken(vacgrammarParser::Identifier, i);
}

tree::TerminalNode* vacgrammarParser::PrimaryExpressionContext::LEFTPAREN() {
  return getToken(vacgrammarParser::LEFTPAREN, 0);
}

vacgrammarParser::ExpressionContext* vacgrammarParser::PrimaryExpressionContext::expression() {
  return getRuleContext<vacgrammarParser::ExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::PrimaryExpressionContext::RIGHTPAREN() {
  return getToken(vacgrammarParser::RIGHTPAREN, 0);
}


size_t vacgrammarParser::PrimaryExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RulePrimaryExpression;
}

void vacgrammarParser::PrimaryExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPrimaryExpression(this);
}

void vacgrammarParser::PrimaryExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPrimaryExpression(this);
}

vacgrammarParser::PrimaryExpressionContext* vacgrammarParser::primaryExpression() {
  PrimaryExpressionContext *_localctx = _tracker.createInstance<PrimaryExpressionContext>(_ctx, getState());
  enterRule(_localctx, 18, vacgrammarParser::RulePrimaryExpression);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(116);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case vacgrammarParser::Constant: {
        enterOuterAlt(_localctx, 1);
        setState(108);
        match(vacgrammarParser::Constant);
        break;
      }

      case vacgrammarParser::Identifier: {
        enterOuterAlt(_localctx, 2);
        setState(109);
        dynamic_cast<PrimaryExpressionContext *>(_localctx)->u = match(vacgrammarParser::Identifier);
        setState(110);
        match(vacgrammarParser::DOT);
        setState(111);
        dynamic_cast<PrimaryExpressionContext *>(_localctx)->a = match(vacgrammarParser::Identifier);
        break;
      }

      case vacgrammarParser::LEFTPAREN: {
        enterOuterAlt(_localctx, 3);
        setState(112);
        match(vacgrammarParser::LEFTPAREN);
        setState(113);
        expression();
        setState(114);
        match(vacgrammarParser::RIGHTPAREN);
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

//----------------- UnaryExpressionContext ------------------------------------------------------------------

vacgrammarParser::UnaryExpressionContext::UnaryExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::PrimaryExpressionContext* vacgrammarParser::UnaryExpressionContext::primaryExpression() {
  return getRuleContext<vacgrammarParser::PrimaryExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::UnaryExpressionContext::NOT() {
  return getToken(vacgrammarParser::NOT, 0);
}

vacgrammarParser::UnaryExpressionContext* vacgrammarParser::UnaryExpressionContext::unaryExpression() {
  return getRuleContext<vacgrammarParser::UnaryExpressionContext>(0);
}


size_t vacgrammarParser::UnaryExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleUnaryExpression;
}

void vacgrammarParser::UnaryExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterUnaryExpression(this);
}

void vacgrammarParser::UnaryExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitUnaryExpression(this);
}

vacgrammarParser::UnaryExpressionContext* vacgrammarParser::unaryExpression() {
  UnaryExpressionContext *_localctx = _tracker.createInstance<UnaryExpressionContext>(_ctx, getState());
  enterRule(_localctx, 20, vacgrammarParser::RuleUnaryExpression);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(121);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case vacgrammarParser::LEFTPAREN:
      case vacgrammarParser::Identifier:
      case vacgrammarParser::Constant: {
        enterOuterAlt(_localctx, 1);
        setState(118);
        primaryExpression();
        break;
      }

      case vacgrammarParser::NOT: {
        enterOuterAlt(_localctx, 2);
        setState(119);
        match(vacgrammarParser::NOT);
        setState(120);
        unaryExpression();
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

//----------------- EqualityExpressionContext ------------------------------------------------------------------

vacgrammarParser::EqualityExpressionContext::EqualityExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::UnaryExpressionContext* vacgrammarParser::EqualityExpressionContext::unaryExpression() {
  return getRuleContext<vacgrammarParser::UnaryExpressionContext>(0);
}

vacgrammarParser::EqualityExpressionContext* vacgrammarParser::EqualityExpressionContext::equalityExpression() {
  return getRuleContext<vacgrammarParser::EqualityExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::EqualityExpressionContext::EQUAL() {
  return getToken(vacgrammarParser::EQUAL, 0);
}


size_t vacgrammarParser::EqualityExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleEqualityExpression;
}

void vacgrammarParser::EqualityExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterEqualityExpression(this);
}

void vacgrammarParser::EqualityExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitEqualityExpression(this);
}


vacgrammarParser::EqualityExpressionContext* vacgrammarParser::equalityExpression() {
   return equalityExpression(0);
}

vacgrammarParser::EqualityExpressionContext* vacgrammarParser::equalityExpression(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  vacgrammarParser::EqualityExpressionContext *_localctx = _tracker.createInstance<EqualityExpressionContext>(_ctx, parentState);
  vacgrammarParser::EqualityExpressionContext *previousContext = _localctx;
  size_t startState = 22;
  enterRecursionRule(_localctx, 22, vacgrammarParser::RuleEqualityExpression, precedence);

    

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(124);
    unaryExpression();
    _ctx->stop = _input->LT(-1);
    setState(131);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<EqualityExpressionContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleEqualityExpression);
        setState(126);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(127);
        match(vacgrammarParser::EQUAL);
        setState(128);
        unaryExpression(); 
      }
      setState(133);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 9, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- AndExpressionContext ------------------------------------------------------------------

vacgrammarParser::AndExpressionContext::AndExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::EqualityExpressionContext* vacgrammarParser::AndExpressionContext::equalityExpression() {
  return getRuleContext<vacgrammarParser::EqualityExpressionContext>(0);
}

vacgrammarParser::AndExpressionContext* vacgrammarParser::AndExpressionContext::andExpression() {
  return getRuleContext<vacgrammarParser::AndExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::AndExpressionContext::AND() {
  return getToken(vacgrammarParser::AND, 0);
}

tree::TerminalNode* vacgrammarParser::AndExpressionContext::ANDAND() {
  return getToken(vacgrammarParser::ANDAND, 0);
}


size_t vacgrammarParser::AndExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleAndExpression;
}

void vacgrammarParser::AndExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAndExpression(this);
}

void vacgrammarParser::AndExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAndExpression(this);
}


vacgrammarParser::AndExpressionContext* vacgrammarParser::andExpression() {
   return andExpression(0);
}

vacgrammarParser::AndExpressionContext* vacgrammarParser::andExpression(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  vacgrammarParser::AndExpressionContext *_localctx = _tracker.createInstance<AndExpressionContext>(_ctx, parentState);
  vacgrammarParser::AndExpressionContext *previousContext = _localctx;
  size_t startState = 24;
  enterRecursionRule(_localctx, 24, vacgrammarParser::RuleAndExpression, precedence);

    

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(135);
    equalityExpression(0);
    _ctx->stop = _input->LT(-1);
    setState(145);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(143);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 10, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<AndExpressionContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleAndExpression);
          setState(137);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(138);
          match(vacgrammarParser::AND);
          setState(139);
          equalityExpression(0);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<AndExpressionContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleAndExpression);
          setState(140);

          if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
          setState(141);
          match(vacgrammarParser::ANDAND);
          setState(142);
          equalityExpression(0);
          break;
        }

        } 
      }
      setState(147);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- OrExpressionContext ------------------------------------------------------------------

vacgrammarParser::OrExpressionContext::OrExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::AndExpressionContext* vacgrammarParser::OrExpressionContext::andExpression() {
  return getRuleContext<vacgrammarParser::AndExpressionContext>(0);
}

vacgrammarParser::OrExpressionContext* vacgrammarParser::OrExpressionContext::orExpression() {
  return getRuleContext<vacgrammarParser::OrExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::OrExpressionContext::OR() {
  return getToken(vacgrammarParser::OR, 0);
}

tree::TerminalNode* vacgrammarParser::OrExpressionContext::OROR() {
  return getToken(vacgrammarParser::OROR, 0);
}


size_t vacgrammarParser::OrExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleOrExpression;
}

void vacgrammarParser::OrExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterOrExpression(this);
}

void vacgrammarParser::OrExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitOrExpression(this);
}


vacgrammarParser::OrExpressionContext* vacgrammarParser::orExpression() {
   return orExpression(0);
}

vacgrammarParser::OrExpressionContext* vacgrammarParser::orExpression(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  vacgrammarParser::OrExpressionContext *_localctx = _tracker.createInstance<OrExpressionContext>(_ctx, parentState);
  vacgrammarParser::OrExpressionContext *previousContext = _localctx;
  size_t startState = 26;
  enterRecursionRule(_localctx, 26, vacgrammarParser::RuleOrExpression, precedence);

    

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(149);
    andExpression(0);
    _ctx->stop = _input->LT(-1);
    setState(159);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        setState(157);
        _errHandler->sync(this);
        switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 12, _ctx)) {
        case 1: {
          _localctx = _tracker.createInstance<OrExpressionContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleOrExpression);
          setState(151);

          if (!(precpred(_ctx, 2))) throw FailedPredicateException(this, "precpred(_ctx, 2)");
          setState(152);
          match(vacgrammarParser::OR);
          setState(153);
          andExpression(0);
          break;
        }

        case 2: {
          _localctx = _tracker.createInstance<OrExpressionContext>(parentContext, parentState);
          pushNewRecursionContext(_localctx, startState, RuleOrExpression);
          setState(154);

          if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
          setState(155);
          match(vacgrammarParser::OROR);
          setState(156);
          andExpression(0);
          break;
        }

        } 
      }
      setState(161);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- ImplyExpressionContext ------------------------------------------------------------------

vacgrammarParser::ImplyExpressionContext::ImplyExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::OrExpressionContext* vacgrammarParser::ImplyExpressionContext::orExpression() {
  return getRuleContext<vacgrammarParser::OrExpressionContext>(0);
}

vacgrammarParser::ImplyExpressionContext* vacgrammarParser::ImplyExpressionContext::implyExpression() {
  return getRuleContext<vacgrammarParser::ImplyExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::ImplyExpressionContext::IMPLY() {
  return getToken(vacgrammarParser::IMPLY, 0);
}


size_t vacgrammarParser::ImplyExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleImplyExpression;
}

void vacgrammarParser::ImplyExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterImplyExpression(this);
}

void vacgrammarParser::ImplyExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitImplyExpression(this);
}


vacgrammarParser::ImplyExpressionContext* vacgrammarParser::implyExpression() {
   return implyExpression(0);
}

vacgrammarParser::ImplyExpressionContext* vacgrammarParser::implyExpression(int precedence) {
  ParserRuleContext *parentContext = _ctx;
  size_t parentState = getState();
  vacgrammarParser::ImplyExpressionContext *_localctx = _tracker.createInstance<ImplyExpressionContext>(_ctx, parentState);
  vacgrammarParser::ImplyExpressionContext *previousContext = _localctx;
  size_t startState = 28;
  enterRecursionRule(_localctx, 28, vacgrammarParser::RuleImplyExpression, precedence);

    

  auto onExit = finally([=] {
    unrollRecursionContexts(parentContext);
  });
  try {
    size_t alt;
    enterOuterAlt(_localctx, 1);
    setState(163);
    orExpression(0);
    _ctx->stop = _input->LT(-1);
    setState(170);
    _errHandler->sync(this);
    alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    while (alt != 2 && alt != atn::ATN::INVALID_ALT_NUMBER) {
      if (alt == 1) {
        if (!_parseListeners.empty())
          triggerExitRuleEvent();
        previousContext = _localctx;
        _localctx = _tracker.createInstance<ImplyExpressionContext>(parentContext, parentState);
        pushNewRecursionContext(_localctx, startState, RuleImplyExpression);
        setState(165);

        if (!(precpred(_ctx, 1))) throw FailedPredicateException(this, "precpred(_ctx, 1)");
        setState(166);
        match(vacgrammarParser::IMPLY);
        setState(167);
        orExpression(0); 
      }
      setState(172);
      _errHandler->sync(this);
      alt = getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx);
    }
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }
  return _localctx;
}

//----------------- ConditionalExpressionContext ------------------------------------------------------------------

vacgrammarParser::ConditionalExpressionContext::ConditionalExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::ImplyExpressionContext* vacgrammarParser::ConditionalExpressionContext::implyExpression() {
  return getRuleContext<vacgrammarParser::ImplyExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::ConditionalExpressionContext::QUESTION() {
  return getToken(vacgrammarParser::QUESTION, 0);
}

vacgrammarParser::ExpressionContext* vacgrammarParser::ConditionalExpressionContext::expression() {
  return getRuleContext<vacgrammarParser::ExpressionContext>(0);
}

tree::TerminalNode* vacgrammarParser::ConditionalExpressionContext::COLON() {
  return getToken(vacgrammarParser::COLON, 0);
}

vacgrammarParser::ConditionalExpressionContext* vacgrammarParser::ConditionalExpressionContext::conditionalExpression() {
  return getRuleContext<vacgrammarParser::ConditionalExpressionContext>(0);
}


size_t vacgrammarParser::ConditionalExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleConditionalExpression;
}

void vacgrammarParser::ConditionalExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterConditionalExpression(this);
}

void vacgrammarParser::ConditionalExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitConditionalExpression(this);
}

vacgrammarParser::ConditionalExpressionContext* vacgrammarParser::conditionalExpression() {
  ConditionalExpressionContext *_localctx = _tracker.createInstance<ConditionalExpressionContext>(_ctx, getState());
  enterRule(_localctx, 30, vacgrammarParser::RuleConditionalExpression);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(173);
    implyExpression(0);
    setState(179);
    _errHandler->sync(this);

    _la = _input->LA(1);
    if (_la == vacgrammarParser::QUESTION) {
      setState(174);
      match(vacgrammarParser::QUESTION);
      setState(175);
      expression();
      setState(176);
      match(vacgrammarParser::COLON);
      setState(177);
      conditionalExpression();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ExpressionContext ------------------------------------------------------------------

vacgrammarParser::ExpressionContext::ExpressionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

vacgrammarParser::ConditionalExpressionContext* vacgrammarParser::ExpressionContext::conditionalExpression() {
  return getRuleContext<vacgrammarParser::ConditionalExpressionContext>(0);
}


size_t vacgrammarParser::ExpressionContext::getRuleIndex() const {
  return vacgrammarParser::RuleExpression;
}

void vacgrammarParser::ExpressionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterExpression(this);
}

void vacgrammarParser::ExpressionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitExpression(this);
}

vacgrammarParser::ExpressionContext* vacgrammarParser::expression() {
  ExpressionContext *_localctx = _tracker.createInstance<ExpressionContext>(_ctx, getState());
  enterRule(_localctx, 32, vacgrammarParser::RuleExpression);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(181);
    conditionalExpression();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- R_rulesContext ------------------------------------------------------------------

vacgrammarParser::R_rulesContext::R_rulesContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::R_rulesContext::RULE() {
  return getToken(vacgrammarParser::RULE, 0);
}

tree::TerminalNode* vacgrammarParser::R_rulesContext::SEMI() {
  return getToken(vacgrammarParser::SEMI, 0);
}

std::vector<vacgrammarParser::Rule_elementContext *> vacgrammarParser::R_rulesContext::rule_element() {
  return getRuleContexts<vacgrammarParser::Rule_elementContext>();
}

vacgrammarParser::Rule_elementContext* vacgrammarParser::R_rulesContext::rule_element(size_t i) {
  return getRuleContext<vacgrammarParser::Rule_elementContext>(i);
}


size_t vacgrammarParser::R_rulesContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_rules;
}

void vacgrammarParser::R_rulesContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_rules(this);
}

void vacgrammarParser::R_rulesContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_rules(this);
}

vacgrammarParser::R_rulesContext* vacgrammarParser::r_rules() {
  R_rulesContext *_localctx = _tracker.createInstance<R_rulesContext>(_ctx, getState());
  enterRule(_localctx, 34, vacgrammarParser::RuleR_rules);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(183);
    match(vacgrammarParser::RULE);
    setState(187);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == vacgrammarParser::LEFTTUPLE) {
      setState(184);
      rule_element();
      setState(189);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(190);
    match(vacgrammarParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Rule_elementContext ------------------------------------------------------------------

vacgrammarParser::Rule_elementContext::Rule_elementContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::Rule_elementContext::LEFTTUPLE() {
  return getToken(vacgrammarParser::LEFTTUPLE, 0);
}

vacgrammarParser::AdminconditionContext* vacgrammarParser::Rule_elementContext::admincondition() {
  return getRuleContext<vacgrammarParser::AdminconditionContext>(0);
}

std::vector<tree::TerminalNode *> vacgrammarParser::Rule_elementContext::COMMA() {
  return getTokens(vacgrammarParser::COMMA);
}

tree::TerminalNode* vacgrammarParser::Rule_elementContext::COMMA(size_t i) {
  return getToken(vacgrammarParser::COMMA, i);
}

vacgrammarParser::PreconditionContext* vacgrammarParser::Rule_elementContext::precondition() {
  return getRuleContext<vacgrammarParser::PreconditionContext>(0);
}

tree::TerminalNode* vacgrammarParser::Rule_elementContext::COLON() {
  return getToken(vacgrammarParser::COLON, 0);
}

std::vector<vacgrammarParser::Normal_assignmentContext *> vacgrammarParser::Rule_elementContext::normal_assignment() {
  return getRuleContexts<vacgrammarParser::Normal_assignmentContext>();
}

vacgrammarParser::Normal_assignmentContext* vacgrammarParser::Rule_elementContext::normal_assignment(size_t i) {
  return getRuleContext<vacgrammarParser::Normal_assignmentContext>(i);
}

tree::TerminalNode* vacgrammarParser::Rule_elementContext::RIGHTTUPLE() {
  return getToken(vacgrammarParser::RIGHTTUPLE, 0);
}


size_t vacgrammarParser::Rule_elementContext::getRuleIndex() const {
  return vacgrammarParser::RuleRule_element;
}

void vacgrammarParser::Rule_elementContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterRule_element(this);
}

void vacgrammarParser::Rule_elementContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitRule_element(this);
}

vacgrammarParser::Rule_elementContext* vacgrammarParser::rule_element() {
  Rule_elementContext *_localctx = _tracker.createInstance<Rule_elementContext>(_ctx, getState());
  enterRule(_localctx, 36, vacgrammarParser::RuleRule_element);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(192);
    match(vacgrammarParser::LEFTTUPLE);
    setState(193);
    admincondition();
    setState(194);
    match(vacgrammarParser::COMMA);
    setState(195);
    precondition();
    setState(196);
    match(vacgrammarParser::COLON);
    setState(197);
    normal_assignment();
    setState(202);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == vacgrammarParser::COMMA) {
      setState(198);
      match(vacgrammarParser::COMMA);
      setState(199);
      normal_assignment();
      setState(204);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(205);
    match(vacgrammarParser::RIGHTTUPLE);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Normal_assignmentContext ------------------------------------------------------------------

vacgrammarParser::Normal_assignmentContext::Normal_assignmentContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::Normal_assignmentContext::DOT() {
  return getToken(vacgrammarParser::DOT, 0);
}

tree::TerminalNode* vacgrammarParser::Normal_assignmentContext::EQUAL() {
  return getToken(vacgrammarParser::EQUAL, 0);
}

tree::TerminalNode* vacgrammarParser::Normal_assignmentContext::Constant() {
  return getToken(vacgrammarParser::Constant, 0);
}

std::vector<tree::TerminalNode *> vacgrammarParser::Normal_assignmentContext::Identifier() {
  return getTokens(vacgrammarParser::Identifier);
}

tree::TerminalNode* vacgrammarParser::Normal_assignmentContext::Identifier(size_t i) {
  return getToken(vacgrammarParser::Identifier, i);
}


size_t vacgrammarParser::Normal_assignmentContext::getRuleIndex() const {
  return vacgrammarParser::RuleNormal_assignment;
}

void vacgrammarParser::Normal_assignmentContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterNormal_assignment(this);
}

void vacgrammarParser::Normal_assignmentContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitNormal_assignment(this);
}

vacgrammarParser::Normal_assignmentContext* vacgrammarParser::normal_assignment() {
  Normal_assignmentContext *_localctx = _tracker.createInstance<Normal_assignmentContext>(_ctx, getState());
  enterRule(_localctx, 38, vacgrammarParser::RuleNormal_assignment);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(207);
    dynamic_cast<Normal_assignmentContext *>(_localctx)->u = match(vacgrammarParser::Identifier);
    setState(208);
    match(vacgrammarParser::DOT);
    setState(209);
    dynamic_cast<Normal_assignmentContext *>(_localctx)->a = match(vacgrammarParser::Identifier);
    setState(210);
    match(vacgrammarParser::EQUAL);
    setState(211);
    match(vacgrammarParser::Constant);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PreconditionContext ------------------------------------------------------------------

vacgrammarParser::PreconditionContext::PreconditionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::PreconditionContext::TRUE() {
  return getToken(vacgrammarParser::TRUE, 0);
}

vacgrammarParser::ExpressionContext* vacgrammarParser::PreconditionContext::expression() {
  return getRuleContext<vacgrammarParser::ExpressionContext>(0);
}


size_t vacgrammarParser::PreconditionContext::getRuleIndex() const {
  return vacgrammarParser::RulePrecondition;
}

void vacgrammarParser::PreconditionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterPrecondition(this);
}

void vacgrammarParser::PreconditionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitPrecondition(this);
}

vacgrammarParser::PreconditionContext* vacgrammarParser::precondition() {
  PreconditionContext *_localctx = _tracker.createInstance<PreconditionContext>(_ctx, getState());
  enterRule(_localctx, 40, vacgrammarParser::RulePrecondition);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(215);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case vacgrammarParser::TRUE: {
        enterOuterAlt(_localctx, 1);
        setState(213);
        match(vacgrammarParser::TRUE);
        break;
      }

      case vacgrammarParser::LEFTPAREN:
      case vacgrammarParser::NOT:
      case vacgrammarParser::Identifier:
      case vacgrammarParser::Constant: {
        enterOuterAlt(_localctx, 2);
        setState(214);
        expression();
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

//----------------- AdminconditionContext ------------------------------------------------------------------

vacgrammarParser::AdminconditionContext::AdminconditionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::AdminconditionContext::TRUE() {
  return getToken(vacgrammarParser::TRUE, 0);
}

vacgrammarParser::ExpressionContext* vacgrammarParser::AdminconditionContext::expression() {
  return getRuleContext<vacgrammarParser::ExpressionContext>(0);
}


size_t vacgrammarParser::AdminconditionContext::getRuleIndex() const {
  return vacgrammarParser::RuleAdmincondition;
}

void vacgrammarParser::AdminconditionContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterAdmincondition(this);
}

void vacgrammarParser::AdminconditionContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitAdmincondition(this);
}

vacgrammarParser::AdminconditionContext* vacgrammarParser::admincondition() {
  AdminconditionContext *_localctx = _tracker.createInstance<AdminconditionContext>(_ctx, getState());
  enterRule(_localctx, 42, vacgrammarParser::RuleAdmincondition);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(219);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case vacgrammarParser::TRUE: {
        enterOuterAlt(_localctx, 1);
        setState(217);
        match(vacgrammarParser::TRUE);
        break;
      }

      case vacgrammarParser::LEFTPAREN:
      case vacgrammarParser::NOT:
      case vacgrammarParser::Identifier:
      case vacgrammarParser::Constant: {
        enterOuterAlt(_localctx, 2);
        setState(218);
        expression();
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

//----------------- R_queryContext ------------------------------------------------------------------

vacgrammarParser::R_queryContext::R_queryContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* vacgrammarParser::R_queryContext::QUERY() {
  return getToken(vacgrammarParser::QUERY, 0);
}

vacgrammarParser::Normal_assignmentContext* vacgrammarParser::R_queryContext::normal_assignment() {
  return getRuleContext<vacgrammarParser::Normal_assignmentContext>(0);
}

tree::TerminalNode* vacgrammarParser::R_queryContext::SEMI() {
  return getToken(vacgrammarParser::SEMI, 0);
}


size_t vacgrammarParser::R_queryContext::getRuleIndex() const {
  return vacgrammarParser::RuleR_query;
}

void vacgrammarParser::R_queryContext::enterRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->enterR_query(this);
}

void vacgrammarParser::R_queryContext::exitRule(tree::ParseTreeListener *listener) {
  auto parserListener = dynamic_cast<vacgrammarListener *>(listener);
  if (parserListener != nullptr)
    parserListener->exitR_query(this);
}

vacgrammarParser::R_queryContext* vacgrammarParser::r_query() {
  R_queryContext *_localctx = _tracker.createInstance<R_queryContext>(_ctx, getState());
  enterRule(_localctx, 44, vacgrammarParser::RuleR_query);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(221);
    match(vacgrammarParser::QUERY);
    setState(222);
    normal_assignment();
    setState(223);
    match(vacgrammarParser::SEMI);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

bool vacgrammarParser::sempred(RuleContext *context, size_t ruleIndex, size_t predicateIndex) {
  switch (ruleIndex) {
    case 11: return equalityExpressionSempred(dynamic_cast<EqualityExpressionContext *>(context), predicateIndex);
    case 12: return andExpressionSempred(dynamic_cast<AndExpressionContext *>(context), predicateIndex);
    case 13: return orExpressionSempred(dynamic_cast<OrExpressionContext *>(context), predicateIndex);
    case 14: return implyExpressionSempred(dynamic_cast<ImplyExpressionContext *>(context), predicateIndex);

  default:
    break;
  }
  return true;
}

bool vacgrammarParser::equalityExpressionSempred(EqualityExpressionContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 0: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool vacgrammarParser::andExpressionSempred(AndExpressionContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 1: return precpred(_ctx, 2);
    case 2: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool vacgrammarParser::orExpressionSempred(OrExpressionContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 3: return precpred(_ctx, 2);
    case 4: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

bool vacgrammarParser::implyExpressionSempred(ImplyExpressionContext *_localctx, size_t predicateIndex) {
  switch (predicateIndex) {
    case 5: return precpred(_ctx, 1);

  default:
    break;
  }
  return true;
}

// Static vars and initialization.
std::vector<dfa::DFA> vacgrammarParser::_decisionToDFA;
atn::PredictionContextCache vacgrammarParser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN vacgrammarParser::_atn;
std::vector<uint16_t> vacgrammarParser::_serializedATN;

std::vector<std::string> vacgrammarParser::_ruleNames = {
  "file", "r_start", "r_user", "user_element", "r_attr", "attr_element", 
  "r_init", "init_element", "init_assignment", "primaryExpression", "unaryExpression", 
  "equalityExpression", "andExpression", "orExpression", "implyExpression", 
  "conditionalExpression", "expression", "r_rules", "rule_element", "normal_assignment", 
  "precondition", "admincondition", "r_query"
};

std::vector<std::string> vacgrammarParser::_literalNames = {
  "", "", "", "", "", "", "'TRUE'", "'('", "';'", "'*'", "','", "'.'", "':'", 
  "'&'", "'&&'", "'|'", "'||'", "'='", "'=>'", "'?'", "')'", "'['", "']'", 
  "'!'", "'<'", "'>'"
};

std::vector<std::string> vacgrammarParser::_symbolicNames = {
  "", "USER", "ATTR", "INIT", "RULE", "QUERY", "TRUE", "LEFTPAREN", "SEMI", 
  "STAR", "COMMA", "DOT", "COLON", "AND", "ANDAND", "OR", "OROR", "EQUAL", 
  "IMPLY", "QUESTION", "RIGHTPAREN", "LEFTBRACKET", "RIGHTBRACKET", "NOT", 
  "LEFTTUPLE", "RIGHTTUPLE", "Identifier", "Constant", "Whitespace", "Newline", 
  "BlockComment", "LineComment"
};

dfa::Vocabulary vacgrammarParser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> vacgrammarParser::_tokenNames;

vacgrammarParser::Initializer::Initializer() {
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
    0x3, 0x21, 0xe4, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 0x9, 
    0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 0x4, 
    0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 0x9, 
    0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 0x4, 
    0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 0x12, 
    0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 0x15, 0x9, 
    0x15, 0x4, 0x16, 0x9, 0x16, 0x4, 0x17, 0x9, 0x17, 0x4, 0x18, 0x9, 0x18, 
    0x3, 0x2, 0x6, 0x2, 0x32, 0xa, 0x2, 0xd, 0x2, 0xe, 0x2, 0x33, 0x3, 0x3, 
    0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x5, 0x3, 0x3b, 0xa, 0x3, 0x3, 
    0x4, 0x3, 0x4, 0x6, 0x4, 0x3f, 0xa, 0x4, 0xd, 0x4, 0xe, 0x4, 0x40, 0x3, 
    0x4, 0x3, 0x4, 0x3, 0x5, 0x3, 0x5, 0x5, 0x5, 0x47, 0xa, 0x5, 0x3, 0x6, 
    0x3, 0x6, 0x6, 0x6, 0x4b, 0xa, 0x6, 0xd, 0x6, 0xe, 0x6, 0x4c, 0x3, 0x6, 
    0x3, 0x6, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x8, 
    0x3, 0x8, 0x6, 0x8, 0x58, 0xa, 0x8, 0xd, 0x8, 0xe, 0x8, 0x59, 0x3, 0x8, 
    0x3, 0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 0x3, 0x9, 
    0x7, 0x9, 0x64, 0xa, 0x9, 0xc, 0x9, 0xe, 0x9, 0x67, 0xb, 0x9, 0x3, 0x9, 
    0x3, 0x9, 0x3, 0xa, 0x3, 0xa, 0x3, 0xa, 0x3, 0xa, 0x3, 0xb, 0x3, 0xb, 
    0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x3, 0xb, 0x5, 0xb, 
    0x77, 0xa, 0xb, 0x3, 0xc, 0x3, 0xc, 0x3, 0xc, 0x5, 0xc, 0x7c, 0xa, 0xc, 
    0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x3, 0xd, 0x7, 0xd, 
    0x84, 0xa, 0xd, 0xc, 0xd, 0xe, 0xd, 0x87, 0xb, 0xd, 0x3, 0xe, 0x3, 0xe, 
    0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 0x3, 0xe, 
    0x7, 0xe, 0x92, 0xa, 0xe, 0xc, 0xe, 0xe, 0xe, 0x95, 0xb, 0xe, 0x3, 0xf, 
    0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 
    0x3, 0xf, 0x7, 0xf, 0xa0, 0xa, 0xf, 0xc, 0xf, 0xe, 0xf, 0xa3, 0xb, 0xf, 
    0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x7, 
    0x10, 0xab, 0xa, 0x10, 0xc, 0x10, 0xe, 0x10, 0xae, 0xb, 0x10, 0x3, 0x11, 
    0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x5, 0x11, 0xb6, 
    0xa, 0x11, 0x3, 0x12, 0x3, 0x12, 0x3, 0x13, 0x3, 0x13, 0x7, 0x13, 0xbc, 
    0xa, 0x13, 0xc, 0x13, 0xe, 0x13, 0xbf, 0xb, 0x13, 0x3, 0x13, 0x3, 0x13, 
    0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 
    0x14, 0x3, 0x14, 0x7, 0x14, 0xcb, 0xa, 0x14, 0xc, 0x14, 0xe, 0x14, 0xce, 
    0xb, 0x14, 0x3, 0x14, 0x3, 0x14, 0x3, 0x15, 0x3, 0x15, 0x3, 0x15, 0x3, 
    0x15, 0x3, 0x15, 0x3, 0x15, 0x3, 0x16, 0x3, 0x16, 0x5, 0x16, 0xda, 0xa, 
    0x16, 0x3, 0x17, 0x3, 0x17, 0x5, 0x17, 0xde, 0xa, 0x17, 0x3, 0x18, 0x3, 
    0x18, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 0x2, 0x6, 0x18, 0x1a, 0x1c, 0x1e, 
    0x19, 0x2, 0x4, 0x6, 0x8, 0xa, 0xc, 0xe, 0x10, 0x12, 0x14, 0x16, 0x18, 
    0x1a, 0x1c, 0x1e, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x2c, 0x2e, 0x2, 
    0x2, 0x2, 0xe4, 0x2, 0x31, 0x3, 0x2, 0x2, 0x2, 0x4, 0x3a, 0x3, 0x2, 
    0x2, 0x2, 0x6, 0x3c, 0x3, 0x2, 0x2, 0x2, 0x8, 0x44, 0x3, 0x2, 0x2, 0x2, 
    0xa, 0x48, 0x3, 0x2, 0x2, 0x2, 0xc, 0x50, 0x3, 0x2, 0x2, 0x2, 0xe, 0x55, 
    0x3, 0x2, 0x2, 0x2, 0x10, 0x5d, 0x3, 0x2, 0x2, 0x2, 0x12, 0x6a, 0x3, 
    0x2, 0x2, 0x2, 0x14, 0x76, 0x3, 0x2, 0x2, 0x2, 0x16, 0x7b, 0x3, 0x2, 
    0x2, 0x2, 0x18, 0x7d, 0x3, 0x2, 0x2, 0x2, 0x1a, 0x88, 0x3, 0x2, 0x2, 
    0x2, 0x1c, 0x96, 0x3, 0x2, 0x2, 0x2, 0x1e, 0xa4, 0x3, 0x2, 0x2, 0x2, 
    0x20, 0xaf, 0x3, 0x2, 0x2, 0x2, 0x22, 0xb7, 0x3, 0x2, 0x2, 0x2, 0x24, 
    0xb9, 0x3, 0x2, 0x2, 0x2, 0x26, 0xc2, 0x3, 0x2, 0x2, 0x2, 0x28, 0xd1, 
    0x3, 0x2, 0x2, 0x2, 0x2a, 0xd9, 0x3, 0x2, 0x2, 0x2, 0x2c, 0xdd, 0x3, 
    0x2, 0x2, 0x2, 0x2e, 0xdf, 0x3, 0x2, 0x2, 0x2, 0x30, 0x32, 0x5, 0x4, 
    0x3, 0x2, 0x31, 0x30, 0x3, 0x2, 0x2, 0x2, 0x32, 0x33, 0x3, 0x2, 0x2, 
    0x2, 0x33, 0x31, 0x3, 0x2, 0x2, 0x2, 0x33, 0x34, 0x3, 0x2, 0x2, 0x2, 
    0x34, 0x3, 0x3, 0x2, 0x2, 0x2, 0x35, 0x3b, 0x5, 0x6, 0x4, 0x2, 0x36, 
    0x3b, 0x5, 0xa, 0x6, 0x2, 0x37, 0x3b, 0x5, 0xe, 0x8, 0x2, 0x38, 0x3b, 
    0x5, 0x24, 0x13, 0x2, 0x39, 0x3b, 0x5, 0x2e, 0x18, 0x2, 0x3a, 0x35, 
    0x3, 0x2, 0x2, 0x2, 0x3a, 0x36, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x37, 0x3, 
    0x2, 0x2, 0x2, 0x3a, 0x38, 0x3, 0x2, 0x2, 0x2, 0x3a, 0x39, 0x3, 0x2, 
    0x2, 0x2, 0x3b, 0x5, 0x3, 0x2, 0x2, 0x2, 0x3c, 0x3e, 0x7, 0x3, 0x2, 
    0x2, 0x3d, 0x3f, 0x5, 0x8, 0x5, 0x2, 0x3e, 0x3d, 0x3, 0x2, 0x2, 0x2, 
    0x3f, 0x40, 0x3, 0x2, 0x2, 0x2, 0x40, 0x3e, 0x3, 0x2, 0x2, 0x2, 0x40, 
    0x41, 0x3, 0x2, 0x2, 0x2, 0x41, 0x42, 0x3, 0x2, 0x2, 0x2, 0x42, 0x43, 
    0x7, 0xa, 0x2, 0x2, 0x43, 0x7, 0x3, 0x2, 0x2, 0x2, 0x44, 0x46, 0x7, 
    0x1c, 0x2, 0x2, 0x45, 0x47, 0x7, 0xb, 0x2, 0x2, 0x46, 0x45, 0x3, 0x2, 
    0x2, 0x2, 0x46, 0x47, 0x3, 0x2, 0x2, 0x2, 0x47, 0x9, 0x3, 0x2, 0x2, 
    0x2, 0x48, 0x4a, 0x7, 0x4, 0x2, 0x2, 0x49, 0x4b, 0x5, 0xc, 0x7, 0x2, 
    0x4a, 0x49, 0x3, 0x2, 0x2, 0x2, 0x4b, 0x4c, 0x3, 0x2, 0x2, 0x2, 0x4c, 
    0x4a, 0x3, 0x2, 0x2, 0x2, 0x4c, 0x4d, 0x3, 0x2, 0x2, 0x2, 0x4d, 0x4e, 
    0x3, 0x2, 0x2, 0x2, 0x4e, 0x4f, 0x7, 0xa, 0x2, 0x2, 0x4f, 0xb, 0x3, 
    0x2, 0x2, 0x2, 0x50, 0x51, 0x7, 0x1c, 0x2, 0x2, 0x51, 0x52, 0x7, 0x17, 
    0x2, 0x2, 0x52, 0x53, 0x7, 0x1d, 0x2, 0x2, 0x53, 0x54, 0x7, 0x18, 0x2, 
    0x2, 0x54, 0xd, 0x3, 0x2, 0x2, 0x2, 0x55, 0x57, 0x7, 0x5, 0x2, 0x2, 
    0x56, 0x58, 0x5, 0x10, 0x9, 0x2, 0x57, 0x56, 0x3, 0x2, 0x2, 0x2, 0x58, 
    0x59, 0x3, 0x2, 0x2, 0x2, 0x59, 0x57, 0x3, 0x2, 0x2, 0x2, 0x59, 0x5a, 
    0x3, 0x2, 0x2, 0x2, 0x5a, 0x5b, 0x3, 0x2, 0x2, 0x2, 0x5b, 0x5c, 0x7, 
    0xa, 0x2, 0x2, 0x5c, 0xf, 0x3, 0x2, 0x2, 0x2, 0x5d, 0x5e, 0x7, 0x1a, 
    0x2, 0x2, 0x5e, 0x5f, 0x7, 0x1c, 0x2, 0x2, 0x5f, 0x60, 0x7, 0xe, 0x2, 
    0x2, 0x60, 0x65, 0x5, 0x12, 0xa, 0x2, 0x61, 0x62, 0x7, 0xc, 0x2, 0x2, 
    0x62, 0x64, 0x5, 0x12, 0xa, 0x2, 0x63, 0x61, 0x3, 0x2, 0x2, 0x2, 0x64, 
    0x67, 0x3, 0x2, 0x2, 0x2, 0x65, 0x63, 0x3, 0x2, 0x2, 0x2, 0x65, 0x66, 
    0x3, 0x2, 0x2, 0x2, 0x66, 0x68, 0x3, 0x2, 0x2, 0x2, 0x67, 0x65, 0x3, 
    0x2, 0x2, 0x2, 0x68, 0x69, 0x7, 0x1b, 0x2, 0x2, 0x69, 0x11, 0x3, 0x2, 
    0x2, 0x2, 0x6a, 0x6b, 0x7, 0x1c, 0x2, 0x2, 0x6b, 0x6c, 0x7, 0x13, 0x2, 
    0x2, 0x6c, 0x6d, 0x7, 0x1d, 0x2, 0x2, 0x6d, 0x13, 0x3, 0x2, 0x2, 0x2, 
    0x6e, 0x77, 0x7, 0x1d, 0x2, 0x2, 0x6f, 0x70, 0x7, 0x1c, 0x2, 0x2, 0x70, 
    0x71, 0x7, 0xd, 0x2, 0x2, 0x71, 0x77, 0x7, 0x1c, 0x2, 0x2, 0x72, 0x73, 
    0x7, 0x9, 0x2, 0x2, 0x73, 0x74, 0x5, 0x22, 0x12, 0x2, 0x74, 0x75, 0x7, 
    0x16, 0x2, 0x2, 0x75, 0x77, 0x3, 0x2, 0x2, 0x2, 0x76, 0x6e, 0x3, 0x2, 
    0x2, 0x2, 0x76, 0x6f, 0x3, 0x2, 0x2, 0x2, 0x76, 0x72, 0x3, 0x2, 0x2, 
    0x2, 0x77, 0x15, 0x3, 0x2, 0x2, 0x2, 0x78, 0x7c, 0x5, 0x14, 0xb, 0x2, 
    0x79, 0x7a, 0x7, 0x19, 0x2, 0x2, 0x7a, 0x7c, 0x5, 0x16, 0xc, 0x2, 0x7b, 
    0x78, 0x3, 0x2, 0x2, 0x2, 0x7b, 0x79, 0x3, 0x2, 0x2, 0x2, 0x7c, 0x17, 
    0x3, 0x2, 0x2, 0x2, 0x7d, 0x7e, 0x8, 0xd, 0x1, 0x2, 0x7e, 0x7f, 0x5, 
    0x16, 0xc, 0x2, 0x7f, 0x85, 0x3, 0x2, 0x2, 0x2, 0x80, 0x81, 0xc, 0x3, 
    0x2, 0x2, 0x81, 0x82, 0x7, 0x13, 0x2, 0x2, 0x82, 0x84, 0x5, 0x16, 0xc, 
    0x2, 0x83, 0x80, 0x3, 0x2, 0x2, 0x2, 0x84, 0x87, 0x3, 0x2, 0x2, 0x2, 
    0x85, 0x83, 0x3, 0x2, 0x2, 0x2, 0x85, 0x86, 0x3, 0x2, 0x2, 0x2, 0x86, 
    0x19, 0x3, 0x2, 0x2, 0x2, 0x87, 0x85, 0x3, 0x2, 0x2, 0x2, 0x88, 0x89, 
    0x8, 0xe, 0x1, 0x2, 0x89, 0x8a, 0x5, 0x18, 0xd, 0x2, 0x8a, 0x93, 0x3, 
    0x2, 0x2, 0x2, 0x8b, 0x8c, 0xc, 0x4, 0x2, 0x2, 0x8c, 0x8d, 0x7, 0xf, 
    0x2, 0x2, 0x8d, 0x92, 0x5, 0x18, 0xd, 0x2, 0x8e, 0x8f, 0xc, 0x3, 0x2, 
    0x2, 0x8f, 0x90, 0x7, 0x10, 0x2, 0x2, 0x90, 0x92, 0x5, 0x18, 0xd, 0x2, 
    0x91, 0x8b, 0x3, 0x2, 0x2, 0x2, 0x91, 0x8e, 0x3, 0x2, 0x2, 0x2, 0x92, 
    0x95, 0x3, 0x2, 0x2, 0x2, 0x93, 0x91, 0x3, 0x2, 0x2, 0x2, 0x93, 0x94, 
    0x3, 0x2, 0x2, 0x2, 0x94, 0x1b, 0x3, 0x2, 0x2, 0x2, 0x95, 0x93, 0x3, 
    0x2, 0x2, 0x2, 0x96, 0x97, 0x8, 0xf, 0x1, 0x2, 0x97, 0x98, 0x5, 0x1a, 
    0xe, 0x2, 0x98, 0xa1, 0x3, 0x2, 0x2, 0x2, 0x99, 0x9a, 0xc, 0x4, 0x2, 
    0x2, 0x9a, 0x9b, 0x7, 0x11, 0x2, 0x2, 0x9b, 0xa0, 0x5, 0x1a, 0xe, 0x2, 
    0x9c, 0x9d, 0xc, 0x3, 0x2, 0x2, 0x9d, 0x9e, 0x7, 0x12, 0x2, 0x2, 0x9e, 
    0xa0, 0x5, 0x1a, 0xe, 0x2, 0x9f, 0x99, 0x3, 0x2, 0x2, 0x2, 0x9f, 0x9c, 
    0x3, 0x2, 0x2, 0x2, 0xa0, 0xa3, 0x3, 0x2, 0x2, 0x2, 0xa1, 0x9f, 0x3, 
    0x2, 0x2, 0x2, 0xa1, 0xa2, 0x3, 0x2, 0x2, 0x2, 0xa2, 0x1d, 0x3, 0x2, 
    0x2, 0x2, 0xa3, 0xa1, 0x3, 0x2, 0x2, 0x2, 0xa4, 0xa5, 0x8, 0x10, 0x1, 
    0x2, 0xa5, 0xa6, 0x5, 0x1c, 0xf, 0x2, 0xa6, 0xac, 0x3, 0x2, 0x2, 0x2, 
    0xa7, 0xa8, 0xc, 0x3, 0x2, 0x2, 0xa8, 0xa9, 0x7, 0x14, 0x2, 0x2, 0xa9, 
    0xab, 0x5, 0x1c, 0xf, 0x2, 0xaa, 0xa7, 0x3, 0x2, 0x2, 0x2, 0xab, 0xae, 
    0x3, 0x2, 0x2, 0x2, 0xac, 0xaa, 0x3, 0x2, 0x2, 0x2, 0xac, 0xad, 0x3, 
    0x2, 0x2, 0x2, 0xad, 0x1f, 0x3, 0x2, 0x2, 0x2, 0xae, 0xac, 0x3, 0x2, 
    0x2, 0x2, 0xaf, 0xb5, 0x5, 0x1e, 0x10, 0x2, 0xb0, 0xb1, 0x7, 0x15, 0x2, 
    0x2, 0xb1, 0xb2, 0x5, 0x22, 0x12, 0x2, 0xb2, 0xb3, 0x7, 0xe, 0x2, 0x2, 
    0xb3, 0xb4, 0x5, 0x20, 0x11, 0x2, 0xb4, 0xb6, 0x3, 0x2, 0x2, 0x2, 0xb5, 
    0xb0, 0x3, 0x2, 0x2, 0x2, 0xb5, 0xb6, 0x3, 0x2, 0x2, 0x2, 0xb6, 0x21, 
    0x3, 0x2, 0x2, 0x2, 0xb7, 0xb8, 0x5, 0x20, 0x11, 0x2, 0xb8, 0x23, 0x3, 
    0x2, 0x2, 0x2, 0xb9, 0xbd, 0x7, 0x6, 0x2, 0x2, 0xba, 0xbc, 0x5, 0x26, 
    0x14, 0x2, 0xbb, 0xba, 0x3, 0x2, 0x2, 0x2, 0xbc, 0xbf, 0x3, 0x2, 0x2, 
    0x2, 0xbd, 0xbb, 0x3, 0x2, 0x2, 0x2, 0xbd, 0xbe, 0x3, 0x2, 0x2, 0x2, 
    0xbe, 0xc0, 0x3, 0x2, 0x2, 0x2, 0xbf, 0xbd, 0x3, 0x2, 0x2, 0x2, 0xc0, 
    0xc1, 0x7, 0xa, 0x2, 0x2, 0xc1, 0x25, 0x3, 0x2, 0x2, 0x2, 0xc2, 0xc3, 
    0x7, 0x1a, 0x2, 0x2, 0xc3, 0xc4, 0x5, 0x2c, 0x17, 0x2, 0xc4, 0xc5, 0x7, 
    0xc, 0x2, 0x2, 0xc5, 0xc6, 0x5, 0x2a, 0x16, 0x2, 0xc6, 0xc7, 0x7, 0xe, 
    0x2, 0x2, 0xc7, 0xcc, 0x5, 0x28, 0x15, 0x2, 0xc8, 0xc9, 0x7, 0xc, 0x2, 
    0x2, 0xc9, 0xcb, 0x5, 0x28, 0x15, 0x2, 0xca, 0xc8, 0x3, 0x2, 0x2, 0x2, 
    0xcb, 0xce, 0x3, 0x2, 0x2, 0x2, 0xcc, 0xca, 0x3, 0x2, 0x2, 0x2, 0xcc, 
    0xcd, 0x3, 0x2, 0x2, 0x2, 0xcd, 0xcf, 0x3, 0x2, 0x2, 0x2, 0xce, 0xcc, 
    0x3, 0x2, 0x2, 0x2, 0xcf, 0xd0, 0x7, 0x1b, 0x2, 0x2, 0xd0, 0x27, 0x3, 
    0x2, 0x2, 0x2, 0xd1, 0xd2, 0x7, 0x1c, 0x2, 0x2, 0xd2, 0xd3, 0x7, 0xd, 
    0x2, 0x2, 0xd3, 0xd4, 0x7, 0x1c, 0x2, 0x2, 0xd4, 0xd5, 0x7, 0x13, 0x2, 
    0x2, 0xd5, 0xd6, 0x7, 0x1d, 0x2, 0x2, 0xd6, 0x29, 0x3, 0x2, 0x2, 0x2, 
    0xd7, 0xda, 0x7, 0x8, 0x2, 0x2, 0xd8, 0xda, 0x5, 0x22, 0x12, 0x2, 0xd9, 
    0xd7, 0x3, 0x2, 0x2, 0x2, 0xd9, 0xd8, 0x3, 0x2, 0x2, 0x2, 0xda, 0x2b, 
    0x3, 0x2, 0x2, 0x2, 0xdb, 0xde, 0x7, 0x8, 0x2, 0x2, 0xdc, 0xde, 0x5, 
    0x22, 0x12, 0x2, 0xdd, 0xdb, 0x3, 0x2, 0x2, 0x2, 0xdd, 0xdc, 0x3, 0x2, 
    0x2, 0x2, 0xde, 0x2d, 0x3, 0x2, 0x2, 0x2, 0xdf, 0xe0, 0x7, 0x7, 0x2, 
    0x2, 0xe0, 0xe1, 0x5, 0x28, 0x15, 0x2, 0xe1, 0xe2, 0x7, 0xa, 0x2, 0x2, 
    0xe2, 0x2f, 0x3, 0x2, 0x2, 0x2, 0x16, 0x33, 0x3a, 0x40, 0x46, 0x4c, 
    0x59, 0x65, 0x76, 0x7b, 0x85, 0x91, 0x93, 0x9f, 0xa1, 0xac, 0xb5, 0xbd, 
    0xcc, 0xd9, 0xdd, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

vacgrammarParser::Initializer vacgrammarParser::_init;
