
// Generated from vacgrammar.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"




class  vacgrammarLexer : public antlr4::Lexer {
public:
  enum {
    USER = 1, ATTR = 2, INIT = 3, RULE = 4, QUERY = 5, TRUE = 6, LEFTPAREN = 7, 
    SEMI = 8, STAR = 9, COMMA = 10, DOT = 11, COLON = 12, AND = 13, ANDAND = 14, 
    OR = 15, OROR = 16, EQUAL = 17, IMPLY = 18, QUESTION = 19, RIGHTPAREN = 20, 
    LEFTBRACKET = 21, RIGHTBRACKET = 22, NOT = 23, LEFTTUPLE = 24, RIGHTTUPLE = 25, 
    Identifier = 26, Constant = 27, DecimalConstant = 28, Whitespace = 29, 
    Newline = 30, BlockComment = 31, LineComment = 32
  };

  vacgrammarLexer(antlr4::CharStream *input);
  ~vacgrammarLexer();

  virtual std::string getGrammarFileName() const override;
  virtual const std::vector<std::string>& getRuleNames() const override;

  virtual const std::vector<std::string>& getChannelNames() const override;
  virtual const std::vector<std::string>& getModeNames() const override;
  virtual const std::vector<std::string>& getTokenNames() const override; // deprecated, use vocabulary instead
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;

  virtual const std::vector<uint16_t> getSerializedATN() const override;
  virtual const antlr4::atn::ATN& getATN() const override;

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;
  static std::vector<std::string> _channelNames;
  static std::vector<std::string> _modeNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  // Individual action functions triggered by action() above.

  // Individual semantic predicate functions triggered by sempred() above.

  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

