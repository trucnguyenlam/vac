
// Generated from rGURA.g4 by ANTLR 4.7

#pragma once


#include "antlr4-runtime.h"


namespace VAC {


class  rGURALexer : public antlr4::Lexer {
public:
  enum {
    USER = 1, ATTR_S = 2, ATTR_M = 3, SCOPE = 4, AR = 5, UAS = 6, UAM = 7, 
    RULE = 8, SPEC = 9, TRUE = 10, NOT = 11, LEFTPAREN = 12, SEMI = 13, 
    STAR = 14, COMMA = 15, DOT = 16, COLON = 17, AND = 18, OR = 19, EQUAL = 20, 
    IMPLY = 21, QUESTION = 22, RIGHTPAREN = 23, LEFTBRACKET = 24, RIGHTBRACKET = 25, 
    LEFTTUPLE = 26, RIGHTTUPLE = 27, Identifier = 28, Constant = 29, Whitespace = 30, 
    Newline = 31, BlockComment = 32, LineComment = 33
  };

  rGURALexer(antlr4::CharStream *input);
  ~rGURALexer();

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

}  // namespace VAC
