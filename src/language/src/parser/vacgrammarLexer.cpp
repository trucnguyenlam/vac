/* lexer header section */

// Generated from vacgrammarLexer.g4 by ANTLR 4.7

/* lexer precinclude section */

#include "vacgrammarLexer.h"




using namespace antlr4;

using namespace Parser;

vacgrammarLexer::vacgrammarLexer(CharStream *input) : Lexer(input) {
  _interpreter = new atn::LexerATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

vacgrammarLexer::~vacgrammarLexer() {
  delete _interpreter;
}

std::string vacgrammarLexer::getGrammarFileName() const {
  return "vacgrammarLexer.g4";
}

const std::vector<std::string>& vacgrammarLexer::getRuleNames() const {
  return _ruleNames;
}

const std::vector<std::string>& vacgrammarLexer::getChannelNames() const {
  return _channelNames;
}

const std::vector<std::string>& vacgrammarLexer::getModeNames() const {
  return _modeNames;
}

const std::vector<std::string>& vacgrammarLexer::getTokenNames() const {
  return _tokenNames;
}

dfa::Vocabulary& vacgrammarLexer::getVocabulary() const {
  return _vocabulary;
}

const std::vector<uint16_t> vacgrammarLexer::getSerializedATN() const {
  return _serializedATN;
}

const atn::ATN& vacgrammarLexer::getATN() const {
  return _atn;
}

/* lexer definitions section */



// Static vars and initialization.
std::vector<dfa::DFA> vacgrammarLexer::_decisionToDFA;
atn::PredictionContextCache vacgrammarLexer::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN vacgrammarLexer::_atn;
std::vector<uint16_t> vacgrammarLexer::_serializedATN;

std::vector<std::string> vacgrammarLexer::_ruleNames = {
  u8"USER", u8"ATTR", u8"INIT", u8"RULE", u8"QUERY", u8"TRUE", u8"LEFTPAREN", 
  u8"SEMI", u8"STAR", u8"COMMA", u8"DOT", u8"COLON", u8"AND", u8"ANDAND", 
  u8"OR", u8"OROR", u8"EQUAL", u8"IMPLY", u8"QUESTION", u8"RIGHTPAREN", 
  u8"LEFTBRACKET", u8"RIGHTBRACKET", u8"NOT", u8"LEFTTUPLE", u8"RIGHTTUPLE", 
  u8"Identifier", u8"IdentifierNondigit", u8"Nondigit", u8"Digit", u8"Constant", 
  u8"DecimalConstant", u8"NonzeroDigit", u8"Sign", u8"Whitespace", u8"Newline", 
  u8"BlockComment", u8"LineComment"
};

std::vector<std::string> vacgrammarLexer::_channelNames = {
  "DEFAULT_TOKEN_CHANNEL", "HIDDEN"
};

std::vector<std::string> vacgrammarLexer::_modeNames = {
  u8"DEFAULT_MODE"
};

std::vector<std::string> vacgrammarLexer::_literalNames = {
  "", "", "", "", "", "", u8"'TRUE'", u8"'('", u8"';'", u8"'*'", u8"','", 
  u8"'.'", u8"':'", u8"'&'", u8"'&&'", u8"'|'", u8"'||'", u8"'='", u8"'=>'", 
  u8"'?'", u8"')'", u8"'['", u8"']'", u8"'!'", u8"'<'", u8"'>'"
};

std::vector<std::string> vacgrammarLexer::_symbolicNames = {
  "", u8"USER", u8"ATTR", u8"INIT", u8"RULE", u8"QUERY", u8"TRUE", u8"LEFTPAREN", 
  u8"SEMI", u8"STAR", u8"COMMA", u8"DOT", u8"COLON", u8"AND", u8"ANDAND", 
  u8"OR", u8"OROR", u8"EQUAL", u8"IMPLY", u8"QUESTION", u8"RIGHTPAREN", 
  u8"LEFTBRACKET", u8"RIGHTBRACKET", u8"NOT", u8"LEFTTUPLE", u8"RIGHTTUPLE", 
  u8"Identifier", u8"Constant", u8"Whitespace", u8"Newline", u8"BlockComment", 
  u8"LineComment"
};

dfa::Vocabulary vacgrammarLexer::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> vacgrammarLexer::_tokenNames;

vacgrammarLexer::Initializer::Initializer() {
  // This code could be in a static initializer lambda, but VS doesn't allow access to private class members from there.
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
    0x2, 0x21, 0xea, 0x8, 0x1, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 
    0x4, 0x9, 0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 
    0x7, 0x4, 0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 
    0xb, 0x9, 0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 
    0xe, 0x4, 0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 
    0x4, 0x12, 0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 
    0x15, 0x9, 0x15, 0x4, 0x16, 0x9, 0x16, 0x4, 0x17, 0x9, 0x17, 0x4, 0x18, 
    0x9, 0x18, 0x4, 0x19, 0x9, 0x19, 0x4, 0x1a, 0x9, 0x1a, 0x4, 0x1b, 0x9, 
    0x1b, 0x4, 0x1c, 0x9, 0x1c, 0x4, 0x1d, 0x9, 0x1d, 0x4, 0x1e, 0x9, 0x1e, 
    0x4, 0x1f, 0x9, 0x1f, 0x4, 0x20, 0x9, 0x20, 0x4, 0x21, 0x9, 0x21, 0x4, 
    0x22, 0x9, 0x22, 0x4, 0x23, 0x9, 0x23, 0x4, 0x24, 0x9, 0x24, 0x4, 0x25, 
    0x9, 0x25, 0x4, 0x26, 0x9, 0x26, 0x3, 0x2, 0x3, 0x2, 0x3, 0x2, 0x3, 
    0x2, 0x3, 0x2, 0x3, 0x2, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 
    0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 
    0x4, 0x3, 0x4, 0x3, 0x4, 0x3, 0x4, 0x3, 0x4, 0x3, 0x5, 0x3, 0x5, 0x3, 
    0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x5, 0x3, 0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 
    0x6, 0x3, 0x6, 0x3, 0x6, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 0x7, 0x3, 
    0x7, 0x3, 0x8, 0x3, 0x8, 0x3, 0x9, 0x3, 0x9, 0x3, 0xa, 0x3, 0xa, 0x3, 
    0xb, 0x3, 0xb, 0x3, 0xc, 0x3, 0xc, 0x3, 0xd, 0x3, 0xd, 0x3, 0xe, 0x3, 
    0xe, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x3, 0x10, 0x3, 0x10, 0x3, 0x11, 
    0x3, 0x11, 0x3, 0x11, 0x3, 0x12, 0x3, 0x12, 0x3, 0x13, 0x3, 0x13, 0x3, 
    0x13, 0x3, 0x14, 0x3, 0x14, 0x3, 0x15, 0x3, 0x15, 0x3, 0x16, 0x3, 0x16, 
    0x3, 0x17, 0x3, 0x17, 0x3, 0x18, 0x3, 0x18, 0x3, 0x19, 0x3, 0x19, 0x3, 
    0x1a, 0x3, 0x1a, 0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x7, 0x1b, 0xa1, 0xa, 
    0x1b, 0xc, 0x1b, 0xe, 0x1b, 0xa4, 0xb, 0x1b, 0x3, 0x1c, 0x3, 0x1c, 0x3, 
    0x1d, 0x3, 0x1d, 0x3, 0x1e, 0x3, 0x1e, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x20, 
    0x5, 0x20, 0xaf, 0xa, 0x20, 0x3, 0x20, 0x3, 0x20, 0x7, 0x20, 0xb3, 0xa, 
    0x20, 0xc, 0x20, 0xe, 0x20, 0xb6, 0xb, 0x20, 0x3, 0x20, 0x5, 0x20, 0xb9, 
    0xa, 0x20, 0x3, 0x20, 0x5, 0x20, 0xbc, 0xa, 0x20, 0x3, 0x21, 0x3, 0x21, 
    0x3, 0x22, 0x3, 0x22, 0x3, 0x23, 0x6, 0x23, 0xc3, 0xa, 0x23, 0xd, 0x23, 
    0xe, 0x23, 0xc4, 0x3, 0x23, 0x3, 0x23, 0x3, 0x24, 0x3, 0x24, 0x5, 0x24, 
    0xcb, 0xa, 0x24, 0x3, 0x24, 0x5, 0x24, 0xce, 0xa, 0x24, 0x3, 0x24, 0x3, 
    0x24, 0x3, 0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 0x25, 0x7, 0x25, 0xd6, 0xa, 
    0x25, 0xc, 0x25, 0xe, 0x25, 0xd9, 0xb, 0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 
    0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 0x26, 0x3, 0x26, 0x3, 0x26, 0x3, 0x26, 
    0x7, 0x26, 0xe4, 0xa, 0x26, 0xc, 0x26, 0xe, 0x26, 0xe7, 0xb, 0x26, 0x3, 
    0x26, 0x3, 0x26, 0x3, 0xd7, 0x2, 0x27, 0x3, 0x3, 0x5, 0x4, 0x7, 0x5, 
    0x9, 0x6, 0xb, 0x7, 0xd, 0x8, 0xf, 0x9, 0x11, 0xa, 0x13, 0xb, 0x15, 
    0xc, 0x17, 0xd, 0x19, 0xe, 0x1b, 0xf, 0x1d, 0x10, 0x1f, 0x11, 0x21, 
    0x12, 0x23, 0x13, 0x25, 0x14, 0x27, 0x15, 0x29, 0x16, 0x2b, 0x17, 0x2d, 
    0x18, 0x2f, 0x19, 0x31, 0x1a, 0x33, 0x1b, 0x35, 0x1c, 0x37, 0x2, 0x39, 
    0x2, 0x3b, 0x2, 0x3d, 0x1d, 0x3f, 0x2, 0x41, 0x2, 0x43, 0x2, 0x45, 0x1e, 
    0x47, 0x1f, 0x49, 0x20, 0x4b, 0x21, 0x3, 0x2, 0x14, 0x4, 0x2, 0x57, 
    0x57, 0x77, 0x77, 0x4, 0x2, 0x55, 0x55, 0x75, 0x75, 0x4, 0x2, 0x47, 
    0x47, 0x67, 0x67, 0x4, 0x2, 0x54, 0x54, 0x74, 0x74, 0x4, 0x2, 0x43, 
    0x43, 0x63, 0x63, 0x4, 0x2, 0x56, 0x56, 0x76, 0x76, 0x4, 0x2, 0x4b, 
    0x4b, 0x6b, 0x6b, 0x4, 0x2, 0x44, 0x44, 0x64, 0x64, 0x4, 0x2, 0x50, 
    0x50, 0x70, 0x70, 0x4, 0x2, 0x4e, 0x4e, 0x6e, 0x6e, 0x4, 0x2, 0x53, 
    0x53, 0x73, 0x73, 0x4, 0x2, 0x5b, 0x5b, 0x7b, 0x7b, 0x5, 0x2, 0x43, 
    0x5c, 0x61, 0x61, 0x63, 0x7c, 0x3, 0x2, 0x32, 0x3b, 0x3, 0x2, 0x33, 
    0x3b, 0x4, 0x2, 0x2d, 0x2d, 0x2f, 0x2f, 0x4, 0x2, 0xb, 0xb, 0x22, 0x22, 
    0x4, 0x2, 0xc, 0xc, 0xf, 0xf, 0x2, 0xee, 0x2, 0x3, 0x3, 0x2, 0x2, 0x2, 
    0x2, 0x5, 0x3, 0x2, 0x2, 0x2, 0x2, 0x7, 0x3, 0x2, 0x2, 0x2, 0x2, 0x9, 
    0x3, 0x2, 0x2, 0x2, 0x2, 0xb, 0x3, 0x2, 0x2, 0x2, 0x2, 0xd, 0x3, 0x2, 
    0x2, 0x2, 0x2, 0xf, 0x3, 0x2, 0x2, 0x2, 0x2, 0x11, 0x3, 0x2, 0x2, 0x2, 
    0x2, 0x13, 0x3, 0x2, 0x2, 0x2, 0x2, 0x15, 0x3, 0x2, 0x2, 0x2, 0x2, 0x17, 
    0x3, 0x2, 0x2, 0x2, 0x2, 0x19, 0x3, 0x2, 0x2, 0x2, 0x2, 0x1b, 0x3, 0x2, 
    0x2, 0x2, 0x2, 0x1d, 0x3, 0x2, 0x2, 0x2, 0x2, 0x1f, 0x3, 0x2, 0x2, 0x2, 
    0x2, 0x21, 0x3, 0x2, 0x2, 0x2, 0x2, 0x23, 0x3, 0x2, 0x2, 0x2, 0x2, 0x25, 
    0x3, 0x2, 0x2, 0x2, 0x2, 0x27, 0x3, 0x2, 0x2, 0x2, 0x2, 0x29, 0x3, 0x2, 
    0x2, 0x2, 0x2, 0x2b, 0x3, 0x2, 0x2, 0x2, 0x2, 0x2d, 0x3, 0x2, 0x2, 0x2, 
    0x2, 0x2f, 0x3, 0x2, 0x2, 0x2, 0x2, 0x31, 0x3, 0x2, 0x2, 0x2, 0x2, 0x33, 
    0x3, 0x2, 0x2, 0x2, 0x2, 0x35, 0x3, 0x2, 0x2, 0x2, 0x2, 0x3d, 0x3, 0x2, 
    0x2, 0x2, 0x2, 0x45, 0x3, 0x2, 0x2, 0x2, 0x2, 0x47, 0x3, 0x2, 0x2, 0x2, 
    0x2, 0x49, 0x3, 0x2, 0x2, 0x2, 0x2, 0x4b, 0x3, 0x2, 0x2, 0x2, 0x3, 0x4d, 
    0x3, 0x2, 0x2, 0x2, 0x5, 0x53, 0x3, 0x2, 0x2, 0x2, 0x7, 0x5e, 0x3, 0x2, 
    0x2, 0x2, 0x9, 0x63, 0x3, 0x2, 0x2, 0x2, 0xb, 0x69, 0x3, 0x2, 0x2, 0x2, 
    0xd, 0x6f, 0x3, 0x2, 0x2, 0x2, 0xf, 0x74, 0x3, 0x2, 0x2, 0x2, 0x11, 
    0x76, 0x3, 0x2, 0x2, 0x2, 0x13, 0x78, 0x3, 0x2, 0x2, 0x2, 0x15, 0x7a, 
    0x3, 0x2, 0x2, 0x2, 0x17, 0x7c, 0x3, 0x2, 0x2, 0x2, 0x19, 0x7e, 0x3, 
    0x2, 0x2, 0x2, 0x1b, 0x80, 0x3, 0x2, 0x2, 0x2, 0x1d, 0x82, 0x3, 0x2, 
    0x2, 0x2, 0x1f, 0x85, 0x3, 0x2, 0x2, 0x2, 0x21, 0x87, 0x3, 0x2, 0x2, 
    0x2, 0x23, 0x8a, 0x3, 0x2, 0x2, 0x2, 0x25, 0x8c, 0x3, 0x2, 0x2, 0x2, 
    0x27, 0x8f, 0x3, 0x2, 0x2, 0x2, 0x29, 0x91, 0x3, 0x2, 0x2, 0x2, 0x2b, 
    0x93, 0x3, 0x2, 0x2, 0x2, 0x2d, 0x95, 0x3, 0x2, 0x2, 0x2, 0x2f, 0x97, 
    0x3, 0x2, 0x2, 0x2, 0x31, 0x99, 0x3, 0x2, 0x2, 0x2, 0x33, 0x9b, 0x3, 
    0x2, 0x2, 0x2, 0x35, 0x9d, 0x3, 0x2, 0x2, 0x2, 0x37, 0xa5, 0x3, 0x2, 
    0x2, 0x2, 0x39, 0xa7, 0x3, 0x2, 0x2, 0x2, 0x3b, 0xa9, 0x3, 0x2, 0x2, 
    0x2, 0x3d, 0xab, 0x3, 0x2, 0x2, 0x2, 0x3f, 0xbb, 0x3, 0x2, 0x2, 0x2, 
    0x41, 0xbd, 0x3, 0x2, 0x2, 0x2, 0x43, 0xbf, 0x3, 0x2, 0x2, 0x2, 0x45, 
    0xc2, 0x3, 0x2, 0x2, 0x2, 0x47, 0xcd, 0x3, 0x2, 0x2, 0x2, 0x49, 0xd1, 
    0x3, 0x2, 0x2, 0x2, 0x4b, 0xdf, 0x3, 0x2, 0x2, 0x2, 0x4d, 0x4e, 0x9, 
    0x2, 0x2, 0x2, 0x4e, 0x4f, 0x9, 0x3, 0x2, 0x2, 0x4f, 0x50, 0x9, 0x4, 
    0x2, 0x2, 0x50, 0x51, 0x9, 0x5, 0x2, 0x2, 0x51, 0x52, 0x9, 0x3, 0x2, 
    0x2, 0x52, 0x4, 0x3, 0x2, 0x2, 0x2, 0x53, 0x54, 0x9, 0x6, 0x2, 0x2, 
    0x54, 0x55, 0x9, 0x7, 0x2, 0x2, 0x55, 0x56, 0x9, 0x7, 0x2, 0x2, 0x56, 
    0x57, 0x9, 0x5, 0x2, 0x2, 0x57, 0x58, 0x9, 0x8, 0x2, 0x2, 0x58, 0x59, 
    0x9, 0x9, 0x2, 0x2, 0x59, 0x5a, 0x9, 0x2, 0x2, 0x2, 0x5a, 0x5b, 0x9, 
    0x7, 0x2, 0x2, 0x5b, 0x5c, 0x9, 0x4, 0x2, 0x2, 0x5c, 0x5d, 0x9, 0x3, 
    0x2, 0x2, 0x5d, 0x6, 0x3, 0x2, 0x2, 0x2, 0x5e, 0x5f, 0x9, 0x8, 0x2, 
    0x2, 0x5f, 0x60, 0x9, 0xa, 0x2, 0x2, 0x60, 0x61, 0x9, 0x8, 0x2, 0x2, 
    0x61, 0x62, 0x9, 0x7, 0x2, 0x2, 0x62, 0x8, 0x3, 0x2, 0x2, 0x2, 0x63, 
    0x64, 0x9, 0x5, 0x2, 0x2, 0x64, 0x65, 0x9, 0x2, 0x2, 0x2, 0x65, 0x66, 
    0x9, 0xb, 0x2, 0x2, 0x66, 0x67, 0x9, 0x4, 0x2, 0x2, 0x67, 0x68, 0x9, 
    0x3, 0x2, 0x2, 0x68, 0xa, 0x3, 0x2, 0x2, 0x2, 0x69, 0x6a, 0x9, 0xc, 
    0x2, 0x2, 0x6a, 0x6b, 0x9, 0x2, 0x2, 0x2, 0x6b, 0x6c, 0x9, 0x4, 0x2, 
    0x2, 0x6c, 0x6d, 0x9, 0x5, 0x2, 0x2, 0x6d, 0x6e, 0x9, 0xd, 0x2, 0x2, 
    0x6e, 0xc, 0x3, 0x2, 0x2, 0x2, 0x6f, 0x70, 0x7, 0x56, 0x2, 0x2, 0x70, 
    0x71, 0x7, 0x54, 0x2, 0x2, 0x71, 0x72, 0x7, 0x57, 0x2, 0x2, 0x72, 0x73, 
    0x7, 0x47, 0x2, 0x2, 0x73, 0xe, 0x3, 0x2, 0x2, 0x2, 0x74, 0x75, 0x7, 
    0x2a, 0x2, 0x2, 0x75, 0x10, 0x3, 0x2, 0x2, 0x2, 0x76, 0x77, 0x7, 0x3d, 
    0x2, 0x2, 0x77, 0x12, 0x3, 0x2, 0x2, 0x2, 0x78, 0x79, 0x7, 0x2c, 0x2, 
    0x2, 0x79, 0x14, 0x3, 0x2, 0x2, 0x2, 0x7a, 0x7b, 0x7, 0x2e, 0x2, 0x2, 
    0x7b, 0x16, 0x3, 0x2, 0x2, 0x2, 0x7c, 0x7d, 0x7, 0x30, 0x2, 0x2, 0x7d, 
    0x18, 0x3, 0x2, 0x2, 0x2, 0x7e, 0x7f, 0x7, 0x3c, 0x2, 0x2, 0x7f, 0x1a, 
    0x3, 0x2, 0x2, 0x2, 0x80, 0x81, 0x7, 0x28, 0x2, 0x2, 0x81, 0x1c, 0x3, 
    0x2, 0x2, 0x2, 0x82, 0x83, 0x7, 0x28, 0x2, 0x2, 0x83, 0x84, 0x7, 0x28, 
    0x2, 0x2, 0x84, 0x1e, 0x3, 0x2, 0x2, 0x2, 0x85, 0x86, 0x7, 0x7e, 0x2, 
    0x2, 0x86, 0x20, 0x3, 0x2, 0x2, 0x2, 0x87, 0x88, 0x7, 0x7e, 0x2, 0x2, 
    0x88, 0x89, 0x7, 0x7e, 0x2, 0x2, 0x89, 0x22, 0x3, 0x2, 0x2, 0x2, 0x8a, 
    0x8b, 0x7, 0x3f, 0x2, 0x2, 0x8b, 0x24, 0x3, 0x2, 0x2, 0x2, 0x8c, 0x8d, 
    0x7, 0x3f, 0x2, 0x2, 0x8d, 0x8e, 0x7, 0x40, 0x2, 0x2, 0x8e, 0x26, 0x3, 
    0x2, 0x2, 0x2, 0x8f, 0x90, 0x7, 0x41, 0x2, 0x2, 0x90, 0x28, 0x3, 0x2, 
    0x2, 0x2, 0x91, 0x92, 0x7, 0x2b, 0x2, 0x2, 0x92, 0x2a, 0x3, 0x2, 0x2, 
    0x2, 0x93, 0x94, 0x7, 0x5d, 0x2, 0x2, 0x94, 0x2c, 0x3, 0x2, 0x2, 0x2, 
    0x95, 0x96, 0x7, 0x5f, 0x2, 0x2, 0x96, 0x2e, 0x3, 0x2, 0x2, 0x2, 0x97, 
    0x98, 0x7, 0x23, 0x2, 0x2, 0x98, 0x30, 0x3, 0x2, 0x2, 0x2, 0x99, 0x9a, 
    0x7, 0x3e, 0x2, 0x2, 0x9a, 0x32, 0x3, 0x2, 0x2, 0x2, 0x9b, 0x9c, 0x7, 
    0x40, 0x2, 0x2, 0x9c, 0x34, 0x3, 0x2, 0x2, 0x2, 0x9d, 0xa2, 0x5, 0x37, 
    0x1c, 0x2, 0x9e, 0xa1, 0x5, 0x37, 0x1c, 0x2, 0x9f, 0xa1, 0x5, 0x3b, 
    0x1e, 0x2, 0xa0, 0x9e, 0x3, 0x2, 0x2, 0x2, 0xa0, 0x9f, 0x3, 0x2, 0x2, 
    0x2, 0xa1, 0xa4, 0x3, 0x2, 0x2, 0x2, 0xa2, 0xa0, 0x3, 0x2, 0x2, 0x2, 
    0xa2, 0xa3, 0x3, 0x2, 0x2, 0x2, 0xa3, 0x36, 0x3, 0x2, 0x2, 0x2, 0xa4, 
    0xa2, 0x3, 0x2, 0x2, 0x2, 0xa5, 0xa6, 0x5, 0x39, 0x1d, 0x2, 0xa6, 0x38, 
    0x3, 0x2, 0x2, 0x2, 0xa7, 0xa8, 0x9, 0xe, 0x2, 0x2, 0xa8, 0x3a, 0x3, 
    0x2, 0x2, 0x2, 0xa9, 0xaa, 0x9, 0xf, 0x2, 0x2, 0xaa, 0x3c, 0x3, 0x2, 
    0x2, 0x2, 0xab, 0xac, 0x5, 0x3f, 0x20, 0x2, 0xac, 0x3e, 0x3, 0x2, 0x2, 
    0x2, 0xad, 0xaf, 0x5, 0x43, 0x22, 0x2, 0xae, 0xad, 0x3, 0x2, 0x2, 0x2, 
    0xae, 0xaf, 0x3, 0x2, 0x2, 0x2, 0xaf, 0xb0, 0x3, 0x2, 0x2, 0x2, 0xb0, 
    0xb4, 0x5, 0x41, 0x21, 0x2, 0xb1, 0xb3, 0x5, 0x3b, 0x1e, 0x2, 0xb2, 
    0xb1, 0x3, 0x2, 0x2, 0x2, 0xb3, 0xb6, 0x3, 0x2, 0x2, 0x2, 0xb4, 0xb2, 
    0x3, 0x2, 0x2, 0x2, 0xb4, 0xb5, 0x3, 0x2, 0x2, 0x2, 0xb5, 0xbc, 0x3, 
    0x2, 0x2, 0x2, 0xb6, 0xb4, 0x3, 0x2, 0x2, 0x2, 0xb7, 0xb9, 0x5, 0x43, 
    0x22, 0x2, 0xb8, 0xb7, 0x3, 0x2, 0x2, 0x2, 0xb8, 0xb9, 0x3, 0x2, 0x2, 
    0x2, 0xb9, 0xba, 0x3, 0x2, 0x2, 0x2, 0xba, 0xbc, 0x5, 0x3b, 0x1e, 0x2, 
    0xbb, 0xae, 0x3, 0x2, 0x2, 0x2, 0xbb, 0xb8, 0x3, 0x2, 0x2, 0x2, 0xbc, 
    0x40, 0x3, 0x2, 0x2, 0x2, 0xbd, 0xbe, 0x9, 0x10, 0x2, 0x2, 0xbe, 0x42, 
    0x3, 0x2, 0x2, 0x2, 0xbf, 0xc0, 0x9, 0x11, 0x2, 0x2, 0xc0, 0x44, 0x3, 
    0x2, 0x2, 0x2, 0xc1, 0xc3, 0x9, 0x12, 0x2, 0x2, 0xc2, 0xc1, 0x3, 0x2, 
    0x2, 0x2, 0xc3, 0xc4, 0x3, 0x2, 0x2, 0x2, 0xc4, 0xc2, 0x3, 0x2, 0x2, 
    0x2, 0xc4, 0xc5, 0x3, 0x2, 0x2, 0x2, 0xc5, 0xc6, 0x3, 0x2, 0x2, 0x2, 
    0xc6, 0xc7, 0x8, 0x23, 0x2, 0x2, 0xc7, 0x46, 0x3, 0x2, 0x2, 0x2, 0xc8, 
    0xca, 0x7, 0xf, 0x2, 0x2, 0xc9, 0xcb, 0x7, 0xc, 0x2, 0x2, 0xca, 0xc9, 
    0x3, 0x2, 0x2, 0x2, 0xca, 0xcb, 0x3, 0x2, 0x2, 0x2, 0xcb, 0xce, 0x3, 
    0x2, 0x2, 0x2, 0xcc, 0xce, 0x7, 0xc, 0x2, 0x2, 0xcd, 0xc8, 0x3, 0x2, 
    0x2, 0x2, 0xcd, 0xcc, 0x3, 0x2, 0x2, 0x2, 0xce, 0xcf, 0x3, 0x2, 0x2, 
    0x2, 0xcf, 0xd0, 0x8, 0x24, 0x2, 0x2, 0xd0, 0x48, 0x3, 0x2, 0x2, 0x2, 
    0xd1, 0xd2, 0x7, 0x31, 0x2, 0x2, 0xd2, 0xd3, 0x7, 0x2c, 0x2, 0x2, 0xd3, 
    0xd7, 0x3, 0x2, 0x2, 0x2, 0xd4, 0xd6, 0xb, 0x2, 0x2, 0x2, 0xd5, 0xd4, 
    0x3, 0x2, 0x2, 0x2, 0xd6, 0xd9, 0x3, 0x2, 0x2, 0x2, 0xd7, 0xd8, 0x3, 
    0x2, 0x2, 0x2, 0xd7, 0xd5, 0x3, 0x2, 0x2, 0x2, 0xd8, 0xda, 0x3, 0x2, 
    0x2, 0x2, 0xd9, 0xd7, 0x3, 0x2, 0x2, 0x2, 0xda, 0xdb, 0x7, 0x2c, 0x2, 
    0x2, 0xdb, 0xdc, 0x7, 0x31, 0x2, 0x2, 0xdc, 0xdd, 0x3, 0x2, 0x2, 0x2, 
    0xdd, 0xde, 0x8, 0x25, 0x2, 0x2, 0xde, 0x4a, 0x3, 0x2, 0x2, 0x2, 0xdf, 
    0xe0, 0x7, 0x31, 0x2, 0x2, 0xe0, 0xe1, 0x7, 0x31, 0x2, 0x2, 0xe1, 0xe5, 
    0x3, 0x2, 0x2, 0x2, 0xe2, 0xe4, 0xa, 0x13, 0x2, 0x2, 0xe3, 0xe2, 0x3, 
    0x2, 0x2, 0x2, 0xe4, 0xe7, 0x3, 0x2, 0x2, 0x2, 0xe5, 0xe3, 0x3, 0x2, 
    0x2, 0x2, 0xe5, 0xe6, 0x3, 0x2, 0x2, 0x2, 0xe6, 0xe8, 0x3, 0x2, 0x2, 
    0x2, 0xe7, 0xe5, 0x3, 0x2, 0x2, 0x2, 0xe8, 0xe9, 0x8, 0x26, 0x2, 0x2, 
    0xe9, 0x4c, 0x3, 0x2, 0x2, 0x2, 0xe, 0x2, 0xa0, 0xa2, 0xae, 0xb4, 0xb8, 
    0xbb, 0xc4, 0xca, 0xcd, 0xd7, 0xe5, 0x3, 0x8, 0x2, 0x2, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

vacgrammarLexer::Initializer vacgrammarLexer::_init;
