#pragma once

#include <string>

namespace Parser {
enum TokenType {
    // Single character tokens, One or two character tokens
    SEMI=0,
    STAR=1,
    COMMA=2,
    DOT=3,
    COLON=4,
    AND=5,
    ANDAND=6,
    OR=7,
    OROR=8,
    EQUAL=9,
    IMPLY=10,
    QUESTION=11,
    NOT=12,
    LEFTPAREN=13,
    RIGHTPAREN=14,
    LEFTBRACKET=15,
    RIGHTBRACKET=16,
    LEFTTUPLE=17,
    RIGHTTUPLE=18,

    // Literals
    IDENTIFIER=19,
    CONSTANT=20,

    // Keywords
    USER=21,
    ATTR=22,
    INIT=23,
    RULE=24,
    QUERY=25,
    VTRUE=26,
    ENDOFFILE=27
};


class Token {
  public:
    Token(TokenType type, std::string lexeme, int literal, int line):
        type(type), lexeme(lexeme), literal(literal), line(line) {}
    ~Token() {}


    std::string ToString(void) const;
    TokenType getType(void) const;
    std::string getLexeme(void) const;
    int getLiteral(void) const;
    int getLine(void) const;

  private:
    TokenType type;
    std::string lexeme;
    int literal;
    int line;
};

}