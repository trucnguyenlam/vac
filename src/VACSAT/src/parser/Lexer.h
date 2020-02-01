#pragma once

#include "Tokens.h"

#include <vector>
#include <map>


namespace Parser
{

class Scanner {
public:
    Scanner(std::string source);
    ~Scanner();

    std::vector<Token *>& scanTokens(void);
    std::vector<Token *>& getTokens(void);

private:
    void scanToken(void);
    char peek(void) const;
    char peekNext(void) const;
    void identifier(void);
    void number(char);
    bool match(char);
    bool isAlphaNumeric(char) const;
    bool isAlpha(char) const;
    bool isDigit(char) const;
    bool isAtEnd(void) const;
    char advance(void);
    void addToken(TokenType type);
    void addToken(TokenType type, int literal);

    std::string source;
    std::vector<Token *> tokens;
    int start;
    int current;
    int line;

    std::map<std::string, TokenType> keywords;
};



}