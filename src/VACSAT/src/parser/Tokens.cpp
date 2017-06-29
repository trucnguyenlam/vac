#include "Tokens.h"

using namespace Parser;

std::string Token::ToString(void) const{
    return std::to_string(type) + " " + lexeme;
}

TokenType Token::getType(void) const{
    return type;
}

std::string Token::getLexeme(void) const{
    return lexeme;
}

int Token::getLiteral(void) const{
    return literal;
}

int Token::getLine(void) const{
    return line;
}

