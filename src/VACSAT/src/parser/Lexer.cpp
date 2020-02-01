#include "Lexer.h"

#include <iostream>

using namespace Parser;

namespace {
int length(int start, int current) {
    return current - start;
}
}

Scanner::Scanner(std::string source):
    source(source) {
    start = 0;
    current = 0;
    line = 1;

    keywords.insert(std::make_pair<std::string, TokenType>("USERS", USER));
    keywords.insert(std::make_pair<std::string, TokenType>("Users", USER));
    keywords.insert(std::make_pair<std::string, TokenType>("ATTRIBUTES", ATTR));
    keywords.insert(std::make_pair<std::string, TokenType>("Attributes", ATTR));
    keywords.insert(std::make_pair<std::string, TokenType>("INIT", INIT));
    keywords.insert(std::make_pair<std::string, TokenType>("RULES", RULE));
    keywords.insert(std::make_pair<std::string, TokenType>("Rules", RULE));
    keywords.insert(std::make_pair<std::string, TokenType>("QUERY", QUERY));
    keywords.insert(std::make_pair<std::string, TokenType>("Query", QUERY));
    keywords.insert(std::make_pair<std::string, TokenType>("TRUE", VTRUE));

}

Scanner::~Scanner() {
    tokens.clear();
}

std::vector<Token *>& Scanner::scanTokens(void) {
    while (!isAtEnd()) {
        start = current;
        scanToken();
    }
    tokens.push_back(new Token(ENDOFFILE, "", 0, line));
    return tokens;
}

std::vector<Token *>& Scanner::getTokens(void) {
    return tokens;
}



void Scanner::scanToken(void) {
    char c = advance();
    switch (c) {
    case '(': addToken(LEFTPAREN); break;
    case ')': addToken(RIGHTPAREN); break;
    case '[': addToken(LEFTBRACKET); break;
    case ']': addToken(RIGHTBRACKET); break;
    case ';': addToken(SEMI); break;
    case '*': addToken(STAR); break;
    case ',': addToken(COMMA); break;
    case '.': addToken(DOT); break;
    case ':': addToken(COLON); break;
    case '?': addToken(QUESTION); break;
    case '!': addToken(NOT); break;
    case '<': addToken(LEFTTUPLE); break;
    case '>': addToken(RIGHTTUPLE); break;
    // Two characters
    case '&': addToken(match('&') ? ANDAND : AND); break;
    case '|': addToken(match('|') ? OROR : OR); break;
    case '=': addToken(match('>') ? IMPLY : EQUAL); break;
    case '/':
        if (match('/')) {
            while (peek() != '\n' && !isAtEnd()) advance();
        } else {
            throw "LexerError: line " + std::to_string(line) + ": / is unexpected!\n";
        }
        break;
    case ' ':
    case '\r':
    case '\t':
        break;

    case '\n':
        line++;
        break;

    case '+':
    case '-':
        advance();
        number(c);
        break;
    default:
        if (isDigit(c)) {
            number('+');
        } else if (isAlpha(c)) {
            identifier();
        } else {
            throw "LexerError: line " + std::to_string(line) \
            + ": unexpected character " + std::to_string(c) + "\n";
        }
        break;
    }
}

char Scanner::peek(void) const {
    // TODO:
    if (isAtEnd()) return '\0';
    return source.at(current);
}

char  Scanner::peekNext(void) const {
    if (current + 1 >= source.length()) return '\0';
    return source.at(current + 1);
}

void Scanner::identifier(void) {
    while (isAlphaNumeric(peek())) advance();

    std::string text = source.substr(start, length(start, current));

    auto it = keywords.find(text);
    if (it == keywords.end()) {
        addToken(IDENTIFIER);
    } else {
        addToken(it->second);
    }
}

void Scanner::number(char sign) {
    while (isDigit(peek())) advance();
    std::string str = sign + source.substr(start, length(start, current));
    addToken(CONSTANT, std::stoi(str));
}

bool Scanner::match(char expected) {
    if (isAtEnd()) return false;
    if (source.at(current) != expected) return false;
    current++;
    return true;
}

bool Scanner::isAlphaNumeric(char c) const {
    return isAlpha(c) || isDigit(c);
}

bool Scanner::isAlpha(char c) const {
    return (c >= 'a' && c <= 'z') ||
           (c >= 'A' && c <= 'Z') ||
           c == '_';
}

// bool Scanner::isSign(char c) const {
//     return c == '+' || c == '-';
// }

bool Scanner::isDigit(char c) const {
    return c >= '0' && c <= '9';
}

bool Scanner::isAtEnd(void) const {
    return current >= source.length();
}

char Scanner::advance(void) {
    current++;
    return source.at(current - 1);
}

void Scanner::addToken(TokenType type) {
    addToken(type, 0);

}

void Scanner::addToken(TokenType type, int literal) {
    std::string text = source.substr(start, length(start, current));
    tokens.push_back(new Token(type, text, literal, line));
}
