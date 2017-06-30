#ifndef PARSER_TRANSLATOR_H
#define PARSER_TRANSLATOR_H

#include "../SMT_Analysis.h"
#include "../Policy.h"

#include "Models.h"
#include "Lexer.h"
#include "Parser.h"
#include <exception>

namespace Parser {

class TranslatorException : public std::exception {
  private:
    std::string _message;
  public:
    TranslatorException(const std::string &msg = "");
    virtual const char* what() const noexcept override;
};

std::shared_ptr<SMT::arbac_policy> parse_new_ac(std::string);
} // Parser


#endif
