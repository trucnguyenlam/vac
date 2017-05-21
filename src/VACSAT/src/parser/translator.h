#ifndef PARSER_TRANSLATOR_H
#define PARSER_TRANSLATOR_H

#include "../SMT_Analysis.h"
#include "../Policy.h"

#include "vacgrammarLexer.h"
#include "vacgrammarParser.h"
#include "MyListener.h"
#include "Models.h"

namespace Parser {
    std::shared_ptr<SMT::arbac_policy> parse_new_ac(std::string);
} // Parser


#endif
