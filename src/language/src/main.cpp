// @author: trucnguyenlam@gmail.com
// @description:
//      main executable to demonstrate the parser
// TODO:
//
// @changeLog:
//    2017.05.01   Initial version

#include <iostream>
#include "parser/vacgrammarLexer.h"
#include "parser/vacgrammarParser.h"
#include "parser/MyListener.h"
#include "parser/Models.h"

using namespace Parser;

int main(int argc, const char* argv[]) {
    std::ifstream stream;
    stream.open(argv[1]);

    antlr4::ANTLRInputStream input(stream);
    vacgrammarLexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);

    // Create parser
    vacgrammarParser parser(&tokens);
    antlr4::tree::ParseTree * program = parser.file();

    // Work through parser tree to produce the model
    MyListener listener;
    antlr4::tree::ParseTreeWalker::DEFAULT.walk(&listener, program);

    // Retrieve policy
    ModelPtr policy = listener.getPolicy();

    // Print policy
    std::cout << policy->to_string();
    return 0;
}