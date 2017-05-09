// @author: trucnguyenlam@gmail.com
// @description:
//      main executable
// TODO:
//
// @changeLog:
//    2017.05.09   Initial version

#include <iostream>
#include "args.hxx"
#include "rGURALexer.h"
#include "rGURAParser.h"
#include "myrGURAListener.h"
#include "myrGURAListener.h"

using namespace VAC;

int main(int argc, const char* argv[]) {
    std::ifstream stream;
    stream.open(argv[1]);

    antlr4::ANTLRInputStream input(stream);
    rGURALexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);

    // Create parser
    rGURAParser parser(&tokens);
    antlr4::tree::ParseTree * program = parser.file();

    // Work through parser tree to produce the model
    myrGURAListener listener;
    antlr4::tree::ParseTreeWalker::DEFAULT.walk(&listener, program);

    return 0;
}