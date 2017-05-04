/*
* @Author: Truc Nguyen Lam
* @Date:   2017-05-03 13:37:26
* @Last Modified by:   Truc Nguyen Lam
* @Last Modified time: 2017-05-03 22:53:09
*/

#include <iostream>
#include "vacgrammarLexer.h"
#include "vacgrammarParser.h"
#include "MyListener.h"
#include "Models.h"


using namespace antlr4;
using namespace SMT;

int main(int argc, const char* argv[]) {
    std::ifstream stream;
    stream.open(argv[1]);

    ANTLRInputStream input(stream);
    vacgrammarLexer lexer(&input);
    CommonTokenStream tokens(&lexer);

    // Create parser
    vacgrammarParser parser(&tokens);
    tree::ParseTree * program = parser.file();

    MyListener listener;
    tree::ParseTreeWalker::DEFAULT.walk(&listener, program);

    return 0;
}