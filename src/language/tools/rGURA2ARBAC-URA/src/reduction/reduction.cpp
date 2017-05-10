#include "reduction.h"

using namespace VAC;

std::string Reduction::reduceRGURAPolicy(const std::string filename) {
    std::ifstream stream;
    stream.open(filename);

    if (not stream.good()) {
        throw ParserException("Error: file" + std::string(filename) + " does not exist!");
    }

    antlr4::ANTLRInputStream input(stream);
    rGURALexer lexer(&input);
    antlr4::CommonTokenStream tokens(&lexer);

    // Create parser
    rGURAParser parser(&tokens);
    antlr4::tree::ParseTree * program = parser.file();

    // Work through parser tree to produce the model
    myrGURAListener listener;
    antlr4::tree::ParseTreeWalker::DEFAULT.walk(&listener, program);

    stream.close();

    rGURAPtr policy = listener.getPolicy();

    std::string ret = to_ARBACURA_policy(policy);
    return ret;
}

// Private
std::string Reduction::to_ARBACURA_policy(rGURAPtr policy) const {

}
