#include "Models.h"
#include "Lexer.h"
#include "Parser.h"

#include <fstream>
#include <sstream>

using namespace Parser;

int main(int argc, char const *argv[]) {
    std::ifstream t(argv[1]);

    std::stringstream buffer;
    buffer << t.rdbuf();
    std::string str = buffer.str();
    t.close();
    Scanner* sc = new Scanner(str);
    // for (const auto & to : sc->scanTokens()) {
    //     std::cout << to->ToString() << std::endl;
    // }

    HandParser *p = new HandParser(sc->scanTokens());
    p->parse();
    std::cout << p->getPolicy()->to_string();

    delete p;
    delete sc;

    return 0;
}