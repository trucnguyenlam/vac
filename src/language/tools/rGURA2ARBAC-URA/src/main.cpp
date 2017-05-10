// @author: trucnguyenlam@gmail.com
// @description:
//      main executable
// TODO:
//
// @changeLog:
//    2017.05.09   Initial version

#include <iostream>
#include "utils/args.hxx"
#include "reduction/reduction.h"

using namespace VAC;

int main(int argc, const char* argv[]) {
    // Parse argument
    args::ArgumentParser cmdparser("This is a reduction from rGURA to ARBAC-URA policy.", "");
    args::HelpFlag help(cmdparser, "help", "Display this help menu", {'h', "help"});
    args::ValueFlag<std::string> input(cmdparser, "X", "input policy (rGURA format)", {'i', "input"});
    args::ValueFlag<std::string> output(cmdparser, "X", "output policy (ARBAC-URA format)", {'o', "output"});

    try {
        cmdparser.ParseCLI(argc, argv);
    } catch (args::Help) {
        std::cout << cmdparser;
        return 0;
    } catch (args::ParseError e) {
        std::cerr << e.what() << std::endl;
        std::cerr << cmdparser;
        return 1;
    } catch (args::ValidationError e) {
        std::cerr << e.what() << std::endl;
        std::cerr << cmdparser;
        return 1;
    }

    if (!input) {
        std::cerr << "Input file is required" << std::endl;
    }

    std::string inputFilename = args::get(input);
    std::string outputpolicy = Reduction().reduceRGURAPolicy(inputFilename);

    std::string outputFilename = inputFilename + ".arbac";
    if (output) {
        outputFilename = args::get(output);
    }

    std::ofstream stream;
    stream.open(outputFilename);
    if (stream.good()){
        stream << outputpolicy;
    }
    stream.close();

    return 0;
}