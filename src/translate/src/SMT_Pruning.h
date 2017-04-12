#pragma once

#include <memory>
#include <SMT.h>


namespace SMT {

    template <typename TVar, typename TExpr>
    class PruningR6 {
        private:
        std::shared_ptr<SMTFactory<TVar, TExpr>> solver;
        public:
        PruningR6(std::shared_ptr<SMTFactory<TVar, TExpr>> solver);
        bool apply(int rule_index, bool is_ca);
    };

    void prune(char* inputFile, FILE* output);
    void transform_2_lazycseq_r6(char* inputFile, FILE *outputFile, int rule_index, int is_ca);
    
    // template <typename TVar, typename TExpr>
    bool apply_r6(int rule_index, bool is_ca);
}
