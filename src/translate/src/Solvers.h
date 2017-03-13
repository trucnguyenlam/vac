/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   SMT.h
 * Author: esteffin
 *
 * Created on 07 February 2017, 13:12
 */

#ifndef SOLVERS
#define SOLVERS

#include "SSA_Structs.h"
#include <string>
#include <yices.h>

// using namespace SSA;

namespace Solvers {

    class YicesSolver : public SSA::SMTSolver {
        public:
            YicesSolver(int bv_size);
            ~YicesSolver();
            void addAssertion(SSA::Expr expr) override;
            void declareVariable(SSA::Variablep variable, int add_init_assert) override;
            SMTSolver::Result getResult() override;
        private:
            context_t *ctx = NULL;
            term_t exprToTerm(SSA::Expr expr);
    };
}

#endif /* SMT */