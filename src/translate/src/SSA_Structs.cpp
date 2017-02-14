#include "SSA_Structs.h"

extern "C" {
/*STMT OPS*/
    void freeStmt(Stmt stmt) {
        switch (stmt->type) {
            case ASSERT:
                freeAssertion((Assertion*)stmt->value);
                break;
            case ASSUME:
                freeAssumption((Assumption*)stmt->value);
                break;
            case ASSIGNMENT:
                freeAssignment((Assignment*)stmt->value);
                break;
            default:
                break;
        }
        free(stmt);
    }
    char* printStmt(Stmt stmt) {
        switch (stmt->type) {
            case ASSERT:
                return printAssertion((Assertion*)stmt->value);
                break;
            case ASSUME:
                return printAssumption((Assumption*)stmt->value);
                break;
            case ASSIGNMENT:
                return printAssignment((Assignment*)stmt->value);
                break;
            case COMMENT:
                return printComment((Comment*)stmt->value);
                break;
            default:
                break;
        }
        return NULL;
    }
    
/*ASSIGNMENT OPS*/
    Stmt createAssignment(Variable *var, Expr val) {
        Assignment* cnt = (Assignment *) malloc(sizeof(Assignment));
        cnt->variable = var;
        cnt->value = val;
        cnt->useless = 0;
        Stmt outer = (Stmt) malloc(sizeof(_Stmt));
        outer->type = ASSIGNMENT;
        outer->value = cnt;
        return outer;
    }
    Assignment* simplifyAssignment(Assignment *assign) {
        //        Expr nval = simplifyExpr(assign->value);
        //        if (expr->type != COND_EXPR) {
        //            assign->value = nval;
        //            assign->useless = true;
        //        }
        //        return assign;
    }
    void freeAssignment(Assignment *assign) {
        /*Cannot free variable cause could be shared...*/
        //freeVariable(assign->variable);
        freeExpr(assign->value);
        free(assign);
    }
    char* printAssignment(Assignment *assign) {
        char* str;
        char* var = printVariable(assign->variable);
        char* expr = printExpr(assign->value);
        int base_length = strlen(var) + strlen(assign_op) + strlen(expr) + strlen(line_end) + 1;
        if (assign->useless) {
            str = (char*) calloc(base_length + 15, sizeof(char));
            sprintf(str, "/* %s %s %s%s */", var, assign_op, expr, line_end);
        }
        else {
            str = (char*) calloc(base_length + 15, sizeof(char));
            sprintf(str, "%s %s %s%s", var, assign_op, expr, line_end);
        }
        free(var);
        free(expr);
        return str;
    }
    
/*ASSERTION OPS*/
    Stmt createAssertion(Expr cond) {
        Assertion* cnt = (Assertion *) malloc(sizeof(Assertion));
        cnt->assertion = cond;
        Stmt outer = (Stmt) malloc(sizeof(_Stmt));
        outer->type = ASSERT;
        outer->value = cnt;
        return outer;
    }
    void freeAssertion(Assertion *assert) {
        freeExpr(assert->assertion);
        free(assert);
    }
    char* printAssertion(Assertion *assert) {
        char* str;
        char* asserted = printExpr(assert->assertion);
        int base_length = strlen(asserted) + strlen(assert_str) + strlen(line_end) + 1 + 10;
        str = (char*) calloc(base_length, sizeof(char));
        sprintf(str, "%s(%s)%s", assert_str, asserted, line_end);
        free(asserted);
        return str;
    }
    
/*ASSUMPTION OPS*/
    Stmt createAssumption(Expr cond) {
        Assumption* cnt = (Assumption *) malloc(sizeof(Assumption));
        cnt->assume = cond;
        Stmt outer = (Stmt) malloc(sizeof(_Stmt));
        outer->type = ASSUME;
        outer->value = cnt;
        return outer;
    }
    void freeAssumption(Assumption *assumption) {
        freeExpr(assumption->assume);
        free(assumption);
    }
    char* printAssumption(Assumption *assumption) {
        char* str;
        char* assump = printExpr(assumption->assume);
        int base_length = strlen(assump) + strlen(assume_str) + strlen(line_end) + 1 + 10;
        str = (char*) calloc(base_length, sizeof(char));
        sprintf(str, "%s(%s)%s", assume_str, assump, line_end);
        free(assump);
        return str;
    }

/*COMMENT OPS*/
    Stmt createComment(const char* comment) {
        Comment* cnt = (Comment*) malloc(sizeof(Comment));
        cnt->comment = (char*) calloc(strlen(comment) + 1, sizeof(char));
        strcpy(cnt->comment, comment);
        Stmt outer = (Stmt) malloc(sizeof(_Stmt));
        outer->type = COMMENT;
        outer->value = cnt;
        return outer;
    }
    void freeComment(Comment* comment) {
        free(comment->comment);
        free(comment);
    }
    char* printComment(Comment* comment) {
        char* str = (char*) calloc(strlen(comment->comment) + 10, sizeof(char));
        if (strlen(comment->comment) > 1) {
            sprintf(str, "/* %s */", comment->comment);
        }
        else {
            sprintf(str, " ");
        }
        return str;
    }
    
/*EXPR OPS*/
    void freeExpr(Expr expr) {
        switch (expr->type) {
            case AND_EXPR:
                freeAndExpr((AndExpr*) expr->value);
                break;
            case COND_EXPR:
                freeCondExpr((CondExpr*) expr->value);
                break;
            case CONSTANT:
                freeConstant((Constant*) expr->value);
                break;
            case NONDET_EXPR:
                freeNondetExpr((NondetExpr*) expr->value);
                break;
            case NOT_EXPR:
                freeNotExpr((NotExpr*) expr->value);
                break;
            case OR_EXPR:
                freeOrExpr((OrExpr*) expr->value);
                break;
            case VARIABLE:
                /*Cannot free variable cause could be shared...*/
                //freeVariable((Variable*) expr->value);
                break;
            case EQ_EXPR:
                freeEqExpr((EqExpr*) expr->value);
            default:
                break;
        }
        free(expr);
    }
    Expr simplifyExpr(Expr expr) {
        //        switch (expr->type) {
        //            case AND_EXPR:
        //                freeAndExpr((AndExpr) expr->value);
        //                break;
        //            case COND_EXPR:
        //                freeCondExpr((CondExpr) expr->value);
        //                break;
        //            case CONSTANT:
        //                freeConstant((Constant) expr->value);
        //                break;
        //            case NONDET_EXPR:
        //                freeNondetExpr((NondetExpr) expr->value);
        //                break;
        //            case NOT_EXPR:
        //                freeNotExpr((NotExpr) expr->value);
        //                break;
        //            case OR_EXPR:
        //                OrExpr((OrExpr) expr->value);
        //                break;
        //            case VARIABLE:
        //                freeVariable((Variable) expr->value);
        //                break;
        //            case VARIABLE:
        //                freeVariable((Variable) expr->value);
        //                break;
        //            case EQ_EXPR:
        //                freeVariable((EqExpr) expr->value);
        //                break;
        //            default:
        //                break;
        //        }
    }
    char* printExpr(Expr expr) {
        switch (expr->type) {
            case AND_EXPR:
                return printAndExpr((AndExpr*) expr->value);
                break;
            case COND_EXPR:
                return printCondExpr((CondExpr*) expr->value);
                break;
            case CONSTANT:
                return printConstant((Constant*) expr->value);
                break;
            case NONDET_EXPR:
                return printNondetExpr((NondetExpr*) expr->value);
                break;
            case NOT_EXPR:
                return printNotExpr((NotExpr*) expr->value);
                break;
            case OR_EXPR:
                return printOrExpr((OrExpr*) expr->value);
                break;
            case VARIABLE:
                return printVariable((Variable*) expr->value);
                break;
            case EQ_EXPR:
                return printEqExpr((EqExpr*) expr->value);
                break;
            default:
                break;
        }
        return NULL;
    }    
    
/*VARIABLE OPS*/
    Variable* createVariable(const char* name, int idx, Expr value, int no_simplify) {
        Variable *var = (Variable*) malloc(sizeof(Variable));
        var->name = (char*) calloc(strlen(name) + 1, sizeof(char));
        strcpy(var->name, name);
        var->idx = idx;
        var->no_simplify = no_simplify;
        var->value = value;
        return var;
    }
    Expr createVariableExpr(const char* name, int idx, Expr value, int no_simplify) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = VARIABLE;
        Variable *var = createVariable(name, idx, value, no_simplify);
        outer->value = var;
        return outer;
    }
    void freeVariable(Variable *var) {
        // if (var->value != NULL) {
        //     freeExpr(var->value);
        // }
        free(var->name);
        free(var);
    }    
    Expr simplifyVariable(Expr var) {
        //        Variable *inner = (Variable*) var->value;
        //        if (inner->value != NULL) {
        //            Expr res = simplifyExpr(inner->value);
        //            free(inner->name);
        //            free(inner);
        //            free(var);
        //            return res;
        //        }
        //        else {
        //            printf("Could not simplify variable %s.\nRetrning NULL\n", printVariable(var));
        //            return NULL;
        //        }
    }
    char* printVariable(Variable *var) {
        // if (var->value != NULL) {
        //     return printExpr(var->value);
        // }
        // else {
        char* str = (char*) calloc(strlen(var->name) + 50, sizeof(char));
        sprintf(str, "%s_%d", var->name, var->idx);
        return str;
        // }
    }
         
/*CONSTANT OPS*/
    Constant* createConstant(int value) {
        Constant *c = (Constant*) malloc(sizeof(Constant));
        c->value = value;
        return c;
    }
    Expr createConstantExpr(int value) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = CONSTANT;
        Constant *c = createConstant(value);
        outer->value = c;
        return outer;
    }
    void freeConstant(Constant *constant) {
        free(constant);
    }    
    Expr simplifyConstant(Expr constant) {
        //        Expr res = createConstant(((Constant)constant->value)->value);
        //        freeExpr(constant);
        //        return res;
    }
    char* printConstant(Constant *constant) {
        char* str = (char*) calloc(50, sizeof(char));
        sprintf(str, "%d", constant->value);
        return str;
    }

/*OR OPS*/
    Expr createOrExpr(Expr lhs, Expr rhs) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = OR_EXPR;
        OrExpr *oe = (OrExpr*) malloc(sizeof(OrExpr));
        oe->lhs = lhs;
        oe->rhs = rhs;
        outer->value = oe;
        return outer;
    }
    void freeOrExpr(OrExpr* or_expr) {
        freeExpr(or_expr->lhs);
        freeExpr(or_expr->rhs);
        free(or_expr);
    }
    Expr simplifyOrExpr(Expr* or_expr) {
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
    char* printOrExpr(OrExpr* or_expr) {
        char* str;
        char* lhs = printExpr(or_expr->lhs);
        char* rhs = printExpr(or_expr->rhs);
        int base_size = strlen(lhs) + strlen(rhs) + strlen(or_op) + 15;
        str = (char*) calloc(base_size, sizeof(char));
        sprintf(str, "(%s %s %s)", lhs, or_op, rhs);
        free(lhs);
        free(rhs);
        return str;
    }

/*AND OPS*/
    Expr createAndExpr(Expr lhs, Expr rhs) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = AND_EXPR;
        AndExpr *ae = (AndExpr*) malloc(sizeof(AndExpr));
        ae->lhs = lhs;
        ae->rhs = rhs;
        outer->value = ae;
        return outer;
    }
    void freeAndExpr(AndExpr* and_expr) {
        freeExpr(and_expr->lhs);
        freeExpr(and_expr->rhs);
        free(and_expr);
    }
    Expr simplifyAndExpr(Expr* and_expr) {
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
    char* printAndExpr(AndExpr* and_expr) {
        char* str;
        char* lhs = printExpr(and_expr->lhs);
        char* rhs = printExpr(and_expr->rhs);
        int base_size = strlen(lhs) + strlen(rhs) + strlen(and_op) + 15;
        str = (char*) calloc(base_size, sizeof(char));
        sprintf(str, "(%s %s %s)", lhs, and_op, rhs);
        free(lhs);
        free(rhs);
        return str;
    }
    
/*NOT OPS*/
    Expr createNotExpr(Expr expr) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = NOT_EXPR;
        NotExpr *ne = (NotExpr*) malloc(sizeof(NotExpr));
        ne->expr = expr;
        outer->value = ne;
        return outer;
    }
    void freeNotExpr(NotExpr* not_expr) {
        freeExpr(not_expr->expr);
        free(not_expr);
    }
    Expr simplifyNotExpr(Expr* not_expr) {
        //        OrExpr inner = (OrExpr) or_expr->value;
        //        Expr nlhs, nrhs;
        //        nlhs = simplifyExpr(inner->lhs);
        //        if (nlhs->type == CONSTANT) {
        //            int v = (Constant) nlhs->value;
        //            if (v) {
        //                freeExpr(or_expr);
        //                return (Constant) nlhs;
        //            }
        //            else {
        //                return rhs->simplify();
        //            }
        //        }
        //        nrhs = rhs->simplify();
        //        if (nrhs.type == CONSTANT) {
        //            if (((Constant) nrhs).value) {
        //                return (Constant) nrhs;
        //            }
        //            else {
        //                return nlhs;
        //            }
        //        }
        //        return new OrExpr(nlhs, nrhs);
    }
    char* printNotExpr(NotExpr* not_expr) {
        char* str;
        char* expr = printExpr(not_expr->expr);
        int base_size = strlen(expr) + strlen(not_op) + 15;
        str = (char*) calloc(base_size, sizeof(char));
        sprintf(str, "%s(%s)", not_op, expr);
        free(expr);
        return str;
    }

/*COND OPS*/
    Expr createCondExpr(Expr cond, Expr choice1, Expr choice2) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = COND_EXPR;
        CondExpr *ce = (CondExpr*) malloc(sizeof(CondExpr));
        ce->cond = cond;
        ce->choice1 = choice1;
        ce->choice2 = choice2;
        outer->value = ce;
        return outer;
    }    
    void freeCondExpr(CondExpr* cond_expr) {
        freeExpr(cond_expr->cond);
        freeExpr(cond_expr->choice1);
        freeExpr(cond_expr->choice2);
        free(cond_expr);
    }
    Expr simplifyCondExpr(CondExpr* cond_expr)  {
        //        Exprc ncond = cond->simplify();
        //        if (ncond->type == CONSTANT) {
        //            if (((shared_ptr<Constant>) ncond)->value) {
        //                return choice1->simplify();
        //            }
        //            else {
        //                return choice2->simplify();
        //            }
        //        }
        //
        //        return new CondExpr(ncond, choice1->simplify(), choice2->simplify());
    }
    char* printCondExpr(CondExpr* cond_expr) {
        char* str;
        char* cond = printExpr(cond_expr->cond);
        char* ch1 = printExpr(cond_expr->choice1);
        char* ch2 = printExpr(cond_expr->choice2);
        int base_size = strlen(cond) + strlen(ch1) + strlen(ch2) + 20;
        str = (char*) calloc(base_size, sizeof(char));
        sprintf(str, "((%s) ? (%s) : (%s))", cond, ch1, ch2);
        free(cond);
        free(ch1);
        free(ch2);
        return str;
    }

/*NONDET OPS*/
    Expr createNondetExpr(Type type) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = NONDET_EXPR;
        NondetExpr *ne = (NondetExpr*) malloc(sizeof(NondetExpr));
        ne->nondet_type = type;
        outer->value = ne;
        return outer;
    }
    void freeNondetExpr(NondetExpr* nondet_expr) {
        free(nondet_expr);
    }
    Expr simplifyNondetExpr(Expr nondet_expr) {
        //
    }
    char* printNondetExpr(NondetExpr* nondet_expr) {
        const char* ty_name = nondet_expr->nondet_type == INT ? "int" : "bool";
        char* typed_str = (char*) calloc(strlen(nondet_str) + 20, sizeof(char));
        sprintf(typed_str, nondet_str, ty_name);
        char* str = (char*) calloc(strlen(typed_str) + 5, sizeof(char));
        sprintf(str, "%s()", typed_str);
        return str;
    }
    
/*EQ OPS*/
    Expr createEqExpr(Expr lhs, Expr rhs) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = EQ_EXPR;
        EqExpr *ee = (EqExpr*) malloc(sizeof(EqExpr));
        ee->lhs = lhs;
        ee->rhs = rhs;
        outer->value = ee;
        return outer;

    }
    void freeEqExpr(EqExpr* eq_expr) {
        freeExpr(eq_expr->lhs);
        freeExpr(eq_expr->rhs);
        free(eq_expr);
    }
    Expr simplifyEqExpr(Expr eq_expr) {
        //      TODO...
    }
    char* printEqExpr(EqExpr* eq_expr) {
        char* str;
        char* lhs = printExpr(eq_expr->lhs);
        char* rhs = printExpr(eq_expr->rhs);
        int base_size = strlen(lhs) + strlen(rhs) + strlen(eq_op) + 15;
        str = (char*) calloc(base_size, sizeof(char));
        sprintf(str, "(%s %s %s)", lhs, eq_op, rhs);
        free(lhs);
        free(rhs);
        return str;
    }
    
/*OTHER OPS*/

    Stmt generateAssignment(Variable* var){
        Stmt ass = createAssignment(var, var->value);
        return ass;
    }

    Expr exprFromVar(Variable* var) {
        Expr outer = (Expr) malloc(sizeof(_Expr));
        outer->type = VARIABLE;
        outer->value = var;
        return outer;
    }

    // Variable* createConstVar(const char* var_name, int occ, int value) {
    //     Expr var_e = createVariable(var_name, occ, 0, NULL);
    //     Variable* var = (Variable*)var_e->value;
    //     Stmt res = createAssignment(var, createConstant(value));
    //     free(var_e);
    //     return res;
    // }
    
    // Stmt createAssign(const char* var_name, int occ, Expr value) {
    //     Expr var_e = createVariable(var_name, occ, 0, NULL);
    //     Variable* var = (Variable*)var_e->value;
    //     Stmt res = createAssignment(var, value);
    //     free(var_e);
    //     return res;
    // }


}