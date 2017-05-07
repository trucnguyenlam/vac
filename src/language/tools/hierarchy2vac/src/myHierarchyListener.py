# Generated from hierarchygrammar.g4 by ANTLR 4.7
from antlr4 import *
from hierarchygrammarListener import hierarchygrammarListener
from hierarchyModel import *

# This class defines a complete listener for a parse tree produced by hierarchygrammarParser.


class myHierarchyListener(hierarchygrammarListener):

    def __init__(self):
        self.policy = Policy()

    # Enter a parse tree produced by hierarchygrammarParser#policy.
    def enterPolicy(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#policy.
    def exitPolicy(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_start.
    def enterR_start(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_start.
    def exitR_start(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_user.
    def enterR_user(self, ctx):
        for u in ctx.Identifier():
            # print u.getText()
            new_user = User(u.getText())
            self.policy.users.append(new_user)

    # Exit a parse tree produced by hierarchygrammarParser#r_user.
    def exitR_user(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_role.
    def enterR_role(self, ctx):
        for r in ctx.Identifier():
            print r.getText()
            new_role = Role(r.getText())
            self.policy.roles.append(new_role)

    # Exit a parse tree produced by hierarchygrammarParser#r_role.
    def exitR_role(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_hier.
    def enterR_hier(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_hier.
    def exitR_hier(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#hier_element.
    def enterHier_element(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#hier_element.
    def exitHier_element(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_pra.
    def enterR_pra(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_pra.
    def exitR_pra(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#pra_element.
    def enterPra_element(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#pra_element.
    def exitPra_element(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_rule.
    def enterR_rule(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_rule.
    def exitR_rule(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#rule_element.
    def enterRule_element(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#rule_element.
    def exitRule_element(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#ca_rule.
    def enterCa_rule(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#ca_rule.
    def exitCa_rule(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#cr_rule.
    def enterCr_rule(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#cr_rule.
    def exitCr_rule(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#precondition.
    def enterPrecondition(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#precondition.
    def exitPrecondition(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#primaryExpression.
    def enterPrimaryExpression(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#primaryExpression.
    def exitPrimaryExpression(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#unaryExpression.
    def enterUnaryExpression(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#unaryExpression.
    def exitUnaryExpression(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#andExpression.
    def enterAndExpression(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#andExpression.
    def exitAndExpression(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#orExpression.
    def enterOrExpression(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#orExpression.
    def exitOrExpression(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#expression.
    def enterExpression(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#expression.
    def exitExpression(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_smer.
    def enterR_smer(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_smer.
    def exitR_smer(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#smer_element.
    def enterSmer_element(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#smer_element.
    def exitSmer_element(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#r_query.
    def enterR_query(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#r_query.
    def exitR_query(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#query_element.
    def enterQuery_element(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#query_element.
    def exitQuery_element(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#config.
    def enterConfig(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#config.
    def exitConfig(self, ctx):
        pass

    # Enter a parse tree produced by hierarchygrammarParser#target.
    def enterTarget(self, ctx):
        pass

    # Exit a parse tree produced by hierarchygrammarParser#target.
    def exitTarget(self, ctx):
        pass
