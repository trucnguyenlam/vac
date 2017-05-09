# Generated from hierarchygrammar.g4 by ANTLR 4.7
from antlr4 import *
from oldvacListener import oldvacListener
from oldvacModel import *

# This class defines a complete listener for a parse tree produced by
# hierarchygrammarParser.


class myHierarchyListener(hierarchygrammarListener):

    def __init__(self):
        self.policy = Policy()
        self.roles = {}
        self.users = {}

    # Enter a parse tree produced by hierarchygrammarParser#r_user.
    def enterR_user(self, ctx):
        for u in ctx.Identifier():
            self.users[u.getText()] = True
            new_user = User(u.getText())
            self.policy.users.append(new_user)

    # Enter a parse tree produced by hierarchygrammarParser#r_role.
    def enterR_role(self, ctx):
        for r in ctx.Identifier():
            self.roles[r.getText()] = True
            new_role = Role(r.getText())
            self.policy.roles.append(new_role)

    # Enter a parse tree produced by hierarchygrammarParser#hier_element.
    def enterHier_element(self, ctx):
        # this should be correct
        isLessThan = True if ctx.order()[0].getText() == '<' else False
        for i in range(0, len(ctx.Identifier())):
            for j in range(i + 1, len(ctx.Identifier())):
                if isLessThan:
                    self.policy.hier.addPartialOrder(
                        ctx.Identifier()[i].getText(),
                        ctx.Identifier()[j].getText())
                else:
                    self.policy.hier.addPartialOrder(
                        ctx.Identifier()[j].getText(),
                        ctx.Identifier()[i].getText())

    # Enter a parse tree produced by hierarchygrammarParser#pra_element.
    def enterPra_element(self, ctx):
        newpra = Permission(
            ctx.Identifier()[0].getText(),
            tuple([ctx.Identifier()[1].getText(), ctx.Identifier()[2].getText()]))
        self.policy.pras.append(newpra)

    # Enter a parse tree produced by hierarchygrammarParser#ca_rule.
    def enterCa_rule(self, ctx):
        admin = ctx.Identifier()[0].getText()
        target = ctx.Identifier()[1].getText()
        precond = self._buildPrecondition(ctx.precondition())
        self.policy.ca_rules.append(CARule(admin, precond, target))

    # Enter a parse tree produced by hierarchygrammarParser#cr_rule.
    def enterCr_rule(self, ctx):
        newrule = CRRule(ctx.Identifier()[
                         0].getText(), ctx.Identifier()[1].getText())
        self.policy.cr_rules.append(newrule)

    # Enter a parse tree produced by hierarchygrammarParser#smer_element.
    def enterSmer_element(self, ctx):
        self.policy.smers.append(
            SMER(ctx.Identifier()[0].getText(), ctx.Identifier()[1].getText()))

    # Enter a parse tree produced by hierarchygrammarParser#query_element.
    def enterQuery_element(self, ctx):
        ua = []
        for c in ctx.config():
            ua.append([r.getText() for r in c.Identifier()])
        index = int(ctx.target().Constant().getText())
        goal = [r.getText() for r in ctx.target().Identifier()]
        self.policy.queries.append(Query(ua, index, goal))

    def _buildPrecondition(self, ctx):
        if ctx.TRUE():
            return Precondition(True, [])
        else:
            conjun = []
            for l in ctx.literal():
                if len(l.children) > 1:
                    conjun.append(Literal(l.Identifier().getText(), True))
                else:
                    conjun.append(Literal(l.Identifier().getText(), False))
            return Precondition(False, conjun)

    def _validRole(self, r):
        return (r in self.roles)

