#!/usr/bin/env python
import os
import os.path
import argparse
import random
import sys
sys.path.append("./")

""" Access Control Policy converter
    maintained by Truc Nguyen Lam, Univerisity of Southampton
"""
"""
Description:
    Remember the name

TODO:
    -

Changelog:
    2017.05.06  Initial version
"""


def saveFile(filename, string):
    try:
        outfile = open(filename, "w")
        outfile.write(string)
        outfile.close()
    except IOError:
        pass


def getRandomChoice():
    # return random.choice([True, False])
    return (not not random.getrandbits(1))


def parsePolicy(inputfilename):
    if not os.path.isfile(inputfilename):
        print "Error: please provide correct input file"

    from antlr4 import FileStream, CommonTokenStream, ParseTreeWalker
    from hierarchygrammarLexer import hierarchygrammarLexer
    from hierarchygrammarParser import hierarchygrammarParser
    from myHierarchyListener import myHierarchyListener

    input = FileStream(inputfilename)
    lexer = hierarchygrammarLexer(input)
    stream = CommonTokenStream(lexer)
    parser = hierarchygrammarParser(stream)
    tree = parser.policy()
    listener = myHierarchyListener()
    walker = ParseTreeWalker()
    walker.walk(listener, tree)
    return listener.policy


def generatePolicy(args):
    # Parse policy first
    policy = parsePolicy(args.input)

    # Check output path
    if args.path:
        try:
            os.makedirs(args.path)
        except OSError:
            pass

    prefix = args.path + "/" + \
        os.path.basename(args.input) if args.path != "" else args.input

    # For roles, which means attribute here
    rolestr = "ATTRIBUTES\n"
    for r in policy.roles:
        rolestr += str(r) + "[1]\n"
    rolestr += ";\n\n"

    # For rules
    rulestr = "RULES\n"
    for ca_rule in policy.ca_rules:
        rulestr += ca_rule.toVACRuleWithHierarchy(policy.hier) + "\n"
    for cr_rule in policy.cr_rules:
        rulestr += cr_rule.toVACRuleWithHierarchy(policy.hier) + "\n"
    rulestr += ";\n\n"

    for index, q in enumerate(policy.queries):
        # userlist = []
        userstr = "USERS\n"
        initstr = "INIT\n"
        for i in range(0, args.nuser):
            # For user
            name = "user%s" % i
            userstr += name + "\n"
            # userlist.append(name)
            # For init
            initstr += "<" + name
            for r in policy.roles:
                if getRandomChoice():
                    initstr += ", " + str(r) + "=1"
                else:
                    initstr += ", " + str(r) + "=0"
            initstr += '>\n'

        for i in range(0, args.nnewuser):
            name = "new_user%s" % i
            userstr += name + "*\n"
            # userlist.append(name)
            # For init
            initstr += "<" + name
            for r in policy.roles:
                if getRandomChoice():
                    initstr += ", " + str(r) + "=1"
                else:
                    initstr += ", " + str(r) + "=0"
            initstr += '>\n'

        # For query
        for index, ua in enumerate(q.ua_configs):
            name = "quser%s" % index
            userstr += name + "\n"
            if len(ua) > 0:
                initstr += "<" + name
                for r in ua:
                    initstr += ", " + str(r) + "=1"
                initstr += '>\n'

        querystr = "QUERY\n"
        querystr += "quser%s" % q.user_index
        for f, r in enumerate(q.goal):
            newquerystr = querystr + ".%s=1;\n\n" % r
            newuserstr = userstr + ";\n\n"
            newinitstr = initstr + ";\n\n"
            ret = newuserstr + rolestr + newinitstr + rulestr + newquerystr
            saveFile(prefix + "%su_%snu_query%s_%s.txt" %
                     (args.nuser, args.nnewuser, index, f), ret)


def main():
    parser = argparse.ArgumentParser(
        description='Access Control Policy Converter')
    parser.add_argument('-i', '--input', metavar='X',
                        help='input policy',
                        type=str, dest='input', required=True)
    parser.add_argument('-p', '--output', metavar='X',
                        help='output path',
                        type=str, dest='path', default="")
    parser.add_argument('-n', '--users', metavar='X',
                        help='generate X normal users',
                        type=int, dest='nuser', default=2)
    parser.add_argument('-u', '--new-users', metavar='X',
                        help='generate X new users',
                        type=int, dest='nnewuser', default=0)
    args = parser.parse_args()
    generatePolicy(args)


if __name__ == '__main__':
    main()
