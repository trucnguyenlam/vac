#!/usr/bin/env python
import argparse
import sys
sys.path.append("./")
from antlr4 import *
from hierarchygrammarLexer import hierarchygrammarLexer
from hierarchygrammarParser import hierarchygrammarParser
from myHierarchyListener import myHierarchyListener

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


def parsePolicy(inputfilename):
    input = FileStream(inputfilename)
    lexer = hierarchygrammarLexer(input)
    stream = CommonTokenStream(lexer)
    parser = hierarchygrammarParser(stream)
    tree = parser.policy()
    # print tree.getText()
    listener = myHierarchyListener()
    walker = ParseTreeWalker()
    walker.walk(listener, tree)

def main():
    parser = argparse.ArgumentParser(description='Access Control Policy Converter')
    parser.add_argument('-i', '--input', metavar='X', help='input policy', type=str, dest='input', required=True)
    parser.add_argument('-o', '--output', metavar='X', help='output path', type=str, dest='path')
    args = parser.parse_args()
    parsePolicy(args.input)


if __name__ == '__main__':
    main()
