# Introduction
2017.04.28  First draft

# Formal Specification
USERS (ident|ident*)+   SEMI

ATTRIBUTES ident[number]+  SEMI

INIT <ident (,.attribute=CONSTANT)+>  SEMI

RULES <precondition (,ident.attribute=CONSTANT)+>+;

QUERY EqualExpression;



# Note


