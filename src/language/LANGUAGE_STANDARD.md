# Introduction
2017.04.28  First draft

# Formal Specification
// Two types of user
// 1. Normal user, e.g., user0
// 2. new (unlimited) user, e.g., user1*
USERS (ident|ident*)+   SEMI

ATTRIBUTES ident[number]+  SEMI

INIT <ident (,.attribute=CONSTANT)+>  SEMI

// ident: user here is not related to the list of user
RULES <precondition (,ident.attribute=CONSTANT)+>+;

// There are three types of query
// 1. ident1 is not in the list of user
// 2. ident1 is a normal user
// 3. ident1 is a new user
QUERY ident1 . attri = CONSTANT;



# Note


