/*
 @author: trucnguyenlam@gmail.com
 @description:
    This grammar is for Hierarchy policy in
            http://www3.cs.stonybrook.edu/~stoller/ccs2007/
 @changelog:
    2017.05.06   Initial version
 */

grammar oldvac;


/* Parser */

policy                      /* start rule */
    :   r_start+
    ;

r_start
    :   r_user
    |   r_newuser
    |   r_role
    |   r_hier
    |   r_ua
    |   r_ca
    |   r_cr
    |   r_admin
    |   r_spec
    ;

r_role
    :   ROLE Identifier* SEMI
    ;

r_user
    :   USER Identifier* SEMI
    ;

r_admin
    :   ADMIN Identifier* SEMI
    ;

r_newuser
    :   NEWUSER (LEFTTUPLE Identifier COMMA predifinedroles RIGHTTUPLE)* SEMI
    ;

predifinedroles
    :   Identifier (AND Identifier)*
    ;

r_ua
    :   UA (LEFTTUPLE Identifier COMMA Identifier RIGHTTUPLE)* SEMI
    ;

r_hier
    :   HIER hier_element* SEMI
    ;

hier_element
    :   LEFTTUPLE Identifier COMMA Identifier RIGHTTUPLE
    ;

r_ca
    :   CA ca_rule* SEMI
    ;

r_cr
    :   CR cr_rule* SEMI
    ;

ca_rule
    :   LEFTTUPLE Identifier COMMA precondition COMMA Identifier RIGHTTUPLE
    ;

cr_rule
    :   LEFTTUPLE (Identifier|FALSE) COMMA Identifier RIGHTTUPLE
    ;

precondition
    :   TRUE
    |   NEW
    |   literal (AND literal)*
    ;

literal
    :   NOT? Identifier
    ;

r_spec
    :   SPEC Identifier? Identifier SEMI
    ;

/* Lexer */
USER    : 'USERS' | 'Users';
NEWUSER : 'NEWUSERS' | 'Newusers';
ROLE    : 'ROLES' | 'Roles';
HIER    : 'HIERARCHY';
UA      : 'UA';
CA      : 'CA';
CR      : 'CR';
ADMIN   : 'ADMIN';
SPEC    : 'SPEC';
TRUE    : 'TRUE';
NEW     : 'NEW';
FALSE   : 'FALSE';
NOT : '-';
AND : '&';

LEFTPAREN : '(';
SEMI : ';';
STAR : '*';
COMMA : ',';
DOT : '.';
COLON : ':';
EQUAL : '=';
IMPLY: '=>';
QUESTION: '?';
RIGHTPAREN : ')';
LEFTBRACKET : '[';
RIGHTBRACKET : ']';
LEFTTUPLE : '<';
RIGHTTUPLE : '>';

Identifier
    :   IdentifierNondigit
        (   IdentifierNondigit
        |   Digit
        )*
    ;

fragment
IdentifierNondigit
    :   Nondigit
    ;

fragment
Nondigit
    :   [a-zA-Z_]
    ;

fragment
Digit
    :   [0-9]
    ;

Constant
    :   DecimalConstant
    ;

fragment
DecimalConstant
    :   Sign? NonzeroDigit Digit*
    |   Sign? Digit
    ;

fragment
NonzeroDigit
    :   [1-9]
    ;

fragment
Sign
    :   '+' | '-'
    ;

Whitespace
    :   [ \t]+
        -> skip
    ;

Newline
    :   (   '\r' '\n'?
        |   '\n'
        )
        -> skip
    ;

BlockComment
    :   '/*' .*? '*/'
        -> skip
    ;

LineComment
    :   '//' ~[\r\n]*
        -> skip
    ;


