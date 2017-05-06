/*
 @author: trucnguyenlam@gmail.com
 @description:
    This grammar is for Hierarchy policy in
            http://www3.cs.stonybrook.edu/~stoller/ccs2007/
 @changelog:
    2017.05.06   Initial version
 */

grammar hierarchygrammar;


/* Parser */

file                      /* start rule */
    :   r_start+
    ;

r_start
    :   r_user
    |   r_role
    |   r_hier
    |   r_pra
    |   r_rule
    |   r_smer
    |   r_query
    ;

r_user
    :   USER Identifier+
    ;

r_role
    :   ROLE Identifier+
    ;

r_hier
    :   HIER hier_element+
    ;

hier_element
    :   Identifier (LEFTTUPLE Identifier)+
    ;

r_pra
    :   PRA pra_element+
    ;

pra_element
    :   PA LEFTPAREN r=Identifier COMMA LEFTBRACKET a=Identifier COMMA r=Identifier RIGHTBRACKET RIGHTPAREN
    ;

r_rule
    :   RULE rule_element+
    ;

rule_element
    :   ca_rule
    |   cr_rule
    ;

ca_rule
    :   CAN_ASSIGN LEFTPAREN a=Identifier COMMA precondition COMMA t=Identifier RIGHTPAREN
    ;

cr_rule
    :   CAN_REVOKE LEFTPAREN a=Identifier COMMA t=Identifier RIGHTPAREN
    ;

precondition
    :   TRUE
    |   expression
    ;

primaryExpression
    :   Identifier
    |   LEFTPAREN expression RIGHTPAREN
    ;

unaryExpression
    :   primaryExpression
    |   NOT unaryExpression
    ;

andExpression
    :   unaryExpression
    |   andExpression AND unaryExpression
    ;

orExpression
    :   andExpression
    |   orExpression OR andExpression
    ;

expression
    :   orExpression
    ;

r_smer
    :   INVA smer_element+
    ;

smer_element
    :   SMER LEFTPAREN Identifier COMMA Identifier RIGHTPAREN
    ;

r_query
    :   QUERY query_element+
    ;

query_element
    :   REACH config+ target
    ;

config
    :   LEFTBRACKET Identifier* RIGHTBRACKET
    ;

target
    :   LEFTPAREN Constant COMMA Identifier+ RIGHTPAREN
    ;


/* Lexer */
USER    : '[USERS]';
ROLE    : '[ROLES]';
HIER    : '[HIERARCHY]';
PRA     : '[PRA]';
RULE    : '[RULES]';
QUERY   : '[QUERY]';
INVA    : '[INVARIANT]';
TRUE    : 'true';
SMER    : 'SMER';
PA         : 'PA';
CAN_ASSIGN : 'can_assign';
CAN_REVOKE : 'can_revoke';
REACH      : 'reach';
NOT : 'not';
AND : 'and';
OR  : 'or';

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


