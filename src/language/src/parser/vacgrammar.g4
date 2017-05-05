/*
 @author: trucnguyenlam@gmail.com
 @description:
    This grammar is defined in LANGUAGE_STANDARD.md file.
    Some rules are borrowed from
        https://raw.githubusercontent.com/antlr/grammars-v4/master/c/C.g4
 @changelog:
    2017.05.02   Initial version
 */


grammar vacgrammar;

/* Parser */

file                      /* start rule */
    :   r_start+
    ;

r_start
    :   r_user
    |   r_attr
    |   r_init
    |   r_rules
    |   r_query
    ;

r_user
    :   USER user_element+ SEMI
    ;

user_element
    :   Identifier STAR?
    ;

r_attr
    :   ATTR attr_element+ SEMI
    ;

attr_element
    :   Identifier LEFTBRACKET Constant RIGHTBRACKET
    ;

r_init
    :   INIT init_element+ SEMI
    ;

init_element
    :   LEFTTUPLE Identifier (COMMA  init_assignment)+ RIGHTTUPLE
    ;

init_assignment
    :   Identifier EQUAL Constant
    ;

primaryExpression
    :   Constant
    |   u=Identifier DOT a=Identifier
    |   LEFTPAREN expression RIGHTPAREN
    ;

unaryExpression
    :   primaryExpression
    |   NOT unaryExpression
    ;

equalityExpression
    :   unaryExpression
    |   equalityExpression EQUAL unaryExpression
    ;

andExpression
    :   equalityExpression
    |   andExpression AND equalityExpression
    |   andExpression ANDAND equalityExpression
    ;

orExpression
    :   andExpression
    |   orExpression OR andExpression
    |   orExpression OROR andExpression
    ;

implyExpression
    :   orExpression
    |   implyExpression IMPLY orExpression
    ;

conditionalExpression
    :   implyExpression (QUESTION expression COLON conditionalExpression)?
    ;

expression
    :   conditionalExpression
    ;

r_rules
    :   RULE rule_element* SEMI
    ;

rule_element
    :   LEFTTUPLE precondition (COMMA normal_assignment)+ RIGHTTUPLE
    ;

normal_assignment
    :   u=Identifier DOT a=Identifier EQUAL Constant
    ;

precondition
    :   TRUE
    |   expression
    ;

r_query
    :   QUERY normal_assignment SEMI
    ;


/* Lexer */

USER    : [Uu][Ss][Ee][Rr][Ss];
ATTR    : [Aa][Tt][Tt][Rr][Ii][Bb][Uu][Tt][Ee][Ss];
INIT    : [Ii][Nn][Ii][Tt];
RULE    : [Rr][Uu][Ll][Ee][Ss];
QUERY   : [Qq][Uu][Ee][Rr][Yy];
TRUE    : 'TRUE';

LEFTPAREN : '(';
SEMI : ';';
STAR : '*';
COMMA : ',';
DOT : '.';
COLON : ':';
AND : '&';
ANDAND : '&&';
OR : '|';
OROR : '||';
EQUAL : '=';
IMPLY: '=>';
QUESTION: '?';
RIGHTPAREN : ')';
LEFTBRACKET : '[';
RIGHTBRACKET : ']';
NOT : '!';
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


