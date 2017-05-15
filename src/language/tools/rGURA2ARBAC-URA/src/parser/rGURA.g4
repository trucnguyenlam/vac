/*
 @author: trucnguyenlam@gmail.com
 @description:
    This grammar (rGURA) is defined in LANGUAGE_STANDARD.md file.
    Some rules are borrowed from
        https://raw.githubusercontent.com/antlr/grammars-v4/master/c/C.g4
 @changelog:
    2017.05.09   Initial version
 */


grammar rGURA;

/* Parser */

file                      /* start rule */
    :   r_start+
    ;

r_start
    :   r_user
    |   r_attr_s
    |   r_attr_m
    |   r_scope
    |   r_admin
    |   r_ua_s
    |   r_ua_m
    |   r_rules
    |   r_spec
    ;

r_user
    :   USER Identifier* SEMI
    ;

r_attr_s
    :   ATTR_S Identifier* SEMI
    ;

r_attr_m
    :   ATTR_M Identifier* SEMI
    ;

r_scope
    :   SCOPE scope_element* SEMI
    ;

scope_element
    :   LEFTTUPLE Identifier sep Identifier+ RIGHTTUPLE
    ;

sep
    : COMMA
    | COLON
    ;

r_admin
    :   AR Identifier* SEMI
    ;

r_ua_s
    :   UAS uas_element* SEMI
    ;

uas_element
    :   Identifier attr_val+
    ;

attr_val
    :   LEFTTUPLE a=Identifier COMMA v=Identifier RIGHTTUPLE
    ;

r_ua_m
    :   UAM uam_element* SEMI
    ;

uam_element
    :   Identifier attr_mval+
    ;

attr_mval
    :   LEFTTUPLE Identifier (COMMA Identifier)+ RIGHTTUPLE
    ;

r_rules
    :   RULE rule_element* SEMI
    ;

rule_element
    :   add_rule
    |   delete_rule
    ;

add_rule
    :   LEFTTUPLE admin=Identifier COMMA precondition COMMA attr=Identifier COMMA value=Identifier RIGHTTUPLE
    ;

delete_rule
    :   LEFTTUPLE admin=Identifier COMMA attr=Identifier COMMA value=Identifier RIGHTTUPLE
    ;

precondition
    :   TRUE
    |   atom (AND atom)*
    ;

atom
    :   NOT? attr=Identifier EQUAL value=Identifier
    ;

r_spec
    :   SPEC (attr=Identifier) (value=Identifier) SEMI
    ;


/* Lexer */

USER    : 'USERS' | 'Users';
ATTR_S  : 'ATTRIBUTE_SINGLE' | 'Attribute_Single';
ATTR_M  : 'ATTRIBUTE_MULTIPLE' | 'Attribute_Multiple';
SCOPE   : 'SCOPE';
AR      : 'ADMINROLES';
UAS     : 'UATTR_S' | 'UAttr_s';
UAM     : 'UATTR_M' | 'UAttr_m';
RULE    : 'RULES' | 'Rules';
SPEC    : 'SPEC';
TRUE    : 'TRUE';
NOT     : 'not';

LEFTPAREN : '(';
SEMI : ';';
STAR : '*';
COMMA : ',';
DOT : '.';
COLON : ':';
AND : '&';
OR : '|';
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


