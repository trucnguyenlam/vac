/*
  @author: Truc Nguyen Lam
    This is the grammar file of the parser for ARBAC format input file

  Changelog:
    2017-04-27  add support for hierarchy (HIERARCHY)
    2015-10-07  first working version
*/

grammar ARBAC;


///////////////////////////////////////////////////////////////////////////////////
///////////////////////////   Parser     //////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
parse : node+;

node : roles | users | newusers | ua | hierarchies | cr | ca | admin | spec;

roles : ('Roles'|'ROLES') (id=ID)* SEMI;

users : ('Users'|'USERS') (id=ID)* SEMI;

newusers : ('Newusers'|'NEWUSERS') (LANGLE id=ID COMMA predifinedroles RANGLE)* SEMI;

predifinedroles: role (CONJUNCTION role)*;

role: id=ID;

ua : 'UA' (LANGLE id1=ID COMMA id2=ID RANGLE)* SEMI ;

hierarchies : 'HIERARCHY' (LANGLE id1=ID COMMA id2=ID RANGLE)* SEMI ;

cr : 'CR' (LANGLE (id1=ID |'FALSE') COMMA id2=ID RANGLE)* SEMI ;

ca : 'CA' (ca_entry)* SEMI ;

ca_entry : LANGLE id1=ID COMMA precondition COMMA id2=ID RANGLE ;

precondition : atom (CONJUNCTION atom)*
              | 'TRUE'
              | 'NEW'
              ;

atom : NOT? id=ID;

admin : 'ADMIN' id=ID* SEMI;

spec : 'SPEC' id=ID spec_tail;

spec_tail : (id=ID)? SEMI ;

//////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////// Lexer  ///////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

ID  : ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'0'..'9'|'_')* ;

LANGLE : '<';

RANGLE : '>';

COMMA : ',';

CONJUNCTION : '&';

NOT : '-';

SEMI : ';';

WS : (' ' | '\t' | '\n' | '\r' | '\f')+ {$channel = HIDDEN;};