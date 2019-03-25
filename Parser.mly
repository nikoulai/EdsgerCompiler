%{
open Printf
open Types
open Ast
open Identifier
(*open Semantic*)
open Error
(*open Parsing*)
(*open Output*)
(*open QuadTypes
open Quads*)
open Lexing
%}

/* Ocamlyacc Declarations */

%token BOOL
%token BREAK
%token BYREF
%token CONTINUE
%token DELETE
%token DOUBLE
%token ELSE
%token FOR
%token FALSE
%token IF
%token INT
%token NEW
%token <int> INT_NUM
%token <float> DOUBLE_NUM
%token NULL
%token RETURN
%token TRUE
%token VOID
%token <string> IDENT
%token <char> CHAR_V
%token CHAR
%token <string> STRING
%token ASSIGN
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token GREATER
%token LESS
%token MOD
%token AMPERSAND
%token NOT
%token Q_MARK
%token COLON
%token COMMA
%token EQUAL
%token N_EQUAL
%token GREAT_EQ
%token LESS_EQ
%token AND
%token OR
%token PPLUS
%token MMINUS
%token ASSIGN_ADD
%token ASSIGN_MINUS
%token ASSIGN_TIMES
%token ASSIGN_DIV
%token ASSIGN_MOD
%token SEMICOLON
%token LPAREN
%token RPAREN
%token LBRACK
%token RBRACK
%token LCBRACK
%token RCBRACK
%token INCLUDE
%token EOF
//%token PLUS MINUS MULTIPLY DIVIDE CARET
%token <string> VAR
%token <float->float> FNCT

/*peirama
%right	ASSIGN  ASSIGN_TIMES  ASSIGN_DIV  ASSIGN_MOD ASSIGN_ADD ASSIGN_MINUS PPLUS MMINUS SEMICOLON
%left LESS GREATER EQUAL N_EQUAL LESS_EQ GREAT_EQ AND OR COMMA
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc UMINUS
%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE
%nonassoc TtypeaS //sto ptr
%nonassoc OTHER  //sto expression
%nonassoc OPOP //sto expression_list
*/

/*--------------------------ORDER---------------------------*/
/*DANGLING IF */
%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE
/* ------------*/
%left COMMA
%nonassoc OPOP 
%nonassoc TtypeaS /*for typea_t shift/reduce conflict */

%nonassoc Q_MARK
%right COMPIF
%left OR
%left AND 
%left LESS GREATER EQUAL N_EQUAL LESS_EQ GREAT_EQ
%right ASSIGNMENT
%left OPERATOR /* all binary_operators for shift/reduce*/
%right	ASSIGN  ASSIGN_TIMES  ASSIGN_DIV  ASSIGN_MOD ASSIGN_ADD
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc CASTING /*bonus*/
%nonassoc PPLUS MMINUS
%nonassoc NEW DELETE
%nonassoc UNOP
%nonassoc LPAREN RPAREN /*see http://caml.inria.fr/pub/docs/manual-ocaml-4.00/manual026.html how conflicts are resolved */
%nonassoc POSTFIX
%nonassoc PREFIX
%nonassoc APP

%start start

%type <unit> start
%type <unit> includes
%type <unit> includ
%type <ast_declaration list> program
%type <ast_declaration list> declarations
%type <ast_declaration> declaration
%type <ast_declaration> var_declaration
%type <ast_declaration> func_declaration
%type <ast_declaration> func_definition
%type <ast_declarator list> declarators
%type <ast_declarator> declarator
%type <ast_type> typea
%type <ast_type> b_typea
%type <ast_param list> op_parameter_list
%type <ast_param list> parameter_list
%type <ast_param> parameter
%type <ast_param list> parameters
%type <ast_stmt> statement
%type <ast_stmt list> statements
%type <string> op_ident
%type <string> op_ident_colon
%type <ast_expr option> op_exp
%type <ast_expr> expression
%type <ast_expr> op_brack_exp
%type <ast_expr list> expression_list
%type <ast_expr list> op_exp_list
%type <ast_expr> constant_exp
%type <ast_unop> unary_op
%type <ast_unas> unary_assignment
%type <ast_bop> binary_op
%type <ast_bas> binary_assignment

%%
start: includes program EOF { ast_tree := Some $2 }
;

/*initialization : { ignore(initSymbolTable 256);
}*/

includes: /* empty */ { () }
| includes includ { () }
;

includ: INCLUDE STRING { () }
;

program : declaration { [$1]}
| program declaration { $1 @ [$2] }
;

declaration : var_declaration { $1 }
| func_declaration { $1 }
| func_definition { $1 }
;

var_declaration : typea declarators SEMICOLON { Vardecl ($1, $2) }
;

declarators: declarator { [$1] }
| declarators COMMA declarator { $1 @ [$3] }
;

typea: b_typea { $1 }
| typea TIMES %prec TtypeaS { Tptr $1 }
;

/*ptr:  empty  {}
| ptr TIMES  %prec TtypeaS {}
;*/

b_typea: INT { Tint }
| DOUBLE { Tdouble }
| BOOL { Tbool }
| CHAR { Tchar }
| VOID {Tvoid}
;

declarator: IDENT { Decl ($1, None) }
| IDENT LBRACK constant_exp RBRACK { Decl ($1, Some $3) }
;

func_declaration : typea IDENT LPAREN op_parameter_list RPAREN SEMICOLON { Fundecl (($1), $2, $4) }
/*| VOID IDENT LPAREN op_parameter_list RPAREN SEMICOLON { Fundecl (Tvoid, $2, $4) }*/
;

op_parameter_list: /* empty */ { [] }
| parameter_list { $1 }
;

parameter_list:
	parameter parameters { $1 :: $2 }
;

parameters :
	/*empty*/ { [] }
	| COMMA parameter parameters { $2 :: $3 }
;

parameter :
	BYREF typea IDENT { ParamByRef ($2, $3) }
	| typea IDENT { Param ($1, $2) }

/*
parameter_list : parameter {}
|parameter_list COMMA parameter {}
;
*/

func_definition: typea IDENT LPAREN op_parameter_list RPAREN LCBRACK declarations statements RCBRACK { Fundefi (($1), $2, $4, $7, $8) }
/*| VOID IDENT LPAREN op_parameter_list RPAREN LCBRACK declarations statements RCBRACK { Fundefi (Tvoid, $2, $4, $7, $8) } */
;

declarations: /* empty */ { [] }
|declarations declaration { $1 @ [$2] }
;

statements: /* empty */ { [] }
|statements statement { $1 @ [$2] }
;



op_exp :
	/* empty */ { None }
	| expression { Some $1 }
;
op_ident_colon :
	/* empty */ { "" }
	| IDENT COLON { $1 }
;
op_ident :
	/* empty */ { "" }
	| IDENT  { $1 }
;

statement : SEMICOLON { Snull }
	      | expression SEMICOLON { Sexpr $1}
	      | LCBRACK statements RCBRACK { Slist $2 }
	      | IF LPAREN expression RPAREN statement %prec LOWER_THAN_ELSE { Sif ($3, $5, None) }
	      | IF LPAREN expression RPAREN statement ELSE statement { Sif ($3, $5, Some $7) }
     	  | op_ident_colon FOR LPAREN  op_exp SEMICOLON op_exp SEMICOLON op_exp RPAREN statement { Sfor (Some $1, $4, $6, $8,$10) }
				| FOR LPAREN  op_exp SEMICOLON op_exp SEMICOLON op_exp RPAREN statement { Sfor (None, $3, $5, $7,$9) }
				| CONTINUE   SEMICOLON { Scont None }
				| CONTINUE  op_ident SEMICOLON { Scont (Some $2) }
				| BREAK SEMICOLON { Sbrk None }
	      | BREAK op_ident SEMICOLON { Sbrk (Some $2) }
	      | RETURN op_exp SEMICOLON { Sreturn $2}
;

expression : IDENT { Eid $1 }
| LPAREN expression RPAREN { $2 }
| TRUE { Ebool true }
| FALSE { Ebool false }
| NULL { Enull }
| INT_NUM { Eint $1 }
| CHAR_V { Echar $1 }
| DOUBLE_NUM { Edoub $1 }
| STRING { Estr $1 }
| IDENT LPAREN op_exp_list RPAREN %prec APP{ Eapp ($1, $3) }
| unary_op expression %prec UNOP { Eunop ($2, $1) }
| unary_assignment expression %prec PREFIX { Eunas ($2, $1) }
| LPAREN typea RPAREN expression %prec CASTING  { Ecast ($2, $4) }
| NEW typea op_brack_exp { Enew ($2,Some $3) }
| NEW typea SEMICOLON { Enew ($2, None) }
| DELETE expression { Edel $2 }
/*| DELETE expression %prec UMINUS {}*/
| expression LBRACK expression RBRACK %prec POSTFIX { Emat($1, $3) }
| expression binary_opand expression %prec AND { Ebop ($1, $3, $2) }
| expression binary_opor expression %prec OR { Ebop ($1, $3, $2) }
| expression binary_op expression %prec OPERATOR { Ebop ($1, $3, $2) }
| expression unary_assignment %prec POSTFIX { Eunas1 ($1, $2) }
| expression binary_assignment expression %prec ASSIGNMENT { Ebas ($1, $3, $2) }
| expression Q_MARK expression COLON expression %prec COMPIF { Eif ($1, $3, $5) }
;


op_exp_list : /* empty */ { [] }
| expression_list { $1 }
;

op_brack_exp : /*empty */ { Eint 1 }
| LBRACK expression RBRACK { $2 }
;

expression_list : expression %prec OPOP { [$1] }
| expression_list COMMA expression %prec COMMA{ $1 @ [$3] }
;

constant_exp : expression { $1 }
;

unary_op :
      AMPERSAND { Tuamp }
      | TIMES { Tutim }
      | PLUS { Tupl }
      | MINUS { Tumin }
      | NOT { Tunot }
;


binary_op :
TIMES %prec TIMES{ Tbtim }
| DIV %prec DIV{ Tbdiv }
| MOD %prec MOD{ Tbmod }
| PLUS %prec PLUS{ Tbpl }
| MINUS %prec MINUS{ Tbmin }
| LESS %prec LESS{ Tblss }
| GREATER %prec GREATER{ Tbgrt }
| LESS_EQ %prec LESS_EQ{ Tbleq }
| GREAT_EQ %prec GREAT_EQ{ Tbgeq }
| EQUAL %prec EQUAL{ Tbeq }
| N_EQUAL %prec N_EQUAL{ Tbneq }
| COMMA %prec COMMA{ Tbcom }
;

binary_opand :
AND { Tband }
;

binary_opor:
OR { Tbor }
;

unary_assignment :
		PPLUS { Tppl }
		| MMINUS { Tmmin }

;

binary_assignment :
		ASSIGN { Tba }
		| ASSIGN_TIMES { Tbatim }
		| ASSIGN_DIV { Tbadiv }
		| ASSIGN_MOD { Tbamod }
		| ASSIGN_ADD { Tbapl }
		| ASSIGN_MINUS { Tbamin }
;
