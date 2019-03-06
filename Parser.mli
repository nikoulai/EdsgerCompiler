type token =
  | BOOL
  | BREAK
  | BYREF
  | CONTINUE
  | DELETE
  | DOUBLE
  | ELSE
  | FOR
  | FALSE
  | IF
  | INT
  | NEW
  | INT_NUM of (int)
  | DOUBLE_NUM of (float)
  | NULL
  | RETURN
  | TRUE
  | VOID
  | IDENT of (string)
  | CHAR_V of (string)
  | CHAR
  | STRING of (string)
  | ASSIGN
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | GREATER
  | LESS
  | MOD
  | AMPERSAND
  | NOT
  | Q_MARK
  | COLON
  | COMMA
  | EQUAL
  | N_EQUAL
  | GREAT_EQ
  | LESS_EQ
  | AND
  | OR
  | PPLUS
  | MMINUS
  | ASSIGN_ADD
  | ASSIGN_MINUS
  | ASSIGN_TIMES
  | ASSIGN_DIV
  | ASSIGN_MOD
  | SEMICOLON
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | LCBRACK
  | RCBRACK
  | INCLUDE
  | EOF
  | VAR of (string)
  | FNCT of (float->float)

val start :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> unit
