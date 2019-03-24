{
	open Lexing
	open Parser
	let incr_linenum lexbuf =
		let pos = lexbuf.Lexing.lex_curr_p in
			lexbuf.Lexing.lex_curr_p <-
			{
				pos with
				Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
				Lexing.pos_bol = pos.Lexing.pos_cnum;
			}
}


let digit = ['0'-'9']
let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let hex_d = ['a'-'f' 'A'-'F' '0'-'9']
rule e_lang = parse

| "bool" { BOOL }
| "break" { BREAK }
| "byref" { BYREF }
| "char" { CHAR }
| "continue" { CONTINUE }
| "delete" { DELETE }
| "double" { DOUBLE }
| "else" { ELSE }
| "for" { FOR }
| "false" { FALSE }
| "if" { IF }
| "int" { INT }
| "new" { NEW }
| "NULL" { NULL }
| "return" { RETURN }
| "true" { TRUE }
| "void" { VOID }

| id as ident { IDENT ident }


| digit+ as inum
{ INT_NUM (int_of_string inum) }

| digit+ '.' digit+ (('e'|'E') ('+'|'-')? (digit+))? as fnum
{ DOUBLE_NUM (float_of_string fnum) }

| '\'' '\\' ('n' | 't' | 'r' | '0'| '\'' | '\"' |('x' (digit|['A'-'F' 'a'-'f']) (digit|['A'-'F' 'a'-'f'])) | '\\') '\'' as character
           		    { let c = Str.global_replace (Str.regexp "\\\\n") "\n" character in
	 		      let c = Str.global_replace (Str.regexp "\\\\t") "\t" c in
	 		      let c = Str.global_replace (Str.regexp "\\\\r") "\r" c in
		      	CHAR_V(c.[1])
                      }

| '"' (("\\n"|"\\t"|"\\r"|"\\0" | "\\\\" |"\\\'"|"\\\"" | ("\\x" hex_d hex_d)) | [^ ''' '"' '\\'])* '"' as string
{ STRING (	let s = Str.global_replace (Str.regexp "\\\\n") "\n" string in
						       	let s = Str.global_replace (Str.regexp "\\\\t") "\t" s in
						       	let s = Str.global_replace (Str.regexp "\\\\r") "\r" s in
						       	let s = Str.global_replace (Str.regexp "\\\\\"") "\"" s in
							String.sub s 1 ((String.length s)-2) 
							 ) }

| "#include"
(*{
	Printf.printf "include\n";
	e_lang lexbuf
}*)
{
	Printf.printf "include\n";
	INCLUDE

}

| '='  {ASSIGN}
| '+'  {PLUS}
| '-'  {MINUS}
| '*'  {TIMES}
| '/'  {DIV}
| '>'  {GREATER}
| '<'  {LESS}
| '%'  {MOD}
| '&'  {AMPERSAND}
| '!'  {NOT}
| '?'  {Q_MARK}
| ':'  {COLON}
| ','  {COMMA}
| "==" {EQUAL}
| "!=" {N_EQUAL}
| ">=" {GREAT_EQ}
| "<=" {LESS_EQ}
| "&&" {AND}
| "||" {OR}
| "++" {PPLUS}
| "--" {MMINUS}
| "+=" {ASSIGN_ADD}
| "-=" {ASSIGN_MINUS}
| "*=" {ASSIGN_TIMES}
| "/=" {ASSIGN_DIV}
| "%=" {ASSIGN_MOD}
| ';'  {SEMICOLON}
| '('  {LPAREN}
| ')'  {RPAREN}
| '['  {LBRACK}
| ']'  {RBRACK}
| '{'  {LCBRACK}
| '}'  {RCBRACK}


| [' ' '\t' '\r']+
{
	e_lang lexbuf

}

| '\n'
{
	incr_linenum lexbuf;
	e_lang lexbuf
}

| "//" [^ '\n']*
{
	incr_linenum lexbuf;
	e_lang lexbuf
}

| "/*"
{
	comment lexbuf
}

| _ as c
{
  let pos = lexbuf.Lexing.lex_curr_p in
  Printf.printf "Invalid Character '%c' at line %d, position %d."
  c pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
  raise Not_found
  }
(*{
	Printf.printf "Unrecognized character: %c\n" c;
}*)

| eof
{
	Printf.printf "EOF\n";
	EOF;
}



and comment = parse
| "*/"
{
	e_lang lexbuf
}

| "\n"
{
	incr_linenum lexbuf;
	comment lexbuf
}

| eof
{
	Printf.printf "comments are not closed";
	raise End_of_file
}

| _ {comment lexbuf}

{
	(*let main () =
		let cin =
			if Array.length Sys.argv > 1
				then open_in Sys.argv.(1)
				else stdin
			in
				let lexbuf = Lexing.from_channel cin in
				try e_lang lexbuf
				with End_of_file -> ()
				let _ = Printexc.print main ()
	*)
}
