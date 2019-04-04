.PHONY: clean distclean pack count

SRCFILES=Ast.ml Error.ml Error.mli Hashcons.ml Hashcons.mli Main.ml Symbol.ml Symbol.mli Types.ml Types.mli \
Codegen.ml extend.ml Identifier.ml Identifier.mli Semantic.ml Symbtest.ml Makefile Lexer.mll Parser.mly README libs \
 $(filter-out Parser.% Lexer.%,$(MLFILES)) \
 $(filter-out Parser.%,$(MLIFILES))

default:
	ocamlbuild -cflag -g -use-ocamlfind Main.byte -pkgs str,llvm

debug:
	ocamlbuild -cflag -g -use-ocamlfind Main.byte -pkgs str,llvm -tag debug

Parser.ml Parser.mli: Parser.mly
	ocamlyacc -v Parser.mly

Lexer.ml: Lexer.mll
	ocamllex Lexer.mll

clean:
	rm -rf _build

distclean: clean
	rm -rf _build Main.byte

pack: clean
	tar cvfz compilerEds.tar.gz $(SRCFILES)

count:
	wc -l $(SRCFILES)
