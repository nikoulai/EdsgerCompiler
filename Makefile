.PHONY: clean distclean pack count

SRCFILES=Makefile extend.ml Lexer.mll Parser.mly Semantic.ml Codegen.ml ExpCodeGen.ml \
  $(filter-out Parser.% Lexer.%,$(MLFILES)) \
  $(filter-out Parser.%,$(MLIFILES))

default:
	ocamlbuild -cflag -g  -use-ocamlfind Main.byte -pkgs str,llvm

debug:
	ocamlbuild -cflag -g  -use-ocamlfind Main.byte -pkgs str,llvm -tag debug

Parser.ml Parser.mli: Parser.mly
	ocamlyacc -v Parser.mly

Lexer.ml: Lexer.mll
	ocamllex Lexer.mll

clean:
	rm -rf _build

distclean: clean
	rm -rf _build Main.byte

pack: clean
	tar cvfz gracec.tar.gz $(SRCFILES)

count:
	wc -l $(SRCFILES)
