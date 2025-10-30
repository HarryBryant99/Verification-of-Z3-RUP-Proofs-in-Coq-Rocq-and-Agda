
# Makefile for z3satchecker OCaml project

OCAML=ocamlc
LEX=ocamllex
YACC=ocamlyacc

OBJS=proven_sat_checker.cmo types.cmo step_converter.cmo parser.cmo lexer.cmo main.cmo

all: z3satchecker

z3satchecker: $(OBJS)
	$(OCAML) -o z3satchecker $(OBJS)

parser.ml parser.mli: parser.mly
	$(YACC) parser.mly

lexer.ml: lexer.mll
	$(LEX) lexer.mll

proven_sat_checker.cmo: proven_sat_checker.ml
	$(OCAML) -c proven_sat_checker.ml

types.cmo: types.ml
	$(OCAML) -c types.ml

parser.cmo: parser.ml parser.mli
	$(OCAML) -c parser.mli
	$(OCAML) -c parser.ml

lexer.cmo: lexer.ml
	$(OCAML) -c lexer.ml

step_converter.cmo: step_converter.ml
	$(OCAML) -c step_converter.ml

main.cmo: main.ml
	$(OCAML) -c main.ml

clean:
	rm -f *.cmo *.cmi parser.ml parser.mli lexer.ml z3satchecker
