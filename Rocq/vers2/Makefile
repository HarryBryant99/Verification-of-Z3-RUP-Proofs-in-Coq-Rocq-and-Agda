OCAMLC=ocamlc
OCAMLLEX=ocamllex
OCAMLYACC=ocamlyacc

SOURCES = rupchecker_z3_datatype.ml tseitincheck.ml parser.mly lexer.mll main.ml
OBJECTS = rupchecker_z3_datatype.cmo tseitincheck.cmo parser.cmo lexer.cmo main.cmo

all: satproofchecker

satproofchecker: $(OBJECTS)
	$(OCAMLC) -o satproofchecker $(OBJECTS)

rupchecker_z3_datatype.cmo: rupchecker_z3_datatype.ml rupchecker_z3_datatype.mli
	$(OCAMLC) -c rupchecker_z3_datatype.mli
	$(OCAMLC) -c rupchecker_z3_datatype.ml

tseitincheck.cmo: tseitincheck.ml
	$(OCAMLC) -c tseitincheck.ml

parser.ml parser.mli: parser.mly
	$(OCAMLYACC) parser.mly

parser.cmo: parser.ml parser.mli
	$(OCAMLC) -c parser.mli
	$(OCAMLC) -c parser.ml

lexer.ml: lexer.mll
	$(OCAMLLEX) lexer.mll

lexer.cmo: lexer.ml
	$(OCAMLC) -c lexer.ml

main.cmo: main.ml
	$(OCAMLC) -c main.ml

clean:
	rm -f *.cmo *.cmi *.ml *.mli satproofchecker parser.ml parser.mli lexer.ml
