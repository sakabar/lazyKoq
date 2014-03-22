COQC = coqc
OCAMLC = ocamlc
.SUFFIXES: .ml .mli .cmo .cmi

main: lazykoq.cmo parser.cmo lexer.cmo main.cmo
	$(OCAMLC) -o $@ $^

lazykoq.ml: Lazykoq.v
	$(COQC) $^

lazykoq.mli: Lazykoq.v
	$(COQC) $^

lazykoq.cmi: lazykoq.mli
	$(OCAMLC) -c $^

%.cmo: %.cmi %.ml
	$(OCAMLC) -c $*.ml

.mli.cmi:
	$(OCAMLC) -c $<

parser.cmi: lazykoq.mli parser.mli
	$(OCAMLC) -c parser.mli

parser.cmo: lazykoq.cmo parser.cmi parser.ml
	$(OCAMLC) -c parser.ml

parser.ml parser.mli: parser.mly
	ocamlyacc $^

lexer.ml: lexer.mll
	ocamllex $^

# lexer.cmi: lazykoq.mli lexer.mli
# 	$(OCAMLC) -c lexer.mli

lexer.cmo: lazykoq.cmo lexer.ml parser.cmo
	$(OCAMLC) -c lexer.ml


.PHONY: clean
clean:
	rm -f *.vo *.glob *.mli *.cmi *.cmo parser.ml parser.mli lexer.ml a.out Lazykoq.ml Lazykoq.mli lazykoq
