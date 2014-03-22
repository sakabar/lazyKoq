coqc Lazykoq.v
ocamllex lexer.mll
ocamlyacc parser.mly

#何故か悪さする。
# $/Users/sak/Dropbox/mba/lazyKoq%ocamlc -c parser.mli 
# File "parser.mli", line 10, characters 48-60:
# Error: Unbound type constructor Lazykoq.expr
rm -f parser.mli 

ocamlc -c lazykoq.mli
ocamlc -c lazykoq.ml

ocamlc -c parser.ml
ocamlc -c lexer.ml
ocamlc -c main.ml

ocamlc -o lazykoq lazykoq.cmo parser.cmo lexer.cmo main.cmo
