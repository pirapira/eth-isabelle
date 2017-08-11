rm -rf lem
mkdir lem
cp ../lem/*.ml lem
# lem -ocaml -lib ../lem julia.lem
MENHIRFLAGS=--infer ocamlbuild -use-menhir -use-ocamlfind -cflag -g -lflag -g -pkgs bignum,batteries juliaTest.native



