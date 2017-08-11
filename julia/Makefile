
all: juliaTest.native

juliaTest.native: julia.lem juliaUtil.ml juliaTest.ml
	../lem -ocaml *.lem
	./compile.sh

build: all
	./maketests.sh

test: all
	./runtests.sh


