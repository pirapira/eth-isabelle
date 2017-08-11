
all: juliaTest.native

juliaTest.native: julia.ml juliaUtil.ml juliaTest.ml
	./compile.sh

build: all
	./maketests.sh

test: all
	./runtests.sh


