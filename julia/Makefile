
all: juliaTest.native

juliaTest.native: julia.ml juliaUtil.ml juliaTest.ml
	sh ./compile.sh

build: all
	sh ./maketests.sh

test: all
	sh ./runtests.sh


