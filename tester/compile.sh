BISECT_COVERAGE=YES ocamlbuild -use-ocamlfind -cflag -g -lflag -g -pkgs yojson,bignum,batteries jsonTest.native evmTest.native runVmTest.native kecTest.native
