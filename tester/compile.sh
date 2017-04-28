cd ..; make lem-ocaml; cd tester
rm -rf lem
mkdir lem
cp ../lem/*.ml lem
BISECT_COVERAGE=YES ocamlbuild -use-ocamlfind -cflag -g -lflag -g -pkgs yojson,bignum,batteries,ecc jsonTest.native evmTest.native runVmTest.native kecTest.native stateTest.native ecdsademo.native stateTestReturnStatus.native runBlockchainTest.native
