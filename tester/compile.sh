cd ..; make lem-ocaml; cd tester
rm -rf lem
mkdir lem
cp ../lem/*.ml lem
rm -f lem/rlp.ml
BISECT_COVERAGE=YES ocamlbuild -use-ocamlfind -cflag -g -lflag -g -pkgs secp256k1,yojson,bignum,batteries,ecc,rlp jsonTest.native evmTest.native runVmTest.native kecTest.native stateTest.native ecdsademo.native stateTestReturnStatus.native runBlockchainTest.native
