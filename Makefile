.PHONY: all all-isabelle light-isabelle deed clean clean-pdf clean-thy clean-ocaml clean-hol lem-thy lem-pdf lem-hol lem-ocaml doc

all: all-isabelle deed lem-thy lem-pdf lem-ocaml lem-hol doc

clean: clean-pdf clean-thy clean-ocaml clean-hol

clean-pdf:
	rm -rf lem/*.tex lem/*.aux lem/*.log lem/*.toc lem/*.pdf lem/*~

clean-thy:
	git clean -fx lem/*.thy

clean-hol:
	git clean -fx lem/*.sml

clean-ocaml:
	git clean -fx lem/*.ml

all-isabelle: attic/Parse.thy ContractSem.thy RelationalSem.thy example/Optimization.thy example/AlwaysFail.thy example/FailOnReentrance.thy example/Deed.thy lem/Block.thy lem/Evm.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy lem/Word4.thy HoareTripleForInstructions.thy HoareTripleForInstructions2.thy
	isabelle build -j 2 -d . all

light-isabelle: attic/Parse.thy ContractSem.thy RelationalSem.thy example/Optimization.thy example/AlwaysFail.thy example/FailOnReentrance.thy lem/Block.thy lem/Evm.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy lem/Word4.thy HoareTripleForInstructions.thy HoareTripleForInstructions2.thy
	isabelle build -b -j 2 -v -d . light

doc: deed lem-pdf

deed: document/output.pdf
document/output.pdf: ContractSem.thy RelationalSem.thy example/Deed.thy document/root.tex lem/Evm.thy lem/Word256.thy lem/Word160.thy lem/Word8.thy lem/Keccak.thy
	sh document_generation.sh

simplewallet: document/simplewallet.pdf
document/simplewallet.pdf: ContractSem.thy RelationalSem.thy example/Deed.thy document/root.tex lem/Evm.thy lem/Word256.thy lem/Word160.thy lem/Word8.thy lem/Keccak.thy
	sh wallet_generation.sh

lem-thy: lem/Block.thy lem/Evm.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy lem/Keccak.thy lem/Word4.thy

lem-hol: lem/blockScript.sml lem/evmScript.sml lem/keccakScript.sml lem/rlpScript.sml lem/word160Script.sml lem/word256Script.sml lem/word8Script.sml lem/keccakScript.sml lem/word4Script.sml

lem-pdf: lem/Evm-use_inc.pdf lem/Block-use_inc.pdf lem/Keccak-use_inc.pdf lem/Rlp-use_inc.pdf

lem-ocaml: lem/evm.ml lem/word256.ml lem/word160.ml lem/word8.ml lem/keccak.ml lem/word4.ml

lem/block.lem: lem/evm.lem
	touch lem/block.lem

lem/Block.thy: lem/block.lem
	lem -isa lem/block.lem

lem/blockScript.sml: lem/block.lem
	lem -hol lem/block.lem

lem/Block-use_inc.tex lem/Block-inc.tex: lem/block.lem
	lem -tex lem/block.lem
	sed 's/default/defWithComment/g' lem/Block-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Block-inc.tex


lem/Block-use_inc.pdf: lem/Block-use_inc.tex lem/Block-inc.tex
	cd lem; pdflatex Block-use_inc.tex; pdflatex Block-use_inc.tex

lem/evm.lem: lem/word256.lem lem/word160.lem lem/word8.lem lem/word4.lem
	touch lem/evm.lem

lem/Evm.thy: lem/evm.lem
	lem -isa lem/evm.lem

lem/evmScript.sml: lem/evm.lem
	lem -hol lem/evm.lem

lem/evm.ml: lem/evm.lem
	lem -ocaml lem/evm.lem

lem/keccak.ml: lem/keccak.lem
	lem -ocaml lem/keccak.lem

lem/keccakScript.sml: lem/keccak.lem
	lem -hol lem/keccak.lem

lem/word256.ml: lem/word256.lem
	lem -ocaml lem/word256.lem

lem/word256Script.sml: lem/word256.lem
	lem -hol lem/word256.lem

lem/word160.ml: lem/word160.lem
	lem -ocaml lem/word160.lem

lem/word160Script.sml: lem/word160.lem
	lem -hol lem/word160.lem

lem/word8.ml: lem/word8.lem
	lem -ocaml lem/word8.lem

lem/word4.ml: lem/word4.lem
	lem -ocaml lem/word4.lem

lem/word8Script.sml: lem/word8.lem
	lem -hol lem/word8.lem

lem/word4Script.sml: lem/word4.lem
	lem -hol lem/word4.lem

lem/Evm-use_inc.tex lem/Evm-inc.tex: lem/evm.lem
	lem -tex lem/evm.lem
	sed 's/default/defWithComment/g' lem/Evm-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Evm-inc.tex

lem/Evm-use_inc.pdf: lem/Evm-use_inc.tex lem/Evm-inc.tex
	cd lem; pdflatex Evm-use_inc.tex; pdflatex Evm-use_inc.tex

lem/keccak.lem: lem/word8.lem lem/evm.lem
	touch lem/keccak.lem

lem/Keccak.thy: lem/keccak.lem
	lem -isa lem/keccak.lem

lem/Keccak-use_inc.tex lem/Keccak-inc.tex: lem/keccak.lem
	lem -tex lem/keccak.lem
	sed 's/default/defWithComment/g' lem/Keccak-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Keccak-inc.tex

lem/Keccak-use_inc.pdf: lem/Keccak-use_inc.tex lem/Keccak-inc.tex
	cd lem; pdflatex Keccak-use_inc.tex; pdflatex Keccak-use_inc.tex

lem/rlp.lem: lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/rlp.lem

lem/Rlp.thy: lem/rlp.lem
	lem -isa lem/rlp.lem

lem/rlpScript.sml: lem/rlp.lem
	lem -hol lem/rlp.lem

lem/Rlp-use_inc.tex lem/Rlp-inc.tex: lem/rlp.lem
	lem -tex lem/rlp.lem
	sed 's/default/defWithComment/g' lem/Rlp-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Rlp-inc.tex

lem/Rlp-use_inc.pdf: lem/Rlp-use_inc.tex lem/Rlp-inc.tex
	cd lem; pdflatex Rlp-use_inc.tex; pdflatex Rlp-use_inc.tex

lem/Word160.thy: lem/word160.lem
	lem -isa lem/word160.lem

lem/Word256.thy: lem/word256.lem
	lem -isa lem/word256.lem

lem/Word8.thy: lem/word8.lem
	lem -isa lem/word8.lem

lem/Word4.thy: lem/word4.lem
	lem -isa lem/word4.lem
