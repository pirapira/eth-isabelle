.PHONY: all all-isabelle deed clean clean-pdf clean-thy clean-ocaml lem-thy lem-pdf lem-ocaml doc lem-coq clean-coq

all: all-isabelle lem-thy lem-pdf lem-ocaml lem-coq deed doc

clean: clean-pdf clean-thy clean-ocaml clean-coq

clean-pdf:
	rm -rf lem/*.tex lem/*.aux lem/*.log lem/*.toc lem/*.pdf lem/*~

clean-thy:
	git clean -fx lem/*.thy

clean-ocaml:
	git clean -fx lem/*.ml

clean-coq:
	git clean -fx lem/*.v

all-isabelle: attic/Parse.thy ContractSem.thy RelationalSem.thy example/Optimization.thy example/AlwaysFail.thy example/FailOnReentrance.thy example/Deed.thy lem/Block.thy lem/Evm.thy lem/EvmNonExec.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy
	isabelle build -d . all

doc: deed lem-pdf

deed: document/output.pdf
document/output.pdf: ContractSem.thy RelationalSem.thy example/Deed.thy document/root.tex lem/Evm.thy lem/Word256.thy lem/Word160.thy lem/Word8.thy lem/Keccak.thy
	sh document_generation.sh

lem-thy: lem/Block.thy lem/Evm.thy lem/EvmNonExec.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy lem/Keccak.thy

lem-coq: lem/block.v lem/evm.v lem/keccak.v lem/rlp.v lem/word160.v lem/word256.v lem/word8.v lem/keccak.v

lem-pdf: lem/Evm-use_inc.pdf lem/Block-use_inc.pdf lem/EvmNonExec-use_inc.pdf lem/Keccak-use_inc.pdf lem/Rlp-use_inc.pdf

lem-ocaml: lem/evm.ml lem/word256.ml lem/word160.ml lem/word8.ml lem/keccak.ml

lem/block.lem: lem/evm.lem
	touch lem/block.lem

lem/Block.thy: lem/block.lem
	lem -isa lem/block.lem

lem/block.v: lem/block.lem
	lem -coq lem/block.lem

lem/Block-use_inc.tex lem/Block-inc.tex: lem/block.lem
	lem -tex lem/block.lem
	sed 's/default/defWithComment/g' lem/Block-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Block-inc.tex


lem/Block-use_inc.pdf: lem/Block-use_inc.tex lem/Block-inc.tex
	cd lem; pdflatex Block-use_inc.tex; pdflatex Block-use_inc.tex

lem/evm.lem: lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/evm.lem

lem/Evm.thy: lem/evm.lem
	lem -isa lem/evm.lem

lem/evm.v: lem/evm.lem
	lem -coq lem/evm.lem

lem/evm.ml: lem/evm.lem
	lem -ocaml lem/evm.lem

lem/keccak.ml: lem/keccak.lem
	lem -ocaml lem/keccak.lem

lem/keccak.v: lem/keccak.lem
	lem -coq lem/keccak.lem

lem/word256.ml: lem/word256.lem
	lem -ocaml lem/word256.lem

lem/word160.ml: lem/word160.lem
	lem -ocaml lem/word160.lem

lem/word8.ml: lem/word8.lem
	lem -ocaml lem/word8.lem

lem/Evm-use_inc.tex lem/Evm-inc.tex: lem/evm.lem
	lem -tex lem/evm.lem
	sed 's/default/defWithComment/g' lem/Evm-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/Evm-inc.tex

lem/Evm-use_inc.pdf: lem/Evm-use_inc.tex lem/Evm-inc.tex
	cd lem; pdflatex Evm-use_inc.tex; pdflatex Evm-use_inc.tex

lem/evmNonExec.lem: lem/evm.lem lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/evmNonExec.lem

lem/EvmNonExec.thy: lem/evmNonExec.lem
	lem -isa lem/evmNonExec.lem

lem/EvmNonExec-use_inc.tex lem/EvmNonExec-inc.tex: lem/evmNonExec.lem
	lem -tex lem/evmNonExec.lem
	sed 's/default/defWithComment/g' lem/EvmNonExec-inc.tex > lem/tmp.txt
	mv lem/tmp.txt lem/EvmNonExec-inc.tex

lem/EvmNonExec-use_inc.pdf: lem/EvmNonExec-use_inc.tex lem/EvmNonExec-inc.tex
	cd lem; pdflatex EvmNonExec-use_inc.tex; pdflatex EvmNonExec-use_inc.tex

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

lem/rlp.v: lem/rlp.lem
	lem -coq lem/rlp.lem

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

lem/word8.v: lem/word8.lem
	lem -coq lem/word8.lem
lem/word160.v: lem/word160.lem
	lem -coq lem/word160.lem

lem/word256.v: lem/word256.lem
	lem -coq lem/word256.lem

lem/Word8.v: lem/word8.lem
	lem -coq lem/word8.lem
