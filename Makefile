.PHONY: all all-isabelle deed

all: all-isabelle deed lem-check

all-isabelle: KEC.thy FunctionalCorrectness.thy Parse.thy ContractEnv.thy Instructions.thy ContractSem.thy RelationalSem.thy HP.thy YellowPaper.thy example/Optimization.thy example/AlwaysFail.thy example/FailOnReentrance.thy example/Deed.thy
	isabelle build -d . all

deed: document/output.pdf
document/output.pdf: KEC.thy ContractEnv.thy Instructions.thy ContractSem.thy RelationalSem.thy example/Deed.thy document/root.tex
	sh document_generation.sh

lem-thy: lem/Block.thy lem/Evm.thy lem/EvmNonExec.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy

lem/block.lem: lem/evm.lem
	touch lem/block.lem

lem/Block.thy: lem/block.lem
	lem -isa lem/block.lem

lem/evm.lem: lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/evm.lem

lem/Evm.thy: lem/evm.lem
	lem -isa lem/evm.lem

lem/Evm-use_inc.tex lem/Evm-inc.tex: lem/evm.lem
	lem -tex lem/evm.lem

lem/Evm-use_inc.pdf: lem/Evm-use_inc.tex lem/Evm-inc.tex
	cd lem; pdflatex Evm-use_inc.tex; pdflatex Evm-use_inc.tex

lem/evmNonExec.lem: lem/evm.lem lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/evmNonExec.lem

lem/EvmNonExec.thy: lem/evmNonExec.lem
	lem -isa lem/evmNonExec.lem

lem/keccak.lem: lem/word8.lem lem/evm.lem
	touch lem/keccak.lem

lem/Keccak.thy: lem/keccak.lem
	lem -isa lem/keccak.lem

lem/rlp.lem: lem/word256.lem lem/word160.lem lem/word8.lem
	touch lem/rlp.lem

lem/Rlp.thy: lem/rlp.lem
	lem -isa lem/rlp.lem

lem/Word160.thy: lem/word160.lem
	lem -isa lem/word160.lem

lem/Word256.thy: lem/word256.lem
	lem -isa lem/word256.lem

lem/Word8.thy: lem/word8.lem
	lem -isa lem/word8.lem
