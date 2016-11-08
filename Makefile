.PHONY: all all-isabelle deed

all: all-isabelle deed lem-check

all-isabelle:
	isabelle build -d . all

deed: document/output.pdf
document/output.pdf:
	sh document_generation.sh

lem-check: lem/Block.thy lem/Evm.thy lem/EvmNonExec.thy lem/Keccak.thy lem/Rlp.thy lem/Word160.thy lem/Word256.thy lem/Word8.thy

lem/Block.thy:
	lem -isa lem/block.lem

lem/Evm.thy:
	lem -isa lem/evm.lem

lem/EvmNonExec.thy:
	lem -isa lem/evmNonExec.lem

lem/Keccak.thy:
	lem -isa lem/keccak.lem

lem/Rlp.thy:
	lem -isa lem/rlp.lem

lem/Word160.thy:
	lem -isa lem/word160.lem

lem/Word256.thy:
	lem -isa lem/word256.lem

lem/Word8.thy:
	lem -isa lem/word8.lem
