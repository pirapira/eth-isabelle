open Yojson.Basic

type blockHeader =
  (* XXX: If the hashes are just 256-bit values, they can also be encoded as big_int *)
  { bhBloom : string
  ; bhCoinbase : Big_int.big_int
  ; bhDifficulty : Big_int.big_int
  ; bhExtraData : string
  ; bhGasLimit : Big_int.big_int
  ; bhGasUsed : Big_int.big_int
  ; bhHash : string
  ; bhMixHash : string
  ; bhNonce : Big_int.big_int
  ; bhNumber : Big_int.big_int
  ; bhParentHash : string
  ; bhReceiptTrie : string
  ; bhStateRoot : string
  ; bhTimestamp : Big_int.big_int
  ; bhTransactionsTrie : string
  ; bhUncleHash : string
  }

val parse_block_header : json -> blockHeader

val format_block_header : blockHeader -> Easy_format.t

type transaction =
  { transactionData : string
  ; transactionGasLimit : Big_int.big_int
  ; transactionGasPrice : Big_int.big_int
  ; transactionNonce : Big_int.big_int
  ; transactionR : Big_int.big_int
  ; transactionS : Big_int.big_int
  ; transactionTo : Big_int.big_int
  ; transactionV : Big_int.big_int
  ; transactionValue : Big_int.big_int
  }

val parse_transaction : json -> transaction

val format_transaction : transaction -> Easy_format.t

type block =
  { blockHeader : blockHeader
  ; blockNumber : Big_int.big_int option
  ; blockRLP : string
  ; blockTransactions : transaction list
  ; blockUncleHeaders : blockHeader list (* ?? *)
  }

exception UnsupportedEncoding

(** [parse_block] parses a Json document into a block.  When the Json document does not contain fields, throws
    [UnsupportedEncoding] exception. *)
val parse_block : json -> block

val format_block : block -> Easy_format.t

(* I think I can reuse existing parsers for genesisBlockHeader, genesisRLP, lastblockhash and postState *)

type testCase =
  { bcCaseBlocks : block list
  ; bcCaseGenesisBlockHeader : blockHeader
  ; bcCaseGenesisRLP : string
  ; bcCaseLastBlockhash : string
  ; bcCasePostState : (string * VmTestParser.account_state) list
  ; bcCasePreState : (string * VmTestParser.account_state) list
  }

val parse_test_file : json -> (string * testCase) list

val format_test_case : testCase -> Easy_format.t
