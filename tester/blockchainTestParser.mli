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
  ; blockNumber : Big_int.big_int
  ; blockRLP : string
  ; blockTransactions : transaction list
  ; blockUncleHeaders : blockHeader list (* ?? *)
  }

val parse_block : json -> block

val format_block : block -> Easy_format.t
