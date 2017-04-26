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
