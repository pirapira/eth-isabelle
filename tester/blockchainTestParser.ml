open Yojson.Basic
open VmTestParser

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

let parse_block_header (j : json) : blockHeader =
  try
  Util.(
    { bhBloom = to_string (member "bloom" j)
    ; bhCoinbase = parse_address_from_field "coinbase" j
    ; bhDifficulty = parse_address_from_field "difficulty" j
    ; bhExtraData = to_string (member "extraData" j)
    ; bhGasLimit = parse_address_from_field "gasLimit" j
    ; bhGasUsed = parse_address_from_field "gasUsed" j
    ; bhHash = to_string (member "hash" j)
    ; bhMixHash = to_string (member "mixHash" j)
    ; bhNonce = parse_address_from_field "nonce" j
    ; bhNumber = parse_address_from_field "number" j
    ; bhParentHash = to_string (member "parentHash" j)
    ; bhReceiptTrie = to_string (member "receiptTrie" j)
    ; bhStateRoot = to_string (member "stateRoot" j)
    ; bhTimestamp = parse_address_from_field "timestamp" j
    ; bhTransactionsTrie = to_string (member "transactionsTrie" j)
    ; bhUncleHash = to_string (member "uncleHash" j)
  })
  with e ->
       let () = Printf.eprintf "error in parse_block_header\n%!" in
       raise e


let format_block_header (bh : blockHeader) : Easy_format.t =
  try
  let open Easy_format in
  let lst : t list =
    [ Label ((Atom ("bloom", atom), label), Atom (bh.bhBloom, atom))
    ; Label ((Atom ("coinbase", atom), label), Atom (Big_int.string_of_big_int bh.bhCoinbase, atom))
    ; Label ((Atom ("difficulty", atom), label), Atom (Big_int.string_of_big_int bh.bhDifficulty, atom))
    ; Label ((Atom ("extraData", atom), label), Atom (bh.bhExtraData, atom))
    ; Label ((Atom ("gasLimit", atom), label), Atom (Big_int.string_of_big_int bh.bhGasLimit, atom))
    ; Label ((Atom ("gasUsed", atom), label), Atom (Big_int.string_of_big_int bh.bhGasUsed, atom))
    ; Label ((Atom ("hash", atom), label), Atom (bh.bhHash, atom))
    ; Label ((Atom ("mixHash", atom), label), Atom (bh.bhMixHash, atom))
    ; Label ((Atom ("nonce", atom), label), Atom (Big_int.string_of_big_int bh.bhNonce, atom))
    ; Label ((Atom ("number", atom), label), Atom (Big_int.string_of_big_int bh.bhNumber, atom))
    ; Label ((Atom ("parentHash", atom), label), Atom (bh.bhParentHash, atom))
    ; Label ((Atom ("receiptTrie", atom), label), Atom (bh.bhReceiptTrie, atom))
    ; Label ((Atom ("stateRoot", atom), label), Atom (bh.bhStateRoot, atom))
    ; Label ((Atom ("timestamp", atom), label), Atom (Big_int.string_of_big_int bh.bhTimestamp, atom))
    ] in
  List (("{", ",", "}", list), lst)
  with e ->
    let () = Printf.eprintf "error in format_block_header\n%!" in
    raise e

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

let parse_transaction (j : json) : transaction =
  let open Util in
  { transactionData = to_string (member "data" j)
  ; transactionGasLimit = parse_address_from_field "gasLimit" j
  ; transactionGasPrice = parse_address_from_field "gasPrice" j
  ; transactionNonce = parse_address_from_field "nonce" j
  ; transactionR = parse_address_from_field "r" j
  ; transactionS = parse_address_from_field "s" j
  ; transactionTo = parse_address_from_field "to" j
  ; transactionV = parse_address_from_field "v" j
  ; transactionValue = parse_address_from_field "value" j
  }

let format_transaction (t : transaction) : Easy_format.t =
  let open Easy_format in
  let lst : t list =
    [ Label ((Atom ("data", atom), label), Atom (t.transactionData, atom))
    ; Label ((Atom ("gasLimit", atom), label), Atom (Big_int.string_of_big_int t.transactionGasLimit, atom))
    ; Label ((Atom ("gasPrice", atom), label), Atom (Big_int.string_of_big_int t.transactionGasPrice, atom))
    ; Label ((Atom ("nonce", atom), label), Atom (Big_int.string_of_big_int t.transactionNonce, atom))
    ; Label ((Atom ("r", atom), label), Atom (Big_int.string_of_big_int t.transactionR, atom))
    ; Label ((Atom ("s", atom), label), Atom (Big_int.string_of_big_int t.transactionS, atom))
    ; Label ((Atom ("to", atom), label), Atom (Big_int.string_of_big_int t.transactionTo, atom))
    ; Label ((Atom ("v", atom), label), Atom (Big_int.string_of_big_int t.transactionV, atom))
    ; Label ((Atom ("value", atom), label), Atom (Big_int.string_of_big_int t.transactionValue, atom))
    ] in
  List (("{", ",", "}", list), lst)

type block =
  { blockHeader : blockHeader
  ; blockNumber : Big_int.big_int
  ; blockRLP : string
  ; blockTransactions : transaction list
  ; blockUncleHeaders : blockHeader list (* ?? *)
  }

let parse_block (j : json) : block =
  let open Util in
  { blockHeader = parse_block_header (member "blockHeader" j)
  ; blockNumber =
      (try parse_big_int_from_field "blocknumber" j
       with e ->
         let () = Printf.eprintf "error in parsing blockNumber\n%!" in
         raise e)
  ; blockRLP = to_string (member "rlp" j)
  ; blockTransactions =
      List.map parse_transaction (to_list (member "transactions" j))
  ; blockUncleHeaders =
      List.map parse_block_header (to_list (member "uncleHeaders" j))
  }

let format_block (b : block) : Easy_format.t =
  let open Easy_format in
  let lst : t list =
    [ Label ((Atom ("blockHeader", atom), label), format_block_header b.blockHeader)
    ; Label ((Atom ("blockNumber", atom), label), Atom (Big_int.string_of_big_int b.blockNumber, atom))
    ; Label ((Atom ("rlp", atom), label), Atom (b.blockRLP, atom))
    ; Label ((Atom ("transactions", atom), label),
             List (("[", ",", "]", list), List.map format_transaction b.blockTransactions))
    ; Label ((Atom ("uncleHeaders", atom), label),
             List (("[", ",", "]", list), List.map format_block_header b.blockUncleHeaders))
    ] in
  List (("{", ",", "}", list), lst)
