let () =
  let () = Printf.printf "49 is as bool list %s\n"
                         (Conv.string_of_bool_list (Word64.boolListFromWord64 (Int64.of_int 49))) in
  let () = Printf.printf "'256' is hashed into %s\n"
                (Conv.string_of_byte_list
                   (Keccak.keccak' (List.map Conv.byte_of_int [50;53;54]))) in
  let () = Printf.printf
             "the last 64 word is split into %s\n"
             (Conv.string_of_byte_list
                (List.rev (Keccak.word_rsplit
                             (Big_int.int64_of_big_int
                             (Big_int.big_int_of_string
"9223372036854775807"))))) in
  let () = Printf.printf
             "the last 64 word is split into a boollist %s\n"
             (Conv.string_of_bool_list
                (Word64.boolListFromWord64
                             (Big_int.int64_of_big_int
                             (Big_int.big_int_of_string "-5899601735930514117")))) in
  let t : BlockchainTestParser.transaction =
    let zero = Big_int.zero_big_int in
    { transactionData = ""
    ; transactionGasLimit = zero
    ; transactionGasPrice = zero
    ; transactionNonce = zero
    ; transactionTo = Some (Big_int.big_int_of_string "0x944400f4b88ac9589a0f17ed4671da26bddb668b")
    ; transactionValue = Big_int.big_int_of_int 1000
    ; transactionR = zero (* dummy: not signed yet *)
    ; transactionS = zero (* dummy: not signed yet *)
    ; transactionV = zero (* dummy: not signed yet *)
    } in
  let hex_to_byte_list = failwith "hex_to_byte_list" in
  let () = assert (BlockchainTestParser.rlp_of_transaction t = hex_to_byte_list "0xdc80808094944400f4b88ac9589a0f17ed4671da26bddb668b8203e880") in

  (* from ~/src/cpp-ethereum2/test/unittests/libdevcrypto/crypto.cpp *)
  (* Transaction(u256 const& _value, u256 const& _gasPrice, u256 const& _gas, Address const& _dest,                      bytes const& _data, u256 const& _nonce, Secret const& _secret): *)
  (*            (              1000,                     0,                0, h160(fromHex("944400f4b88ac9589a0f17ed4671da26bddb668b")), {}, 0, p.secret()) *)
  ()
