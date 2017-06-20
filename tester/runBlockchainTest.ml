open Yojson.Basic

exception SkipTest

let parsed_transaction_into_model_transaction tr : Block.transaction =
  failwith "parsed_transaction_into_model_transaction"

let test_one_case (path : string) (case_name, test) =
  let strip_singleton_list lst =
    if List.length lst <> 1 then raise SkipTest else List.nth lst 0 in
  try
    let block = strip_singleton_list test.BlockchainTestParser.bcCaseBlocks in
    let tr = strip_singleton_list block.BlockchainTestParser.blockTransactions in
    let tr = parsed_transaction_into_model_transaction tr in
    let pre_st = test.BlockchainTestParser.bcCasePreState in
    let pre_st = List.map (fun (a,b,_) -> (a,b)) (StateTestLib.make_state_list pre_st) in
    let post_st = test.BlockchainTestParser.bcCasePostState in
    let post_st = StateTestLib.make_state_list post_st in
    let state (x : Word160.word160) = try List.assoc x pre_st with _ -> Block.empty_account0 x in
    let block_info = BlockchainTestParser.block_info_of block in
    let net = Evm.network_of_block_number (Word256.word256ToNatural (block_info.Evm.block_number)) in
    let state = StateTestLib.run_tr tr state block_info net in
    let diff_found = ref false in
    List.iter (fun (a,cmp, storage_list) ->
      let acc = state a in
      if acc.Block.account_balance0 <> cmp.Block.account_balance0 then begin
        Printf.printf "address %s has balance %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.Block.account_balance0)
         (Conv.decimal_of_word256 cmp.Block.account_balance0);
        diff_found := true
      end;
      if acc.Block.account_nonce <> cmp.Block.account_nonce then begin
        Printf.printf "address %s has nonce %s, but it should be %s!\n%!" (Conv.string_of_address a) (Conv.decimal_of_word256 acc.Block.account_nonce)
         (Conv.decimal_of_word256 cmp.Block.account_nonce);
         diff_found := true
      end;
      List.iter (StateTestLib.compare_storage diff_found a acc.Block.account_storage0) storage_list) post_st;
    (if !diff_found then () else ())
  with SkipTest ->
    Printf.printf "...... skipping %s\n" case_name

let test_one_file path =
  let () = Printf.printf "file: %s\n" path in
  let j = Yojson.Basic.from_file path in
  let () = Printf.printf ".... JSON parsed!\n" in
  try
    let testCases = BlockchainTestParser.parse_test_file j in
    let () = Printf.printf ".... test parsed!\n" in
    let () = List.iter (test_one_case path) testCases in
    ()
  with BlockchainTestParser.UnsupportedEncoding ->
    let () = Printf.printf ".... has an unsupported encoding.\n" in
    ()

let _ =
  let () = Printf.printf "runBlockchainTest is not running any test yet. \n%!" in
  let () = TraverseJsons.traverse "../tests/BlockchainTests" test_one_file in
  ()
