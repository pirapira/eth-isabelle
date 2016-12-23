open Yojson.Basic
open Jsonparser
open Constant


let spec_includes_actual (spec_storage : list_storage) (touched : Word256.word256 list) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  let () = Printf.printf "sia\n" in
  (* for each touched index, check that the actual storage and the spec storage have the same thing. *)
  let f (idx : Word256.word256) =
    let () = Printf.printf " idx touched: %s\n" (Big_int.string_of_big_int (Conv.big_int_of_word256 idx)) in
    let () = Printf.printf " actual word: %s\n" (Conv.string_of_word256 (actual_storage idx)) in
    let actual_value : Big_int.big_int = Conv.big_int_of_word256 (actual_storage idx) in
    let spec_idx : Big_int.big_int = Conv.big_int_of_word256 idx in
    let spec_value = (* This procedure needs to be split away. *)
      try Big_int.big_int_of_string (Conv.bigint_assoc spec_idx spec_storage)
      with Not_found -> Big_int.zero_big_int
    in
    let () = Printf.printf " comparing idx: %s, actual: %s, spec: %s (by %s)\n" (Big_int.string_of_big_int (Conv.big_int_of_word256 idx))
                           (Big_int.string_of_big_int actual_value) (Big_int.string_of_big_int spec_value) (Big_int.string_of_big_int spec_idx) in
    let ret = Big_int.eq_big_int actual_value spec_value in
    let () = assert ret in
    ret
  in
  List.for_all f touched

let actual_includes_spec (spec_storage : list_storage) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  let () = Printf.printf "ais\n" in
  (* for each pair in spec_storage, check the actual_storage *)
  let f ((idx : Big_int.big_int), (v : string)) =
    let spec_value = Big_int.big_int_of_string v in
    let actual_idx = (Conv.word256_of_big_int idx) in
    let actual_value = Conv.big_int_of_word256 (actual_storage actual_idx) in
    let () = Printf.printf " comparing idx: %s spec: %s, actual: %s (by idx: %s)\n" (Big_int.string_of_big_int idx) (Big_int.string_of_big_int spec_value) (Big_int.string_of_big_int actual_value) (Conv.string_of_word256 actual_idx) in
    let ret = Big_int.eq_big_int spec_value actual_value in
    let () = assert ret in
    ret in
  List.for_all f spec_storage

let storage_comparison
      (addr : Word160.word160)
      (spec_post : (string * account_state) list)
      (touched : Word256.word256 list)
      (actual_storage : Word256.word256 -> Word256.word256) : bool =
  let spec_storage : list_storage =
    try
      let lookup_addr = Conv.string_of_address addr in
      (*      let () = Printf.printf "looking upa address %s\n" lookup_addr in *)
      let a : account_state = List.assoc lookup_addr spec_post in
      a.storage
    with Not_found -> [] in
  let ret0 = spec_includes_actual spec_storage touched actual_storage in
  (*   let () = Printf.printf "storage comparison done one direction\n" in *)
  let ret1 = actual_includes_spec spec_storage actual_storage in
  (*  let () = Printf.printf "storage comparison done \n" in *)
  ret0 && ret1

let balance_comparison
      (addr : Word160.word160)
      (spec_post : (string * account_state) list)
      (actual_balance : Word160.word160 -> Word256.word256) =
  let spec_balance : Big_int.big_int =
    try
      let lookup_addr = Conv.string_of_address addr in
      let a : account_state = List.assoc lookup_addr spec_post in
      a.balance
    with Not_found -> Big_int.zero_big_int in
  let actual_balance = Conv.big_int_of_word256 (actual_balance addr) in
  Big_int.eq_big_int spec_balance actual_balance

let test_one_case j : bool =
  let test_case : test_case = parse_test_case j in
  let open Evm in
  let open Conv in
  (*val program_sem : variable_ctx -> constant_ctx -> int -> nat -> program_result*)
  (* TODO: cut below as a function, maybe into Conv *)

  let addr : address = word160_of_big_int test_case.exec.address in
  let initial_storage : storage = lookup_storage addr test_case.pre in
  let initial_balance : address -> w256 = construct_global_balance test_case.pre in
  let v : variable_ctx =
    { vctx_stack = []
    ; vctx_memory = empty_memory
    ; vctx_memory_usage = Nat_big_num.of_int 0
    ; vctx_storage = initial_storage
    ; vctx_pc = Nat_big_num.of_int 0
    ; vctx_balance = initial_balance
    ; vctx_caller = word160_of_big_int test_case.exec.caller
    ; vctx_value_sent = word256_of_big_int test_case.exec.value
    ; vctx_data_sent = byte_list_of_hex_string test_case.exec.data
    ; vctx_storage_at_call = initial_storage
    ; vctx_balance_at_call = initial_balance
    ; vctx_origin = word160_of_big_int test_case.exec.origin
    ; vctx_ext_program = construct_ext_program test_case.pre
    ; vctx_block = construct_block_info test_case
    ; vctx_gas = Nat_big_num.of_string_nat (Big_int.string_of_big_int test_case.exec.gas)
    ; vctx_account_existence = construct_account_existence test_case.pre
    ; vctx_touched_storage_index = []
    } in
  let () = Conv.print_variable_ctx v in
  let c : constant_ctx =
    { cctx_program = test_case.exec.code
    ; cctx_this = Conv.word160_of_big_int test_case.exec.address
    } in
  let () = Conv.print_constant_ctx c in
  let number = Nat_big_num.of_string (Big_int.string_of_big_int test_case.exec.gas) in
  let ret : program_result = Evm.program_sem v c number (Nat_big_num.to_int number) in
  match ret with
  | ProgramStepRunOut -> false
  | ProgramToEnvironment (ContractCall carg, st, bal, touched, pushed_opt) ->
     let () = Printf.eprintf "We are not looking whatever happens after the contract calls\n" in
     true
  | ProgramToEnvironment (ContractCreate carg, st, bal, touched, pushed_opt) ->
     let () = Printf.eprintf "We are not looking whatever happens after the contract creates" in
     true
  | ProgramToEnvironment (ContractFail, st, bal, touched, pushed_opt) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | [], None, None, None, None -> true
       | _ -> failwith "some postconditions are there for a failing case"
     end
  | ProgramToEnvironment (ContractSuicide, st, bal, touched, pushed_opt) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | spec_created, Some spec_gas, Some spec_logs, Some spec_out, Some spec_post ->
          let () = Printf.eprintf "We are not filling in the gap of a transaction and a message call yet.  For the suicide case, this means we cannot compare the storage and the balance." in
          true
       | _ -> failwith "Some post conditions not available"
     end
  | ProgramToEnvironment (ContractReturn retval, st, bal, touched, None) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | spec_created, Some spec_gas, Some spec_logs, Some spec_out, Some spec_post ->
          let got_retval : string = hex_string_of_byte_list "0x" retval in
          let () = Printf.printf "got_retval: %s spec_out: %s\n%!" got_retval spec_out in
          let () = assert (got_retval = spec_out) in
          let () = assert (storage_comparison (Conv.word160_of_big_int test_case.exec.address) spec_post touched st) in
          let () = assert (balance_comparison (Conv.word160_of_big_int test_case.exec.address) spec_post bal) in
          true
       | _ -> failwith "Some post conditions not available"
     end
  | ProgramToEnvironment (ContractReturn retval, st, bal, touched, Some _) ->
     false
  | ProgramInvalid -> false
  | ProgramAnnotationFailure -> false
  | ProgramInit _ -> false

let test_one_file (path : string) : unit =
  let vm_arithmetic_test : json = Yojson.Basic.from_file path in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  List.iter
    (fun (label, j) ->
      let () = Printf.printf "===========================test case: %s\n" label in
      let success : bool = test_one_case j in
      assert success
    )
    vm_arithmetic_test_assoc

let () =
  let () = Printf.printf "hello\n" in
(*
  let () = test_one_file "../tests/VMTests/vmArithmeticTest.json" in
  let () = test_one_file "../tests/VMTests/vmBitwiseLogicOperationTest.json" in
  let () = test_one_file "../tests/VMTests/vmPushDupSwapTest.json" in
  let () = test_one_file "../tests/VMTests/vmInputLimitsLight.json" in
  let () = test_one_file "../tests/VMTests/vmInputLimits.json" in
  let () = test_one_file "../tests/VMTests/vmIOandFlowOperationsTest.json" in
  let () = test_one_file "../tests/VMTests/vmPerformanceTest.json" in
 *)
  (* don't know where to get the block headers from
  let () = test_one_file "../tests/VMTests/vmBlockInfoTest.json" in *)
  let () = test_one_file "../tests/VMTests/vmEnvironmentalInfoTest.json" in
  let () = Printf.printf "all tests passed.\n" in
  ()
