open Yojson.Basic
open Jsonparser
open Constant


let spec_includes_actual (spec_storage : list_storage) (touched : Word256.word256 list) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  (* for each touched index, check that the actual storage and the spec storage have the same thing. *)
  let f (idx : Word256.word256) =
    let () = Printf.printf " idx touched: %s\n" (Big_int.string_of_big_int (Conv.big_int_of_word256 idx)) in
    let () = Printf.printf " actual word: %s\n" (Conv.string_of_word256 (actual_storage idx)) in
    let actual_value : Big_int.big_int = Conv.big_int_of_word256 (actual_storage idx) in
    let spec_value = (* This procedure needs to be split away. *)
      try Big_int.big_int_of_string (Conv.bigint_assoc (Conv.big_int_of_word256 idx) spec_storage)
      with Not_found -> Big_int.zero_big_int
    in
    let () = Printf.printf " comparing idx: %s, actual: %s, spec: %s\n" (Big_int.string_of_big_int (Conv.big_int_of_word256 idx))
                           (Big_int.string_of_big_int actual_value) (Big_int.string_of_big_int spec_value) in
    let ret = Big_int.eq_big_int actual_value spec_value in
    let () = assert ret in
    ret
  in
  List.for_all f touched

let actual_includes_spec (spec_storage : list_storage) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  (* for each pair in spec_storage, check the actual_storage *)
  let f ((idx : Big_int.big_int), (v : string)) =
    let spec_value = Big_int.big_int_of_string v in
    let actual_value = Conv.big_int_of_word256 (actual_storage (Conv.word256_of_big_int idx)) in
    let () = Printf.printf " comparing idx: %s spec: %s, actual: %s\n" (Big_int.string_of_big_int idx) (Big_int.string_of_big_int spec_value) (Big_int.string_of_big_int actual_value) in
    let ret = Big_int.eq_big_int spec_value actual_value in
    let () = assert ret in
    spec_value = actual_value in
  List.for_all f spec_storage

let storage_comparison
      (addr : Word160.word160)
      (spec_post : (string * account_state) list)
      (touched : Word256.word256 list)
      (actual_storage : Word256.word256 -> Word256.word256) : bool =
  let spec_storage : list_storage =
    try
      let a : account_state = List.assoc (Conv.string_of_address addr) spec_post in
      a.storage
    with Not_found -> [] in
  spec_includes_actual spec_storage touched actual_storage &&
    actual_includes_spec spec_storage actual_storage

(* for now executes the first vmTest found in a particular file *)
let () =
  let () = Printf.printf "hello\n" in
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let (label, j) = List.nth vm_arithmetic_test_assoc 0 in
  let () = Printf.printf "test case: %s\n" label in
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
    ; vctx_memory_usage = 0
    ; vctx_storage = initial_storage
    ; vctx_pc = 0
    ; vctx_balance = initial_balance
    ; vctx_caller = word160_of_big_int test_case.exec.caller
    ; vctx_value_sent = word256_of_big_int test_case.exec.value
    ; vctx_data_sent = byte_list_of_hex_string test_case.exec.data
    ; vctx_storage_at_call = initial_storage
    ; vctx_balance_at_call = initial_balance
    ; vctx_origin = word160_of_big_int test_case.exec.origin
    ; vctx_ext_program = construct_ext_program test_case.pre
    ; vctx_block = construct_block_info test_case
    ; vctx_gas = Big_int.int_of_big_int test_case.exec.gas
    ; vctx_account_existence = construct_account_existence test_case.pre
    ; vctx_touched_storage_index = []
    } in
  let () = Conv.print_variable_ctx v in
  let c : constant_ctx =
    { cctx_program = test_case.exec.code
    ; cctx_this = Conv.word160_of_big_int test_case.exec.address
    } in
  let () = Conv.print_constant_ctx c in
  let number = Big_int.int_of_big_int test_case.exec.gas in
  let ret : program_result = Evm.program_sem v c number number in
  match ret with
  | ProgramStepRunOut -> failwith "runout"
  | ProgramToEnvironment (ContractCall carg, st, bal, touched, pushed_opt) -> failwith "call"
  | ProgramToEnvironment (ContractCreate carg, st, bal, touched, pushed_opt) -> failwith "create"
  | ProgramToEnvironment (ContractFail, st, bal, touched, pushed_opt) -> failwith "fail"
  | ProgramToEnvironment (ContractSuicide, st, bal, touched, pushed_opt) -> failwith "suicide"
  | ProgramToEnvironment (ContractReturn retval, st, bal, touched, pushed_opt) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | spec_created, Some spec_gas, Some spec_logs, Some spec_out, Some spec_post ->
          let got_retval : string = hex_string_of_byte_list "0x" retval in
          let () = assert (got_retval = spec_out) in
          let () = assert (storage_comparison (Conv.word160_of_big_int test_case.exec.address) spec_post touched st) in
          failwith "comparison needed"
       | _ -> failwith "Some post conditions not available"
     end
  | ProgramInvalid -> failwith "invalid"
  | ProgramAnnotationFailure -> failwith "annotation failure"
  | ProgramInit _ -> failwith "should not happen"
