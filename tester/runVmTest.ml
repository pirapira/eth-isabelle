open Yojson.Basic
open VmTestParser
open Constant
open TestResult


let spec_includes_actual (spec_storage : list_storage) (touched : Word256.word256 list) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  (* for each touched index, check that the actual storage and the spec storage have the same thing. *)
  let f (idx : Word256.word256) =
    let actual_value : Big_int.big_int = Conv.big_int_of_word256 (actual_storage idx) in
    let spec_idx : Big_int.big_int = Conv.big_int_of_word256 idx in
    let spec_value = (* This procedure needs to be split away. *)
      try Big_int.big_int_of_string (Conv.bigint_assoc spec_idx spec_storage)
      with Not_found -> Big_int.zero_big_int
    in
    let ret = Big_int.eq_big_int actual_value spec_value in
    let () = assert ret in
    ret
  in
  List.for_all f touched

let actual_includes_spec (spec_storage : list_storage) (actual_storage : Word256.word256 -> Word256.word256) : bool =
  (* for each pair in spec_storage, check the actual_storage *)
  let f ((idx : Big_int.big_int), (v : string)) =
    let spec_value = Big_int.big_int_of_string v in
    let actual_idx = (Conv.word256_of_big_int idx) in
    let actual_value = Conv.big_int_of_word256 (actual_storage actual_idx) in
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
      let a : account_state = List.assoc lookup_addr spec_post in
      a.storage
    with Not_found -> [] in
  let ret0 = spec_includes_actual spec_storage touched actual_storage in
  let ret1 = actual_includes_spec spec_storage actual_storage in
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

let compare_topics (actual : Keccak.w256) (spec : Big_int.big_int) =
  Big_int.eq_big_int spec (Conv.big_int_of_word256 actual)

let compare_log_entry (actual : Evm.log_entry) (spec : log) =
  assert(Big_int.eq_big_int (Conv.big_int_of_word160 actual.Evm.log_addr) spec.logAddress);
  assert(BatList.for_all2 compare_topics actual.Evm.log_topics spec.topics);
  assert(spec.logData = Conv.hex_string_of_byte_list "0x" actual.Evm.log_data);
  true

let log_comparison
    (actual_log : Evm.log_entry list) (spec_log : log list) =
  let actual_log = List.rev actual_log in
  List.length actual_log = List.length spec_log &&
    (BatList.for_all2 compare_log_entry actual_log spec_log)


let test_one_case j : testResult =
  let test_case : test_case = parse_test_case j in
  let open Evm in
  let open Conv in
  (*val program_sem : variable_ctx -> constant_ctx -> int -> nat -> program_result*)
  (* TODO: cut below as a function, maybe into Conv *)

  let addr : address = word160_of_big_int test_case.exec.address in
  let initial_storage : storage = lookup_storage addr test_case.pre in
  let initial_balance : address -> Keccak.w256 = construct_global_balance test_case.pre in
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
    ; vctx_logs = []
    ; vctx_refund = Nat_big_num.of_int 0
    } in
  let c : constant_ctx =
    { cctx_program = test_case.exec.code
    ; cctx_this = Conv.word160_of_big_int test_case.exec.address
    ; cctx_hash_filter = (fun _ -> true)
    } in
  let number = Nat_big_num.of_string (Big_int.string_of_big_int test_case.exec.gas) in
  let net = Evm.network_of_block_number (Word256.word256ToNatural (v.vctx_block.block_number)) in
  let ret : instruction_result = Conv.program_sem_wrapper c (Nat_big_num.to_int number) net (InstructionContinue v) in
  match ret with
  | InstructionContinue _ ->
     let () = Printf.printf "InstructionContinue\n" in
     TestFailure
  | InstructionToEnvironment (ContractCall carg, v, pushed_opt) ->
     let () = Printf.eprintf "We are not looking whatever happens after the contract calls\n" in
     TestSkipped
  | InstructionToEnvironment (ContractDelegateCall carg, v, pushed_opt) ->
     let () = Printf.eprintf "We are not looking whatever happens after the contract calls\n" in
     TestSkipped
  | InstructionToEnvironment (ContractCreate carg, v, pushed_opt) ->
     let () = Printf.eprintf "We are not looking whatever happens after the contract creates" in
     TestSkipped
  | InstructionToEnvironment (ContractFail _, v, pushed_opt) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | [], None, None, None, None -> TestSuccess
       | _ -> failwith "some postconditions are there for a failing case"
     end
  | InstructionToEnvironment (ContractSuicide _, v, pushed_opt) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | spec_created, Some spec_gas, Some spec_logs, Some spec_out, Some spec_post ->
          let () = Printf.eprintf "We are not filling in the gap of a transaction and a message call yet.  For the suicide case, this means we cannot compare the storage and the balance.\n" in
          TestSuccess
       | _ -> failwith "Some post conditions not available"
     end
  | InstructionToEnvironment (ContractReturn retval, v, None) ->
     begin
       match test_case.callcreates, test_case.gas, test_case.logs, test_case.out, test_case.post with
       | spec_created, Some spec_gas, Some spec_logs, Some spec_out, Some spec_post ->
          let got_retval : string = hex_string_of_byte_list "0x" retval in
          if (got_retval <> spec_out) then TestFailure
          else if not (storage_comparison (Conv.word160_of_big_int test_case.exec.address) spec_post v.vctx_touched_storage_index v.vctx_storage) then TestFailure
          else if not (balance_comparison (Conv.word160_of_big_int test_case.exec.address) spec_post v.vctx_balance) then TestFailure
          else if not (log_comparison v.vctx_logs spec_logs) then TestFailure
          else TestSuccess
       | _ -> failwith "Some post conditions not available"
     end
  | InstructionToEnvironment (ContractReturn retval, v, Some _) ->
     let () = Printf.printf "unexpected return format\n" in
     TestFailure

let test_one_file ((num_success : int ref), (num_failure : int ref), (num_skipped : int ref)) (case_name : string option) (path : string) : unit =
  let vm_arithmetic_test : json = Yojson.Basic.from_file path in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let () =  List.iter
    (fun (label, j) ->
      let hit =
        match case_name with
        | Some search ->
           (try
             let _ = BatString.find label search in
             true
           with Not_found -> false)
        | None -> true
      in
      if hit then
        begin
          let () = Printf.printf "===========================test case: %s\n" label in
          match test_one_case j with
          | TestSuccess -> num_success := !num_success + 1
          | TestFailure -> num_failure := !num_failure + 1
          | TestSkipped -> num_skipped := !num_skipped + 1
        end
    )
    vm_arithmetic_test_assoc in
  ()

let () =
  let case_name : string option =
    if Array.length BatSys.argv > 1 then Some (Array.get BatSys.argv 1) else None in
  let num_success = ref 0 in
  let num_failure = ref 0 in
  let num_skipped = ref 0 in
  let counters = (num_success, num_failure, num_skipped) in
  let () = TraverseJsons.traverse "../tests/VMTests" (test_one_file counters case_name) in
  let () = Printf.printf "success: %i\n" !num_success in
  let () = Printf.printf "failure: %i\n" !num_failure in
  let () = Printf.printf "skipped: %i\n" !num_skipped in
  ()
