theory FailOnReentrance

imports Main "../ContractSem"

begin

abbreviation fail_on_reentrance_program :: "inst list"
where
"fail_on_reentrance_program ==
  Stack (PUSH_N [0]) #
  Storage SLOAD #
  Dup 1 #
  Stack (PUSH_N [2]) #
  Pc JUMP #
  Stack (PUSH_N [1]) #
  Arith ADD #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Stack (PUSH_N [0]) #
  (* TODO: change some of these arguments to value, address *)
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Misc CALL #
  Arith ISZERO #
  Stack (PUSH_N [0]) #
  Pc JUMPI #
  Stack (PUSH_N [0]) #
  Stack (PUSH_N [0]) #
  Storage SSTORE #
  Misc STOP # []"

end
