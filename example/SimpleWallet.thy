theory SimpleWallet

imports "../HoareTripleForInstructions2"

begin

(*
PUSH 0
SLOAD
CALLER
EQ
PUSH ??
JUMPI
STOP
?? JUMPDEST
PUSH 0
DUP1
DUP1
DUP1
ADDRESS
BALANCE
CALLER
GAS
CALL
STOP
*)

(* First try
PUSH 0
DUP1
DUP1
DUP1
*)

lemma push0_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1023\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0]))}
                      (stack_height (h + 1) **
                       stack h (word_rcat [0]) **
                       program_counter (2 + k) **
                       gas_pred (g - Gverylow) **
                       continuing
                      )"
apply(rule weaken_post)
 apply(rule strengthen_pre)
  apply(rule_tac k = k and h = h and g = g in push_gas_triple)
 apply(simp)
apply(auto simp add: word_rcat_def bin_rcat_def)
done

lemma add_comm_pc:
  " PcElm (x + y) \<in> s \<Longrightarrow>  PcElm (y + x) \<in> s"
(* sledgehammer *)
  by (simp add: semiring_normalization_rules(24))

lemma push0dup1_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1022\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0)}
                      (stack_height (h + 2) **
                       stack (Suc h) (word_rcat [0]) **
                       stack h (word_rcat [0]) **
                       program_counter (3 + k) **
                       gas_pred (g - 2 * Gverylow) **
                       continuing
                      )"
apply(simp)
apply(rule impI)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0]))}"
           and cR = "{(k + 2, Dup 0)}"  in composition)
  apply(auto)
 apply(rule strengthen_pre)
  apply(rule_tac h = h and g = g in push0_triple)
 apply(auto)
apply(rule strengthen_pre)
 apply(rule weaken_post)
  apply(rule_tac h = "(Suc h)" and g = "g - Gverylow" and w = "word_rcat [0]" in dup_gas_triple)
 apply(auto simp add: word_rcat_def bin_rcat_def)
  apply(rule leibniz)
   apply blast
  apply(auto)
 apply(rule add_comm_pc; simp)
apply(rule leibniz)
 apply blast
apply(auto)
done

lemma true_is_emp [simp] :
 "\<langle> True \<rangle> = emp"
using pure_def emp_def apply blast
done

lemma emp_sep2 [simp] :
  "emp ** rest = rest"
using emp_sep apply blast
done

lemma dup1dup1_triple :
   "triple {OutOfGas} (\<langle> h \<le> 1021\<rangle> **
                       stack_height (Suc h) **
                       stack h w **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Dup 0),
                       (k + 1, Dup 0)}
                      (stack_height (Suc (Suc (Suc h))) **
                       stack h w **
                       stack (Suc h) w **
                       stack (Suc (Suc h)) w **
                       program_counter (2 + k) **
                       gas_pred (g - 2 * Gverylow) **
                       continuing
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Dup 0)}" and cR = "{(k + 1, Dup 0)}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
  apply(rule_tac h = "Suc h" and w = w and g = g in dup_gas_triple)
 apply(auto)
apply(rule_tac R = "stack h w" in frame_backward)
 apply(rule_tac h = "Suc (Suc h)" and w = w and g = "g - Gverylow" in dup_gas_triple)
 apply(auto)
 apply (simp add: commute_in_four sep_commute)
apply (simp add: commute_in_four sep_commute)
done

end
