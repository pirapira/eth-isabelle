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

lemma triple_code_eq :
  "triple s p c r \<Longrightarrow> c = c' \<Longrightarrow> triple s p c' r"
apply(simp)
done

lemma sep_functional :
  "a = b \<Longrightarrow> c = d \<Longrightarrow> a ** c = b ** d"
apply(simp)
done

lemma rotate4 :
  "a ** b ** c ** d = b ** c ** d ** a"
  using sep_assoc sep_commute by auto

lemma first_three :
  "a ** b ** c ** d = R \<Longrightarrow> c ** b ** a ** d = R"
proof -
 assume "a ** b ** c ** d = R"
 moreover have "a ** b ** c ** d = c ** b ** a ** d"
  using sep_assoc sep_commute by auto
 ultimately show "c ** b ** a ** d = R"
  by auto
qed
   

lemma pddd_triple :
"triple {OutOfGas} (\<langle> h \<le> 1020\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0)}
                      (stack_height (h + 4) **
                       stack (Suc (Suc (Suc h))) (word_rcat [0]) **
                       stack (Suc (Suc h)) (word_rcat [0]) **
                       stack (Suc h) (word_rcat [0]) **
                       stack h (word_rcat [0]) **
                       program_counter (5 + k) **
                       gas_pred (g - 4 * Gverylow) **
                       continuing
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Dup 0)}"
           and cR = "{(k + 3, Dup 0),
                       (k + 4, Dup 0)}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
 apply(rule_tac h = h and g = g in push0dup1_triple)
 apply(auto)
apply(rule_tac R = "stack h (word_rcat [0])" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac k = "3 + k" and h = "Suc h" and w = "word_rcat [0]" and g = "g - 2 * Gverylow" in dup1dup1_triple)
  apply(auto)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule rotate4)
apply(rule sep_functional)
 (* sledgehammer *)
 apply (metis Suc3_eq_add_3 Suc_eq_plus1_left add.commute add_numeral_left numeral_One semiring_norm(2) semiring_norm(8))
apply(rule first_three)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp add: word_rcat_def bin_rcat_def)
apply(rule sep_functional)
 apply(simp add: word_rcat_def bin_rcat_def)
apply(rule rotate4)
done

lemma abcbca :
  "a ** b ** c = b ** c ** a"
  using sep_assoc sep_commute by auto

lemma uu_addr [simp] :
  "(ucast (ucast (a :: address) :: w256) :: address) = a"
apply(rule ucast_down_ucast_id)
apply(simp add: is_down_def target_size_def source_size_def word_size)
done

lemma this_balance :
  "triple {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000\<rangle>
           ** block_number_pred bn ** stack_height h ** program_counter k ** this_account t ** 
           balance t b ** gas_pred g ** continuing)
          {(k, Info ADDRESS), (k + 1, Info BALANCE)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h b ** balance t b
           ** program_counter (2 + k) ** this_account t ** gas_pred (g - Gbase - 400)
           ** continuing )"
apply(auto)
apply(rule_tac cL = "{(k, Info ADDRESS)}" and cR = "{(k + 1, Info BALANCE)}" in composition)
  apply(auto)
 apply(rule_tac R = "balance t b ** block_number_pred bn" in frame_backward)
  apply(rule_tac h = h and g = g and t = t in address_gas_triple)
  using sep_assoc sep_commute apply auto
apply(rule_tac R = "this_account t" in frame_backward)
 apply(rule_tac h = h and g = "g - 2" and bn = bn and a = "ucast t" and b = b in balance_gas_triple)
 apply(auto)
done

lemma caller_gas :
"
triple {OutOfGas}
          (\<langle> h \<le> 1022 \<rangle> ** stack_height h ** program_counter k ** caller c ** gas_pred g ** continuing)
          {(k, Info CALLER), (k + 1, Info GAS)}
          (stack_height (h + 2) ** stack (Suc h) (word_of_int (g - Gbase - 2)) ** stack h (ucast c)
           ** program_counter (2 + k) ** caller c ** gas_pred (g - Gbase - 2) ** continuing )
"
apply(auto)
apply(rule_tac cL = "{(k, Info CALLER)}" and cR = "{(k + 1, Info GAS)}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
  apply(rule_tac h = "h" and c = c and g = g in caller_gas_triple) 
 apply(auto)
apply(rule_tac R = "stack h (ucast c) ** caller c" in frame_backward)
  apply(rule_tac h = "Suc h" and g = "g - 2" in gas_gas_triple)
 apply(auto)
 using sep_assoc sep_commute apply auto
done

lemma program_counter_comm :
  "program_counter (x + y) = program_counter (y + x)"
(* sledgehammer *)
proof -
  have "y + x = x + y"
    by presburger
  then show ?thesis
    by presburger
qed

lemma first_three_args :
  "triple {OutOfGas}
          (\<langle> h \<le> 1021 \<and> unat bn \<ge> 2463000\<rangle>
           ** block_number_pred bn ** caller c ** stack_height h ** program_counter k ** this_account t ** 
           balance t b ** gas_pred g ** continuing)
          {(k, Info ADDRESS), (k + 1, Info BALANCE), (k + 2, Info CALLER), (k + 3, Info GAS)}
          (block_number_pred bn ** caller c ** stack_height (h + 3) ** 
           stack (Suc (Suc h)) (word_of_int (g - 2 * Gbase - 402)) ** stack (Suc h) (ucast c) ** stack h b ** balance t b
           ** program_counter (4 + k) ** this_account t ** gas_pred (g - 2 * Gbase - 402)
           ** continuing )"
apply(auto)
apply(rule_tac cL = "{(k, Info ADDRESS), (k + 1, Info BALANCE)}"
           and cR = "{(k + 2, Info CALLER), (k + 3, Info GAS)}" in composition)
  apply(auto)
 apply(rule_tac R = "caller c" in frame_backward)
   apply(rule_tac h = h and bn = bn and g = g and t = t and b = b in this_balance)
  apply(auto)
 using sep_assoc sep_commute apply auto
apply(rule_tac R = "balance t b ** stack h b ** block_number_pred bn ** this_account t" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac k = "k + 2" and h = "Suc h" and c = c and g = "g - Gbase - 400" in caller_gas)
   apply simp
   apply auto[1]
 apply auto
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
(* sledgehammer *)
  apply (simp add: Suc3_eq_add_3 semiring_normalization_rules(24))
apply(simp)
done

   

end
