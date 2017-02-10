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

lemma first_two:
 "b ** a ** rest = R \<Longrightarrow> a ** b ** rest = R"
  by (simp add: abcbca sep_commute)

lemma five_plus:
 "5 + h = Suc (Suc (Suc (Suc (Suc h))))"
apply(simp)
done

lemma six_plus:
 "6 + h = Suc (Suc (Suc (Suc (Suc (Suc h)))))"
apply(simp)
done


lemma seven_args:
"triple {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Info GAS)
                      }
                      (block_number_pred bn ** caller c **
                       stack_height (h + 7) **
                       stack (Suc (Suc (Suc (Suc (Suc (Suc h)))))) (word_of_int (g - 4 * Gverylow - 2 * Gbase - 402)) **
                       stack (Suc (Suc (Suc (Suc (Suc h))))) (ucast c) **
                       stack (Suc (Suc (Suc (Suc h)))) b **
                       stack (Suc (Suc (Suc h))) (word_rcat [0]) **
                       stack (Suc (Suc h)) (word_rcat [0]) **
                       stack (Suc h) (word_rcat [0]) **
                       stack h (word_rcat [0]) **
                       program_counter (9 + k) **
                       this_account t **
                       balance t b **
                       gas_pred (g - 4 * Gverylow - 2 * Gbase - 402) **
                       continuing
                      )"
apply(auto)
 apply(rule_tac cL = "{(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0)}"
            and cR = "{(5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Info GAS)}" in composition)
  apply(auto)
 apply(rule_tac R = "block_number_pred bn **
      caller c ** this_account t ** balance t b" in frame_backward)
   apply(rule_tac h = h and g = g in pddd_triple)
  using sep_assoc sep_commute apply auto
apply(rule_tac R = "
      stack h (word_rcat [0]) **
      stack (Suc h) (word_rcat [0]) **
      stack (Suc (Suc h)) (word_rcat [0]) **
      stack (Suc (Suc (Suc h))) (word_rcat [0])"
      in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac k = "5 + k" and bn = bn and h = "h + 4" 
             and c = c and t = t and b = b
             and g = "g - 4 * Gverylow" in first_three_args)
  apply(simp)
 apply(simp)
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
apply(rule first_two)
apply(rule sep_functional)
 apply (simp add: semiring_normalization_rules(24))
apply(rule first_two)
apply(rule sep_functional)
 apply(simp)
apply(rule first_two)
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply (metis add.left_commute numeral_Bit0 s2n_ths(1) s2n_ths(2))
apply(rule sep_functional)
 apply(simp)
apply(rule sep_functional)
 apply(simp add: five_plus)
apply(rule sep_functional)
 apply(simp)
apply(simp add: six_plus)
done

lemma pc_not_topmost [simp] :
  "\<forall> h. PcElm x6
       \<notin> stack_topmost_elms h lst"
apply(induction lst) 
 apply(simp add: stack_topmost_elms.simps)
apply(simp add: stack_topmost_elms.simps)
done

lemma contract_action_not_topmost [simp] :
  "\<forall> h. ContractActionElm x19
       \<notin> stack_topmost_elms h lst"
apply(induction lst; simp add: stack_topmost_elms.simps)
done

lemma plus_seven :
"h + 7 = Suc (Suc (Suc (Suc (Suc (Suc (Suc h))))))"
apply(simp)
done

lemma stack_topmost_translate_inner :
"(stack_topmost h [out_size, out_begin, in_size, in_begin, v, r, g] ** rest) s =
                       ((stack_height (h + 7) **
                       stack (Suc (Suc (Suc (Suc (Suc (Suc h)))))) g **
                       stack (Suc (Suc (Suc (Suc (Suc h))))) r **
                       stack (Suc (Suc (Suc (Suc h)))) v **
                       stack (Suc (Suc (Suc h))) in_begin **
                       stack (Suc (Suc h)) in_size **
                       stack (Suc h) out_begin **
                       stack h out_size) **
                       rest) s"
apply(auto simp add: stack_topmost_def)
  apply(rule leibniz)
   apply blast
  apply(auto)
  apply(rename_tac elm; case_tac elm; simp)
  apply(case_tac x2; simp)
  apply(case_tac "a = h"; simp)
  apply(case_tac "a = Suc h"; simp)
  apply(case_tac "a = Suc (Suc h)"; simp)
  apply(case_tac "a = Suc (Suc (Suc h))"; simp)
  apply(case_tac "a = Suc (Suc (Suc (Suc h)))"; simp)
  apply(case_tac "a = Suc (Suc (Suc (Suc (Suc h))))"; simp)
  apply(case_tac "a = Suc (Suc (Suc (Suc (Suc (Suc h)))))"; simp)
 apply(simp add: stack_topmost_elms.simps plus_seven)
 apply(auto)
apply(rule leibniz)
 apply blast
apply(simp add: stack_topmost_elms.simps plus_seven)
apply(auto)
done


lemma stack_topmost_translate :
"(stack_topmost h [out_size, out_begin, in_size, in_begin, v, r, g] ** rest) s =
                       (stack_height (h + 7) **
                       stack (Suc (Suc (Suc (Suc (Suc (Suc h)))))) g **
                       stack (Suc (Suc (Suc (Suc (Suc h))))) r **
                       stack (Suc (Suc (Suc (Suc h)))) v **
                       stack (Suc (Suc (Suc h))) in_begin **
                       stack (Suc (Suc h)) in_size **
                       stack (Suc h) out_begin **
                       stack h out_size **
                       rest) s"
apply(simp only: stack_topmost_translate_inner)
apply(simp)
done

lemma tri_sep :
  "\<forall> s. c s = d s \<Longrightarrow> (a ** b ** c) k = (a ** b ** d) k"
apply(simp add: sep_def)
done

lemma stack_topmost_special_translate :
"(a ** b ** stack_topmost h [out_size, out_begin, in_size, in_begin, v, r, g] ** rest) s =
                       (a ** b ** stack_height (h + 7) **
                       stack (Suc (Suc (Suc (Suc (Suc (Suc h)))))) g **
                       stack (Suc (Suc (Suc (Suc (Suc h))))) r **
                       stack (Suc (Suc (Suc (Suc h)))) v **
                       stack (Suc (Suc (Suc h))) in_begin **
                       stack (Suc (Suc h)) in_size **
                       stack (Suc h) out_begin **
                       stack h out_size **
                       rest) s"
apply(rule tri_sep)
apply(simp only: stack_topmost_translate)
apply(simp)
done

lemma seven_args_packed:
"triple {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Info GAS)
                      }
                      (block_number_pred bn ** caller c **
                       stack_topmost h [word_rcat [0], word_rcat [0], word_rcat [0], word_rcat [0],
                         b, ucast c, word_of_int (g - 4 * Gverylow - 2 * Gbase - 402)] **
                       program_counter (9 + k) **
                       this_account t **
                       balance t b **
                       gas_pred (g - 4 * Gverylow - 2 * Gbase - 402) **
                       continuing
                      )"
apply(rule weaken_post)
 apply(rule seven_args)
apply(simp only: stack_topmost_special_translate)
apply blast
done

lemma pick_fifth_L :
  "e ** a ** b ** c ** d ** rest = R \<Longrightarrow> a ** b ** c ** d ** e ** rest = R"
proof -
 have "e ** a ** b ** c ** d ** rest = a ** b ** c ** d ** e ** rest"
  using first_two by presburger
 moreover assume "e ** a ** b ** c ** d ** rest = R"
 ultimately show "a ** b ** c ** d ** e ** rest = R"
  by auto
qed

lemma pick_sixth_last_L :
  "f ** a ** b ** c ** d ** e = R \<Longrightarrow>
   a ** b ** c ** d ** e ** f = R"
proof -
 have "f ** a ** b ** c ** d ** e = a ** b ** c ** d ** e ** f"
  using rotate4 by auto
 moreover assume "f ** a ** b ** c ** d ** e = R"
 ultimately show "a ** b ** c ** d ** e ** f = R"
  by auto
qed


lemma pick_fourth_L :
  "d ** a ** b ** c ** rest = R \<Longrightarrow> a ** b ** c ** d ** rest = R"
proof -
 have "d ** a ** b ** c ** rest = a ** b ** c ** d** rest"
  using first_two by presburger
 moreover assume "d ** a ** b ** c ** rest = R"
 ultimately show "a ** b ** c ** d ** rest = R"
  by auto
qed

lemma pick_third_L :
  "c ** a ** b ** rest = R \<Longrightarrow> a ** b ** c ** rest = R"
proof -
 have "c ** a ** b ** rest = a ** b ** c ** rest"
  using first_two by presburger
 moreover assume "c ** a ** b ** rest = R"
 ultimately show "a ** b ** c ** rest = R"
  by auto
qed


lemma call_with_args:
"triple {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       continuing ** memory_usage u

                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Info GAS),
                       (9 + k, Misc CALL)
                      }
                      (block_number_pred bn ** caller c **
                       memory_usage u **
                       stack_topmost h [] **
                       program_counter (10 + k) **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       not_continuing **
                       action (ContractCall \<lparr> callarg_gas = word_of_int (g - 4 * Gverylow - 2 * Gbase - 402)
                                , callarg_code = c
                                , callarg_recipient = c
                                , callarg_value = b
                                , callarg_data = []
                                , callarg_output_begin = word_rcat [0]
                                , callarg_output_size = word_rcat [0] \<rparr>)
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Info GAS)}"
            and cR = "{(9 + k, Misc CALL)}" in composition)
  apply(auto)
 apply(rule_tac R = "memory_usage u" in frame_backward)
   apply(rule_tac k = k and h = h and c = c and bn = bn and t = t and b = b and g = g in seven_args_packed)
  apply(simp)
 apply simp
apply(rule_tac R = "block_number_pred bn **
      caller c" in frame_backward)
  apply(rule_tac h = h and v = b and fund = b and input = "[]" 
        and in_size = "word_rcat [0]" and in_begin = "word_rcat [0]"
        and out_size = "word_rcat [0]" and out_begin = "word_rcat [0]"
        and g = "word_of_int (g - 4 * Gverylow - 406)" and r = "ucast c"
        and this = t and u = u
        in call_gas_triple)
 apply(simp add: word_rcat_def bin_rcat_def)
 apply(rule pick_fourth_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_third_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_fifth_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_sixth_last_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_third_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_third_L)
 apply(rule sep_functional)
  apply(simp)
 apply (metis abcbca)
apply(simp add: word_rcat_def bin_rcat_def M_def)
apply(rule pick_fourth_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_fifth_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_fifth_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_fourth_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_fourth_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_third_L)
apply(rule sep_functional)
 apply(simp)
apply(rule pick_third_L)
apply(rule sep_functional)
 apply(simp)
apply (metis abcbca)
done

end
