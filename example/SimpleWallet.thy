theory SimpleWallet

imports "../HoareTripleForInstructions2"

begin

(*
0: PUSH 0
2: SLOAD
3: CALLER
4: EQ
5: PUSH 9
7: JUMPI
8: STOP
9: JUMPDEST
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

lemma pick_ninth_L :
  "i ** a ** b ** c ** d ** e ** f ** g ** h ** rest = R \<Longrightarrow>
   a ** b ** c ** d ** e ** f ** g ** h ** i ** rest = R"
proof -
 have "i ** a ** b ** c ** d ** e ** f ** g ** h ** rest
     = a ** b ** c ** d ** e ** f ** g ** h ** i ** rest"
  using first_two by presburger
 moreover assume "i ** a ** b ** c ** d ** e ** f ** g ** h ** rest = R"
 ultimately show "a ** b ** c ** d ** e ** f ** g ** h ** i ** rest = R"
  by auto
qed



lemma pick_fifth_last_L :
  "e ** a ** b ** c ** d = R \<Longrightarrow> a ** b ** c ** d ** e = R"
proof -
 have "e ** a ** b ** c ** d = a ** b ** c ** d ** e"
  using rotate4 by auto
 moreover assume "e ** a ** b ** c ** d = R"
 ultimately show "a ** b ** c ** d ** e = R"
  by auto
qed

lemma pick_fourth_last_L :
  "d ** a ** b ** c = R \<Longrightarrow> a ** b ** c ** d = R"
proof -
 have "d ** a ** b ** c = a ** b ** c ** d"
  using rotate4 by auto
 moreover assume "d ** a ** b ** c = R"
 ultimately show "a ** b ** c ** d = R"
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

lemma pick_second_L :
  "b ** a ** rest = R \<Longrightarrow> a ** b ** rest = R"
proof -
 have "b ** a ** rest = a ** b ** rest"
  using first_two by presburger
 moreover assume "b ** a ** rest = R"
 ultimately show "a ** b ** rest = R"
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

lemma pick_secondL:
 "a ** rest = R \<Longrightarrow> a ** b ** rest = b ** R"
  by (simp add: first_two)

lemma pick_thirdL:
 "a ** b ** rest = R \<Longrightarrow> a ** b ** c ** rest = c ** R"
  by (simp add: pick_third_L)

lemma sep_ac :
 "a ** b ** c = b ** a ** c"
  using first_two by blast

lemma equal_pred :
 "P = Q \<Longrightarrow> \<forall> s. P s \<longrightarrow> Q s"
apply(simp)
done


lemma cons_eq :
  "a = b \<Longrightarrow> c ** a = c ** b"
apply(simp)
done

lemma push0sload :
   "triple {OutOfGas} (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k **
                       storage (word_rcat [0]) w **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD)}
                      (block_number_pred bn **
                       stack_height (h + 1) **
                       stack h w **
                       program_counter (3 + k) **
                       storage (word_rcat [0]) w **
                       gas_pred (g - Gverylow - Gsload (unat bn)) **
                       continuing
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0]))}"
           and cR = "{(k + 2, Storage SLOAD)}" in composition)
  apply(auto)
 apply(rule_tac R = "block_number_pred bn ** storage (word_rcat [0]) w"
    in frame_backward)
   apply(rule_tac h = h and g = g in push_gas_triple)
  apply(simp)
  apply(rule pick_secondL)
  apply(rule pick_secondL)
  apply(rule pick_thirdL)
  apply(auto simp: sep_commute)
 apply(rule sep_ac)
apply(rule_tac R = "emp" in frame_backward)
  apply(rule_tac bn = bn and h = h and w = w and g = "g - Gverylow"
        and idx = "word_rcat [0]"
        in sload_gas_triple)
 apply(simp)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_second_L)
 apply(rule sep_functional)
  apply(simp add: program_counter_comm)
 apply(rule sep_functional)
  apply (simp add: word_rcat_def bin_rcat_def)
 apply(rule sep_commute)
apply(simp)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule cons_eq)
apply(simp add: word_rcat_def bin_rcat_def)
using sep_commute apply auto
done

lemma caller_eq :
  "triple {OutOfGas}  ( \<langle> h \<le> 1022 \<rangle> **
                        stack_height (h + 1) **
                        stack h w **
                        program_counter k ** caller c **
                        gas_pred g **
                        continuing
                      )
                      {(k, Info CALLER), (k + 1, Arith inst_EQ)}
                      ( stack_height (h + 1) **
                        stack h (if ucast c = w then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word)) **
                        program_counter (k + 2) ** caller c **
                        gas_pred (g - Gbase - Gverylow) **
                        continuing )"
apply(auto)
 apply(rule_tac cL = "{(k, Info CALLER)}"
           and cR = "{(k + 1, Arith inst_EQ)}" in composition)
   apply(auto)
  apply(rule_tac R = "stack h w" in frame_backward)
    apply(rule_tac h = "Suc h" and g = g and c = c in caller_gas_triple)
   apply(simp)
   apply(rule cons_eq)
   apply(rule pick_secondL)
   apply(rule pick_secondL)
   apply(rule pick_secondL)
   apply(rule sep_commute)
  apply(simp)
 apply(rule_tac R = "caller c" in frame_backward)
   apply(rule_tac h = h and g = "g - 2" and v = "ucast c" and w = "ucast c"
       in eq_gas_triple)
  apply(simp)
  apply(rule cons_eq)
  apply(rule cons_eq)
  apply(rule pick_fifth_last_L)
  apply(rule cons_eq)
  apply(rule cons_eq)
  apply(rule pick_secondL)
  apply(rule sep_commute)
 apply(simp)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(rule pick_secondL)
 apply(rule sep_commute)
apply(rule_tac cL = "{(k, Info CALLER)}"
          and cR = "{(k + 1, Arith inst_EQ)}" in composition)
  apply(auto)
 apply(rule_tac R = "stack h w" in frame_backward)
   apply(rule_tac h = "Suc h" and g = g and c = c in caller_gas_triple)
  apply(simp)
  apply(rule cons_eq)
  apply(rule pick_secondL)
  apply(rule pick_secondL)
  apply(rule pick_secondL)
  apply(rule sep_commute)
 apply(simp)
apply(rule_tac R = "caller c" in frame_backward)
  apply(rule_tac h = h and g = "g - 2" and v = "ucast c" and w = "w"
      in eq_gas_triple)
 apply(simp)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_fifth_last_L)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_secondL)
 apply(rule sep_commute)
apply(simp)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule sep_functional)
 apply(rule program_counter_comm)
apply(rule pick_secondL)
apply(rule sep_commute)
done

lemma abccba :
  "a ** b ** c = c ** b ** a"
  using abel_semigroup.left_commute sep_three set_pred.abel_semigroup_axioms by fastforce

lemma first_four :
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ)}
                      (block_number_pred bn **
                       stack_height (h + 1) **
                       stack h (if ucast c = w then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word)) **
                       program_counter (5 + k) ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred (g + (- Gsload (unat bn) - 2) - 2 * Gverylow) **
                       continuing
                      )"
apply(simp only: move_pureL)
apply(rule impI)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD)}"
           and cR = "{(k + 3, Info CALLER), (k + 4, Arith inst_EQ)}" in composition)
  apply blast
 apply(rule_tac R = "caller c" in frame_backward)
   apply(rule_tac h = h and bn = bn and w = w and g = g in push0sload)
  apply(simp)
  apply(rule cons_eq)
  apply(rule cons_eq)
  apply(rule cons_eq)
  apply(rule pick_secondL)
  apply(rule abcbca)
 apply(simp)
apply(rule_tac R = "storage (word_rcat [0]) w ** block_number_pred bn" in frame_backward)
  apply(rule triple_code_eq)
   apply(rule_tac k = "k + 3" and h = h and w = w and c = c and g = "g - Gverylow - Gsload (unat bn)" in caller_eq)
  apply simp
  apply auto[1]
 apply(simp)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_second_L)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(rule pick_fifth_last_L)
 apply(rule cons_eq)
 apply(rule pick_thirdL)
 apply(rule abccba)
apply(auto)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_third_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule abccba)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_third_L)
apply(rule sep_functional)
 apply(simp)
apply(rule abccba)
done


lemma pushjumpi_false:
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<rangle> **
                       stack_height (h + 1) **
                       stack h 0 **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [x])), (k + 2, Pc JUMPI)}
                      (stack_height h **
                       program_counter (k + 3) **
                       gas_pred (g - Gverylow - Ghigh) **
                       continuing)"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [x]))}"
           and cR = "{(k + 2, Pc JUMPI)}" in composition)
  apply blast
 apply(rule_tac R = "stack h 0" in frame_backward)
   apply(rule_tac g = g and h = "Suc h" in push_gas_triple)
  apply(simp)
  apply(rule cons_eq)
  apply(rule pick_secondL)
  apply(rule pick_secondL)
  apply(rule sep_commute)
 apply simp
apply(rule_tac R = "emp" in frame_backward)
  apply(rule_tac h = h and g = "g - Gverylow" and d = "(word_rcat [x])"
        in jumpi_false_gas_triple)
 apply(simp)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_fourth_last_L)
 apply(rule cons_eq)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(simp)
apply(simp add: program_counter_comm)
done

lemma pushjumpistop_false :
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<rangle> **
                       stack_height (h + 1) **
                       stack h 0 **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [x])), (k + 2, Pc JUMPI),
                       (k + 3, Misc STOP)}
                      (stack_height h **
                       program_counter (k + 3) **
                       gas_pred (g - Gverylow - Ghigh) **
                       not_continuing ** action (ContractReturn []))"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [x])), (k + 2, Pc JUMPI)}"
           and cR = "{(k + 3, Misc STOP)}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
 apply(rule_tac h = h and g = g in pushjumpi_false)
 apply(auto)
apply(rule_tac R = "gas_pred (g - Gverylow - Ghigh)" in frame_backward)
  apply(rule_tac h = h in stop_gas_triple)
 apply(simp)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule sep_commute)
apply(simp)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule pick_secondL)
apply(rule sep_commute)
done

lemma prefix_invalid_caller:
"triple {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<and> ucast c \<noteq> w\<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (k + 5, Stack (PUSH_N [x])), (k + 7, Pc JUMPI),
                       (k + 8, Misc STOP)}
                      (block_number_pred bn **
                       stack_height h **
                       program_counter (8 + k) ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred (g + (- Gsload (unat bn) - 2) - 2 * Gverylow - Gverylow - Ghigh) **
                       not_continuing ** action (ContractReturn []))"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ)}"
           and cR = "{(k + 5, Stack (PUSH_N [x])), (k + 7, Pc JUMPI),
                       (k + 8, Misc STOP)}" in composition)
  apply(auto)
 apply(rule_tac R = emp in frame_backward)
   apply(rule_tac h = h and bn = bn and c = c and g = g and w = w in first_four)
  apply(simp)
 apply(simp)
apply(rule_tac R = "block_number_pred bn ** caller c ** storage (word_rcat [0]) w" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac h = h and k = "k + 5" and x = x in pushjumpistop_false)
  apply(auto)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_second_L)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(rule pick_fourth_L)
 apply(rule sep_functional)
  apply simp
 apply(rule pick_fourth_last_L)
 apply(simp)
apply(simp)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_fourth_L)
apply(rule cons_eq)
apply(rule pick_fourth_L)
apply(rule cons_eq)
apply(rule pick_fourth_last_L)
apply(simp)
done

lemma bintrunc_byte_uint :
  "bintrunc 8 (uint (d :: byte)) = uint d"
apply(rule Word.bintr_uint)
apply(simp)
done

lemma word_rcat_single [simp] :
  "(word_rcat [(d :: byte)] :: w256) = ucast d"
apply(simp add: word_rcat_def bin_rcat_def bintrunc_byte_uint ucast_def)
done

lemma uint_ucast_bw [simp] :
  "uint (ucast (d :: byte) :: w256) = uint d"
apply(rule uint_up_ucast)
apply(simp add: is_up source_size_def target_size_def)
done


lemma pushjumpi_true:
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<and> cond \<noteq> 0 \<rangle> **
                       stack_height (h + 1) **
                       stack h cond **
                       program_counter k **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [d])), (k + 2, Pc JUMPI), ((uint (ucast d :: w256)), Pc JUMPDEST)}
                      (stack_height h **
                       program_counter (uint d) **
                       gas_pred (g - Gverylow - Ghigh) **
                       continuing)"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [d]))}" 
           and cR = "{(k + 2, Pc JUMPI), ((uint (ucast d :: w256)), Pc JUMPDEST)}" in composition)
  apply(auto)
 apply(rule_tac R = "stack h cond" in frame_backward)
   apply(rule_tac h = "h + 1" and g = g in push_gas_triple)
  apply(simp)
  apply(rule cons_eq)
  apply(rule pick_secondL)
  apply(rule pick_secondL)
  apply(rule sep_commute)
 apply(simp)
apply(rule_tac R = "emp" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac g = "g - Gverylow" and cond = cond and h = h and k = "k + 2" and d = "ucast d" in jumpi_true_gas_triple)
  apply(simp)
 apply(simp)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_fourth_last_L)
 apply(rule cons_eq)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(simp)
apply(simp)
done


lemma prefix_true:
   "triple {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}
                      (block_number_pred bn **
                       stack_height h **
                       program_counter (uint d) ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred (g + (- Gsload (unat bn) - 2) - 3 * Gverylow - Ghigh) **
                       continuing
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ)}"
           and cR = "{(5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}" in composition)
  apply(auto)
 apply(rule_tac R = emp in frame_backward)
   apply(rule_tac h = h and g = g and bn = bn and c = c and w = "ucast c" in first_four)
  apply(simp)
 apply(simp)
apply(rule_tac R = "block_number_pred bn ** caller c ** storage (word_rcat [0]) (ucast c)" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac h = h and k = "k + 5" and d = d and cond = 1 in pushjumpi_true)
  apply(auto)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_second_L)
 apply(rule sep_functional)
  apply(rule program_counter_comm)
 apply(rule pick_fourth_L)
 apply(rule sep_functional)
  apply(simp)
 apply(rule pick_fourth_last_L)
 apply(simp)
apply(simp)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_fourth_last_L)
apply(simp)
done

lemma prefix_true_over_JUMPDEST:
"triple {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred g **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}
                      (block_number_pred bn **
                       stack_height h **
                       program_counter ((uint d) + 1) ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred (g + (- Gsload (unat bn) - 2) - 3 * Gverylow - Ghigh - Gjumpdest) **
                       continuing
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}"
           and cR = "{((uint (ucast d :: w256)), Pc JUMPDEST)}" in composition)
  apply(auto)
 apply(rule_tac R = emp in frame_backward)
   apply(rule_tac triple_code_eq)
    apply(rule_tac bn = bn and h = h and c = c and g = g in prefix_true)
   apply(simp)
  apply(simp)
 apply(simp)
apply(rule_tac R = "block_number_pred bn **
   caller c ** storage (word_rcat [0]) (ucast c)" in frame_backward)
  apply(rule_tac h = h in jumpdest_gas_triple)
 apply(simp)
 apply(rule pick_secondL)
 apply(rule pick_secondL)
 apply(rule pick_fourth_L)
 apply(rule cons_eq)
 apply(rule pick_fourth_last_L)
 apply(simp)
apply(simp)
apply(rule pick_secondL)
apply(rule pick_secondL)
apply(rule pick_fourth_last_L)
apply(simp)
done


lemma check_pass_whole:
  "triple {OutOfGas} (\<langle> h \<le> 1017 \<and> unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred g **
                       continuing **
                       this_account t **
                       balance t b **
                       memory_usage u
                      )
                      {(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST),
                       ((uint d) + 1, Stack (PUSH_N [0])),
                       (3 + (uint d), Dup 0),
                       (4 + uint d, Dup 0),
                       (5 + uint d, Dup 0),
                       (6 + uint d, Info ADDRESS),
                       (7 + uint d, Info BALANCE),
                       (8 + uint d, Info CALLER),
                       (9 + uint d, Info GAS),
                       (10 + uint d, Misc CALL)
                      }
                      (memory_usage u **
                       stack_topmost h [] **
                       program_counter (uint d + 11) **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       not_continuing **
                       action (ContractCall \<lparr>
                                  callarg_gas = word_of_int (g + (- Gjumpdest - Ghigh - 7 * Gverylow - Gsload (unat bn)) - 408)
                                , callarg_code = c
                                , callarg_recipient = c
                                , callarg_value = b
                                , callarg_data = []
                                , callarg_output_begin = word_rcat [0]
                                , callarg_output_size = word_rcat [0] \<rparr>) **
                       block_number_pred bn **
                       caller c **
                       storage (word_rcat [0]) (ucast c)
                      )"
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}"
           and cR = "{((uint d) + 1, Stack (PUSH_N [0])),
                       (3 + (uint d), Dup 0),
                       (4 + uint d, Dup 0),
                       (5 + uint d, Dup 0),
                       (6 + uint d, Info ADDRESS),
                       (7 + uint d, Info BALANCE),
                       (8 + uint d, Info CALLER),
                       (9 + uint d, Info GAS),
                       (10 + uint d, Misc CALL)}" in composition)
  apply(auto)
 apply(rule_tac R = "this_account t ** balance t b ** memory_usage u" in
       frame_backward)
   apply(rule triple_code_eq)
    apply(rule_tac h = h in prefix_true_over_JUMPDEST)
   apply(simp)
  apply(auto)
apply(rule_tac R = "storage (word_rcat [0]) (ucast c)" in
      frame_backward)
  apply(rule_tac triple_code_eq)
   apply(rule_tac bn = bn and  h = h and k = "uint d + 1" in call_with_args)
  apply(simp)
 apply(simp)
 apply(rule cons_eq)
 apply(rule pick_third_L)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_fourth_L)
 apply(rule cons_eq)
 apply(rule pick_fourth_L)
 apply(rule cons_eq)
 apply(rule pick_second_L)
 apply(rule cons_eq)
 apply(rule pick_second_L)
 apply(rule cons_eq)
 apply(rule sep_commute)
apply(simp)
apply(rule pick_ninth_L)
apply(rule cons_eq)
apply(rule pick_ninth_L)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule cons_eq)
apply(rule sep_functional)
 apply(rule program_counter_comm)
apply(simp)
done

(* whole_concrete_program *)

definition whole_concrete_program :: "(int * inst) set"
where "whole_concrete_program =
     {(0, Stack (PUSH_N [0])), (2, Storage SLOAD),
                       (3, Info CALLER), (4, Arith inst_EQ),
                       (5, Stack (PUSH_N [8])), (7, Pc JUMPI),
                       (8, Pc JUMPDEST),
                       (9, Stack (PUSH_N [0])),
                       (11, Dup 0),
                       (12, Dup 0),
                       (13, Dup 0),
                       (14, Info ADDRESS),
                       (15, Info BALANCE),
                       (16, Info CALLER),
                       (17, Info GAS),
                       (18, Misc CALL)}"

(* check_pass_whole_concrete *)
lemma check_pass_whole_concrete:
  "triple {OutOfGas} (\<langle>unat bn \<ge> 2463000 \<rangle> **
                       block_number_pred bn **
                       stack_height 0 **
                       program_counter 0 ** caller c **
                       storage (word_rcat [0]) (ucast c) **
                       gas_pred g **
                       continuing **
                       this_account t **
                       balance t b **
                       memory_usage 0
                      )
                      whole_concrete_program
                      (memory_usage 0 **
                       stack_topmost 0 [] **
                       program_counter 19 **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       not_continuing **
                       action (ContractCall \<lparr>
                                  callarg_gas = word_of_int (g + (- Gjumpdest - Ghigh - 7 * Gverylow - Gsload (unat bn)) - 408)
                                , callarg_code = c
                                , callarg_recipient = c
                                , callarg_value = b
                                , callarg_data = []
                                , callarg_output_begin = word_rcat [0]
                                , callarg_output_size = word_rcat [0] \<rparr>) **
                       block_number_pred bn **
                       caller c **
                       storage (word_rcat [0]) (ucast c)
                      )"
apply(auto)
apply(rule triple_code_eq)
 apply(rule_tac R = "emp" in frame_backward)
   apply(rule_tac k = 0 and d = 8 and h = 0 and bn = bn and c = c and g = g and u = 0 in  check_pass_whole)
  apply(simp)
 apply(simp)
apply(simp add: whole_concrete_program_def)
done
  

(*
prefix_invalid_caller_concrete:
*)

end
