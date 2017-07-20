theory SimpleWallet

imports "../Hoare/HoareTripleForInstructions2" "../Hoare/HoareTripleForLogGasCall"

begin

context
  includes hoare_bundle hoare_inst_bundle
           sep_crunch_bundle simp_for_triples_bundle    
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
   "triple net {OutOfGas} (\<langle> h \<le> 1023\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       account_existence c existence **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0]))}
                      (stack_height (h + 1) **
                       stack h (word_rcat [0]) **
                       program_counter (2 + k) **
                       gas_pred (g - Gverylow) **
                       account_existence c existence **
                       continuing
                      )"
apply(rule weaken_post)
 apply(rule strengthen_pre)
  apply(rule_tac k = k and h = h and g = g in push_gas_triple)
apply(auto simp add: word_rcat_def bin_rcat_def continuing_def)
done

lemma add_comm_pc:
  " PcElm (x + y) \<in> s \<Longrightarrow>  PcElm (y + x) \<in> s"
(* sledgehammer *)
  by (simp add: semiring_normalization_rules(24))

lemma seventh_pure [simp] :
  "(rest ** a ** b ** c ** d ** e ** \<langle> P \<rangle>) s =
  (P \<and> (rest ** a ** b ** c ** d ** e) s)"
proof -
  have "(rest ** a ** b ** c ** d ** e ** \<langle> P \<rangle>) s = (\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e) s"
    by (simp add: sep_conj_ac)
  moreover have "(\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e) s = (P \<and> (rest ** a ** b ** c ** d ** e) s)"
    by (simp only: pure_sep)
  ultimately show ?thesis
    by auto
qed

lemma eighth_pure [simp] :
  "(rest ** a ** b ** c ** d ** e ** f ** \<langle> P \<rangle>) s =
  (P \<and> (rest ** a ** b ** c ** d ** e ** f) s)"
proof -
  have "(rest ** a ** b ** c ** d ** e ** f ** \<langle> P \<rangle>) s = (\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f) s"
    by (simp add: sep_conj_ac)
  moreover have "(\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f) s = (P \<and> (rest ** a ** b ** c ** d ** e ** f) s)"
    by (simp only: pure_sep)
  ultimately show ?thesis
    by auto
qed

lemma ninth_pure [simp] :
  "(rest ** a ** b ** c ** d ** e ** f ** g ** \<langle> P \<rangle>) s =
  (P \<and> (rest ** a ** b ** c ** d ** e ** f ** g) s)"
proof -
  have "(rest ** a ** b ** c ** d ** e ** f ** g ** \<langle> P \<rangle>) s = (\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f ** g) s"
    by (simp add: sep_conj_ac)
  moreover have "(\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f ** g) s = (P \<and> (rest ** a ** b ** c ** d ** e ** f ** g) s)"
    by (simp only: pure_sep)
  ultimately show ?thesis
    by auto
qed

lemma tenth_pure [simp] :
  "(rest ** a ** b ** c ** d ** e ** f ** g ** h ** \<langle> P \<rangle>) s =
  (P \<and> (rest ** a ** b ** c ** d ** e ** f ** g ** h) s)"
proof -
  have "(rest ** a ** b ** c ** d ** e ** f ** g ** h ** \<langle> P \<rangle>) s = (\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f ** g ** h) s"
    by (simp add: sep_conj_ac)
  moreover have "(\<langle> P \<rangle> ** rest ** a ** b ** c ** d ** e ** f ** g ** h) s = (P \<and> (rest ** a ** b ** c ** d ** e ** f ** g ** h) s)"
    by (simp only: pure_sep)
  ultimately show ?thesis
    by auto
qed


lemma pre_fifth_pure [simp]:
  "triple net failures (a ** b ** c ** d ** \<langle> P \<rangle>) cod post =
   (P \<longrightarrow> triple net failures (a ** b ** c ** d) cod post)"
  apply(auto simp add: triple_def)
    apply (sep_simp simp: pure_sep)+
done


lemma pre_sixth_pure [simp]:
  "triple net failures (a ** b ** c ** d ** e ** \<langle> P \<rangle>) cod post =
   (P \<longrightarrow> triple net failures (a ** b ** c ** d ** e) cod post)"
  apply(auto simp add: triple_def)
    apply (sep_simp simp: pure_sep)+
done

lemma pre_seventh_pure [simp]:
  "triple net failures (a ** b ** c ** d ** e ** f ** \<langle> P \<rangle>) cod post =
   (P \<longrightarrow> triple net failures (a ** b ** c ** d ** e ** f) cod post)"
  apply(auto simp add: triple_def)
   apply (sep_simp simp: pure_sep)+
done

lemma pre_eigth_pure [simp]:
  "triple net failures (a ** b ** c ** d ** e ** f ** g ** \<langle> P \<rangle>) cod post =
   (P \<longrightarrow> triple net failures (a ** b ** c ** d ** e ** f ** g) cod post)"
  apply(auto simp add: triple_def)
    apply (sep_simp simp: pure_sep)+
done

lemma pc_add [simp]:
  "PcElm (x + y) = PcElm (y + x)"
apply(auto)
done

lemma push0dup1_triple :
   "triple net {OutOfGas} (\<langle> h \<le> 1022\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       account_existence c existence **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0)}
                      (stack_height (h + 2) **
                       stack (Suc h) (word_rcat [0]) **
                       stack h (word_rcat [0]) **
                       program_counter (3 + k) **
                       gas_pred (g - 2 * Gverylow) **
                       account_existence c existence **
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
  apply(auto simp add: word_rcat_def bin_rcat_def elim: back_subst[where P=continuing])
done

lemma true_is_emp [simp] :
 "\<langle> True \<rangle> = emp"
using pure_def emp_def apply blast
done

lemma dup1dup1_triple :
   "triple net {OutOfGas} (\<langle> h \<le> 1021\<rangle> **
                       stack_height (Suc h) **
                       stack h w **
                       program_counter k **
                       gas_pred g **
                       account_existence c existence **
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
                       account_existence c existence **
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
 apply(auto simp: sep_conj_ac)
done

lemma triple_code_eq :
  "triple net s p c r \<Longrightarrow> c = c' \<Longrightarrow> triple net s p c' r"
apply(simp)
done

(* lemma sep_functional :
  "a = b \<Longrightarrow> c = d \<Longrightarrow> a ** c = b ** d"
apply(simp add: sep_conj_ac)
done

lemma rotate4 :
  "a ** b ** c ** d = b ** c ** d ** a"
  using sep_assoc sep_commute by auto

lemma first_three :
  "a ** b ** c ** d = R \<Longrightarrow> c ** b ** a ** d = R"
apply simp
done


lemma pick_third_L :
  "c ** a ** b ** rest = R \<Longrightarrow> a ** b ** c ** rest = R"
proof simp
qed

lemma pick_thirdL:
 "a ** b ** rest = R \<Longrightarrow> a ** b ** c ** rest = c ** R"
  by (simp add: pick_third_L)
 *)
lemma pddd_triple :
"triple net {OutOfGas} (\<langle> h \<le> 1020\<rangle> **
                       stack_height h **
                       program_counter k **
                       gas_pred g **
                       account_existence c existence **
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
                       account_existence c existence **
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
  apply(auto simp: )[1]
  apply simp
  apply (simp only: sep_conj_ac)
  apply (rule ext)
  apply (simp add: word_rcat_def bin_rcat_def sep_conj_ac continuing_def set_diff_eq)    
  apply (rule iffI)
  apply (clarsimp simp add: word_rcat_def bin_rcat_def)
  apply (rule conjI)
   apply (subgoal_tac "h + 4 = (Suc (Suc (Suc (Suc h))))"; simp)
  apply (erule back_subst[where P="\<lambda>v. v = {ContinuingElm True}"])
   apply (auto)[1]
  apply (clarsimp simp add: word_rcat_def bin_rcat_def)
  apply (rule conjI)
   apply (subgoal_tac "h + 4 = (Suc (Suc (Suc (Suc h))))"; simp only:)
apply (erule back_subst[where P="\<lambda>v. v = {ContinuingElm True}"])
apply (auto)[1]
done


lemma uu_addr [simp] :
  "(ucast (ucast (a :: address) :: w256) :: address) = a"
apply(rule ucast_down_ucast_id)
apply(simp add: is_down_def target_size_def source_size_def word_size)
done

lemma this_balance :
  "triple net {OutOfGas}
          (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle>
           ** block_number_pred bn ** stack_height h ** program_counter k ** this_account t ** 
           balance t b ** gas_pred g ** account_existence c existence **continuing)
          {(k, Info ADDRESS), (k + 1, Info BALANCE)}
          (block_number_pred bn ** stack_height (h + 1) ** stack h b ** balance t b
           ** program_counter (2 + k) ** this_account t ** gas_pred (g - Gbase - 400)
           ** account_existence c existence **continuing )"
apply(auto)
apply(rule_tac cL = "{(k, Info ADDRESS)}" and cR = "{(k + 1, Info BALANCE)}" in composition)
  apply(auto)
 apply(rule_tac R = "balance t b ** block_number_pred bn" in frame_backward)
   apply(rule_tac h = h and g = g and t = t in address_gas_triple)
   apply (auto simp: sep_conj_ac)                            
apply(rule_tac R = "this_account t" in frame_backward)
 apply(rule_tac h = h and g = "g - 2" and bn = bn and a = "ucast t" and b = b in balance_gas_triple)
 apply(auto simp: sep_conj_ac)
done

lemma caller_gas :
"
triple net {OutOfGas}
          (\<langle> h \<le> 1022 \<rangle> ** stack_height h ** program_counter k ** caller c ** gas_pred g **
           account_existence c existence ** continuing)
          {(k, Info CALLER), (k + 1, Stack (PUSH_N [8, 0]))}
          (stack_height (h + 2) ** stack (Suc h) (word_rcat [(8 :: byte), 0]) ** stack h (ucast c)
           ** program_counter (4 + k) ** caller c ** gas_pred (g - 2 - Gverylow) ** 
                       account_existence c existence ** continuing )
"
apply(auto)
apply(rule_tac cL = "{(k, Info CALLER)}" and cR = "{(k + 1, Stack (PUSH_N [8, 0]))}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
  apply(rule_tac h = "h" and c = c and g = g in caller_gas_triple) 
 apply(auto)
apply(rule_tac R = "stack h (ucast c) ** caller c" in frame_backward)
  apply(rule_tac h = "Suc h" and g = "g - 2" in push_gas_triple)
 apply(auto simp: sep_conj_ac)
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
  "triple net {OutOfGas}
          (\<langle> h \<le> 1021 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle>
           ** block_number_pred bn ** caller c ** stack_height h ** program_counter k ** this_account t ** 
           balance t b ** gas_pred g ** account_existence c existence ** continuing)
          {(k, Info ADDRESS), (k + 1, Info BALANCE), (k + 2, Info CALLER), (k + 3, Stack (PUSH_N [8, 0]))}
          (block_number_pred bn ** caller c ** stack_height (h + 3) ** 
           stack (Suc (Suc h)) (word_rcat [(8 :: byte), 0]) ** stack (Suc h) (ucast c) ** stack h b ** balance t b
           ** program_counter (6 + k) ** this_account t ** gas_pred (g - 404 - Gverylow)
           ** account_existence c existence **continuing )"
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Info ADDRESS), (k + 1, Info BALANCE)}"
           and cR = "{(k + 2, Info CALLER), (k + 3, Stack (PUSH_N [8, 0]))}" in composition)
  apply(auto)[1]
 apply(rule_tac R = "caller c" in frame_backward)
   apply(rule_tac h = h and bn = bn and g = g and t = t and b = b in this_balance)
  apply(auto)
 apply (auto simp: sep_conj_ac)
apply(rule_tac R = "balance t b ** stack h b ** block_number_pred bn ** this_account t" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac k = "k + 2" and h = "Suc h" and c = c and g = "g - Gbase - 400" in caller_gas)
   apply simp
   apply auto[1]
  apply (auto simp: sep_conj_ac)[1]
  apply (clarsimp simp: sep_conj_ac)
   apply (subgoal_tac "(Suc (Suc (Suc h))) = h + 3"; simp only: sep_conj_ac)
done

lemma four_plus:
 " h + 4 = (Suc (Suc (Suc (Suc h))))"
apply(simp)
done

lemma five_plus:
 "h + 5 = Suc (Suc (Suc (Suc (Suc h))))"
apply(simp)
done

lemma six_plus:
 "h + 6 = Suc (Suc (Suc (Suc (Suc (Suc h)))))"
apply(simp)
done

lemma sep_conj_eq:
  "P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> (P \<and>* Q) = (P' \<and>* Q')"
  by auto

lemma seven_args:
"triple net {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn \<and> at_least_eip150 net\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       account_existence c existence **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Stack (PUSH_N [8, 0]))
                      }
                      (block_number_pred bn ** caller c **
                       stack_height (h + 7) **
                       stack (Suc (Suc (Suc (Suc (Suc (Suc h)))))) (word_rcat [(8 :: byte), 0]) **
                       stack (Suc (Suc (Suc (Suc (Suc h))))) (ucast c) **
                       stack (Suc (Suc (Suc (Suc h)))) b **
                       stack (Suc (Suc (Suc h))) (word_rcat [0]) **
                       stack (Suc (Suc h)) (word_rcat [0]) **
                       stack (Suc h) (word_rcat [0]) **
                       stack h (word_rcat [0]) **
                       program_counter (11 + k) **
                       this_account t **
                       balance t b **
                       gas_pred (g - 404 - 5 * Gverylow) **
                       account_existence c existence **
                       continuing
                      )"
apply(simp only: move_pureL)
apply(auto)
 apply(rule_tac cL = "{(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0)}"
            and cR = "{(5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Stack (PUSH_N [8, 0]))}" in composition)
  apply(auto)
 apply(rule_tac R = "block_number_pred bn **
      caller c ** this_account t ** balance t b" in frame_backward)
  apply(rule_tac h = h and g = g in pddd_triple)
  apply (simp add: sep_conj_ac)
  apply (rule refl)
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
  apply(simp add: sep_conj_ac)+
  apply (rule sep_conj_eq[OF refl] )+
  apply (rule ext, rule iffI)
   apply (sep_cancel)+
  apply (simp only: semiring_normalization_rules(24) )
   apply (sep_cancel)+
  apply (auto simp:  four_plus five_plus six_plus)[1]
  apply(simp only :  four_plus five_plus six_plus)
       apply (sep_cancel)+
  apply (simp only: semiring_normalization_rules(24) four_plus five_plus six_plus)
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
by (auto simp add: stack_topmost_def four_plus five_plus six_plus plus_seven elim!:back_subst[where P=rest])


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
apply(simp add: sep_conj_def)
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
"triple net {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn \<and> at_least_eip150 net\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       account_existence c existence **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Stack (PUSH_N [8, 0]))
                      }
                      (block_number_pred bn ** caller c **
                       stack_topmost h [word_rcat [0], word_rcat [0], word_rcat [0], word_rcat [0],
                         b, ucast c, 2048] **
                       program_counter (11 + k) **
                       this_account t **
                       balance t b **
                       gas_pred (g - 404 - 5 * Gverylow) **
                       account_existence c existence **
                       continuing
                      )"
apply(rule weaken_post)
 apply(rule seven_args)
apply(simp only: stack_topmost_special_translate)
  apply (rule allI)
  apply (rule impI)
  apply sep_cancel+
  apply (simp add: word_rcat_def bin_rcat_def bin_cat_def)
  done

lemma word_of_int_bin_cat:
  "((word_of_int (bin_cat 8 8 0))::256 word) = 2048"
  by (simp add: bin_cat_def)
lemma call_with_args:
"triple net {OutOfGas} (\<langle> h \<le> 1017 \<and> 2463000 \<le> unat bn \<and> at_least_eip150 net\<rangle>
                    ** block_number_pred bn ** caller c **
                       stack_height h **
                       program_counter k **
                       this_account t **
                       balance t b **
                       gas_pred g **
                       account_existence c existence **
                       continuing ** memory_usage u

                      )
                      {(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Stack (PUSH_N [8, 0])),
                       (11 + k, Misc CALL)
                      }
                      (block_number_pred bn ** caller c **
                       memory_usage u **
                       stack_topmost h [] **
                       program_counter (12 + k) **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       account_existence c existence **
                       not_continuing **
                       action (ContractCall \<lparr>
                                  callarg_gas = (word_of_int (Ccallgas 2048 (ucast c) b
                                      (\<not> existence) ((g - 404 - 5 * Gverylow)) net
                                      (calc_memu_extra u 2048 (ucast c) b 0 0 0 0)))
                                , callarg_code = c
                                , callarg_recipient = c
                                , callarg_value = b
                                , callarg_data = []
                                , callarg_output_begin = word_rcat [0]
                                , callarg_output_size = word_rcat [0] \<rparr>)
                      )"
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])),
                       (k + 2, Dup 0),
                       (k + 3, Dup 0),
                       (k + 4, Dup 0),
                       (5 + k, Info ADDRESS),
                       (6 + k, Info BALANCE),
                       (7 + k, Info CALLER),
                       (8 + k, Stack (PUSH_N [8, 0]))}"
            and cR = "{(11 + k, Misc CALL)}" in composition)
    apply(auto)
  apply(rule_tac R = "memory_usage u" in frame_backward)
  apply(rule_tac k = k and h = h and c = c and bn = bn and t = t and b = b and g = g in seven_args_packed)
      apply(simp add: )
    apply (rule refl)
 apply simp
apply(rule_tac R = "block_number_pred bn **
      caller c" in frame_backward)
  apply(rule_tac h = h and v = b and fund = b and input = "[]" 
        and in_size = "word_rcat [0]" and in_begin = "word_rcat [0]"
        and out_size = "word_rcat [0]" and out_begin = "word_rcat [0]"
        and g = "2048" and r = "ucast c"
        and this = t and u = u and existence = existence
        in call_gas_triple)
     apply(simp add: word_rcat_def bin_rcat_def word_of_int_bin_cat)
     apply (rule ext, rule iffI)
     apply sep_cancel+
     apply (rule ext, rule iffI)
     apply sep_cancel+
     apply (auto simp:)[1]
       apply (simp only: memory_usage_def M_def)
      apply(simp add: word_rcat_def bin_rcat_def M_def)
       apply blast
      apply(auto simp add: word_rcat_def bin_rcat_def word_of_int_bin_cat M_def)[1]
   apply (auto simp add: balance_def)[1]
    (* Is this true? x
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule cons_eq)
 apply(rule pick_fifth_L)
 apply(rule sep_functional)
  apply(simp)
 apply blast
apply(simp add: word_rcat_def bin_rcat_def M_def)
done *)
  sorry


lemma equal_pred :
 "P = Q \<Longrightarrow> \<forall> s. P s \<longrightarrow> Q s"
apply(simp)
done


lemma push0sload :
   "triple net {OutOfGas} (\<langle> h \<le> 1023 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle> **
                       block_number_pred bn **
                       stack_height h **
                       program_counter k **
                       storage (word_rcat [0::8 word]) w **
                       gas_pred g **
                       account_existence c existence **
                       continuing
                      )
                      {(k, Stack (PUSH_N [0::8 word])), (k + 2, Storage SLOAD)}
                      (block_number_pred bn **
                       stack_height (h + 1) **
                       stack h w **
                       program_counter (3 + k) **
                       storage (word_rcat [0::8 word]) w **
                       gas_pred (g - Gverylow - Gsload net) **
                       account_existence c existence **
                       continuing
                      )"
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0]))}"
           and cR = "{(k + 2, Storage SLOAD)}" in composition)
  apply(auto)
 apply(rule_tac R = "block_number_pred bn ** storage (word_rcat [0:: 8 word]) w"
    in frame_backward)
   apply(rule_tac h = h and g = g in push_gas_triple)
    apply(simp add: sep_conj_ac)
   apply (rule sep_conj_eq[OF refl])+
    apply (rule refl)
 apply(simp)
apply(rule_tac R = "emp" in frame_backward)
  apply(rule_tac bn = bn and h = h and w = w and g = "g - Gverylow"
        and idx = "(word_rcat [0:: 8 word]):: 256 word"
        in sload_gas_triple)
   apply(auto)
   apply (simp add: sep_conj_ac)
   apply (rule sep_conj_eq[OF refl])+
    apply (simp only: semiring_normalization_rules(24))
   apply (rule sep_conj_eq[OF refl])+
    apply (sep_simp simp: emp_sep)
done

lemma caller_eq :
  "triple net {OutOfGas}  ( \<langle> h \<le> 1022 \<rangle> **
                        stack_height (h + 1) **
                        stack h w **
                        program_counter k ** caller c **
                        gas_pred g **
                        account_existence c existence **
                        continuing
                      )
                      {(k, Info CALLER), (k + 1, Arith inst_EQ)}
                      ( stack_height (h + 1) **
                        stack h (if ucast c = w then((word_of_int 1) ::  256 word) else((word_of_int 0) ::  256 word)) **
                        program_counter (k + 2) ** caller c **
                        gas_pred (g - Gbase - Gverylow) **
                        account_existence c existence **
                        continuing )"
apply(simp only: move_pureL)
apply(auto)
 apply(rule_tac cL = "{(k, Info CALLER)}"
           and cR = "{(k + 1, Arith inst_EQ)}" in composition)
   apply(auto)
  apply(rule_tac R = "stack h w" in frame_backward)
    apply(rule_tac h = "Suc h" and g = g and c = c in caller_gas_triple)
     apply(simp add: sep_conj_ac)
       apply (rule sep_conj_eq[OF refl])+
     apply(simp add: sep_conj_ac)
    apply (sep_simp simp: emp_sep)

  apply(simp)
 apply(rule_tac R = "caller c" in frame_backward)
   apply(rule_tac h = h and g = "g - 2" and v = "ucast c" and w = "ucast c"
       in eq_gas_triple)
    apply(simp)
    apply (simp add: sep_conj_ac semiring_normalization_rules(24))+
apply(rule_tac cL = "{(k, Info CALLER)}"
          and cR = "{(k + 1, Arith inst_EQ)}" in composition)
  apply(auto)
 apply(rule_tac R = "stack h w" in frame_backward)
   apply(rule_tac h = "Suc h" and g = g and c = c in caller_gas_triple)
    apply(simp add: sep_conj_ac)
   apply (rule refl)
 apply(simp)
apply(rule_tac R = "caller c" in frame_backward)
  apply(rule_tac h = h and g = "g - 2" and v = "ucast c" and w = "w"
      in eq_gas_triple)
    apply (simp add: sep_conj_ac semiring_normalization_rules(24))+
done

lemma first_four :
   "triple net {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle> **
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
                       gas_pred (g + (- Gsload net - 2) - 2 * Gverylow) **
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
 apply(simp)
apply(rule_tac R = "storage (word_rcat [0]) w ** block_number_pred bn" in frame_backward)
  apply(rule triple_code_eq)
   apply(rule_tac k = "k + 3" and h = h and w = w and c = c and g = "g - Gverylow - Gsload net" in caller_eq)
  apply auto
done


lemma pushjumpi_false:
   "triple net {OutOfGas} (\<langle> h \<le> 1022 \<rangle> **
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
  apply(auto)
apply(rule_tac R = "emp" in frame_backward)
  apply(rule_tac h = h and g = "g - Gverylow" and d = "(word_rcat [x])"
        in jumpi_false_gas_triple)
 apply(auto)
done

lemma pushjumpistop_false :
   "triple net {OutOfGas} (\<langle> h \<le> 1022 \<rangle> **
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
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [x])), (k + 2, Pc JUMPI)}"
           and cR = "{(k + 3, Misc STOP)}" in composition)
  apply(auto)
 apply(rule strengthen_pre)
 apply(rule_tac h = h and g = g in pushjumpi_false)
 apply(auto)
apply(rule_tac R = "gas_pred (g - Gverylow - Ghigh)" in frame_backward)
  apply(rule_tac h = h in stop_gas_triple)
 apply(auto)
done

lemma prefix_invalid_caller:
"triple net {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net \<and> ucast c \<noteq> w\<rangle> **
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
                       gas_pred (g + (- Gsload net - 2) - 2 * Gverylow - Gverylow - Ghigh) **
                       not_continuing ** action (ContractReturn []))"
apply(simp only: move_pureL)
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
  apply(rule_tac h = h and k = "k + 5" and x = x and g = "(g + (- Gsload net - 2) - 2 * Gverylow)"
        in pushjumpistop_false)
  apply(auto)
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
   "triple net {OutOfGas} (\<langle> h \<le> 1022 \<and> cond \<noteq> 0 \<rangle> **
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
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [d]))}" 
           and cR = "{(k + 2, Pc JUMPI), ((uint (ucast d :: w256)), Pc JUMPDEST)}" in composition)
  apply(auto)
 apply(rule_tac R = "stack h cond" in frame_backward)
   apply(rule_tac h = "h + 1" and g = g in push_gas_triple)
  apply(simp)
 apply(simp)
apply(rule_tac R = "emp" in frame_backward)
  apply(rule triple_code_eq)
  apply(rule_tac g = "g - Gverylow" and cond = cond and h = h and k = "k + 2" and d = "ucast d" in jumpi_true_gas_triple)
  apply(simp)
 apply(auto)
done


lemma prefix_true:
   "triple net {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net \<rangle> **
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
                       gas_pred (g + (- Gsload net - 2) - 3 * Gverylow - Ghigh) **
                       continuing
                      )"
apply(simp only: move_pureL)
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
  apply(rule_tac h = h and k = "k + 5" and d = d and cond = 1 and g = "g + (- Gsload net - 2) - 2 * Gverylow" in pushjumpi_true)
  apply(auto)
done

lemma prefix_true_over_JUMPDEST:
"triple net {OutOfGas} (\<langle> h \<le> 1022 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net \<rangle> **
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
                       gas_pred (g + (- Gsload net - 2) - 3 * Gverylow - Ghigh - Gjumpdest) **
                       continuing
                      )"
apply(simp only: move_pureL)
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
  apply(rule_tac h = h and g = "g + (- Gsload net - 2) - 3 * Gverylow - Ghigh" in jumpdest_gas_triple)
 apply(auto)
done


lemma check_pass_whole:
  "triple net {OutOfGas} (\<langle> h \<le> 1017 \<and> unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle> **
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
                       (k + 8, Misc STOP),
                       ((uint (ucast d :: w256)), Pc JUMPDEST),
                       ((uint d) + 1, Stack (PUSH_N [0])),
                       (3 + (uint d), Dup 0),
                       (4 + uint d, Dup 0),
                       (5 + uint d, Dup 0),
                       (6 + uint d, Info ADDRESS),
                       (7 + uint d, Info BALANCE),
                       (8 + uint d, Info CALLER),
                       (9 + uint d, Stack (PUSH_N [8, 0])),
                       (12 + uint d, Misc CALL)
                      }
                      (memory_usage u **
                       stack_topmost h [] **
                       program_counter (uint d + 13) **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       not_continuing **
                       action (ContractCall \<lparr>
                                  callarg_gas = word_rcat [(8 :: byte), 0]
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
apply(simp only: move_pureL)
apply(auto)
apply(rule_tac cL = "{(k, Stack (PUSH_N [0])), (k + 2, Storage SLOAD),
                       (k + 3, Info CALLER), (k + 4, Arith inst_EQ),
                       (5 + k, Stack (PUSH_N [d])), (k + 7, Pc JUMPI),
                       (k + 8, Misc STOP),
                       ((uint (ucast d :: w256)), Pc JUMPDEST)}"
           and cR = "{((uint d) + 1, Stack (PUSH_N [0])),
                       (3 + (uint d), Dup 0),
                       (4 + uint d, Dup 0),
                       (5 + uint d, Dup 0),
                       (6 + uint d, Info ADDRESS),
                       (7 + uint d, Info BALANCE),
                       (8 + uint d, Info CALLER),
                       (9 + uint d, Stack (PUSH_N [8, 0])),
                       (12 + uint d, Misc CALL)}" in composition)
  apply(auto)
 apply(rule_tac R = "this_account t ** balance t b ** memory_usage u" in
       frame_backward)
   apply(rule code_extension_backward)
    apply(rule_tac h = h and k = k in prefix_true_over_JUMPDEST)
   apply(simp)
  apply(auto)
apply(rule_tac R = "storage (word_rcat [0]) (ucast c)" in
      frame_backward)
  apply(rule_tac triple_code_eq)
   apply(rule_tac bn = bn and  h = h and k = "uint d + 1" and g = "g + (- Gsload net - 2) - 3 * Gverylow - Ghigh - Gjumpdest" in call_with_args)
  apply(simp)
(* apply(auto)
done *)
oops

(* whole_concrete_program *)

definition whole_concrete_program :: "(int * inst) set"
where "whole_concrete_program =
     {(0, Stack (PUSH_N [0])),   (* 6000 *)
      (2, Storage SLOAD),        (* 54 *)
      (3, Info CALLER),          (* 33 *)
      (4, Arith inst_EQ),        (* 14 *)
      (5, Stack (PUSH_N [9])),   (* 6009 *)
      (7, Pc JUMPI),             (* 57 *)
      (8, Misc STOP),            (* 00 *)
      (9, Pc JUMPDEST),          (* 5b *)
      (10, Stack (PUSH_N [0])),  (* 6000 *)
      (12, Dup 0),               (* 80 *)
      (13, Dup 0),               (* 80 *)
      (14, Dup 0),               (* 80 *)
      (15, Info ADDRESS),        (* 30 *)
      (16, Info BALANCE),        (* 31 *)
      (17, Info CALLER),         (* 33 *)
      (18, Stack (PUSH_N [8, 0])), (* 610800 *)
      (21, Misc CALL)}"          (* f1 *)
(* An implicit Misc STOP follows *)

(* The runtime code has 22 bytes: *)
(* 6000543314600957005b6000808080303133610800f1 *)

(* To deploy this:
0: CALLER      33
1: 0           6000
3: SSTORE      55
4: 22          6016
6: x           6010
8: 0           6000
10: CODECOPY   39
11: 22         6016
13: 0          6000
15: RETURN     f3
x = 16:        6000543314600957005b6000808080303133610800f1
*)

(* The bytecode is: *)
(* 336000556016601060003960166000f36000543314600957005b6000808080303133610800f1 *)

(* check_pass_whole_concrete *)
lemma check_pass_whole_concrete:
  "triple net {OutOfGas} (\<langle>unat bn \<ge> 2463000 \<and> at_least_eip150 net\<rangle> **
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
                       program_counter 22 **
                       this_account t **
                       balance t 0 **
                       gas_any **
                       not_continuing **
                       action (ContractCall \<lparr>
                                  callarg_gas = word_rcat [(8 :: byte), 0]
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
apply(simp only: move_pureL)
apply(auto)
apply(rule triple_code_eq)
 apply(rule_tac R = "emp" in frame_backward)
   apply(rule_tac k = 0 and d = 9 and h = 0 and bn = bn and c = c and g = g and u = 0 in  check_pass_whole)
  apply(simp)
 apply(simp)
apply(simp add: whole_concrete_program_def)
done
  
lemma whole_program_invalid_caller:
"triple net {OutOfGas} (\<langle>unat bn \<ge> 2463000 \<and> at_least_eip150 net \<and> ucast c \<noteq> w\<rangle> **
                       block_number_pred bn **
                       stack_height 0 **
                       program_counter 0 ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred g **
                       continuing
                      )
                      whole_concrete_program
                      (block_number_pred bn **
                       stack_height 0 **
                       program_counter 8 ** caller c **
                       storage (word_rcat [0]) w **
                       gas_pred (g + (- Gsload net - 2) - 2 * Gverylow - Gverylow - Ghigh) **
                       not_continuing ** action (ContractReturn []))"
apply(auto)
apply(rule code_extension_backward)
 apply(rule_tac R = emp in frame_backward)
   apply(rule_tac h = 0 and bn = bn and c = c and w = w and x = 9 in prefix_invalid_caller)
  apply(simp)
 apply(simp)
apply(simp add: whole_concrete_program_def)
done

(* how to test the contract

// build geth

$ cd shared
$ git clone git@github.com:ethereum/go-ethereum.git
$ cd go-ethereum
$ make


// setup chain

$ rm -rf ~/dapps/testing/00
$ mkdir -p ~/dapps/testing/00
$ cat > ~/dapps/testing/00/genesis.json
{
  "alloc": { },
  "nonce": "0x0000000000000042",
  "difficulty": "0x00400",
  "mixhash": "0x0000000000000000000000000000000000000000000000000000000000000000",
  "coinbase": "0x0000000000000000000000000000000000000000",
  "timestamp": "0x00",
  "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000000",
  "extraData": "0x11bbe8db4e347b4e8c937c1c8370e4b5ed33adb3db69cbdb7a38e1e50b1b82fa",
  "gasLimit": "0x4c4b40"
}

$ build/bin/geth --datadir ~/dapps/testing/00/ --networkid 4995690 init ~/dapps/testing/00/genesis.json
$ build/bin/geth --datadir ~/dapps/testing/00/ --networkid 4995690 --nodiscover --maxpeers 0 --verbosity 6 console 2>> ~/dapps/testing/00/00.log




// create two accounts

> eth.accounts
[]
// see how many there are

> personal.newAccount("empty")
> personal.newAccount("empty")

> owner = eth.accounts[0]
> other = eth.accounts[1]

// mine some ether.
> miner.start(8); admin.sleepBlocks(3); miner.stop()

> personal.unlockAccount(owner)

// send half ether from owner to other
> eth.sendTransaction({from: owner, to: other, value: eth.getBalance(owner) / 2})
> miner.start(8); admin.sleepBlocks(1); miner.stop()

> eth.getBalance(owner)
> eth.getBalance(other)

// owner deploys the contract
> bytecode = "0x336000556016601060003960166000f36000543314600957005b6000808080303133610800f1"

> tx = eth.sendTransaction({from: owner, data: bytecode })
> miner.start(8); admin.sleepBlocks(1); miner.stop()

// get the transaction receipt
> re = eth.getTransactionReceipt(tx)

// set contract as the address of the contract
> contract = re.contractAddress

// check the storage content of the contract
> eth.getStorageAt(contract, 0, "latest")
"0x0000000000000000000000008d8182285c55959f8c33995492edc3facf3e00c3"
> owner
"0x8d8182285c55959f8c33995492edc3facf3e00c3"
> eth.getCode(contract, "latest")
"0x6000543314600957005b60008080803031335af1"

// send owner to contract, some amount —> should bounce
> personal.unlockAccount(owner)
> eth.sendTransaction({from: owner, to: contract, value: web3.toWei(2, "ether")})
> miner.start(8);  admin.sleepBlocks(1)
> miner.stop()

> eth.getBalance(owner)
173515625000000000000
> eth.getBalance(contract)
0

// send other to contract, some amount —> the contract’s balance should increase
> personal.unlockAccount(other)
> eth.sendTransaction({from: other, to: contract, value: web3.toWei(3, "ether")})
> miner.start(8); admin.sleepBlocks(1); miner.stop()

> eth.getBalance(other)
52702703580000000000
> eth.getBalance(contract)
3000000000000000000

// send other to contract, some more amount —> the contract’s balance should again increase
> eth.sendTransaction({from: other, to: contract, value: web3.toWei(1, "ether")})
>     
> eth.getBalance(other)
51702282160000000000
> eth.getBalance(contract)
4000000000000000000

// owner calls the contract —> all funds should move from the contract to the owner
> eth.getBalance(owner)
> personal.unlockAccount(owner)
> eth.sendTransaction({from: owner, to: contract})

> miner.start(8); admin.sleepBlocks(1); miner.stop()
> eth.getBalance(owner)
> eth.getBalance(contract)


*)

end

end
