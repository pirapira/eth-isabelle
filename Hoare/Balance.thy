theory Balance
  imports "EvmFacts" "../lem/Block"
begin

(*
lemma balance_env :
"instruction_sem v c inst net =
 InstructionToEnvironment act v2 x33 \<Longrightarrow>
 vctx_balance v2 = vctx_balance v"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: rw
           split:list.splits)
         apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a (vctx_memory v))")
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x8 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x9; clarsimp simp: instruction_sem_simps Let_def split: list.splits  pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: Let_def instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
done

lemma balance_continue :
"instruction_sem v c inst net =
 InstructionContinue v2 \<Longrightarrow>
 vctx_balance v2 = vctx_balance v"
apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
apply (case_tac x1 ; 
          clarsimp simp: rw
           split:list.splits)
         apply (case_tac x2 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
apply(case_tac "\<not> cctx_hash_filter c ( cut_memory x21 x21a (vctx_memory v))")
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x8 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x9; clarsimp simp: instruction_sem_simps Let_def split: list.splits  pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: Let_def instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
done

lemma balance_continue_next :
"next_state stopper c (InstructionContinue v) =
 InstructionContinue v2 \<Longrightarrow>
 vctx_balance v2 = vctx_balance v"
apply (simp add:next_state_def)
apply (cases "\<not> check_annotations v c"; auto)
apply (cases "vctx_next_instruction v c"; auto)
apply (case_tac " check_resources v c (vctx_stack v) a"; auto)
using balance_continue apply simp
done

lemma balance_env_next :
"next_state stopper c (InstructionContinue v) =
 InstructionToEnvironment args v2 zz \<Longrightarrow>
 vctx_balance v2 = vctx_balance v"
apply (simp add:next_state_def)
apply (cases "\<not> check_annotations v c"; auto)
apply (cases "vctx_next_instruction v c"; auto)
apply (case_tac " check_resources v c (vctx_stack v) a"; auto)
using balance_env apply simp
done


fun sum_aux :: "(address \<Rightarrow> w256) \<Rightarrow> nat \<Rightarrow> nat" where
"sum_aux bal 0 = 0"
| "sum_aux bal (Suc n) = unat (bal (word_of_int (int n))) + sum_aux bal n"

definition sum :: "(address \<Rightarrow> w256) \<Rightarrow> nat" where
"sum bal = sum_aux bal (2^160)"


definition total_balance :: "global0 \<Rightarrow> nat" where
"total_balance g = sum (\<lambda>a. account_balance0 (g_current g a))"
definition total_balance_nat :: "(address \<Rightarrow> account) \<Rightarrow> nat" where
"total_balance_nat g = sum (\<lambda>a. account_balance0 (g a))"

definition total_balance :: "(address \<Rightarrow> account) \<Rightarrow> int" where
"total_balance g = int (sum (\<lambda>a. account_balance0 (g a)))"
*)

definition abal :: "(address \<Rightarrow> account) \<Rightarrow> nat \<Rightarrow> int" where
"abal st = (\<lambda>i. uint (account_balance0 (st (word_of_int (int i)))))"

definition total_balance :: "(address \<Rightarrow> account) \<Rightarrow> int" where
"total_balance g = sum (abal g) {0..2^160-1}"
(*
   (\<Sum>i::nat=0..2^160-1.
     uint (account_balance0 (g (word_of_int (int i)))))"
*)
lemma balance_same1 :
"account_balance0
                 (if a = cctx_this (g_cctx st1)
                  then g_current st1
                        (cctx_this (g_cctx st1))
                       \<lparr>account_storage0 :=
                          vctx_storage v\<rparr>
                  else g_current st1 a) =
 account_balance0 (g_current st1 a)"
by auto

lemma balance_same2 :
"account_balance0
                 (if a = addr
                  then st1 addr
                       \<lparr>account_storage0 :=
                          vctx_storage v\<rparr>
                  else st1 a) =
 account_balance0 (st1 a)"
by auto

lemma total_balance_update_return :
"total_balance (update_return acc addr v) = total_balance acc"
apply (simp add: total_balance_def abal_def
 update_return_def update_world_def
 balance_same2)
done

lemma update_if :
  "(if a = b then c else update_world acc b nb a) =
   (if a = b then c else acc a)"
apply (auto simp add: update_world_def)
done

(*
lemma balance_if :
"account_balance0 (if a = addr
                  then x
                  else y) =
 (if a = addr then account_balance0 x else account_balance0 y)"
*)
lemma account_balance_double :
  "x\<lparr>account_balance0 := a, account_balance0 := b \<rparr> =
   x\<lparr>account_balance0 := b \<rparr>"
apply (auto)
done

fun balance_list_aux :: "(address \<Rightarrow> w256) \<Rightarrow> nat \<Rightarrow> w256 list" where
"balance_list_aux bal 0 = []"
| "balance_list_aux bal (Suc n) =
     bal (word_of_int (int n)) # balance_list_aux bal n"

definition balance_list :: "(address \<Rightarrow> w256) \<Rightarrow> w256 list" where
"balance_list bal = balance_list_aux bal (2^160)"

lemma balance_list_eq_aux :
  "x < n \<Longrightarrow>
   balance_list_aux bal n ! x = bal (word_of_int (int (n-x-1)))"
apply (induction n arbitrary:x rule:balance_list_aux.induct)
apply (auto)
apply (case_tac "x=n")
apply auto
oops

lemma sum_one :
  "(\<Sum>i::nat=l..l. f i) = (f l)"
  by simp

lemma sum_zero :
  "(\<Sum>i::nat=l+1..l. f i) = 0"
  by simp

lemma sum_ub_add_nat: assumes "(m::nat) \<le> n"
  shows "sum f {m..n + p} = sum f {m..n} + sum f {n + 1..n + p}"
proof-
  have "{m .. n+p} = {m..n} \<union> {n+1..n+p}" using \<open>m \<le> n\<close> by auto
  thus ?thesis by (auto simp: ivl_disj_int sum.union_disjoint
    atLeastSucAtMost_greaterThanAtMost)
qed

lemma sum_ub_add_nat2: assumes "(m::nat) \<le> n"
  shows "sum f {m..n + p} = sum f {m..<n} + sum f {n..n + p}"
proof-
  have "{m .. n+p} = {m..<n} \<union> {n..n+p}" using \<open>m \<le> n\<close> by auto
  thus ?thesis by (auto simp: ivl_disj_int sum.union_disjoint
    atLeastSucAtMost_greaterThanAtMost)
qed

lemma sum_split :
  "l \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow>
   (\<Sum>i::nat=l..n. f i) =
   (\<Sum>i::nat=l..k. f i) + (\<Sum>i::nat=k+1..n. f i)"
apply (simp)
using sum_ub_add_nat [of l k f "n-k"]
apply force
done

lemma sum_split2 :
  "l \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow>
   (\<Sum>i::nat=l..n. f i) =
   (\<Sum>i::nat=l..<k. f i) + (\<Sum>i::nat=k..n. f i)"
using sum_ub_add_nat2 [of l k f "n-k"]
apply force
done

lemma sum_if :
  assumes a:"k \<le> n"
  shows 
   "(\<Sum>i::nat=0..n. (if i = k then (x::int) else f i)) =
    (\<Sum>i=0..<k. f i) + x + (\<Sum>i=k+1..n. f i)"
proof -
  have b1: "sum f {0..<k} = (\<Sum>i=0..<k. (if i = k then x else f i))"
    by auto
  have b2: "sum f {k+1..n} = (\<Sum>i=k+1..n. (if i = k then x else f i))"
    by auto
  have b3: "x = (\<lambda>i. if i = k then (x::int) else f i) k" by auto
  then have "sum f {0..<k} + x = (\<Sum>i=0..k. (if i = k then x else f i))"
     using b1 sum_split2 [of 0 k k "%i. (if i = k then x else f i)"]
     by force
  then show ?thesis using b2
    by (metis (no_types, lifting) assms le_add2 le_add_same_cancel2 sum_split) 
qed

lemma sum_single :
  assumes a:"k \<le> n"
  shows 
   "(\<Sum>i::nat=0..n. (if i = k then (x::int) else 0)) = x"
using a sum_if [of k n x "%i. 0"] by auto

lemma sum_update :
  assumes a:"k \<le> n"
  shows 
   "(\<Sum>i::nat=0..n. (if i = k then (x::int) else f i)) =
    (\<Sum>i=0..n. f i) + x - f k"
proof -
  have b1:
   "(\<Sum>i::nat=0..n. (if i = k then (x::int) else f i)) =
    sum f {0..<k} + x + sum f {k+1..n}"
   using a sum_if by force
  have eq: "f = (%i. if i = k then f k else f i)" by auto
  then have b2:
    "sum (%i. if i = k then f k else f i) {0..n} = 
     sum f {0..n}" by metis
  then have b3:
    "sum f {0..<k} + sum f {k+1..n} = 
     sum f {0..n} - f k"
   using a sum_if [of k n "f k" f] by force
  then show ?thesis using b1 by auto
qed

lemma word_unat : "addr = word_of_int (int (unat addr))"
  by (metis uint_nat word_of_int_uint)

lemma find_mod_address :
  "uint (word_of_int x::address) = (x::int) mod 2^160"
apply (auto simp:uint_word_of_int)
done

lemma unat_mod_address [simp]:
  "unat (word_of_int (int x)::address) = x mod 2^160"
apply (simp add: find_mod_address unat_def)
  by (metis (mono_tags, hide_lams)
 Divides.transfer_int_nat_functions(2)
 nat_int.Rep_inverse' of_nat_numeral)

lemma test_eq :
"i < 2^160 \<Longrightarrow>
 (word_of_int (int i) = addr) = (i = unat (addr::address))"
apply auto
apply (metis uint_nat word_of_int_uint)
done

lemma sum_eq_small :
   "(\<forall>i\<le>n. f i = g i) \<Longrightarrow>
   sum f {0..n} = sum g {0..n}"
  by auto

lemma massage :
"uint (account_balance0 (st  addr)) =
 uint (account_balance0 (st (word_of_int (int (unat addr)))))"
by (metis uint_nat word_of_int_uint)

lemma addr_small : "unat (addr::address) \<le> 2^160-1"
apply (subst word_unat)
apply auto
done

lemma total_balance_update_world :
"total_balance (update_world st addr acc) = 
 total_balance st + uint (account_balance0 acc) -
                    uint (account_balance0 (st addr))"
apply (auto simp add:update_world_def total_balance_def abal_def
  if_distrib)
apply (subst sum_eq_small [of _ _
  "%i.  if i = unat addr
        then uint (account_balance0 acc)
        else uint
              (account_balance0
                (st (word_of_int (int i))))"])
apply (auto simp:test_eq)
apply (subst massage[of st addr])
apply (rule sum_update [of "unat addr" _
  "uint (account_balance0 acc)"
  "%i. uint (account_balance0 (st (word_of_int (int i))))"])
using addr_small
by force

lemma test : "(a::address) \<ge> 0"
apply auto
done

lemma uint_sub : "b \<le> a \<Longrightarrow> uint (a-b) = uint a - uint b"
  by (simp add: uint_minus_simple_alt)

lemma uint_add :
   "a+b \<ge> a \<Longrightarrow>
   uint (a+b) = uint a + uint b"
by (auto simp:uint_plus_simple)

lemma solution :
 "d \<le> a \<Longrightarrow> r+d \<ge> r \<Longrightarrow>
  uint (a - d) + (uint (r + d) - uint r - uint a) = 0"
apply (simp add:uint_add uint_sub)
done

lemma total_balance_update :
"v \<le> account_balance0 (acc addr) \<Longrightarrow>
 account_balance0 (acc recv) \<le>
    account_balance0 (acc recv) + v \<Longrightarrow>
 total_balance (transfer_balance acc addr recv v) = 
 total_balance acc"
apply (cases "addr = recv")
subgoal
apply (auto simp add: total_balance_def
 update_return_def update_world_def update_call_def
 transfer_balance_def add_balance_def sub_balance_def Let_def
 balance_same2 update_if if_distrib abal_def)
apply metis
done
apply (auto simp add:
 update_return_def update_world_def update_call_def
 transfer_balance_def Let_def
 balance_same2 update_if if_distrib add_balance_def sub_balance_def 
 total_balance_update_world)
apply (rule solution)
apply auto
done

lemma total_balance_update_call :
"callarg_value args \<le> account_balance0 (acc addr) \<Longrightarrow>
 account_balance0 (acc (callarg_recipient args)) \<le>
    account_balance0 (acc (callarg_recipient args)) +
    callarg_value args \<Longrightarrow>
 total_balance (update_call acc addr args) = 
 total_balance acc"
  by (simp add: total_balance_update update_call_def)

lemma total_balance_update_call2 :
"addr = callarg_recipient args \<Longrightarrow>
 total_balance (update_call acc addr args) = total_balance acc"
apply (auto simp add: total_balance_def
 update_return_def update_world_def update_call_def
 transfer_balance_def add_balance_def sub_balance_def Let_def
 balance_same2 update_if if_distrib abal_def)
apply metis
done

lemma total_balance_update_same :
"total_balance (transfer_balance acc addr addr v) = 
 total_balance acc"
apply (auto simp add: total_balance_def
 update_return_def update_world_def update_call_def
 transfer_balance_def add_balance_def sub_balance_def Let_def
 balance_same2 update_if if_distrib abal_def)
apply metis
done

lemma sum_split_one :
  "l \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow>
   (\<Sum>i::nat=l..n. f i) =
   (\<Sum>i::nat=l..<k. f i) + f k + (\<Sum>i::nat=k+1..n. f i)"
  by (metis add.commute sum_last_plus sum_split)

lemma abal_eq :
 "uint (account_balance0 (st a)) = abal st (unat a)"
apply (auto simp add:abal_def)
  by (metis word_unat)

lemma balance_split :
"k \<le> unat a \<Longrightarrow> unat a \<le> n \<Longrightarrow>
 sum (abal st) {k..n} =
    sum (abal st) {k..< unat a} +
    uint (account_balance0 (st a)) +
    sum (abal st) {unat a+1..n}"
apply (simp add:abal_eq)
using sum_split_one [of k "unat a" n "abal st"]
apply simp
done

lemma abal_nonneg : "abal st k \<ge> 0"
  by (simp add: abal_def)

lemma abal_sum_nonneg : "sum (abal st) {a..b} \<ge> 0"
  by (simp add: abal_nonneg sum_nonneg)

lemma overflow_one :
assumes a1:"total_balance st < 2^256"
shows
 "uint (account_balance0 (st a)) < 2^256"
proof -
  have "total_balance st = sum (abal st) {0..2 ^ 160 - 1}"
   by (simp add:total_balance_def) 
  then have aux:"total_balance st =
      sum (abal st) {0..< unat a} +
      uint (account_balance0 (st a)) +
      sum (abal st) {unat a+1..2^160-1}"
    using balance_split [of 0 a "2^160-1" st]
    by (metis addr_small total_balance_def zero_le)
  have bsmall: "unat a \<le> 2 ^ 160 - 1" by (metis addr_small)
  then show ?thesis using a1 aux abal_sum_nonneg
    by (smt abal_nonneg sum_nonneg) 
qed

lemma overflow_pair :
assumes a1:"total_balance st < 2^256"
and a2:"a < b"
shows
 "uint (account_balance0 (st a)) +
  uint (account_balance0 (st b)) < 2^256"
proof -
  have "total_balance st = sum (abal st) {0..2 ^ 160 - 1}"
   by (simp add:total_balance_def) 
  then have aux:"total_balance st =
      sum (abal st) {0..< unat a} +
      uint (account_balance0 (st a)) +
      sum (abal st) {unat a+1..2^160-1}"
    using balance_split [of 0 a "2^160-1" st]
    by (metis addr_small total_balance_def zero_le)
  have bsmall: "unat b \<le> 2 ^ 160 - 1" by (metis addr_small)
  from a2 have "unat a + 1 \<le> unat b"
    by (metis Suc_eq_plus1 Suc_leI not_less  word_le_nat_alt) 
  then have "sum (abal st) {unat a+1..2^160-1} =
    sum (abal st) {unat a+1..< unat b} +
    uint (account_balance0 (st b)) +
    sum (abal st) {unat b+1..2^160-1}"
  using bsmall balance_split [of "unat a + 1" b "2^160-1" st] by force
  then have a:"total_balance st =
    sum (abal st) {0..< unat a} +
    uint (account_balance0 (st a)) +
    sum (abal st) {unat a+1..< unat b} +
    uint (account_balance0 (st b)) +
    sum (abal st) {unat b+1..2^160-1}"
  using aux by force
  then show ?thesis using a1 abal_sum_nonneg
    by (smt abal_nonneg sum_nonneg) 
qed

lemma find_mod :
  "uint (word_of_int x::w256) = (x::int) mod 2^256"
apply (auto simp:uint_word_of_int)
done

lemma uint_back : "uint (x::w256) = uint (word_of_int (uint x) :: w256)"
using word_of_int_uint [of x] by force

lemma overflow_plus :
  assumes a:"uint (a::w256) + uint b < 2^256"
  shows "uint (a + b) = uint a + uint b"
proof -
  have "uint (a + b) mod 2 ^ 256 = uint a + uint b"
    using a
    by (simp add: find_mod int_mod_eq' word_add_def)
  then show ?thesis using a
    by (metis find_mod word_of_int_uint)
qed

lemma overflow_small :
  "uint (a::w256) + uint b < 2^256 \<Longrightarrow>
  a \<le> a + b"
using overflow_plus [of a b] uint_plus_simple_iff by blast

lemma overflow :
"total_balance st < 2^256 \<Longrightarrow>
 x \<le> account_balance0 (st sender) \<Longrightarrow>
 sender \<noteq> r \<Longrightarrow>
 account_balance0 (st r) \<le>
 account_balance0 (st r) + x"
apply (cases "r < sender")
apply (rule overflow_small [of "account_balance0 (st r)" x])
using overflow_pair [of st r sender]
  apply (simp add: word_le_def)
apply (cases "sender < r")
apply (rule overflow_small [of "account_balance0 (st r)" x])
using overflow_pair [of st sender r]
  apply (simp add: word_le_def)
apply auto
done

lemma account_balance_return :
"account_balance0 (update_return st1 addr v r) =
 account_balance0 (st1 r)"
by (simp add:update_return_def update_world_def)

definition states :: "global0 \<Rightarrow> world_state list" where
"states g = (g_current g#map (%e. let (x,_,_,_) = e in x) (g_stack g))"

(* sorted lists *)
definition balance_inv :: "global0 \<Rightarrow> bool" where
"balance_inv g ==
   sorted (map total_balance (states g)) \<and>
   total_balance (last (states g)) \<le> total_balance (g_orig g)"

lemma tr_orig :
   "next0 net (Continue st1) = Continue st2 \<Longrightarrow>
    g_orig st1 = g_orig st2"
by (auto simp add:next0_def Let_def
  split:if_split_asm option.split_asm list.split_asm
   contract_action.split_asm stack_hint.split_asm
   instruction_result.splits)

lemma inv_depend :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    g_current st1 = g_current st2 \<Longrightarrow>
    g_stack st1 = g_stack st2 \<Longrightarrow>
    balance_inv st2"
by (simp add: balance_inv_def states_def)

lemma inv_current :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    total_balance (g_current st1) \<ge> total_balance (g_current st2) \<Longrightarrow>
    g_stack st1 = g_stack st2 \<Longrightarrow>
    balance_inv st2"
apply (auto simp add: balance_inv_def states_def)
  by (smt sorted_Cons)

lemma sorted_pop : "sorted (a#lst) \<Longrightarrow> sorted lst"
  by (simp add: sorted_Cons)

lemma sorted_dup : "sorted (a#lst) \<Longrightarrow> sorted (a#a#lst)"
  by simp


lemma inv_pop_states :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    states st1 = a # states st2 \<Longrightarrow>
    balance_inv st2"
apply (auto simp add: balance_inv_def)
using sorted_pop
apply force
  by (simp add: states_def)

lemma inv_pop :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    (g_current st2,e1,e2,e3) # g_stack st2 = g_stack st1 \<Longrightarrow>
    balance_inv st2"
apply (rule inv_pop_states [of st1 st2 "g_current st1"])
apply (auto simp add:states_def)
  by (metis (mono_tags, lifting) case_prod_conv list.simps(9))

lemma states_not_nil : "states st = [] \<Longrightarrow> False"
  by (simp add: states_def)

lemma inv_dup_states :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    states st2 = hd (states st1) # states st1 \<Longrightarrow>
    balance_inv st2"
apply (auto simp add: balance_inv_def)
using states_not_nil apply force
using sorted_dup
  by (metis hd_Cons_tl hd_map sorted_single)

lemma inv_dup :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    g_current st1 = g_current st2 \<Longrightarrow>
    (g_current st1,e1,e2,e3) # g_stack st1 = g_stack st2 \<Longrightarrow>
    balance_inv st2"
apply (rule inv_dup_states [of st1 st2])
apply (auto simp add:states_def)
  by (metis (mono_tags, lifting) case_prod_conv list.simps(9))

lemma inv_return :
  "balance_inv st \<Longrightarrow>
   balance_inv (st\<lparr>g_current := update_return (g_current st) addr v\<rparr>)"
using inv_current
  by (simp add: total_balance_update_return)

(* push state *)
lemma inv_push :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    total_balance (g_current st2) \<le> total_balance (g_current st1) \<Longrightarrow>
    (g_current st1,e1,e2,e3) # g_stack st1 = g_stack st2 \<Longrightarrow>
    balance_inv st2"
using inv_current [of "st2\<lparr> g_current := g_current st1\<rparr>" st2]
 and inv_dup by force

lemma inv_discard_aux :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    total_balance (g_current st2) \<le> total_balance (g_current st1) \<Longrightarrow>
    total_balance (g_current st1) \<le> total_balance disc \<Longrightarrow>
    (disc,e1,e2,e3) # g_stack st2 = g_stack st1 \<Longrightarrow>
    balance_inv st2"
using inv_current [of "st2\<lparr> g_current := disc\<rparr>" st2]
  inv_pop [of st1 "st2\<lparr> g_current := disc\<rparr>" e1 e2 e3]
 by force

lemma tb_update_nonce :
  "total_balance (update_nonce st x) = total_balance st"
by (auto simp add:update_nonce_def Let_def
  total_balance_update_world)

lemma tb_create_account :
  "total_balance (create_account st x y) = total_balance st"
by (auto simp add:create_account_def Let_def
  total_balance_update_world set_account_code_def)

lemma inv_stack_same :
  "balance_inv st \<Longrightarrow>
   total_balance a = total_balance b \<Longrightarrow>
   g_stack st = (a,x,y,z)#rest \<Longrightarrow>
   balance_inv (st\<lparr> g_stack := (b,x2,y2,z2) # rest \<rparr>)"
by (auto simp add:balance_inv_def states_def)

lemma inv_stack_same2 :
  "balance_inv st \<Longrightarrow>
   total_balance a = total_balance b \<Longrightarrow>
   g_stack st = (a,x,y,z)#rest \<Longrightarrow>
   g_stack st2 = (b,x2,y2,z2) # rest \<Longrightarrow>
   g_current st2 = g_current st \<Longrightarrow>
   g_orig st2 = g_orig st \<Longrightarrow>
   balance_inv st2"
by (auto simp add:balance_inv_def states_def)

lemma account_balance_nonce :
"account_balance0 (update_nonce st1 v r) =
 account_balance0 (st1 r)"
by (simp add:update_nonce_def update_world_def Let_def)

lemma account_balance_same :
"account_balance0 acc = account_balance0 (st1 v) \<Longrightarrow> 
 account_balance0 (update_world st1 v acc r) =
 account_balance0 (st1 r)"
by (simp add:update_nonce_def update_world_def Let_def)

lemma sort_out_create :
  "total_balance (g_current st1) < 2^256 \<Longrightarrow>
   balance_inv st1 \<Longrightarrow>
   g_stack st2 = (b,x2,y2,z2)#g_stack st1 \<Longrightarrow>
   g_orig st1 = g_orig st2 \<Longrightarrow>
   b = update_nonce (g_current st1) sender \<Longrightarrow>
   account_balance0 new_acc =
     account_balance0 (g_current st1 new_addr) \<Longrightarrow>
   account_balance0 (g_current st1 sender) \<ge> v \<Longrightarrow>
   g_current st2 =
      transfer_balance
          (update_world
               (update_return
                 (update_nonce (g_current st1) sender)
                      sender vc) new_addr new_acc)
      sender new_addr v \<Longrightarrow>
   balance_inv st2"
apply (rule inv_stack_same2 [of "st2\<lparr> g_stack :=
  (g_current st1, x2, y2, z2) # g_stack st1\<rparr>" "g_current st1"
  "update_nonce (g_current st1) sender" x2 y2 z2
   "g_stack st1" st2])
apply (auto simp:tb_update_nonce)
apply (rule inv_push)
apply auto
apply (cases "new_addr = sender")
apply simp
apply (subst total_balance_update_same)
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce)
(* new_addr \<noteq> sender *)
apply (subst total_balance_update)
apply (auto simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
using overflow apply force
done

lemma inv_depend_suicide :
"balance_inv
     (st1\<lparr>g_stack := rest,
          g_current := cur\<rparr>) \<Longrightarrow>
 balance_inv
     (st1\<lparr>g_stack := rest,
          g_current := cur,
          g_cctx := ctx,
          g_vmstate := vmstate,
          g_killed := killed \<rparr>)"
using inv_depend
apply force
done

lemma inv_depend_normal :
"balance_inv
     (st1\<lparr>g_stack := rest,
          g_current := cur\<rparr>) \<Longrightarrow>
 balance_inv
     (st1\<lparr>g_stack := rest,
          g_current := cur,
          g_cctx := ctx,
          g_vmstate := vmstate \<rparr>)"
using inv_depend
apply force
done

lemma inv_head :
  "balance_inv st1 \<Longrightarrow>
   g_stack st1 = (a, aa, aaa, b) # list \<Longrightarrow>
   total_balance (g_current st1) \<le> total_balance a"
by (auto simp add:balance_inv_def states_def)

lemma inv_discard :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    total_balance (g_current st2) \<le> total_balance (g_current st1) \<Longrightarrow>
    (disc,e1,e2,e3) # g_stack st2 = g_stack st1 \<Longrightarrow>
    balance_inv st2"
using inv_discard_aux [of st1 st2 disc e1 e2 e3]
  inv_head [of st1 disc e1 e2 e3 "g_stack st2"] by force

lemma sorted_first_last :
  "sorted (a#lst) \<Longrightarrow>
   a \<le> last (a#lst)"
  by (simp add: sorted_Cons)

lemma inv_orig_current :
   "balance_inv st \<Longrightarrow>
    total_balance (g_current st) \<le> total_balance (g_orig st)"
apply (simp add: balance_inv_def states_def)
using sorted_first_last [of "total_balance (g_current st)"
  "map (total_balance \<circ> (\<lambda>(x, u1, u2, u3). x))
       (g_stack st)"]
  by (smt List.map.compositionality last.simps last_map map_is_Nil_conv)

lemma compare_uint : "x \<le> y \<Longrightarrow>  x - uint b \<le> y"
  using diff_mono by fastforce

lemma tr_balance_finished :
   "next0 net (Continue st1) = Finished st2 \<Longrightarrow>
    total_balance (g_current st1) < 2^256 \<Longrightarrow>
    balance_inv st1 \<Longrightarrow>
    total_balance (f_state st2) \<le> total_balance (g_orig st1)"
apply (simp add:next0_def Let_def)
apply (cases "g_vmstate st1"; auto simp add:Let_def)
apply (case_tac "x21"; auto  simp add:Let_def split:if_splits)
apply (case_tac "g_stack st1"; auto simp add:Let_def)
apply (case_tac "g_stack st1"; auto simp add:Let_def)
subgoal for x32 x33 dst
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)
using inv_orig_current [of st1] compare_uint apply force

apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
inv_orig_current [of st1] compare_uint
apply (simp add: uint_plus_simple_iff)
done
apply (case_tac "list = [] \<and> g_create st1"; auto)
apply (case_tac b; auto)
subgoal for x32 x33 dst a aa ab
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)

using inv_orig_current [of st1] compare_uint apply force

apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
inv_orig_current [of st1] compare_uint
apply (simp add: uint_plus_simple_iff)
done
subgoal for x32 x33 dst a aa ab
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)

using inv_orig_current [of st1] compare_uint apply force

apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
inv_orig_current [of st1] compare_uint
apply (simp add: uint_plus_simple_iff)
done
subgoal for x32 x33 dst a aa ab
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)

using inv_orig_current [of st1] compare_uint apply force

apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
inv_orig_current [of st1] compare_uint
apply (simp add: uint_plus_simple_iff)
done
apply (case_tac "g_stack st1"; auto)
  apply (simp add: inv_orig_current total_balance_update_return)
apply (case_tac b; auto)
apply (case_tac "x6 = [] \<and> list = [] \<and> g_create st1"; simp)
  apply (auto simp add: inv_orig_current total_balance_update_return)[1]
apply (case_tac "vctx_gas x22 < 200 * int (length x6) \<and>
                homestead_block
                \<le> sint (block_number (vctx_block x22))"; simp)
apply (case_tac "vctx_gas x22 < 200 * int (length x6)"; auto)
done

lemma tr_balance_continue :
   "next0 net (Continue st1) = Continue st2 \<Longrightarrow>
    total_balance (g_current st1) < 2^256 \<Longrightarrow>
    balance_inv st1 \<Longrightarrow>
    balance_inv st2"
apply (simp add:next0_def Let_def)
apply (cases "g_vmstate st1"; auto)
using inv_depend apply force
subgoal for act v zz
apply (cases act; auto simp add:Let_def)
apply (case_tac "callarg_recipient x1 <s 256";auto)
apply (auto simp add:Let_def)
apply (case_tac
   "account_balance0
               (update_return (g_current st1)
                 (cctx_this (g_cctx st1)) v
                 (cctx_this (g_cctx st1)))
              < callarg_value x1 \<or>
              1023 < length (g_stack st1)";auto)
apply (rule inv_depend[of "st1
         \<lparr>g_current := update_return (g_current st1)
             (cctx_this (g_cctx st1)) v \<rparr>"])
apply (auto)
using inv_return apply force
apply (rule inv_depend[of "st1
         \<lparr>g_current := update_return (g_current st1)
             (cctx_this (g_cctx st1)) v \<rparr>"])
apply (auto)
using inv_return apply force
apply (simp add:Let_def)
apply(rule inv_push [of st1 st2])
apply auto

subgoal for args
apply (cases "cctx_this (g_cctx st1) = callarg_recipient args")

apply (subst total_balance_update_call2)
apply (auto simp:total_balance_update_return
  account_balance_return)
apply (subst total_balance_update_call)
apply (auto simp:total_balance_update_return
  account_balance_return)
apply (rule overflow [of "g_current st1" "callarg_value args"
  "cctx_this (g_cctx st1)" "callarg_recipient args"])
apply auto
done
(* delegate call  *)
subgoal for args
apply (cases "1023 < length (g_stack st1)";auto)
apply (rule inv_depend [of "st1\<lparr> g_current :=
       update_return (g_current st1)
        (cctx_this (g_cctx st1)) v\<rparr>" _])
apply auto
using inv_depend [of "st2\<lparr> g_current :=
       update_return (g_current st1)
        (cctx_this (g_cctx st1)) v\<rparr>" st2]
using inv_return apply force
apply(rule inv_push [of st1 _])
apply (auto simp:total_balance_update_return)
done
(* contract creation *)
subgoal for args
apply (split if_splits)
using inv_depend apply force
apply (simp add:Let_def)
apply (rule sort_out_create [of st1 st2 _ _ _ _ _
"(empty_account0
         _
        \<lparr>account_balance0 := _,
           account_exists := True\<rparr>)"
"calc_address _ _"
  "createarg_value args"])
apply (auto simp add:account_balance_return
account_balance_nonce)
done
subgoal for failure
apply (cases "g_stack st1"; auto)
subgoal for a aa ab b list
apply (rule inv_depend [of "st1\<lparr>g_stack := list, g_current := a\<rparr>"])
apply auto
using   inv_pop
apply force
done done
(* suicide *)
apply (cases "g_stack st1"; auto)
subgoal for dst a aa aaa b list
apply (auto simp add:Let_def)
apply (cases "list = [] \<and> g_create st1";simp)
apply clarsimp
apply (rule inv_depend_suicide)
apply (rule inv_discard[of st1 _ a])
apply clarsimp
apply clarsimp
apply clarsimp
apply (cases b)
apply clarsimp
subgoal
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
apply (simp add: uint_plus_simple_iff)
done
subgoal
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
apply (simp add: uint_plus_simple_iff)
done
subgoal
apply (simp add:total_balance_update_world
account_balance_return
  tb_create_account
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same)
apply (cases "dst = cctx_this (g_cctx st1)")
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  tb_create_account
  account_balance_same update_world_def)
apply (simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
using overflow [of "g_current st1"
  "account_balance0
       (g_current st1 (cctx_this (g_cctx st1)))"
 "cctx_this (g_cctx st1)" dst]
apply (simp add: uint_plus_simple_iff)
done
apply force
done
apply (cases "g_stack st1"; auto)
apply (case_tac b; auto)
subgoal for x6 saved_state aa ab list x2
apply (cases "x6 = [] \<and> list = [] \<and> g_create st1"; simp)
apply (cases "vctx_gas v < 200 * int (length x6) \<and>
             homestead_block
             \<le> sint (block_number (vctx_block v))"; simp)
apply clarsimp
using inv_pop apply force
apply (cases "vctx_gas v < 200 * int (length x6)"; clarsimp)
apply (rule inv_depend_normal)
subgoal
apply(rule inv_discard[of st1 _ saved_state])
apply (auto simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def)
done
apply (rule inv_depend_normal)
apply(rule inv_discard[of st1 _ saved_state])
apply (auto simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def
  tb_create_account)
done
subgoal for x6 saved_state aa ab list x31 x32
apply (rule inv_depend_normal)
apply(rule inv_discard[of st1 _ saved_state])
apply (auto simp add:total_balance_update_world
account_balance_return
  total_balance_update_return
  tb_update_nonce account_balance_nonce
  account_balance_same update_world_def
  tb_create_account)
done
done
done

lemma uint_fact :
   "x \<le> x+y \<Longrightarrow>
   uint (x+y) - uint x- uint y = 0"
  by (simp add: uint_plus_simple_iff)

lemma prepare_create_aux :
"g_orig st = state \<Longrightarrow>
 g_stack st = [] \<Longrightarrow>
 account_balance0 (state sender) \<ge> gas_value \<Longrightarrow>
 g_current st =
         update_world state sender
          (state sender
           \<lparr>account_balance0 :=
              account_balance0 (state sender) -
              gas_value\<rparr>) \<Longrightarrow>
 balance_inv st"
apply (simp add: balance_inv_def states_def
  total_balance_update_world)
  using word_le_def word_sub_le by auto

lemma uint_minus : "x \<le> y \<Longrightarrow> uint (y - x) \<le> uint y"
  using word_le_def word_sub_le by auto


lemma uint_mul_small :
   "uint (a::w256) * uint b < 2^256 \<Longrightarrow>
    uint (a*b) = uint a * uint b"
  by (simp add: mod_pos_pos_trivial uint_word_ariths(3))

lemma uint_mul_compare :
   "uint (a::w256) * uint b \<le> uint c \<Longrightarrow>
    a*b \<le> c"
using uint_mul_small [of a b]
proof -
  assume a1: "uint a * uint b \<le> uint c"
  then have "\<exists>i. \<not> uint (word_of_int i::256 word) < uint a * uint b"
    by (metis (no_types) not_le word_of_int_uint)
    then have "\<not> 2 ^ 256 \<le> uint a * uint b"
      by (metis (no_types) Divides.pos_mod_bound find_mod not_le order_trans zless2p)
    then have "uint a * uint b < 2 ^ 256"
      by (metis not_le)
  then show ?thesis
    using a1 by (metis (no_types) \<open>uint a * uint b < 2 ^ 256 \<Longrightarrow> uint (a * b) = uint a * uint b\<close> word_le_def)
qed

lemma unat_mul_compare :
   "unat (a::w256) * unat b \<le> unat c \<Longrightarrow>
    a*b \<le> c"
using uint_mul_compare [of a b c]
  le_unat_uoi word_le_nat_alt by fastforce


lemma gas_compare :
   "unat x + unat (a::w256) * unat b \<le> unat c \<Longrightarrow>
    a*b \<le> c"
using unat_mul_compare [of a b c]
  le_add2 order_trans by blast

lemma uint_stuff_aux :
"value \<le> sender \<Longrightarrow>
 recv \<le> recv + value \<Longrightarrow>
 uint (sender - value) +
(uint (recv + value) - uint recv) \<le> uint sender"
  using solution by fastforce

lemma uint_stuff :
"value \<le> sender - gas_value \<Longrightarrow>
 value \<le> sender \<Longrightarrow>
 recv \<le> recv + value \<Longrightarrow>
 uint (sender - gas_value - value) +
(uint (recv + value) - uint recv) \<le> uint (sender - gas_value)"
apply (rule uint_stuff_aux [of "value" "sender-gas_value" recv], auto)
done

lemma prepare_normal_aux :
"g_orig st = update_world state sender
               (state sender
                \<lparr>account_nonce := nonce,
                   account_balance0 :=
                     account_balance0 (state sender) -
                     gas_value \<rparr>) \<Longrightarrow>
 g_stack st = [] \<Longrightarrow>
 value \<le> account_balance0 (state sender) - gas_value \<Longrightarrow>
 value \<le> account_balance0 (state sender) \<Longrightarrow>
 account_balance0 (state recv) \<le> account_balance0 (state recv) + value \<Longrightarrow>
 g_current st = update_world
                 (update_world state sender
                   (state sender
                    \<lparr>account_nonce := nonce,
                       account_balance0 :=
                         account_balance0 (state sender) -
                         gas_value - value\<rparr>)) recv 
                    (update_world state sender
                      (state sender
                       \<lparr>account_nonce := nonce,
                          account_balance0 :=
                            account_balance0 (state sender) -
                            gas_value -
                            value\<rparr>)
                      recv
                     \<lparr>account_balance0 :=
                        account_balance0
                         (update_world state sender
                           (state sender
                            \<lparr>account_nonce := nonce,
                               account_balance0 :=
                                 account_balance0 (state sender) -
                                 gas_value -
                                 value\<rparr>)
                           recv) +
                        value\<rparr>)
 \<Longrightarrow> balance_inv st"
apply (simp add: balance_inv_def states_def
  total_balance_update_world)
apply (cases "sender = recv")
apply (simp add: balance_inv_def states_def
  total_balance_update_world update_world_def)
apply (simp add: balance_inv_def states_def
  total_balance_update_world update_world_def)
using uint_stuff [of "value" "account_balance0 (state sender)"
  gas_value "account_balance0 (state recv)"]
 apply force
done

lemma prepare_normal_same :
"g_orig st = update_world state sender
               (state sender
                \<lparr>account_nonce := nonce,
                   account_balance0 :=
                     account_balance0 (state sender) -
                     gas_value \<rparr>) \<Longrightarrow>
 g_stack st = [] \<Longrightarrow>
 g_current st = update_world
                 (update_world state sender
                   (state sender
                    \<lparr>account_nonce := nonce,
                       account_balance0 :=
                         account_balance0 (state sender) -
                         gas_value - value\<rparr>)) sender
                    (update_world state sender
                      (state sender
                       \<lparr>account_nonce := nonce,
                          account_balance0 :=
                            account_balance0 (state sender) -
                            gas_value -
                            value\<rparr>)
                      sender
                     \<lparr>account_balance0 :=
                        account_balance0
                         (update_world state sender
                           (state sender
                            \<lparr>account_nonce := nonce,
                               account_balance0 :=
                                 account_balance0 (state sender) -
                                 gas_value -
                                 value\<rparr>)
                           sender) +
                        value\<rparr>)
 \<Longrightarrow> balance_inv st"
apply (simp add: balance_inv_def states_def
  total_balance_update_world update_world_def)
done

lemma prepare_create_aux2 :
"g_orig st = g_current st \<Longrightarrow>
 g_stack st = [] \<Longrightarrow>
 balance_inv st"
by (simp add: balance_inv_def states_def
  total_balance_update_world)

lemma prepare_balance :
  "start_transaction tr state block = Continue st \<Longrightarrow>
   total_balance state < 2^256 \<Longrightarrow>
   balance_inv st"
apply (simp add:start_transaction_def Let_def
 split:option.split_asm if_split_asm)
apply (rule prepare_create_aux2, auto)
subgoal for recv
apply (cases "tr_from tr \<noteq> recv")
apply (rule prepare_normal_aux, auto)
  using linorder_not_less word_less_nat_alt apply auto[1]
apply (simp add: word_le_nat_alt)
using overflow [of state "tr_value tr" "tr_from tr" recv]
  word_le_nat_alt
apply force
apply (rule prepare_normal_same, auto)
done
done

lemma again2 :
  "uint (sender::w256) \<ge> uint price * uint limit \<Longrightarrow>
   uint (sender - price * limit) =
   uint sender - (uint price * uint limit)"
  by (metis (no_types, hide_lams) int_mod_eq' le_less_trans uint_lt uint_mul_compare uint_mult_ge0 uint_sub uint_word_ariths(3))

(*
lemma again_step1 :
  "unat (sender::w256) \<ge> x + unat price * unat limit \<Longrightarrow>
   unat (sender::w256) \<ge> unat price * unat limit"
*)

lemma again_step2 :
  "a \<ge> 0 \<Longrightarrow> b \<ge> 0 \<Longrightarrow> c \<ge> 0 \<Longrightarrow>
   nat a \<ge> nat b * nat c \<Longrightarrow>
   a \<ge> b * c"
  by (simp add: le_nat_iff)


lemma again_step3 :
  "unat (sender::w256) \<ge> unat (price::w256) * unat (limit::w256) \<Longrightarrow>
   uint sender \<ge> uint price * uint limit"
  by (simp add: unat_def le_nat_iff)

lemma again :
  "unat (sender::w256) \<ge> x + unat price * unat limit \<Longrightarrow>
   uint (sender - price * limit) - uint sender =
    - (uint price * uint limit)"
using again2 again_step3 by force

lemma prepare_total_balance :
  "start_transaction tr state block = Continue st \<Longrightarrow>
   total_balance state < 2^256 \<Longrightarrow>
   total_balance (g_orig st) =
   total_balance state -
   uint (tr_gas_price tr) * uint (tr_gas_limit tr)"
apply (auto simp add:start_transaction_def Let_def
  total_balance_update_world
 split:option.split_asm if_split_asm)
using again [of "unat (tr_value tr)"]
apply force
using again [of "unat (tr_value tr)"]
apply force
done

lemma duh : "unat v + x \<le> unat sender \<Longrightarrow> v \<le> sender"
  by (simp add: word_le_nat_alt)

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g" by auto

lemma add_balance_zero :
  "add_balance state addr 0 = state"
apply (rule funext)
apply (simp add:add_balance_def update_world_def)
done

lemma sub_add_balance :
  "add_balance (sub_balance state addr x) addr x = state"
apply (rule funext)
apply (simp add:sub_balance_def add_balance_def update_world_def Let_def)
done

lemma helper :
"word256FromNatural (nat (uint a) * unat b) = a*b"
  by (simp add: unat_def word256FromNatural_def word_arith_nat_mult word_of_nat)

lemma end_transaction_nothing :
  "end_transaction (nothing_happens state tr) tr block
   = state"
apply (auto simp: nothing_happens_def end_transaction_def Let_def
   kill_accounts.simps helper add_balance_zero )
  by (simp add: mult.commute sub_add_balance)

lemma nothing_happens_other :
 "addr \<noteq> tr_from tr \<Longrightarrow>
  account_balance0 (f_state (nothing_happens state tr) addr) =
  account_balance0 (state addr)"
by (simp add:nothing_happens_def
  sub_balance_def update_world_def Let_def)

lemma simple_transaction_other :
  "start_transaction tr state block = Finished st \<Longrightarrow>
   addr \<noteq> tr_from tr \<Longrightarrow>
   account_balance0 (f_state st addr) =
   account_balance0 (state addr)"
by (auto simp add:start_transaction_def Let_def
  total_balance_update_world nothing_happens_other
  account_balance_nonce update_world_def
 split:option.split_asm if_split_asm)

lemma nothing_happens_sender :
 "account_balance0 (f_state (nothing_happens state tr) (tr_from tr)) =
  account_balance0 (state (tr_from tr)) - tr_gas_price tr * tr_gas_limit tr"
by (simp add:nothing_happens_def
  sub_balance_def update_world_def Let_def)

lemma simple_transaction_sender :
  "start_transaction tr state block = Finished st \<Longrightarrow>
   account_balance0 (f_state st (tr_from tr)) =
   account_balance0 (state (tr_from tr)) -
   tr_gas_price tr * tr_gas_limit tr"
by (auto simp add:start_transaction_def Let_def
  total_balance_update_world nothing_happens_sender
  account_balance_nonce update_world_def
 split:option.split_asm if_split_asm)

lemma simple_transaction_overflow :
  "start_transaction tr state block = Finished st \<Longrightarrow>
   unat (tr_gas_price tr) * unat (tr_gas_limit tr) >
   unat (account_balance0 (state (tr_from tr))) \<Longrightarrow>
   st = nothing_happens state tr"
apply (auto simp add:start_transaction_def Let_def
  total_balance_update_world nothing_happens_sender
  account_balance_nonce update_world_def
 split:option.split_asm if_split_asm)
done

lemma end_transaction_zero_price :
  "tr_gas_price tr = 0 \<Longrightarrow>
   f_killed st = [] \<Longrightarrow>
   end_transaction st tr block = f_state st"
by (auto simp: nothing_happens_def end_transaction_def Let_def
   kill_accounts.simps helper add_balance_zero word256FromNatural_def)

lemma simple_calc :
 "uint a + uint b < 2^256 \<Longrightarrow>
  uint (a + b) - uint (a::w256) = uint b"
  by (simp add: overflow_plus)

lemma calc_aux :
"part \<le> totl \<Longrightarrow>
 uint (sender::w256) + uint part < 2^256 \<Longrightarrow>
 uint cb + uint (totl-part) < 2^256 \<Longrightarrow>
 uint (sender + part) +
    (uint (cb + (totl - part)) -
     uint cb -
     uint sender) =
 uint totl"
  by (simp add: uint_sub overflow_plus)

lemma overflow_le : assumes
  a1: "part \<le> totl" and
  a2: "uint sender + uint totl < 2 ^ 256"
shows "uint sender + uint part < 2 ^ 256"
proof -
  have "uint part \<le> uint totl"
    using a1 by (metis word_le_def)
  then show "uint sender + uint part < 2 ^ 256"
    using a2 by linarith
qed


lemma calc :
"part \<le> totl \<Longrightarrow>
 uint (sender::w256) + uint totl < 2^256 \<Longrightarrow>
 uint cb + uint totl < 2^256 \<Longrightarrow>
 uint (sender + part) +
    (uint (cb + (totl - part)) -
     uint cb -
     uint sender) =
 uint totl"
apply (rule calc_aux)
apply (simp add:overflow_le)
using overflow_le apply force
  using overflow_le word_sub_le by blast

lemma foo :
   "uint (tr_gas_price tr * tr_gas_limit tr) = 
    uint (tr_gas_limit tr * tr_gas_price tr)"
by auto

lemma grugbr_aux1 :
  "0 \<le> gas_left \<Longrightarrow>
   gas_left \<le> uint (limit :: w256) \<Longrightarrow>
   uint limit * uint (price::w256) < 2^256 \<Longrightarrow>
   gas_left * uint price < 2^256"
  by (meson le_less_trans mult_right_mono uint_range_size)

lemma grugbr_aux2 :
  "0 \<le> gas_left \<Longrightarrow>
   gas_left \<le> uint (limit :: w256) \<Longrightarrow>
   uint limit * uint (price::w256) < 2^256 \<Longrightarrow>
   gas_left * uint price \<le> uint (limit * price)"
  by (simp add: mult_right_mono uint_mul_small)

lemma grugbr :
  "0 \<le> gas_left \<Longrightarrow>
   gas_left \<le> uint (limit :: w256) \<Longrightarrow>
   uint limit * uint price < 2^256 \<Longrightarrow>
   word_of_int (gas_left * uint price) \<le> limit * price"
using grugbr_aux1 [of gas_left limit price]
   grugbr_aux2 [of gas_left limit price]
  by (metis (no_types, hide_lams) int_mod_eq' int_word_uint le_less_trans uint_lt uint_mul_compare wi_hom_mult word_of_int_uint)

lemma grugbr2 :
  "0 \<le> gas_left \<Longrightarrow>
   gas_left \<le> uint (limit :: w256) \<Longrightarrow>
   uint limit * uint price < 2^256 \<Longrightarrow>
   word_of_int (gas_left * int (unat price)) \<le> limit * price"
by (metis grugbr uint_mul_small uint_nat)


lemma tb_end_transaction :
"gas_left \<ge> 0 \<Longrightarrow>
 gas_left \<le> uint (tr_gas_limit tr) \<Longrightarrow>
 uint (tr_gas_limit tr) * uint (tr_gas_price tr) < 2^256 \<Longrightarrow>
 uint (account_balance0 (state (tr_from tr))) +
 uint (tr_gas_limit tr * tr_gas_price tr) < 2^256 \<Longrightarrow>
 uint (account_balance0 (state (block_coinbase block))) +
 uint (tr_gas_limit tr * tr_gas_price tr) < 2^256 \<Longrightarrow>
 total_balance (end_transaction
    \<lparr>f_state = state, f_killed = [], f_gas = gas_left, f_refund = 0, f_logs = []\<rparr>
    tr block) =
 total_balance state + (uint (tr_gas_price tr * tr_gas_limit tr))"
apply (simp add: end_transaction_def Let_def kill_accounts.simps
  add_balance_def total_balance_update_world)
apply (auto simp add:update_world_def)
using simple_calc apply force
apply (simp add: foo)
apply (rule calc, auto)
apply (simp add :word256FromNatural_def)
apply (rule grugbr2, auto)
done

lemma txdatacost_nonneg : "txdatacost lst \<ge> 0"
apply (induction lst)
apply (auto simp add:txdatacost.simps)
done

lemma igas_nonneg : "calc_igas tr state block \<ge> 0"
by (auto simp add:calc_igas_def Let_def txdatacost_nonneg
  split:option.split)

lemma aux_1 :
  "unat (tr_gas_limit tr) \<ge> nat \<bar>calc_igas tr state block\<bar> \<Longrightarrow>
   int (unat (tr_gas_limit tr)) -
    calc_igas tr state block
    \<le> uint (tr_gas_limit tr)"
by (auto simp add:igas_nonneg unat_def)

lemma aux_2 :
  "sender \<ge> vl + price * limit \<Longrightarrow>
   sender < 2^256 \<Longrightarrow>
   int limit * int price < 2 ^ 256"
  by (metis add_leE le_less_trans mult.commute numeral_pow of_nat_less_iff of_nat_mult of_nat_numeral)

lemma unat_small : "unat (x::w256) < 2^256"
proof -
  { assume "\<exists>i. \<not> uint x < i \<and> 0 < i \<and> (0::int) \<noteq> numeral (Num.pow (num.Bit0 num.One) (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 num.One)))))))))"
    then have "\<not> uint x \<le> 0 \<and> (0::int) \<noteq> numeral (Num.pow (num.Bit0 num.One) (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 num.One)))))))))"
      by (meson le_less_trans)
    then have "uint x < numeral (Num.pow (num.Bit0 num.One) (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 num.One)))))))))"
      by (metis (no_types) find_mod numeral_pow word_of_int_uint zmod_trival_iff) }
  then show ?thesis
    by (metis (no_types) numeral_pow of_nat_less_iff of_nat_numeral power_not_zero uint_nat zero_less_power zero_not_eq_two zless2)
qed

lemma aux_3 :
  "unat (sender :: w256) \<ge> vl +
   unat (price) * unat (limit) \<Longrightarrow>
   uint (sender - price * limit) + uint (limit*price) < 2^256"
proof -
  assume a1: "vl + unat price * unat limit \<le> unat sender"
  have f2: "\<forall>w. int (unat (w::256 word)) < numeral (Num.pow (num.Bit0 num.One) (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 (num.Bit0 num.One)))))))))"
    by (metis (no_types) less_imp_of_nat_less numeral_pow of_nat_numeral unat_small)
  have "limit * price \<le> sender"
    using a1 by (simp add: semiring_normalization_rules(7) unat_mul_compare)
    then show ?thesis
      using f2 by (metis (no_types) add.commute diff_add_cancel numeral_pow semiring_normalization_rules(7) uint_add uint_nat)
  qed

lemma cool :
 "uint (cb::w256) +
  uint (sender::w256) < 2^256 \<Longrightarrow>
  gas_value \<le> sender \<Longrightarrow>
  uint cb +
  uint (gas_value::w256)
    < 115792089237316195423570985008687907853269984665640564039457584007913129639936"
using Balance.overflow_le by auto

lemma handle_minus :
  "b \<le> a \<Longrightarrow>
   uint a - uint b = uint (a-b)"
  by (simp add: uint_minus_simple_alt)

lemma aux_4 :
 "gas_value \<le> sender \<Longrightarrow>
  uint (sender - gas_value) +
    (uint gas_value - uint sender) = 0"
using handle_minus by force

lemma end_simple_transaction :
  "start_transaction tr state block = Finished st \<Longrightarrow>
   unat (tr_gas_price tr) * unat (tr_gas_limit tr) \<le>
   unat (account_balance0 (state (tr_from tr))) \<Longrightarrow>
   uint (account_balance0 (state (tr_from tr))) +
   uint (account_balance0 (state (block_coinbase block))) < 2^256 \<Longrightarrow>
   total_balance state = total_balance (end_transaction st tr block)"
apply (auto simp add:start_transaction_def Let_def
  total_balance_update_world nothing_happens_sender
  account_balance_nonce update_world_def end_transaction_nothing
 split:option.split_asm if_split_asm)
apply (subst end_transaction_zero_price, auto)
using tb_update_nonce apply force
apply (subst tb_end_transaction)
apply (auto simp add:igas_nonneg)[1]
apply (auto simp add:igas_nonneg unat_def)[1]
apply (subst Word.uint_nat)
apply (subst Word.uint_nat)
apply (rule aux_2[of "unat (tr_value tr)"
 _ _ "unat (account_balance0 (state (tr_from tr)))"], auto)
using unat_small apply force
apply (simp add:account_balance_nonce
  update_world_def)
using aux_3 [of "unat (tr_value tr)"
  "tr_gas_price tr" "tr_gas_limit tr"
  "account_balance0 (state (tr_from tr))"]
apply force
apply (simp add:account_balance_nonce
  update_world_def)
subgoal
apply auto
using aux_3 [of "unat (tr_value tr)"
  "tr_gas_price tr" "tr_gas_limit tr"
  "account_balance0 (state (tr_from tr))"]
apply force
apply (rule cool[of "account_balance0
       (state (block_coinbase block))"
  "account_balance0
       (state (tr_from tr))"
"tr_gas_limit tr * tr_gas_price tr"], auto)
  by (simp add: gas_compare linorder_not_less mult.commute)
apply (simp add:tb_update_nonce
  total_balance_update_world)
apply (rule aux_4)
  using gas_compare linorder_not_less by blast

end

