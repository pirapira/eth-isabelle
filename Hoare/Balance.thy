theory Balance
  imports "EvmFacts" "../lem/Block"
begin

lemma balance_env :
"instruction_sem v c inst =
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
"instruction_sem v c inst =
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

(*

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
   "next0 (Continue st1) = Continue st2 \<Longrightarrow>
    g_orig st1 = g_orig st2"
apply (simp add:next0_def Let_def)
apply (cases "g_vmstate st1"; auto)
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
apply (auto simp add:Let_def)
apply (case_tac "1023 < length (g_stack st1)"; auto)
apply (case_tac "account_balance0
               (g_current st1 (cctx_this (g_cctx st1)))
              < createarg_value x3 \<or>
              1023 < length (g_stack st1)";
       auto simp add:Let_def)
apply(case_tac "g_stack st1"; auto)
apply(case_tac "g_stack st1"; auto simp add:Let_def)
apply(case_tac "list = [] \<and> g_create st1"; auto simp add:Let_def)
apply(case_tac "g_stack st1"; auto simp add:Let_def)
apply(case_tac "b"; auto)
apply(case_tac "x6 = [] \<and> list = [] \<and> g_create st1"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6) \<and>
                homestead_block
                \<le> unat
                    (block_number
                      (vctx_block v))"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6)"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6) \<and>
                homestead_block
                \<le> unat
                    (block_number
                      (vctx_block v))"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6)"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6) \<and>
                homestead_block
                \<le> unat
                    (block_number
                      (vctx_block v))"; auto)
apply(case_tac "vctx_gas v
                < 200 * int (length x6)"; auto)
done
done

lemma inv_depend :
   "balance_inv st1 \<Longrightarrow>
    g_orig st1 = g_orig st2 \<Longrightarrow>
    g_current st1 = g_current st2 \<Longrightarrow>
    g_stack st1 = g_stack st2 \<Longrightarrow>
    balance_inv st2"
apply (simp add: balance_inv_def states_def)
done

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

lemma tr_balance :
   "next0 (Continue st1) = Continue st2 \<Longrightarrow>
    total_balance (g_current st1) < 2^256 \<Longrightarrow>
    balance_inv st1 \<Longrightarrow>
    balance_inv st2"
apply (simp add:next0_def Let_def)
apply (cases "g_vmstate st1"; auto)
using inv_depend apply force
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

lemma tr_balance :
   "next0 (Continue st1) = Continue st2 \<Longrightarrow>
    total_balance (g_current st1) < 2^256 \<Longrightarrow>
    total_balance (g_current st1) \<ge>
    total_balance (g_current st2)"
apply (simp add:next0_def Let_def)
apply (cases "g_vmstate st1"; auto)
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
apply (simp add: total_balance_def abal_def
 update_return_def update_world_def)
apply (simp add:balance_same1)
apply (simp add: total_balance_def
 update_return_def update_world_def abal_def
 balance_same1)
apply (auto simp add:Let_def)
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

apply (simp add: total_balance_def
 update_return_def update_world_def
 update_call_def update_tr_def Let_def)

apply auto
end
