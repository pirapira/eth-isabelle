theory "HoareTripleForMemory" 

imports  "lem/Evm" "Hoare"
 "HoareTripleForInstructions"
 "HoareTripleForStorage"

begin

definition memory :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"memory ind w = memory_range ind (word_rsplit w)"


lemma memory_range_elms_cut_memory2 :
  "length lst = unat in_size \<Longrightarrow> 
   memory_range_elms in_begin lst \<subseteq> variable_ctx_as_set x1 \<Longrightarrow>
   cut_memory in_begin in_size (vctx_memory x1) = lst"
using memory_range_elms_cut_memory by force

lemma word_length : "length (word_rsplit (w::w256) :: 8 word list) = 32"
apply(rule length_word_rsplit_even_size)
apply(auto simp:word_size)
done

lemma word_32 : "unat (32::w256) = 32"
apply auto
done

lemma memory_word_meaning :
  "memory_range_elms memaddr (word_rsplit (table::w256))
          \<subseteq> variable_ctx_as_set v \<Longrightarrow>
   cut_memory memaddr 32 (vctx_memory v) = word_rsplit table"
apply (rule memory_range_elms_cut_memory2)
apply auto
apply (auto simp:word_length)
done

lemma helper :
  assumes a:" cut_memory_aux (addr+1) x mem @
           cut_memory_aux
            ((addr+1) + word_of_int (int x)) y mem =
           cut_memory_aux (addr+1) (x + y) mem"
  shows "cut_memory_aux (addr + 1) x mem @
       cut_memory_aux
        (addr + word_of_int (1 + int x)) y mem =
       cut_memory_aux (addr + 1) (x + y) mem"
proof -
  have a: "addr + word_of_int (1 + int x) =
       (addr+1) + word_of_int (int x)"
    by (metis (no_types, hide_lams) add.assoc of_nat_Suc word_of_nat) 
  show ?thesis by (subst a) (rule assms)
qed

lemma cut_memory_aux_append :
  "cut_memory_aux addr x mem @
   cut_memory_aux (addr+word_of_int (int x)) y mem =
   cut_memory_aux addr (x+y) mem"
apply (induction x arbitrary:addr)
apply(auto simp:cut_memory_aux.simps)
using helper
apply force
done

lemma word_of_nat : "word_of_int (int (unat x)) = x"
  by (metis uint_nat word_of_int_uint)

lemma unat_add_smaller : "unat (x+y) \<le> unat x + unat y"
  by (smt add_diff_cancel_right' le_diff_conv trans_le_add2 un_ui_le unat_sub_if_size)

lemma unat_uint_smaller : "uint x \<le> int (unat x)"
  by (simp add: uint_nat)

lemma int_unat_add :
   "int (unat x) + int (unat y) = int (unat x + unat y)"
  by simp

lemma int_inj : "int x = int y \<Longrightarrow> x = y"
apply auto
done

lemma unat_add_aux :
   assumes a:"unat (x::w256) + unat (y::w256) < 2 ^ 256"
   shows "int (unat x + unat y) =
          uint (word_of_int (int (unat x + unat y))::w256)"
proof -
  have b:"uint (word_of_int (int (unat x + unat y))::w256) =
        int (unat x + unat y) mod 2^256" 
        by (auto simp:uint_word_of_int)
  have "int (unat x + unat y) < 2^256" using a
    by auto
  then show ?thesis using b
    by (simp add: semiring_numeral_div_class.mod_less)
qed

lemma unat_fold : "int (unat x) = uint x"
apply (auto simp:uint_nat)
done

lemma unat_add :
   "unat (x::w256) + unat (y::w256) < 2^256 \<Longrightarrow>
    unat (x+y) = unat x + unat y"
apply (subst word_add_def)
apply (subst uint_nat)
apply (subst uint_nat)
apply (subst int_unat_add)
apply (rule int_inj)
apply (subst unat_fold)
using unat_add_aux by simp

lemma cut_memory_append :
  "unat x + unat y < 2^256 \<Longrightarrow>
   cut_memory addr x mem @ cut_memory (addr+x) y mem =
   cut_memory addr (x+y) mem"
apply (simp add:cut_memory_def)
apply (subst unat_add [of x y])
apply auto
using cut_memory_aux_append [of addr "unat x" mem "unat y"]
and word_of_nat [of x]
apply force
done

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply(auto)
done

lemma word_of_inc : "word_of_int (1 + x) = 1 + word_of_int x"
  by (metis one_word.abs_eq wi_hom_add)

lemma memory_append :
   "memory_range x l1 **
      memory_range (x+(word_of_int (int (length l1))::w256)) l2 =
    memory_range x (l1@l2)"
apply (induction l1 arbitrary:x)
apply auto
apply (subst word_of_inc)
  by (metis (no_types, hide_lams) add.assoc)


lemma sep_memory_range2 :
"      unat (len_word :: w256) = length input \<Longrightarrow>
       (rest ** memory_range begin_word input) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
using sep_memory_range by force

definition tk :: "byte list \<Rightarrow> byte list" where
"tk lst = take (2^255) lst"

definition memory_ran :: "w256 \<Rightarrow> byte list \<Rightarrow> set_pred" where
"memory_ran addr lst = memory_range addr (tk lst)"

lemma sep_memory [simp] :
  "((rest ** memory a w)) s =
   (memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w)))"
apply (subst memory_def)
apply (rule sep_memory_range2)
apply (auto simp:word_length)
apply (rule word_32)
done

lemma unat_word_of_nat :
   "x < 2^256 \<Longrightarrow>
    unat (word_of_int (int x)::w256) = x"
proof -
  assume "x < 2 ^ 256"
  then have "int x = uint (word_of_int (int x)::256 word)"
    by (metis (no_types) less_imp_of_nat_less numeral_pow of_nat_0_le_iff of_nat_numeral semiring_numeral_div_class.mod_less word_of_int_mod)
  then show ?thesis
    by (metis (full_types) nat_int.Rep_eqD uint_nat)
qed

lemma sep_memory_ran [simp] :
  "((rest ** memory_ran a w)) s =
   (memory_range_elms a (tk w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (tk w)))"
apply(subst tk_def)
apply(subst tk_def)
apply (subst memory_ran_def)
apply(subst tk_def)
apply (rule sep_memory_range2)
apply (auto simp:word_length)
apply (rule unat_word_of_nat)
apply (auto)
done

lemma sep_memory2 [simp] :
  "(rest ** memory a w) s ==
   memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w))"
using sep_memory
apply force
done

lemma sep_memory_ran2 [simp] :
  "(rest ** memory_ran a w) s ==
   memory_range_elms a (tk w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (tk w))"
apply auto
done

lemma sep_memory3 [simp] :
  "(memory a w ** rest) s ==
   memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w))"
using sep_memory
apply force
done

lemma sep_memory_ran3 [simp] :
  "(memory_ran a w ** rest) s ==
   memory_range_elms a (tk w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (tk w))"
apply auto
done

lemma sep_memory4 [simp] :
  "((rest1 ** memory a w ** rest) s) =
   (memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   (rest1 ** rest) (s - memory_range_elms a (word_rsplit w)))"
proof -
  have a : "rest1 ** memory a w ** rest = (rest1 ** rest) ** memory a w"
    by auto
  then show ?thesis by
   (subst a) (rule sep_memory)
qed

lemma sep_memory_ran4 [simp] :
  "((rest1 ** memory_ran a w ** rest) s) =
   (memory_range_elms a (tk w) \<subseteq> s \<and>
   (rest1 ** rest) (s - memory_range_elms a (tk w)))"
proof -
  have a : "rest1 ** memory_ran a w ** rest =
     (rest1 ** rest) ** memory_ran a w"
    by auto
  then show ?thesis by
   (subst a) (rule sep_memory_ran)
qed

declare memory_range_elms.simps [simp]


declare meter_gas_def [simp del]

lemma subtract_gas_annotation :
 "subtract_gas x res = InstructionAnnotationFailure \<Longrightarrow>
  res = InstructionAnnotationFailure"
apply(cases res)
apply(auto)
done

lemma mload_inst [simp] :
   "inst_size (Memory MLOAD) = 1"
apply (auto simp:inst_size_def inst_code.simps)
done

lemma get_good_mem_elem_nat_aux :
"(x \<in> memory_range_elms (addr+1)
                 lst \<Longrightarrow>
           \<exists>a. x =
               MemoryElm
                (addr + 1 +
                 word_of_int (int a),
                 lst ! a) \<and>
               a < length lst) \<Longrightarrow>
       x \<in> memory_range_elms (addr + 1)
             lst \<Longrightarrow>
       \<exists>aa. x =
            MemoryElm
             (addr + word_of_int (int aa),
              (a # lst) ! aa) \<and>
            aa < Suc (length lst)"
apply auto
subgoal for aa
apply (rule_tac exI[of _ "aa+1"])
apply auto
  by (simp add: word_of_inc)
done

lemma get_good_mem_elem_nat :
  "x \<in> memory_range_elms addr lst \<Longrightarrow>
   \<exists>a. x = MemoryElm (addr+(word_of_int (int a)::w256), lst!a) \<and>
       a < length lst"
apply (induction lst arbitrary:addr)
apply auto
apply (rule exI[of _ 0])
apply auto
using get_good_mem_elem_nat_aux
apply force
done

lemma get_good_mem_elem :
  assumes a:"x \<in> memory_range_elms addr lst"
    and b:"length lst < 2^256"
  shows "\<exists>a. x = MemoryElm (addr+a, lst!unat a) \<and> unat a < length lst"
proof -
from a have "\<exists>n. x = MemoryElm (addr+(word_of_int (int n)::w256), lst!n)
  \<and> n < length lst"
  using get_good_mem_elem_nat by auto
then obtain n where
   c:"x = MemoryElm (addr+(word_of_int (int n)), lst!n) \<and>
    n < length lst" by auto
then have "n < 2^256" using b by auto
then have "x = MemoryElm (addr + (word_of_int (int n)::w256),
           lst ! unat (word_of_int (int n)::w256)) \<and>
           unat (word_of_int (int n)::w256) < length lst" using b and c
   by (auto simp:unat_word_of_nat)
then show ?thesis by force
qed


lemma memory_not_changed :
  "memory_range_elms memaddr (word_rsplit (w::w256))
       \<subseteq> variable_ctx_as_set x1 \<Longrightarrow>
   xa \<in> memory_range_elms memaddr (word_rsplit (w::w256)) \<Longrightarrow>
   xa \<in> contexts_as_set
           (x1\<lparr>vctx_pc := new_pc,
                 vctx_stack := new_stack,
                 vctx_memory_usage := memu\<rparr>)
           co_ctx"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma read_split :
  "read_word_from_bytes 0 (word_rsplit w) = w"
by (auto simp:byte_list_fill_right_def word_length
         read_word_from_bytes_def word_rcat_rsplit)

lemma memory_works :
 assumes a:"memory_range_elms memaddr (word_rsplit (w::w256))
       \<subseteq> variable_ctx_as_set x1"
 shows "read_word_from_bytes 0
        (cut_memory memaddr 32 (vctx_memory x1)) = w"
proof -
   have "length (word_rsplit (w::w256):: byte list) = 32"
     by (auto simp:word_length)
   then have "cut_memory memaddr 32 (vctx_memory x1) =
              word_rsplit w"
     using a memory_range_elms_cut_memory
     by force
   then show ?thesis by (auto simp:read_split)
qed

lemma set_dir1 :
  "vctx_stack x1 = memaddr # t \<Longrightarrow>
   x \<noteq> StackHeightElm (Suc (length t)) \<Longrightarrow>
   x \<noteq> CodeElm (vctx_pc x1, Memory MLOAD) \<Longrightarrow>
       x \<notin> memory_range_elms memaddr
             (word_rsplit v) \<Longrightarrow>
       x \<noteq> StackElm (length t, memaddr) \<Longrightarrow>
       x \<noteq> PcElm (vctx_pc x1) \<Longrightarrow>
       x \<in> contexts_as_set x1 co_ctx \<Longrightarrow>
       x \<noteq>
       MemoryUsageElm
        (vctx_memory_usage x1) \<Longrightarrow>
       x \<noteq> GasElm (vctx_gas x1) \<Longrightarrow>
       x \<noteq> GasElm newgas \<Longrightarrow>
       x \<noteq> ContinuingElm True \<Longrightarrow>
       x \<in> contexts_as_set
             (x1\<lparr>vctx_pc := vctx_pc x1 + 1,
                   vctx_stack := nstack # t,
                   vctx_memory_usage := memu\<rparr>)
             co_ctx"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma set_dir2 :
  "vctx_stack x1 = memaddr # t \<Longrightarrow>
   memu = memu2 \<Longrightarrow>
   newpc = newpc2 \<Longrightarrow>
   nstack = nstack2 \<Longrightarrow>
   x \<noteq> GasElm newgas  \<Longrightarrow>
   x \<noteq> MemoryUsageElm memu \<Longrightarrow>
       x \<noteq>
       CodeElm
        (vctx_pc x1, Memory MLOAD) \<Longrightarrow>
       x \<noteq> PcElm newpc2 \<Longrightarrow>
       x \<noteq>
       StackHeightElm (Suc (length t)) \<Longrightarrow>
       x \<notin> memory_range_elms memaddr
             (word_rsplit v) \<Longrightarrow>
       x \<noteq> StackElm (length t, nstack2) \<Longrightarrow>
       x \<in> contexts_as_set
             (x1\<lparr>vctx_pc := newpc,
                   vctx_stack :=
                     nstack #
                     t,
                   vctx_memory_usage :=
                     memu2\<rparr>)
             co_ctx \<Longrightarrow>
       x \<noteq> ContinuingElm True \<Longrightarrow>
       x \<noteq> GasElm (vctx_gas x1) \<Longrightarrow>
       x \<in> contexts_as_set x1 co_ctx"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma mload_gas_triple :
  "triple {OutOfGas}
     (\<langle> h \<le> 1023 \<rangle> **
       stack h memaddr **
       stack_height (h+1) **
       program_counter k **   
       memory_usage memu **
       memory memaddr v **
       gas_pred g **
       continuing)
     {(k, Memory MLOAD)}
    (stack_height (h + 1) **
     stack h v **
     memory memaddr v **
     memory_usage (M memu memaddr 32) **
     program_counter (k + 1) **
     gas_pred (g - Gverylow + Cmem memu -
               Cmem (M memu memaddr 32)) **
     continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
(* apply(case_tac presult) *)
apply(case_tac presult;
   auto simp add: meter_gas_def mload_def
        memory_inst_numbers.simps    
        instruction_result_as_set_def vctx_advance_pc_def
        memory_not_changed memory_works)
apply (rule leibniz)
apply blast
apply auto
apply (rule set_dir1)
apply auto
apply (rule set_dir2)
apply auto
done

lemma sha_annotation :
  "sha3 v c = InstructionAnnotationFailure \<Longrightarrow> False"
apply (auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(simp)
apply auto
apply (case_tac "\<not> cctx_hash_filter c (cut_memory a aa (vctx_memory v))")
apply auto
done

lemma subtract_gas_environment :
   "subtract_gas x res =
     InstructionToEnvironment act v opt \<Longrightarrow>
    res = InstructionToEnvironment act
      (v\<lparr> vctx_gas := vctx_gas v + x \<rparr>) opt"
apply(cases res)
apply(auto)
done

lemma sha_env :
  "length (vctx_stack v) \<ge> 2 \<Longrightarrow>
   sha3 v c = InstructionToEnvironment act nv opt \<Longrightarrow>
   act = ContractFail [OutOfGas]"
apply (auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(simp)
apply auto
apply (case_tac "\<not> cctx_hash_filter c (cut_memory a aa (vctx_memory v))")
apply auto
done

lemma sha_fail_helper :
  assumes a:"subtract_gas x (sha3 v c) =
       InstructionToEnvironment act nv opt"
  and   b:"length (vctx_stack v) \<ge> 2"
  shows "failed_for_reasons {OutOfGas}
        (InstructionToEnvironment act nv opt)"
proof -
  have "act = ContractFail [OutOfGas]" using 
    subtract_gas_environment and sha_env and a
    and b  by fastforce
  then show ?thesis by auto
qed

lemma subtract_gas_continue :
   "subtract_gas x res = InstructionContinue v \<Longrightarrow>
    res = InstructionContinue
      (v\<lparr> vctx_gas := vctx_gas v + x \<rparr>)"
apply(cases res)
apply(auto)
done

lemma sha_continue :
  "sha3 v c = InstructionContinue nv \<Longrightarrow>
   nv = vctx_advance_pc c v\<lparr>
      vctx_stack :=
        keccak (cut_memory (hd (vctx_stack v))
            (hd (tl (vctx_stack v))) (vctx_memory v)) #
        tl (tl (vctx_stack v)),
      vctx_memory_usage :=
        M (vctx_memory_usage v) (hd (vctx_stack v))
          (hd (tl (vctx_stack v)))  \<rparr>"
apply (auto simp:sha3_def)
apply(cases "vctx_stack v")
apply(simp)
apply(cases "tl (vctx_stack v)")
apply(simp)
apply(simp)
apply auto
apply (case_tac "\<not> cctx_hash_filter c (cut_memory a aa (vctx_memory v))")
apply (auto)
done

lemma sha_continue_helper :
  "subtract_gas x (sha3 v c) = InstructionContinue nv \<Longrightarrow>
   nv = vctx_advance_pc c v\<lparr>
      vctx_gas := vctx_gas v - x,
      vctx_stack :=
        keccak (cut_memory (hd (vctx_stack v))
            (hd (tl (vctx_stack v))) (vctx_memory v)) #
        tl (tl (vctx_stack v)),
      vctx_memory_usage :=
        M (vctx_memory_usage v) (hd (vctx_stack v))
          (hd (tl (vctx_stack v)))  \<rparr>"
apply (cases "sha3 v c")
apply(auto)
using sha_continue
apply force
done

lemma rsplit_length :
 "32 = (word_of_int
     (int (length (word_rsplit (w::w256)::byte list)))::w256)"
  using word_length by auto


lemma hash_memory_split :
  "memory addr table ** memory (addr+32) key =
   memory_range addr (word_rsplit table @ word_rsplit key)"
apply (simp add:memory_def)
apply (subst rsplit_length)
using memory_append [of addr "word_rsplit table"
                        "word_rsplit key"]
apply auto
done

lemma simp_len [simp] :
   "length ((word_rsplit (table::w256) :: byte list) @
            (word_rsplit (key::w256) :: byte list)) = 64"
apply (auto simp:word_length)
done

lemma tk_simp [simp] :
   "tk (word_rsplit table @ word_rsplit key) =
   word_rsplit (table::w256) @ word_rsplit (key::w256)"
apply (auto simp:tk_def word_length)
done

lemma magic_hash_property :
  "no_assertion c \<Longrightarrow>
   vctx_stack v = addr # 64 # blah \<Longrightarrow>
   cut_memory addr 64 (vctx_memory v) =
      word_rsplit table @ word_rsplit key \<Longrightarrow>
   sha3 v c = InstructionContinue nv \<Longrightarrow>
   hash2 table key = 0 \<Longrightarrow> False"
apply(auto simp:sha3_def)
apply (case_tac "\<not> cctx_hash_filter c
    (word_rsplit table @ word_rsplit key)")
apply(auto simp:no_assertion_def magic_filter_def)
done

lemma cut_memory_works :
  assumes a:"memory_range_elms addr
           (word_rsplit table @ word_rsplit key)
          \<subseteq> variable_ctx_as_set v"
  shows "cut_memory addr 64 (vctx_memory v) =
    word_rsplit (table::w256) @ word_rsplit (key::w256)"
proof -
   have "length (word_rsplit (table::w256) @ word_rsplit (key::w256) :: byte list) = 64"
     by (auto simp:word_length)
   then show ?thesis
     using a memory_range_elms_cut_memory
     by force
qed

lemma many_such_cases :
 "contexts_as_set
           (v\<lparr>vctx_pc := pca, vctx_gas := gasa,
                 vctx_stack := stacka,
                 vctx_memory_usage := memu \<rparr>) c =
  (contexts_as_set v c -
     stack_as_set (vctx_stack v) -
     {PcElm (vctx_pc v),
      GasElm (vctx_gas v),
      MemoryUsageElm (vctx_memory_usage v)})
  \<union> {PcElm pca,
      GasElm gasa,
      MemoryUsageElm memu} \<union> stack_as_set stacka"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma sort_out_sets_again :
 "vctx_stack x1 = memaddr # 64 # ta \<Longrightarrow>
  stack_new = stack_new2 \<Longrightarrow>
  memu = memu2 \<Longrightarrow>
  newgas = newgas2 \<Longrightarrow>
 vctx_stack x1 = memaddr # 64 # ta \<Longrightarrow>
          contexts_as_set x1 co_ctx -
          {GasElm (vctx_gas x1)} -
          {MemoryUsageElm
            (vctx_memory_usage x1)} -
          {PcElm (vctx_pc x1)} -
          {StackElm (Suc (length ta), memaddr)} -
          {StackHeightElm
            (Suc (Suc (length ta)))} -
          {CodeElm (vctx_pc x1, Arith SHA3)} -
          memory_range_elms memaddr
           memstuff -
          {StackElm (length ta, 64)} =
          insert (PcElm (vctx_pc x1 + 1))
           (insert
             (GasElm  newgas)
             (insert
               (MemoryUsageElm
                 memu)
               (contexts_as_set x1 co_ctx -
                stack_as_set (memaddr # 64 # ta) -
                {PcElm (vctx_pc x1),
                 GasElm (vctx_gas x1),
                 MemoryUsageElm
                  (vctx_memory_usage x1)} \<union>
                stack_as_set
                 (stack_new #
                  ta)))) -
          {StackHeightElm (Suc (length ta))} -
          {PcElm (vctx_pc x1 + 1)} -
          {StackElm
            (length ta, stack_new2)} -
          {CodeElm (vctx_pc x1, Arith SHA3)} -
          memory_range_elms memaddr memstuff -
          {MemoryUsageElm
            memu2} -
          {GasElm newgas2}"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
  using le_less_Suc_eq by force

(*** need hoare triple for sha  *)
lemma hash2_gas_triple :
  "triple {OutOfGas}
     (\<langle> h \<le> 1022 \<rangle> **
       stack (h+1) memaddr **
       stack h 64 **
       stack_height (h+2) **
       program_counter k **   
       memory_usage memu **
(* memory memaddr table ** memory (memaddr+32) key ** *)
       memory_ran memaddr
        (word_rsplit table @ word_rsplit key) **
       gas_pred g **
       continuing)
     {(k, Arith SHA3)}
    (\<langle> hash2 table key \<noteq> 0 \<rangle> **
     stack_height (h + 1) **
     stack h (hash2 table key) **
     memory_ran memaddr (word_rsplit table @ word_rsplit key) **
     memory_usage (M memu memaddr 64) **
     program_counter (k + 1) **
     gas_pred (g - Gsha3 - Gsha3word * 2 + Cmem memu -
               Cmem (M memu memaddr 64)) **
     continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult)
defer
apply simp
apply simp
apply simp
apply(case_tac
"subtract_gas
          (meter_gas (Arith SHA3) x1 co_ctx)
          (sha3 x1 co_ctx)")
defer
apply simp
using subtract_gas_annotation sha_annotation
apply fastforce
apply simp
using sha_fail_helper apply simp
apply simp
subgoal for co_ctx presult rest x1 x1a
using sha_continue_helper
   [of "(meter_gas (Arith SHA3) x1 co_ctx)"
       x1 co_ctx x1a]
apply simp
apply(auto simp add: instruction_result_as_set_def)



apply (simp add:cut_memory_works)
apply (rule sym)
apply (rule hash_compat)
apply auto
apply (rule_tac
 magic_hash_property [of co_ctx x1 memaddr _ table key])
apply auto
using cut_memory_works
apply force
using subtract_gas_continue
apply force
apply (rule_tac
 magic_hash_property [of co_ctx x1 memaddr _ table key])
apply auto
using cut_memory_works
apply force
using subtract_gas_continue
apply force
apply (simp add:meter_gas_def)
apply(rule leibniz)

 apply blast
apply (simp add:vctx_advance_pc_def many_such_cases)
apply (simp add:meter_gas_def)

apply (rule sort_out_sets_again)

apply auto



apply (simp add:cut_memory_works)
apply (rule sym)
apply (rule hash_compat)
apply auto
apply (rule_tac
 magic_hash_property [of co_ctx x1 memaddr _ table key])
apply auto
using cut_memory_works
apply force
using subtract_gas_continue
apply force
done
done


(* nothing will work properly because everything is mod 2^256 *)

lemma store_get [simp] :
"unat a < length lst \<Longrightarrow>
 store_byte_list_memory addr lst mem (addr+a) = lst!unat a"
apply (auto simp:store_byte_list_memory_def)
done


lemma memory_contra :
assumes a:"x \<in> memory_range_elms addr (word_rsplit (w::w256))"
and b:"\<forall>a. x \<noteq>
        MemoryElm
         (a, store_byte_list_memory addr (word_rsplit w) mem a)"
shows "False"
proof -
from a have "\<exists>a. x = MemoryElm (addr+a, (word_rsplit w)!unat a) \<and>
                 unat a < 32"
using get_good_mem_elem and word_length by force
then obtain a where
   aa:"x = MemoryElm (addr+a, (word_rsplit w)!unat a) \<and> unat a < 32" by auto
then have "x = MemoryElm (addr+a,
     store_byte_list_memory addr (word_rsplit w) mem (addr+a))"
  using store_get and word_length by force
then show False using b by force
qed

lemma memory_was_changed :
       "x \<in> memory_range_elms memaddr
             (word_rsplit w) \<Longrightarrow>
       x \<in> contexts_as_set
             (x1\<lparr>vctx_pc := vctx_pc x1 + 1,
                   vctx_stack := ta,
                   vctx_memory :=
                     store_word_memory memaddr w (vctx_memory x1),
                   vctx_memory_usage := memu\<rparr>)
             co_ctx"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def store_word_memory_def)
using memory_contra [of x memaddr w "vctx_memory x1"]
 by auto



lemma mstore_inst [simp] :
   "inst_size (Memory MSTORE) = 1"
apply (auto simp:inst_size_def inst_code.simps)
done


declare memory_as_set_def [simp del]

lemma memory_range_at_memory_set [simp]:
   "memory_range_elms memaddr lst
       \<subseteq> variable_ctx_as_set v \<Longrightarrow>
   memory_range_elms memaddr lst \<subseteq> memory_as_set (vctx_memory v)"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma memory_at_set [simp]:
   "memory_range_elms memaddr lst \<subseteq> memory_as_set (vctx_memory v)
    \<Longrightarrow> memory_range_elms memaddr lst
       \<subseteq> variable_ctx_as_set v"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done



definition range_elms :: "w256 \<Rightarrow> byte list \<Rightarrow> state_element set" where
"range_elms addr lst =
   {MemoryElm (addr+word_of_int (int i),lst!i)| i. i < length lst}"

(* defining eq for memory_range_elms *)
lemma range_elems_aux :
  "range_elms begin (a # lst) =
   {MemoryElm (begin, a)} \<union> range_elms (begin + 1) lst"
apply (auto simp add:range_elms_def)
  using less_Suc_eq_0_disj word_of_inc apply fastforce
  apply (metis (no_types, hide_lams) Word.word_of_nat less_Suc_eq_0_disj nth_Cons' nth_Cons_Suc of_nat_Suc)
apply (rule exI[of _ 0])
apply simp
  by (metis (no_types, hide_lams) Suc_less_eq2 Word.word_of_nat nth_Cons_Suc of_nat_Suc)


lemma range_elms_eq :
   "memory_range_elms addr lst = range_elms addr lst"
apply (induction lst arbitrary:addr)
apply (simp add:range_elms_def)
apply (auto simp: range_elems_aux)
done

lemma extract_memory_range :
  "MemoryElm (a, v) \<in> range_elms addr lst \<Longrightarrow>
   \<exists>i. addr+word_of_int (int i) = a \<and> i < length lst"
apply (auto simp: range_elms_def)
done

lemma extract_memory_range2 :
  "MemoryElm (a, v) \<in> range_elms addr lst \<Longrightarrow>
   \<exists>i. addr+i = a \<and> unat i < length lst"
apply (auto simp: range_elms_def)
by (metis (no_types, hide_lams) Word.word_of_nat le_unat_uoi less_trans not_less)

lemma extract_memory_range3 :
  "(\<exists>i. (addr::w256)+i = (a::w256) \<and> unat i < length lst) \<Longrightarrow>
   unat (a-addr) < length lst"
apply auto
done

lemma extract_memory_range4 :
  "MemoryElm (a, v) \<notin> range_elms addr lst \<Longrightarrow>
   length lst \<ge> 2^256 \<or> lst ! unat (a-addr) \<noteq> v \<or>
   (unat (a-addr) \<ge> length lst)"
apply (auto simp: range_elms_def)
  by (simp add: word_of_nat not_less)

lemma cut_index_one :
  "mem addr = cut_memory addr 1 mem ! 0"
apply (auto simp:cut_memory_def cut_memory_aux.simps)
done

lemma unat_minus :
 "unat (i::w256) \<le> n \<Longrightarrow>
  n < 2^256 \<Longrightarrow>
  unat i + unat ((word_of_int (int n)::w256) - i) = n"
  by (simp add: unat_sub_if' unat_word_of_nat)

lemma unat_minus_one :
 "unat (i::w256) < n \<Longrightarrow>
  n < 2^256 \<Longrightarrow>
  unat (i+1) +
  unat ((word_of_int (int n)::w256) - (i + 1)) = n"
apply (rule unat_minus)
  apply (metis Suc_eq_plus1 add_strict_right_mono less_Suc_eq_le unatSuc unat_0 w256_add_com zero_le)
apply auto
done

lemma unat_inc :
  "unat (i::w256) < n \<Longrightarrow>
   n < 2^256 \<Longrightarrow>
   unat (i+1) = unat i + unat (1::w256)"
apply (rule unat_add)
  by auto

lemma word_minus_plus :
   "(w::w256) - (i::w256) - (1::w256) = (w - (i + (1::w256)))"
apply auto
done

lemma unat_minus_one2 :
assumes  a:"unat (i::w256) < n"
and b:  "n < 2^256"
shows "unat (1::w256) +
  unat ((word_of_int (int n)::w256) - i - (1::w256)) =
   n - unat i"
proof -

have "unat (i+1) +
  unat ((word_of_int (int n)::w256) - (i + 1)) = n"
using unat_minus_one and unat_inc and a and b by force
have "unat i + unat (1::w256) +
  unat ((word_of_int (int n)::w256) - (i + (1::w256))) = n"
using unat_minus_one and unat_inc and a and b by force
then have "unat i + unat (1::w256) +
  unat ((word_of_int (int n)::w256) - i - (1::w256)) = n"
apply (subst word_minus_plus)
apply auto
done
then show ?thesis by auto
qed

lemma cut_aux_length :
   "length (cut_memory_aux addr i mem) = i"
apply (induction i arbitrary:addr mem)
apply (auto simp:cut_memory_aux.simps)
done

lemma cut_length [simp] : 
   "length (cut_memory addr i mem) = unat i"
apply (simp add:cut_memory_def cut_aux_length)
done

lemma unat_index [simp] :
   "length l1 = unat (i::w256) \<Longrightarrow>
    (l1@l2)!unat i = l2!0"
  by (simp add: nth_append)

lemma cut_index :
  assumes a:"unat (i::w256) < length lst"
  and   b:"length lst < 2^256"
  shows "mem (addr+i) =
         cut_memory addr (word_of_int (int (length lst)))
                    mem ! unat i"
proof -
  have
   "cut_memory addr i mem @
    cut_memory (addr+i)
           ((word_of_int (int (length lst))::w256)-i) mem =
    cut_memory addr (i
    + ((word_of_int (int (length lst))::w256)-i)) mem"
using a and b and unat_minus and cut_memory_append by force
then have s1:
   "cut_memory addr i mem @
    cut_memory (addr+i)
           ((word_of_int (int (length lst))::w256)-i) mem =
    cut_memory addr (word_of_int (int (length lst))::w256) mem"
using a and b and unat_minus and cut_memory_append by force
have
 "cut_memory (addr+i) (1::w256) mem @
  cut_memory ((addr+i)+(1::w256))
           (((word_of_int (int (length lst))::w256)-i)-(1::w256)) mem
= cut_memory (addr+i)
           ((1::w256)+(((word_of_int (int (length lst))::w256)-i)-(1::w256))) mem"
apply (rule cut_memory_append)
using a and b
and unat_minus_one2 [of i "length lst" ]
apply simp
done
then have s2:
 "cut_memory (addr+i) (1::w256) mem @
  cut_memory ((addr+i)+(1::w256))
           (((word_of_int (int (length lst))::w256)-i)-(1::w256)) mem
= cut_memory (addr+i)
           ((word_of_int (int (length lst))::w256)-i) mem"
by auto
from s1 and s2 have
"cut_memory addr (word_of_int (int (length lst))::w256) mem
= cut_memory addr i mem @
 cut_memory (addr+i) (1::w256) mem @
 cut_memory ((addr+i)+(1::w256))
           (((word_of_int (int (length lst))::w256)-i)-(1::w256)) mem
"
by auto
then show ?thesis
apply auto
apply (simp add: nth_append   cut_index_one)
done
qed
(*
using a and b and unat_minus and cut_memory_append by force
*)

lemma stuff_aux :
"cut_memory memaddr 32 (vctx_memory x1) =
  word_rsplit (old_v::w256) \<Longrightarrow>
 ( a = memaddr + word_of_int (int (unat (a-memaddr))) \<and>
        vctx_memory x1 a =
          (word_rsplit (old_v::w256)::byte list) ! (unat (a-memaddr)) \<longrightarrow>
        \<not> (unat (a-memaddr)) <
         length ((word_rsplit old_v)::byte list) ) \<Longrightarrow>
    vctx_memory x1 a \<noteq>
    (word_rsplit (v::w256) :: byte list) ! unat (a - memaddr) \<Longrightarrow>
    x = MemoryElm (a, vctx_memory x1 a) \<Longrightarrow>
    unat (a - memaddr) < 32 \<Longrightarrow> False"

apply (auto simp:word_length)
  apply (simp add: word_of_nat)
using cut_index [of "a - memaddr" "(word_rsplit v::byte list)" 
                   "vctx_memory x1" memaddr]
and word_length
apply auto
done

declare memory_range_at_memory_set [simp del]

lemma cut_stuff2 :
"length lst = 32 \<Longrightarrow>
  memory_range_elms memaddr lst \<subseteq>
   variable_ctx_as_set x1 \<Longrightarrow>
  cut_memory memaddr 32 (vctx_memory x1) = lst"
using memory_range_elms_cut_memory 
apply auto
done

lemma cut_stuff :
"length lst = 32 \<Longrightarrow>
  memory_range_elms memaddr lst \<subseteq>
   memory_as_set (vctx_memory (x1::variable_ctx)) \<Longrightarrow>
  cut_memory memaddr 32 (vctx_memory x1) = lst"
using memory_at_set [of memaddr lst x1]
apply auto
done

lemma stuff :
"cut_memory memaddr 32 (vctx_memory x1) =
  word_rsplit (old_v::w256) \<Longrightarrow>
 x \<notin> memory_range_elms memaddr (word_rsplit old_v) \<Longrightarrow>
 x \<notin> memory_as_set
      (store_word_memory memaddr v (vctx_memory x1)) \<Longrightarrow>
 x \<in> memory_as_set (vctx_memory x1) \<Longrightarrow>
 False"
apply (simp add:range_elms_eq)
apply (auto simp:memory_as_set_def range_elms_def
  store_word_memory_def  store_byte_list_memory_def)
subgoal for a
apply (cases "unat (a-memaddr) < 32")
apply (auto simp:word_length)
using stuff_aux
apply force
done
done

declare word_length [simp add]
declare unat_word_of_nat [simp add]

(*
lemma memory_lookup :
  "MemoryElm (i,x) \<in> memory_as_set (vctx_memory x1) \<Longrightarrow>
   x = vctx_memory x1 i"
*)

lemma work_on_it2 :
"cut_memory memaddr 32 (vctx_memory x1) =
     (word_rsplit (old_v::w256))  \<Longrightarrow>
    x \<notin> memory_range_elms memaddr
          (word_rsplit old_v) \<Longrightarrow>
    x \<in> memory_range_elms memaddr
          (word_rsplit (new_v::w256)) \<Longrightarrow>
    x \<in> memory_as_set (vctx_memory x1) \<Longrightarrow>
    False"
apply (auto simp:range_elms_eq range_elms_def memory_as_set_def)
subgoal for i
using cut_index [of "word_of_int (int i)"
     "(word_rsplit old_v::byte list)" 
                   "vctx_memory x1" memaddr]
apply auto
done
done


declare word_of_nat [simp add]


lemma work_on_it :
"memory_range_elms memaddr
     (word_rsplit (old_v::w256))
    \<subseteq> memory_as_set (vctx_memory x1) \<Longrightarrow>
    x \<notin> memory_range_elms memaddr
          (word_rsplit old_v) \<Longrightarrow>
    x \<in> memory_range_elms memaddr
          (word_rsplit (new_v::w256)) \<Longrightarrow>
    x \<in> memory_as_set (vctx_memory (x1::variable_ctx)) \<Longrightarrow>
    False"
apply (rule work_on_it2[of memaddr x1 old_v])
apply auto
done

lemma one_more_obstacle :
" memory_range_elms memaddr
          (word_rsplit (old_v::w256))
         \<subseteq> memory_as_set (vctx_memory (x1::variable_ctx)) \<Longrightarrow>
  x \<notin> memory_range_elms memaddr (word_rsplit (v::w256)) \<Longrightarrow>
 x \<in> memory_range_elms memaddr
               (word_rsplit old_v) \<Longrightarrow>
         x \<in> memory_as_set
               (store_word_memory memaddr v
                 (vctx_memory x1)) \<Longrightarrow>
         False"
apply (auto simp:range_elms_eq range_elms_def memory_as_set_def
store_word_memory_def)
done


lemma stuff2 :
"memory_range_elms memaddr (word_rsplit (old_v::w256)) \<subseteq>
   memory_as_set (vctx_memory (x1::variable_ctx)) \<Longrightarrow>
 x \<notin> memory_range_elms memaddr (word_rsplit (old_v::w256)) \<Longrightarrow>
 x \<notin> memory_as_set
      (store_word_memory memaddr v (vctx_memory x1)) \<Longrightarrow>
 x \<in> memory_as_set (vctx_memory x1) \<Longrightarrow>
 False"
apply (rule stuff[of memaddr x1 old_v])
apply auto
done

lemma still_left2 :
  "cut_memory memaddr 32 (vctx_memory x1) =
     (word_rsplit (old_v::w256)) \<Longrightarrow>
   x \<notin> memory_range_elms memaddr
               (word_rsplit (v::w256)) \<Longrightarrow>
  x \<notin> memory_as_set
               (vctx_memory x1) \<Longrightarrow>   
  x \<in> memory_as_set
               (store_word_memory memaddr v
                 (vctx_memory x1)) \<Longrightarrow>
  False"
apply (simp add:range_elms_eq)
apply (auto simp:memory_as_set_def range_elms_def
  store_word_memory_def  store_byte_list_memory_def)
subgoal for a
apply (cases "unat (a-memaddr) < 32")
apply auto
done
done

lemma still_left :
  "memory_range_elms memaddr
          (word_rsplit (old_v::w256))
         \<subseteq> memory_as_set (vctx_memory x1) \<Longrightarrow>
   x \<notin> memory_range_elms memaddr
               (word_rsplit (v::w256)) \<Longrightarrow>
  x \<notin> memory_as_set
               (vctx_memory x1) \<Longrightarrow>   
  x \<in> memory_as_set
               (store_word_memory memaddr v
                 (vctx_memory (x1::variable_ctx))) \<Longrightarrow>
  False"
apply (rule still_left2 [of memaddr x1 old_v])
apply (auto)
done

lemma range_not_in_constant [simp] :
 "x \<in> memory_range_elms memaddr lst \<Longrightarrow>
    x \<in> constant_ctx_as_set co_ctx \<Longrightarrow> False"
apply (induction lst arbitrary:memaddr)
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma other_similar :
"memory_range_elms memaddr
          (word_rsplit (old_v::w256))
         \<subseteq> memory_as_set (vctx_memory x1) \<Longrightarrow>
         x \<notin> memory_range_elms memaddr
               (word_rsplit old_v) \<Longrightarrow>
         x \<in> contexts_as_set x1 co_ctx \<Longrightarrow>
         x \<in> memory_range_elms memaddr
               (word_rsplit (v::w256)) \<Longrightarrow>
         False"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
apply (rule range_not_in_constant[of x memaddr _ co_ctx])
apply auto
apply (rule work_on_it)
apply auto
done




lemma plz_sort_it_out :
 "vctx_stack x1 = memaddr # v # ta \<Longrightarrow>
  memu = memu2 \<Longrightarrow>
  newmem = store_word_memory memaddr v (vctx_memory x1) \<Longrightarrow>
  newgas = newgas2 \<Longrightarrow>
  new_pc = new_pc2 \<Longrightarrow>
(*
  memory_range_elms memaddr
        (word_rsplit old_v)
       \<subseteq> variable_ctx_as_set x1 \<Longrightarrow>
*)
  memory_range_elms memaddr
        (word_rsplit old_v)
       \<subseteq> memory_as_set (vctx_memory x1) \<Longrightarrow>
  contexts_as_set x1 co_ctx -
       {GasElm (vctx_gas x1)} -
       {MemoryUsageElm (vctx_memory_usage x1)} -
       {PcElm (vctx_pc x1)} -
       {StackElm (length ta, v)} -
       memory_range_elms memaddr
        (word_rsplit (old_v::w256)) -
       {StackElm
         (Suc (length ta), memaddr)} -
       {CodeElm
         (vctx_pc x1, Memory MSTORE)} -
       {StackHeightElm
         (Suc (Suc (length ta)))} =
       insert
        (GasElm
          newgas2)
        (insert (ContinuingElm True)
          (contexts_as_set
            (x1\<lparr>vctx_pc := new_pc2,
                  vctx_stack := ta,
                  vctx_memory :=
                    newmem,
                  vctx_memory_usage :=
                    memu2\<rparr>)
            co_ctx -
           {GasElm (vctx_gas x1)})) -
       {ContinuingElm True} -
       {StackHeightElm (length ta)} -
       memory_range_elms memaddr (word_rsplit (v::w256)) -
       {PcElm new_pc} -
       {CodeElm
         (vctx_pc x1, Memory MSTORE)} -
       {MemoryUsageElm memu} -
       {GasElm newgas}"
apply (auto)
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)[1]
using le_less_Suc_eq apply fastforce
(*
using le_less_Suc_eq apply fastforce
subgoal for idx
proof -
  fix idx :: nat
  assume a1: "idx < Suc (Suc (length ta))"
  assume a2: "[v, memaddr] ! (idx - length ta) \<noteq> memaddr"
  assume "\<not> idx < length ta"
  then have f3: "\<forall>w. [w] ! (idx - length ta - 1) = (rev ta @ [[w] ! (idx - length ta - 1), w]) ! idx"
    by (metis over_one_rev')
  { assume "\<exists>w. [w::256 word] ! (idx - length ta - 1) \<noteq> w"
    then have "idx \<le> length ta"
      using f3 a1 by (metis (no_types) not_less_eq over_two_rev)
    then have "[v, memaddr] ! (idx - length ta) = v"
      by simp }
  then show "[v, memaddr] ! (idx - length ta) = v"
    using a2 by (metis (no_types) nth_non_equal_first_eq)
next
qed
*)
using stuff2 [of memaddr old_v x1 _ v]
apply force
using other_similar [of memaddr old_v x1 _ co_ctx v]
apply force
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)[1]
using still_left [of memaddr old_v x1 _ v]
apply force
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)[1]
apply (rule range_not_in_constant[of _ memaddr _ co_ctx])
apply auto
apply (auto simp:range_elms_eq range_elms_def memory_as_set_def
store_word_memory_def)
done

lemma memory_range_fact :
"memory_range_elms memaddr
        (word_rsplit old_v)
       \<subseteq> variable_ctx_as_set x1 \<Longrightarrow>
 x \<in> memory_range_elms memaddr
             (word_rsplit old_v) \<Longrightarrow>
 x \<in> memory_as_set (vctx_memory x1)"
apply(auto simp add: contexts_as_set_def variable_ctx_as_set_def stack_as_set_def ext_program_as_set_def
       balance_as_set_def)
done

lemma mstore_gas_triple :
  "triple {OutOfGas}
     (\<langle> h \<le> 1022 \<rangle> **
       stack (h+1) memaddr **
       stack h v **
       stack_height (h+2) **
       program_counter k **   
       memory_usage memu **
       memory memaddr old_v **
       gas_pred g **
       continuing)
     {(k, Memory MSTORE)}
    (stack_height h **
     memory memaddr v **
     memory_usage (M memu memaddr 32) **
     program_counter (k + 1) **
     gas_pred (g - Gverylow + Cmem memu -
               Cmem (M memu memaddr 32)) **
     continuing )"
apply(auto simp add: triple_def)
apply(rule_tac x = 1 in exI)
apply(case_tac presult;
   auto simp add: meter_gas_def mstore_def
        memory_inst_numbers.simps    
        instruction_result_as_set_def vctx_advance_pc_def)
apply (rule memory_was_changed)
apply auto

defer
apply (rule leibniz)
apply blast
apply (rule plz_sort_it_out)
apply (auto simp:memory_range_fact)
done

end
