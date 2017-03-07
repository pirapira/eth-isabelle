theory "HashMap" 

imports  "lem/Evm" "Hoare" "HoareTripleForInstructions"

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

lemma cut_memory_aux :
  "cut_memory_aux addr x mem @
   cut_memory_aux (addr+word_of_int (int x)) y mem =
   cut_memory_aux addr (x+y) mem"
apply (induction x arbitrary:addr)
apply(auto simp:cut_memory_aux.simps)
using helper
apply force
done

lemma cut_memory_append :
  "cut_memory addr x mem @ cut_memory (addr+x) y mem =
   cut_memory addr (x+y) mem"
apply (induction y)
apply(auto)

(*
definition memory :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"memory ind w = memory_range ind [
   (word_rsplit w)!0,
   (word_rsplit w)!1,
   (word_rsplit w)!2,
   (word_rsplit w)!3,
   (word_rsplit w)!4,
   (word_rsplit w)!5,
   (word_rsplit w)!6,
   (word_rsplit w)!7,
   (word_rsplit w)!8,
   (word_rsplit w)!9,
   (word_rsplit w)!10,
   (word_rsplit w)!11,
   (word_rsplit w)!12,
   (word_rsplit w)!13,
   (word_rsplit w)!14,
   (word_rsplit w)!15,
   (word_rsplit w)!16,
   (word_rsplit w)!17,
   (word_rsplit w)!18,
   (word_rsplit w)!19,
   (word_rsplit w)!20,
   (word_rsplit w)!21,
   (word_rsplit w)!22,
   (word_rsplit w)!23,
   (word_rsplit w)!24,
   (word_rsplit w)!25,
   (word_rsplit w)!26,
   (word_rsplit w)!27,
   (word_rsplit w)!28,
   (word_rsplit w)!29,
   (word_rsplit w)!30,
   (word_rsplit w)!31
]"
*)

lemma sep_memory_range2 :
"      unat (len_word :: w256) = length input \<Longrightarrow>
       (rest ** memory_range begin_word input) s =
       ((memory_range_elms begin_word input \<subseteq> s) \<and> rest (s - memory_range_elms begin_word input)) 
"
using sep_memory_range by force

lemma sep_memory [simp] :
  "((rest ** memory a w)) s =
   (memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w)))"
apply (subst memory_def)
apply (rule sep_memory_range2)
apply (auto simp:word_length)
apply (rule word_32)
done

lemma sep_memory2 [simp] :
  "(rest ** memory a w) s ==
   memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w))"
using sep_memory
apply force
done

lemma sep_memory3 [simp] :
  "(memory a w ** rest) s ==
   memory_range_elms a (word_rsplit w) \<subseteq> s \<and>
   rest (s - memory_range_elms a (word_rsplit w))"
using sep_memory
apply force
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

(* declare memory_def [simp]
 declare memory_range.simps [simp]
 *)

declare meter_gas_def [simp del]

lemma subtract_gas_annotation :
 "subtract_gas x res = InstructionAnnotationFailure \<Longrightarrow>
  res = InstructionAnnotationFailure"
apply(cases res)
apply(auto)
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

(*** need hoare triple for sha  *)
lemma hash2_gas_triple :
  "triple {OutOfGas}
     (\<langle> h \<le> 1022 \<rangle> **
       stack (h+1) 64 **
       stack h memaddr **
       stack_height (h+2) **
       program_counter k **
       memory memaddr table ** memory (memaddr+32) key **
       gas_pred g **
       continuing)
     {(k, Arith SHA3)}
    (\<langle> hash2 table key \<noteq> 0 \<rangle> **
     stack_height (h + 1) **
     stack h (hash2 table key) **
     memory memaddr table ** memory (memaddr+32) key **
     program_counter (k + 1) **
     gas_pred (g - Gsha3 - Gsha3word * 2) ** continuing )"
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



(*
apply (simp)
; auto simp add: instruction_result_as_set_def)
apply(rule leibniz)
 apply blast
apply auto
*)
lemma s : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply(auto)
done

fun storage_array :: "w256 \<Rightarrow> w256 list \<Rightarrow> set_pred" where
"storage_array ind [] = emp"
| "storage_array ind (a#b) = storage ind a ** storage_array (ind+1) b"

fun assoc :: "(w256*w256) list \<Rightarrow> set_pred" where
  "assoc [] = emp"
| "assoc ((key,a)#xs) = storage key a ** assoc xs"

definition hash_pair :: "w256 \<Rightarrow> w256*w256 \<Rightarrow> w256*w256" where
"hash_pair table p = (hash2 table (fst p), snd p)"

definition hash_pair_z :: "w256 \<Rightarrow> w256*w256 \<Rightarrow> w256*w256" where
"hash_pair_z table p = (hash2 table (fst p), 0)"

definition mapping :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
"mapping ind lst = assoc (map (hash_pair ind) lst)"

fun get :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> w256" where
  "get k [] = 0"
| "get k ((ok,ov)#xs) = (if k = ok then ov else get k xs)"

fun mem :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> bool" where
  "mem k [] = False"
| "mem k ((ok,ov)#xs) = (k = ok \<or> mem k xs)"

fun remove :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> (w256*w256) list" where
  "remove k [] = []"
| "remove k ((ok,ov)#xs) =
   (if k = ok then xs else (ok,ov)#remove k xs)"

fun add :: "w256 \<Rightarrow> w256 \<Rightarrow> (w256*w256) list \<Rightarrow> (w256*w256) list" where
"add k v lst = (k,v)#remove k lst"

lemma add_not_mem : "\<not> (mem k lst) \<Longrightarrow> add k v lst = (k,v)#lst"
apply (induction lst)
apply(auto)
done

lemma stored :
   "mem k mp \<Longrightarrow>
    assoc mp = assoc (remove k mp) ** storage k (get k mp)"
apply (induction mp)
apply(auto)
done

lemma stored_hash_from_mapping :
   "mem k mp \<Longrightarrow>
    mapping ind mp =
    mapping ind (remove k mp) ** storage (hash2 ind k) (get k mp)"
apply (induction mp)
apply(auto simp:mapping_def hash_pair_def)
done

lemma minus_test : "a - {x} - {y} = a - {y} - {x}"
apply auto
done

lemma mapping_cons :
   "mapping ind ((k,v)#mp) = storage (hash2 ind k) v ** mapping ind mp"
apply (induction mp)
apply(auto simp:mapping_def minus_test hash_pair_def)
done

lemma set_storage1 :
  assumes a:"mem key m"
  shows "triple {OutOfGas}
    (\<langle> h \<le> 1024 \<rangle> **
     stack (h+1) (hash2 table key) **
     stack h v **
     stack_height (h+2) **
     mapping table m **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SSTORE)}
    (mapping table (add key v m) **
     program_counter (k+1) **
     gas_pred (g - Csstore (get key m) v) **
     stack_height h **
     continuing)" (is "triple _ ?pre _ ?post")
proof -
  from a have good_pre: "?pre =
     (\<langle> h \<le> 1024 \<rangle> **
     stack_height (h+2) **
     stack (h+1) (hash2 table key) **
     stack h v **
     program_counter k **
     storage (hash2 table key) (get key m) **
     gas_pred g **
     continuing) **
     mapping table (remove key m)"
     (is "?pre = ?presmall ** _")
     by (auto simp:stored_hash_from_mapping)
  have good_post: "?post = (
     stack_height h **
     program_counter (k+1) **
     storage (hash2 table key) v **
     gas_pred (g - Csstore (get key m) v) **
     continuing) **
     mapping table (remove key m)" (is "_ = ?postsmall ** _")

     by (auto simp:mapping_cons)
  have "triple {OutOfGas} ?presmall {(k, Storage SSTORE)} ?postsmall"
    by (rule sstore_gas_triple)
  then have "triple {OutOfGas} (?presmall ** mapping table (remove key m))
      {(k, Storage SSTORE)} (?postsmall ** mapping table (remove key m))"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed

lemma set_storage2 :
  assumes a:"\<not> (mem key m)"
  shows "triple {OutOfGas}
    (\<langle> h \<le> 1024 \<rangle> **
     stack (h+1) (hash2 table key) **
     stack h v **
     stack_height (h+2) **
     mapping table m **
     storage (hash2 table key) 0 **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SSTORE)}
    (mapping table (add key v m) **
     program_counter (k+1) **
     gas_pred (g - Csstore 0 v) **
     stack_height h **
     continuing)" (is "triple _ ?pre _ ?post")
proof -
  have good_pre: "?pre =
     (\<langle> h \<le> 1024 \<rangle> **
     stack_height (h+2) **
     stack (h+1) (hash2 table key) **
     stack h v **
     program_counter k **
     storage (hash2 table key) 0 **
     gas_pred g **
     continuing) **
     mapping table m"
     (is "?pre = ?presmall ** _")
     by (auto simp:stored_hash_from_mapping)
  from a have good_post: "?post = (
     stack_height h **
     program_counter (k+1) **
     storage (hash2 table key) v **
     gas_pred (g - Csstore 0 v) **
     continuing) **
     mapping table m" (is "_ = ?postsmall ** _")
     by (subst add_not_mem) (auto simp:mapping_cons)
  have "triple {OutOfGas} ?presmall {(k, Storage SSTORE)} ?postsmall"
    by (rule sstore_gas_triple)
  then have "triple {OutOfGas} (?presmall ** mapping table m)
      {(k, Storage SSTORE)} (?postsmall ** mapping table m)"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed

definition perhaps_alloc ::
   "w256 \<Rightarrow> w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
"perhaps_alloc ind k lst =
    (if mem k lst then emp else storage (hash2 ind k) 0)"

lemma mem_perhaps :
  "mem key m \<Longrightarrow>
   mapping table m ** perhaps_alloc table key m =
   mapping table m"
apply(auto simp:perhaps_alloc_def)
done

lemma mem_perhaps_not :
  "\<not>mem key m \<Longrightarrow>
   mapping table m ** perhaps_alloc table key m =
   mapping table m ** storage (hash2 table key) 0"
apply(auto simp:perhaps_alloc_def)
done

lemma not_mem_get_zero : "\<not>mem key m \<Longrightarrow> get key m = 0"
apply (induction m)
apply (auto)
done

lemma set_storage :
  "triple {OutOfGas}
    (\<langle> h \<le> 1024 \<rangle> **
     stack (h+1) (hash2 table key) **
     stack h v **
     stack_height (h+2) **
     (mapping table m ** perhaps_alloc table key m) **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SSTORE)}
    (mapping table (add key v m) **
     program_counter (k+1) **
     gas_pred (g - Csstore (get key m) v) **
     stack_height h **
     continuing)"
apply (cases "mem key m")
apply(subst mem_perhaps)
apply(simp)
using set_storage1
apply(simp)
apply(subst mem_perhaps_not)
apply(simp)
apply(subst not_mem_get_zero)
apply(simp)
using set_storage2
apply(auto)
done

lemma get_storage1 :
  assumes a:"mem key m"
  shows
  "triple {OutOfGas}
    (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     stack_height (h+1) **
     stack h (hash2 table key) **
     mapping table m **
     block_number_pred bn **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SLOAD)}
    (stack h (get key m) **
     mapping table m **
     program_counter (k+1) **
     block_number_pred bn **
     gas_pred (g - Gsload (unat bn)) **
     stack_height (h+1) **
     continuing)"
 (is "triple _ ?pre _ ?post")
proof -
  from a have good_pre: "?pre =
     (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     block_number_pred bn ** stack_height (h + 1) **
     stack h (hash2 table key) **
     program_counter k **
     storage (hash2 table key) (get key m) **
     gas_pred g ** continuing) **
     mapping table (remove key m)"
     (is "?pre = ?presmall ** _")
     by (auto simp:stored_hash_from_mapping)
  have good_post: "?post = (
     block_number_pred bn ** stack_height (h + 1) **
     stack h (get key m) ** 
     program_counter (k + 1) **
     storage (hash2 table key) (get key m) **
     gas_pred (g - Gsload (unat bn)) ** continuing ) **
     mapping table (remove key m)" (is "_ = ?postsmall ** _")
     by (subst stored_hash_from_mapping) (auto simp:a)
  have "triple {OutOfGas} ?presmall {(k, Storage SLOAD)} ?postsmall"
    by (rule sload_gas_triple)
  then have "triple {OutOfGas} (?presmall ** mapping table (remove key m))
      {(k, Storage SLOAD)} (?postsmall ** mapping table (remove key m))"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed

lemma get_storage2 :
  assumes a:"\<not>mem key m"
  shows
  "triple {OutOfGas}
    (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     stack_height (h+1) **
     stack h (hash2 table key) **
     mapping table m **
     storage (hash2 table key) (get key m) **
     block_number_pred bn **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SLOAD)}
    (stack h (get key m) **
     mapping table m **
     storage (hash2 table key) (get key m) **
     program_counter (k+1) **
     block_number_pred bn **
     gas_pred (g - Gsload (unat bn)) **
     stack_height (h+1) **
     continuing)"
 (is "triple _ ?pre _ ?post")
proof -
  from a have good_pre: "?pre =
     (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     block_number_pred bn ** stack_height (h + 1) **
     stack h (hash2 table key) **
     program_counter k **
     storage (hash2 table key) 0 **
     gas_pred g ** continuing) **
     mapping table m"
     (is "?pre = ?presmall ** _")
     by (simp add:not_mem_get_zero)
  from a have good_post: "?post = (
     block_number_pred bn ** stack_height (h + 1) **
     stack h 0 ** 
     program_counter (k + 1) **
     storage (hash2 table key) 0 **
     gas_pred (g - Gsload (unat bn)) ** continuing ) **
     mapping table m" (is "_ = ?postsmall ** _")
     by (simp add:not_mem_get_zero)
  have "triple {OutOfGas} ?presmall {(k, Storage SLOAD)} ?postsmall"
    by (rule sload_gas_triple)
  then have "triple {OutOfGas} (?presmall ** mapping table m)
      {(k, Storage SLOAD)} (?postsmall ** mapping table m)"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed

lemma get_storage :
  "triple {OutOfGas}
    (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     stack_height (h+1) **
     stack h (hash2 table key) **
     ( mapping table m ** perhaps_alloc table key m ) **
     block_number_pred bn **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SLOAD)}
    (stack h (get key m) **
     ( mapping table m ** perhaps_alloc table key m ) **
     program_counter (k+1) **
     block_number_pred bn **
     gas_pred (g - Gsload (unat bn)) **
     stack_height (h+1) **
     continuing)"
apply (cases "mem key m")
apply(subst mem_perhaps)
apply(simp)
apply(subst mem_perhaps)
apply(simp)
using get_storage1
apply(simp)
apply(subst mem_perhaps_not)
apply(simp)
apply(subst mem_perhaps_not)
apply(simp)
using get_storage2
apply(auto simp:not_mem_get_zero)
done

definition zero_table :: "w256 \<Rightarrow> state_element set" where
"zero_table table = {StorageElm (hash2 table key,0) | key.
  hash2 table key \<noteq> 0}"

(* set with exactly correct elems *)
definition alloc_zero_table :: "w256 \<Rightarrow> set_pred" where
"alloc_zero_table table = (\<lambda>st. st = zero_table table)"

definition alloc_zero_tables :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"alloc_zero_tables t1 t2 = (\<lambda>st. st = zero_table t1 \<union> zero_table t2)"

definition memory :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"memory ind w = memory_range ind (word_rsplit w)"


lemma separate_table :
  "a \<noteq> b \<Longrightarrow> zero_table a \<inter> zero_table b = {}"
apply (auto simp:zero_table_def)
using hash_inj
apply force
done

lemma separate_table2 :
  "a \<noteq> b \<Longrightarrow>
  alloc_zero_tables a b = alloc_zero_table a ** alloc_zero_table b"
apply(auto simp:alloc_zero_table_def alloc_zero_tables_def
   sep_def separate_table)
done

definition assoc_set ::
  "(w256*w256) list \<Rightarrow> state_element set" where
"assoc_set m = {StorageElm (a,b) | a b. (a,b) \<in> set m}"

definition mapping_set ::
  "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> state_element set" where
"mapping_set table m = assoc_set (map (hash_pair table) m)"

definition mapping_set_z ::
  "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> state_element set" where
"mapping_set_z table m = assoc_set (map (hash_pair_z table) m)"

definition mapping_zero ::
   "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> state_element set" where
"mapping_zero table m = zero_table table - mapping_set_z table m"

definition alloc_zero ::
   "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
"alloc_zero table m = (\<lambda>st. st = mapping_zero table m)"

lemma start_table :
   "alloc_zero_table t = alloc_zero t [] ** mapping t []"
apply(auto simp:alloc_zero_table_def alloc_zero_def sep_def
  mapping_def mapping_zero_def mapping_set_def emp_def
  assoc_set_def mapping_set_z_def)
done

lemma easy : "p \<in> set m \<Longrightarrow> f p \<in> set (map f m)"
apply (induction m)
apply auto
done


lemma hp_simp : "fst \<circ> hash_pair t = hash2 t \<circ> fst"
apply(auto simp:hash_pair_def)
done

lemma hp_simp2 : "fst (hash_pair t (a, b)) = hash2 t a"
apply(auto simp:hash_pair_def)
done

lemma easy2 : "aa \<notin> fst ` set m \<Longrightarrow> (aa, b) \<in> set m \<Longrightarrow> False"
  by (simp add: rev_image_eqI)

lemma add_mapping_set :
  "mem a m \<Longrightarrow> fst ` (set m) = fst ` (set (add a b m))"
apply (induction m)
apply (simp)
apply (auto)
apply force
defer
apply force
subgoal for aa b m aaa ba
apply (cases "a = aa")
apply force
apply force
done
subgoal for aa b m aaa ba
apply (cases "a = aa")
apply force
apply force
done
done

lemma hp_unfold : "(hash2 t key, b) = hash_pair t (key,b)"
apply (simp add:hash_pair_def)
done

lemma hp_z_unfold : "(hash2 t key, 0) = hash_pair_z t (key,b)"
apply (simp add:hash_pair_z_def)
done

lemma storage_simp :
 "hash2 t key \<noteq> 0 \<Longrightarrow>
  (StorageElm (hash2 t key, 0) \<in> mapping_set_z t m) =
  (key \<in> fst ` (set m))"
apply (auto simp:mapping_set_z_def assoc_set_def hash_pair_z_def)
using hash_inj2
apply force
subgoal for b
using Set.imageI [of "(key,b)" "set m" "hash_pair_z t"]
apply (subst hp_z_unfold)
apply force
done
done

declare add.simps [simp del]

lemma add_mapping_set2 :
  "mem a m \<Longrightarrow> fst ` (set (add a b m)) = fst ` (set m)"
using add_mapping_set
apply simp
done

lemma alloc_zero_mem :
  "mem a m \<Longrightarrow>
   mapping_zero t (add a b m) = mapping_zero t m"
apply(auto simp:alloc_zero_table_def alloc_zero_def sep_def
  emp_def zero_table_def mapping_zero_def)
apply (auto simp:storage_simp)
apply (auto simp:add_mapping_set2)
apply force
using add_mapping_set
apply force
done

lemma mem_as_set : "\<not> mem aa m \<Longrightarrow> (aa, b) \<in> set m \<Longrightarrow> False"
apply (induction m)
apply (auto)
done

(* alloc zero needs to carry the invariant *)
lemma alloc_zero_split : 
  "hash2 t a \<noteq> 0 \<Longrightarrow>
  alloc_zero t m = alloc_zero t (add a b m) ** perhaps_alloc t a m"
apply(auto simp:alloc_zero_table_def alloc_zero_def sep_def
  emp_def zero_table_def perhaps_alloc_def)
apply(rule s)
apply (simp add:alloc_zero_mem)
apply(auto)[1]
apply(rule s)
apply (simp add:add_not_mem)
apply (auto)
apply (rule exI [of "_" "{StorageElm (hash2 t a, 0)}"])

apply (auto simp:mapping_zero_def mapping_set_z_def
   hash_pair_z_def assoc_set_def storage_def)
apply (simp add:zero_table_def)
apply auto
defer
apply (simp add:zero_table_def)
apply auto
subgoal for aa b
using hash_inj2 [of t a t aa]
apply auto
using mem_as_set
apply force
done
subgoal for aa b
using hash_inj2 [of t a t aa]
apply auto
using mem_as_set
apply force
done
done

lemma alloc_zero_split2 : 
  "hash2 t a \<noteq> 0 \<Longrightarrow>
   alloc_zero t (add a b m) ** perhaps_alloc t a m = alloc_zero t m"
using alloc_zero_split
apply simp
done

lemma alloc_table :
   "hash2 t a \<noteq> 0 \<Longrightarrow>
    alloc_zero t m ** mapping t m =
    mapping t m ** (alloc_zero t (add a b m) ** perhaps_alloc t a m)"
apply (subst alloc_zero_split2)
apply auto
done

definition htable :: "w256 \<Rightarrow> (w256 * w256) list \<Rightarrow> set_pred" where
"htable t m = alloc_zero t m ** mapping t m"

lemma set_table :
    assumes a:"hash2 table key \<noteq> 0"
    shows "triple {OutOfGas}
    (\<langle> h \<le> 1024 \<rangle> **
     stack (h+1) (hash2 table key) **
     stack h v **
     stack_height (h+2) **
     htable table m **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SSTORE)}
    (htable table (add key v m) **
     program_counter (k+1) **
     gas_pred (g - Csstore (get key m) v) **
     stack_height h **
     continuing)" (is "triple _ ?pre _ ?post")
proof -
  have good_pre: "?pre =
     (\<langle> h \<le> 1024 \<rangle> **
     stack (h+1) (hash2 table key) **
     stack h v **
     stack_height (h+2) **
     (mapping table m ** perhaps_alloc table key m) **
     program_counter k **
     gas_pred g **
     continuing) **
     alloc_zero table (add key v m)"
     (is "?pre = ?presmall ** _")
    using a
 apply (subst htable_def)
 apply (subst alloc_table)
 apply (auto)
 done
  have good_post: "?post = (
     mapping table (add key v m) **
     program_counter (k+1) **
     gas_pred (g - Csstore (get key m) v) **
     stack_height h **
     continuing) **
     alloc_zero table (add key v m)"
     (is "_ = ?postsmall ** _")
     apply (subst htable_def) apply (auto) done
  have "triple {OutOfGas} ?presmall {(k, Storage SSTORE)} ?postsmall"
   using set_storage by force
  then have "triple {OutOfGas} (?presmall ** alloc_zero table (add key v m))
      {(k, Storage SSTORE)} (?postsmall ** alloc_zero table (add key v m))"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed

lemma get_table :
  assumes a:"hash2 table key \<noteq> 0"
  shows
    "triple {OutOfGas}
    (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     stack_height (h+1) **
     stack h (hash2 table key) **
     htable table m **
     block_number_pred bn **
     program_counter k **
     gas_pred g **
     continuing)
    {(k, Storage SLOAD)}
    (stack h (get key m) **
     htable table m **
     program_counter (k+1) **
     block_number_pred bn **
     gas_pred (g - Gsload (unat bn)) **
     stack_height (h+1) **
     continuing)"
 (is "triple _ ?pre _ ?post")
proof -
  from a have good_pre: "?pre =
    (\<langle>h \<le> 1023 \<and> unat bn \<ge> 2463000 \<rangle> **
     stack_height (h+1) **
     stack h (hash2 table key) **
     ( mapping table m ** perhaps_alloc table key m ) **
     block_number_pred bn **
     program_counter k **
     gas_pred g **
     continuing) ** alloc_zero table (add key 0 m)"
     (is "?pre = ?presmall ** _")
      apply (subst htable_def)
      apply (subst alloc_table)
      apply (auto)
      done
  from a have good_post: "?post = (
     stack h (get key m) **
     ( mapping table m ** perhaps_alloc table key m ) **
     program_counter (k+1) **
     block_number_pred bn **
     gas_pred (g - Gsload (unat bn)) **
     stack_height (h+1) **
     continuing) **
     alloc_zero table (add key 0 m)" (is "_ = ?postsmall ** _")
      apply (subst htable_def)
      apply (subst alloc_table)
      apply (auto)
      done
  have "triple {OutOfGas} ?presmall {(k, Storage SLOAD)} ?postsmall"
    by (rule get_storage)
  then have "triple {OutOfGas} (?presmall ** alloc_zero table (add key 0 m))
      {(k, Storage SLOAD)} (?postsmall ** alloc_zero table (add key 0 m))"
    by (rule frame)
  then show ?thesis using good_pre and good_post by simp
qed


end

