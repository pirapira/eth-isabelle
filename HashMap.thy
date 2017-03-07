theory "HashMap" 

imports  "lem/Evm" "Hoare" "HoareTripleForInstructions"

begin


lemma s : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply(auto)
done

fun storage_array :: "w256 \<Rightarrow> w256 list \<Rightarrow> set_pred" where
"storage_array ind [] = emp"
| "storage_array ind (a#b) = storage ind a ** storage_array (ind+1) b"

axiomatization hash2 :: "w256 \<Rightarrow> w256 \<Rightarrow> w256" where
hash_inj :
    "hash2 b v1 = hash2 c v2 \<Longrightarrow> b = c \<or> hash2 b v1 = 0"
and hash_inj2 :
   "hash2 b v1 = hash2 c v2 \<Longrightarrow> v1 = v2  \<or> hash2 b v1 = 0"
and hash_compat :
   "hash2 a b \<noteq> 0 \<Longrightarrow> hash2 a b = keccak (word_rsplit a@ word_rsplitb)"

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

