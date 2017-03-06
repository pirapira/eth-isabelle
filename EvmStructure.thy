theory "EvmStructure" 

imports  "lem/Evm" "Hoare"
  "HoareTripleForInstructions"

begin

(* accessors for variables *)
type_synonym 'a access = "variable_ctx \<Rightarrow> 'a"

definition const :: "nat \<Rightarrow> nat access" where
"const w ctx = w"

definition cell :: "nat \<Rightarrow> nat access" where
"cell w ctx = unat (vctx_storage ctx (word256FromNat w))"

definition arr :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) access" where
"arr addr len ctx x = (if x < len then cell (addr+x) ctx else 0)"

definition cannot_modify :: "w256 \<Rightarrow> 'a access \<Rightarrow> bool" where
"cannot_modify w x = (\<forall>ctx t. x ctx = x (vctx_update_storage w t ctx))" 

lemma cannot_update_const : "cannot_modify addr (const c)"
apply(simp add:cannot_modify_def const_def)
done

lemma cannot_update_cell :
  "addr1 \<noteq> addr2 \<Longrightarrow> cannot_modify addr1 (cell (unat addr2))"
apply(simp add:cannot_modify_def cell_def word256FromNat_def unat_def
  vctx_update_storage_def)
done

lemma s : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply(auto)
done

lemma test : "(a::int) mod 100 \<ge> 0"
apply arith
done

lemma word_of_int_le :
 "(word_of_int x :: 256 word) \<le> (word_of_int y :: 256 word) \<Longrightarrow>
  x mod 2^256 \<le> y mod 2^256" 
apply (auto simp:uint_word_of_int word_le_def)
done

lemma l : "(x::int) mod 2^256 < addr \<Longrightarrow> x < 2^256 \<Longrightarrow> x \<ge> 0 \<Longrightarrow>
  x < addr"
using int_mod_ge by fastforce

lemma ll : "(word_of_int x :: 256 word) < (addr::256 word) \<Longrightarrow>
   uint (word_of_int x :: 256 word) < uint addr"
  by (simp add: word_less_def)

lemma ll_a : "(word_of_int x :: 256 word) \<le> (addr::256 word) \<Longrightarrow>
   uint (word_of_int x :: 256 word) \<le> uint addr"
  by (simp add: word_le_def)

lemma ll_b : "(word_of_int x :: 256 word) \<ge> (addr::256 word) \<Longrightarrow>
   uint (word_of_int x :: 256 word) \<ge> uint addr"
  by (simp add: word_le_def)

lemma l2 : 
  assumes a:"(word_of_int x :: 256 word) < (addr::256 word)"
  and small:"x < 2^256" and  natural:"x \<ge> 0"
  shows "x < uint addr"
proof -
from a and ll have b: "uint (word_of_int x :: 256 word) < uint addr" by auto
have "uint (word_of_int x :: 256 word) = x mod 2^256" by
   (auto simp:uint_word_of_int)
then have "uint (word_of_int x :: 256 word) = x" using natural and small
  by (simp add: natural int_mod_eq) 
then show ?thesis using b by auto
qed

lemma l2_a : 
  assumes a:"(word_of_int x :: 256 word) \<le> (addr::256 word)"
  and small:"x < 2^256" and  natural:"x \<ge> 0"
  shows "x \<le> uint addr"
proof -
from a and ll_a have b: "uint (word_of_int x :: 256 word) \<le> uint addr" by auto
have "uint (word_of_int x :: 256 word) = x mod 2^256" by
   (auto simp:uint_word_of_int)
then have "uint (word_of_int x :: 256 word) = x" using natural and small
  by (simp add: natural int_mod_eq) 
then show ?thesis using b by auto
qed

lemma l2_b : 
  assumes a:"(word_of_int x :: 256 word) \<ge> (addr::256 word)"
  and small:"x < 2^256" and  natural:"x \<ge> 0"
  shows "x \<ge> uint addr"
proof -
from a and ll_b have b: "uint (word_of_int x :: 256 word) \<ge> uint addr" by auto
have "uint (word_of_int x :: 256 word) = x mod 2^256" by
   (auto simp:uint_word_of_int)
then have "uint (word_of_int x :: 256 word) = x" using natural and small
  by (simp add: natural int_mod_eq) 
then show ?thesis using b by auto
qed

lemma k : 
  "word_of_int (uint (addr2::256 word) + int x) < addr2 \<Longrightarrow>
   uint addr2 + int x < 2^256 \<Longrightarrow>
   False"
using l2 not_add_less2 of_nat_0_le_iff by fastforce

lemma k_d : 
  "addr2 + x + 1 \<le> word_of_int (uint (addr2::256 word) + uint x) \<Longrightarrow>
   uint addr2 + uint x + 1 < 2^256 \<Longrightarrow>
   uint (addr2 + x + 1) \<le> uint (addr2::256 word) + uint x"
using l2_b
apply fastforce
done

lemma word_size : "uint (w::256 word) < 2^256"
using word.uint [of w] by simp

lemma k_a : 
  assumes a: "addr2 + len \<le> (word_of_int (uint addr2 + int x) :: 256 word)"
  and small:"uint (addr2::256 word) + uint (len::256 word) < 2^256"
  and xlen: "x < nat (uint len)"
  shows "False"
proof -
  have s1:"uint (addr2 + len :: 256 word) < 2^256" by (rule word_size)
  from xlen and small have s2:"uint addr2 + int x < 2^256" by auto
  from small and s1 have com: "uint (addr2 + len) = uint addr2 + uint len"
    by (meson dual_order.order_iff_strict l2_a not_le order_trans uint_add_lem uint_lt zero_le_numeral zero_le_power)
  from a have "(word_of_int (uint (addr2 + len)) :: 256 word) \<le>
   (word_of_int (uint addr2 + int x) :: 256 word)" by auto
  then have "uint (addr2 + len) mod 2^256 \<le>
             (uint addr2 + int x) mod 2^256"
    using word_of_int_le by blast 
  from this and s1 and s2 have "uint (addr2 + len) \<le> uint addr2 + int x"
    using a add_nonneg_nonneg l2_b of_nat_0_le_iff uint_nonnegative by blast
  from this and xlen and com show False by auto
qed

lemma kk :
   "uint (addr2::256 word) + uint len < 2^256 \<Longrightarrow>
    x < nat (uint (len::256 word)) \<Longrightarrow>
    uint addr2 + int x < 2^256"
  by linarith

lemma cannot_update_array_small :
  "addr1 < addr2 \<Longrightarrow>
   uint (addr2::256 word) + uint (len::256 word) < 2^256 \<Longrightarrow>
   cannot_modify addr1 (arr (unat addr2) (unat len))"
apply(simp add:cannot_modify_def cell_def word256FromNat_def unat_def
  vctx_update_storage_def arr_def)
apply(auto)
apply(rule s)
apply(simp add:cannot_modify_def cell_def word256FromNat_def unat_def
  vctx_update_storage_def arr_def)
apply(auto)
using k kk
apply fastforce
done

lemma cannot_update_array_large :
  "addr1 \<ge> addr2 + len \<Longrightarrow>
   uint (addr2::256 word) + uint (len::256 word) < 2^256 \<Longrightarrow>
   cannot_modify addr1 (arr (unat addr2) (unat len))"
apply(simp add:cannot_modify_def cell_def word256FromNat_def unat_def
  vctx_update_storage_def arr_def)
apply(auto)
apply(rule s)
apply(simp add:cannot_modify_def cell_def word256FromNat_def unat_def
  vctx_update_storage_def arr_def)
apply(auto)
using k_a
apply fastforce
done

(* separation logic statement for cell?

storage :: w256 \<Rightarrow> w256 \<Rightarrow> set_pred

*)

fun storage_array :: "w256 \<Rightarrow> w256 list \<Rightarrow> set_pred" where
"storage_array ind [] = emp"
| "storage_array ind (a#b) = storage ind a ** storage_array (ind+1) b"

definition hash :: "w256 \<Rightarrow> w256 \<Rightarrow> w256 option" where
"hash a b = None"

definition hash3 :: "w256 \<Rightarrow> w256 \<Rightarrow> w256" where
"hash3 a b = (case hash a b of
   None \<Rightarrow> undefined
 | Some h \<Rightarrow> h )"

axiomatization hash2 :: "w256 \<Rightarrow> w256 \<Rightarrow> w256" where
hash_inj : "hash2 b v1 = hash2 c v2 \<Longrightarrow> b = c"
and hash_inj2 : "hash2 b v1 = hash2 c v2 \<Longrightarrow> v1 = v2"
and hash_foo : "hash3 a b = hash2 a b"
(*
lemma "False"
using hash3_def hash_def hash_inj hash_inj2 hash_foo
*)

fun assoc :: "(w256*w256) list \<Rightarrow> set_pred" where
  "assoc [] = emp"
| "assoc ((key,a)#xs) = storage key a ** assoc xs"

(*
fun mapping :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
  "mapping ind [] = emp"
| "mapping ind ((key,a)#tll) = (case super_hash key a of
    None \<Rightarrow> mapping ind tll (* what is the correct way to handle? *)
  | Some h \<Rightarrow> storage h a ** mapping ind tll)"
*)

definition mapping :: "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
"mapping ind lst = assoc (map (\<lambda>p. (hash2 ind (fst p), snd p)) lst)"

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

(*
fun add :: "w256 \<Rightarrow> w256 \<Rightarrow> (w256*w256) list \<Rightarrow> (w256*w256) list" where
  "add k v [] = [(k,v)]"
| "add k v ((ok,ov)#xs) =
   (if k = ok then (k,v)#xs else (ok,ov)#add k v xs)"
*)

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
apply(auto simp:mapping_def)
done

lemma minus_test : "a - {x} - {y} = a - {y} - {x}"
apply auto
done

lemma mapping_cons :
   "mapping ind ((k,v)#mp) = storage (hash2 ind k) v ** mapping ind mp"
apply (induction mp)
apply(auto simp:mapping_def minus_test)
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
"zero_table table = {StorageElm (hash2 table key,0) | key. True}"

(* set with exactly correct elems *)
definition alloc_zero_table :: "w256 \<Rightarrow> set_pred" where
"alloc_zero_table table = (\<lambda>st. st = zero_table table)"

definition alloc_zero_tables :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"alloc_zero_tables t1 t2 = (\<lambda>st. st = zero_table t1 \<union> zero_table t2)"

definition memory :: "w256 \<Rightarrow> w256 \<Rightarrow> set_pred" where
"memory ind w = memory_range ind (word_rsplit w)"

(*
lemma hash_inj : "hash2 a b = hash2 a c \<Longrightarrow>
   b = c \<or> hash2 a b = undefined \<or> hash2 a c = undefined"
apply(simp add:hash2_def hash_def)
done

lemma hash_inj2 : "hash2 b v1 = hash2 c v2 \<Longrightarrow>
   b = c \<or> hash2 b v1 = undefined \<or> hash2 c v2 = undefined"
apply(simp add:hash2_def hash_def)
done

lemma undef : "hash2 undefined undefined = undefined"
apply(simp add:hash2_def hash_def)
done

lemma foo : "(1::int) \<noteq> undefined"
apply auto
*)

lemma separate_table :
  "a \<noteq> b \<Longrightarrow> zero_table a \<inter> zero_table b = {}"
apply (auto simp:zero_table_def hash_inj)
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
"mapping_set table m =
   assoc_set (map (\<lambda>p. (hash2 table (fst p), snd p)) m)"
(*
   {StorageElm (hash2 table a,b) | a b. (a,b) \<in> set m}"
*)

definition mapping_zero ::
   "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> state_element set" where
"mapping_zero table m = zero_table table - mapping_set table m"

definition alloc_zero ::
   "w256 \<Rightarrow> (w256*w256) list \<Rightarrow> set_pred" where
"alloc_zero table m = (\<lambda>st. st = mapping_zero table m)"

lemma start_table : "alloc_zero_table t = alloc_zero t [] **
                     mapping t []"
apply(auto simp:alloc_zero_table_def alloc_zero_def sep_def
  mapping_def mapping_zero_def mapping_set_def emp_def
  assoc_set_def)
done

(* does not work because may have several times
  the same element*)
definition diff_keys :: "(w256*w256) list \<Rightarrow> bool" where
"diff_keys m = (card (set (map fst m)) = length m)"

lemma card_insert : "k \<in> s \<Longrightarrow> card (insert k s) = card s"
apply(auto simp:Set.insert_absorb)
done

lemma insert_union : "k \<notin> s \<Longrightarrow> insert k s = s \<union> {k}"
apply(auto)
done

lemma card_insert_cmp : "card (insert k s) \<ge> card s"
apply (cases "k \<notin> s")
apply(auto simp:Set.insert_absorb)
apply (metis card_infinite card_insert_le card_mono eq_iff subset_insertI)
done

lemma card_insert_alt :
  "finite s \<Longrightarrow>
   card (insert k s) = card s + 1 \<or> card (insert k s) = card s"
apply (cases "k \<notin> s")
apply(auto simp:Set.insert_absorb)
done

lemma card_insert_alt2 :
  "finite s \<Longrightarrow>
   k \<notin> s \<Longrightarrow>
   card (insert k s) = card s + 1"
apply(auto)
done

lemma card_insert_len :
 "card (insert k (set l)) = length l + 1 \<Longrightarrow>
  card (set l) = length l"
apply (cases "k \<notin> set l")
apply(simp)
apply(auto)
apply(simp add:Set.insert_absorb)
using card_length [of l]
apply arith
done

lemma helper : "length l = length (map fst l)"
apply auto
done

lemma diff_keys_cons : "diff_keys ((k,v)#l) \<Longrightarrow> diff_keys l"
apply (subst diff_keys_def)
apply (subst (asm) diff_keys_def)
apply (subst helper)
apply (rule card_insert_len)
apply(auto)
done

lemma card_set_cons :
    "p \<in> set m \<Longrightarrow>
    card (set (p # m)) = length (p # m) \<Longrightarrow>
    False"
apply(simp add:Set.insert_absorb)
using card_length [of m]
apply arith
done

lemma easy : "p \<in> set m \<Longrightarrow> f p \<in> set (map f m)"
apply (induction m)
apply auto
done

lemma cannot_add_same :
  "(a, b) \<in> set m \<Longrightarrow>
   diff_keys ((a,b)#m) \<Longrightarrow> False"
apply (subst (asm) diff_keys_def)
apply (subst (asm) helper)
apply (rule card_set_cons [of "a" "map fst m"])
using easy [of "(a,b)" m fst]
apply auto
done

lemma assoc_as_set :
   "diff_keys m \<Longrightarrow> assoc m s = (s = assoc_set m)"
apply (induction m arbitrary:s)
apply(simp add:assoc_set_def emp_def)
subgoal for a m s
apply (induction a)
apply(simp)
subgoal for aa bb
using diff_keys_cons [of aa bb m]
apply(simp)
apply (rule pqqp)
apply(simp add:assoc_set_def emp_def)
apply blast
apply(simp add:assoc_set_def emp_def)
apply auto
using cannot_add_same
apply fastforce
done

lemma mapping_as_set :
  "diff_keys m \<Longrightarrow> 
   mapping t m s = (s = mapping_set t m)"
apply(simp add:mapping_def mapping_set_def emp_def)
using assoc_as_set

apply(simp add:mapping_set_def)

lemma alloc_table :
   "alloc_zero t m ** mapping t m =
    alloc_zero t (p#m) ** mapping t (p#m)"
apply(auto simp:alloc_zero_table_def alloc_zero_def sep_def
  emp_def
  zero_table_def)
apply(rule s)
apply(auto)

(*
lemma set_storage :
  "triple {OutOfGas}
    (memory 0 table ** memory 1 key ** stack h v **
     stack_height (h+1) **
     mapping table m **
     program_counter k **
     gas_pred g **
     continuing)
    {(k,Stack (PUSH_N (word_rsplit 64))),
     (k+1,Stack (PUSH_N (word_rsplit 0))),
     (k+2, Arith SHA3),
     (k+3, Storage SSTORE)}
    (memory 0 table ** memory 1 key ** stack h v **
     mapping table (add key v m) **
     program_counter (k+4) **
     gas_pred g **
     stack_height h **
     continuing)"

lemma get_storage :
  "triple {OutOfGas}
    (memory 0 table ** memory 1 key **
     stack_height h **
     mapping table m **
     program_counter k **
     gas_pred g **
     continuing)
    {(k,Stack (PUSH_N (word_rsplit 64))),
     (k+1,Stack (PUSH_N (word_rsplit 0))),
     (k+2, Arith SHA3),
     (k+3, Storage SLOAD)}
    (memory 0 table ** memory 1 key ** stack h v **
     mapping table m **
     program_counter (k+4) **
     gas_pred g **
     stack (h+1) **
     stack_height (h+1) **
     continuing)"
*)

end


