theory StoreByteList

imports Main "Hoare"

begin

lemma word_of_nat [simp] : "word_of_int (int (unat x)) = x"
  by (metis uint_nat word_of_int_uint)

fun store_byte_list_memory_old  :: "w256 \<Rightarrow> byte list \<Rightarrow> memory \<Rightarrow> memory"  where
 " store_byte_list_memory_old pos [] orig = orig"
|" store_byte_list_memory_old pos (h # t) orig = (
     store_byte_list_memory_old (pos +((word_of_int 1) ::  256 word)) t
       (\<lambda> p .  if pos = p then h else orig p))"

lemma find_mod :
  "uint (word_of_int x::w256) = (x::int) mod 2^256"
apply (auto simp:uint_word_of_int)
done

lemma unat_mod [simp]:
  "unat (word_of_int (int x)::w256) = x mod 2^256"
apply (simp add: find_mod unat_def)
  by (metis (mono_tags, hide_lams) Divides.transfer_int_nat_functions(2) nat_int.Rep_inverse' of_nat_numeral)

lemma simp_take :
 "n > 0 \<Longrightarrow>
  take n (a # lst) = a#take (n-1) lst"
using List.take_Suc_Cons [of "n-1" a lst]
apply auto
done

lemma take_index [simp] :
  "i < n \<Longrightarrow>
   i < length lst \<Longrightarrow>
  index (take n lst) i = Some (lst!i)"
apply(simp)
done

lemma minus_one_large :
   "(-1::int) mod 2^256 = 2^256-1"
apply auto
done

lemma minus_one_word :
   "uint (-1::w256) = 2^256-1"
proof -
  have "uint ((word_of_int (-1))::w256) = (-1) mod 2^256"
   using find_mod
   by blast
  then have "uint ((-1)::w256) = (-1) mod 2^256" by auto
  then show ?thesis using minus_one_large by auto
qed

lemma minus_one_word_nat :
   "unat (-1::w256) = 2^256-1"
using minus_one_word
  by (simp add: unat_def)

lemma split_new :
 "n < 2^256 \<Longrightarrow>
  store_byte_list_memory w
     (a # take n lst) mem x =
  store_byte_list_memory (w+1) (take n lst)
    (\<lambda>p. if w = p then a else mem p) x"
apply (auto simp add:store_byte_list_memory_def)
apply (cases "unat (-1) < n")
apply (auto simp: minus_one_word_nat)
apply (cases "unat (x - w) \<le> n")
apply (cases "unat (x - w) \<le> length lst")
apply auto
apply (cases "unat (x - (w+1)) < n")
apply (cases "unat (x - (w+1)) < length lst")
apply auto
subgoal
proof -
  assume a1: "w \<noteq> x"
  assume a2: "unat (x - (w + 1)) < n"
  have "x - w \<noteq> 0"
    using a1 by auto
  then have "lst ! unat (x - (1 + w)) = take n lst ! (unat (x - w) - 1) \<and> 0 \<noteq> unat (x - w)"
    using a2 by (simp add: add.commute diff_add_eq_diff_diff_swap unat_eq_zero unat_minus_one)
  then show "(a # take n lst) ! unat (x - w) = lst ! unat (x - (w + 1))"
    by (simp add: add.commute)
qed
subgoal proof -
  assume a1: "w \<noteq> x"
  assume a2: "unat (x - w) \<le> length lst"
  assume a3: "\<not> unat (x - (w + 1)) < length lst"
  have f4: "\<forall>n. (0::nat) + (n - 0) = n"
    using linordered_semidom_class.add_diff_inverse by blast
  have f5: "(0::nat) + 0 = 0"
    by blast
  have f6: "\<forall>w wa. (w::256 word) + (wa - w) = wa"
    by auto
  have f7: "\<forall>w wa. (w::256 word) + wa - w = wa"
  by simp
  have f8: "\<forall>w. unat ((w::256 word) - 1) < unat w \<or> 0 = w"
    using f5 f4 by (metis (no_types) One_nat_def diff_is_0_eq' diff_less lessI not_le unat_eq_zero unat_minus_one)
  have f9: "\<forall>n. (0::nat) + n = n"
    by linarith
  have "\<forall>n. unat (x - w) - (n + length lst) = 0"
  using a2 by force
  then have "length lst = unat (x - (1 + w)) \<or> x - w = 0"
    using f9 a3 by (metis (no_types) add.commute diff_diff_add linordered_semidom_class.add_diff_inverse unat_minus_one)
  then show "(a # lst) ! unat (x - w) = mem x"
    using f8 f7 f6 a2 a1 by (metis (no_types) diff_add_eq_diff_diff_swap not_le right_minus_eq)
qed
  apply (metis (mono_tags, hide_lams) add.left_neutral cancel_ab_semigroup_add_class.diff_right_commute diff_add_cancel diff_add_eq_diff_diff_swap less_le_trans measure_unat)

apply (cases "unat (x - (w+1)) < n")
apply (cases "unat (x - (w+1)) < length lst")
apply auto
subgoal proof -
  assume a1: "\<not> unat (x - w) \<le> length lst"
  assume "unat (x - (w + 1)) < length lst"
  then have f2: "Suc (unat (x - (w + 1))) \<le> length lst"
    by (metis Suc_leI)
  have "\<forall>n. \<not> n \<le> length lst \<or> unat (of_nat n::256 word) = n"
    using a1 by (metis (no_types) le_unat_uoi less_imp_le not_less)
  then show "mem x = lst ! unat (x - (w + 1))"
    using f2 a1 by fastforce
qed
apply (cases "unat (x - (w+1)) < n")
apply (cases "unat (x - (w+1)) < length lst")
apply auto
proof -
  assume a1: "w \<noteq> x"
  assume a2: "\<not> unat (x - w) \<le> n"
  assume a3: "unat (x - (w + 1)) < n"
  have "\<forall>n. n + 1 = Suc n"
    by presburger
  then have f4: "\<forall>n. n \<le> 0 \<or> Suc (n - 1) = n"
    by (metis (no_types) One_nat_def not_less_eq_eq ordered_cancel_comm_monoid_diff_class.diff_add)
  have f5: "Suc (unat (x - (w + 1))) \<le> n"
    using a3 by auto
  have "\<not> unat (x - w) \<le> 0"
    using a2 by linarith
  then have "x - w = 0"
    using f5 f4 a2 by (metis (no_types) diff_diff_add unat_minus_one)
  then show "mem x = lst ! unat (x - (w + 1))"
    using a1 by (metis right_minus_eq)
  qed

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply auto
done


lemma store_byte_list_eq :
  "n \<le> 2^256 \<Longrightarrow>
   store_byte_list_memory_old w (take n lst) mem =
   store_byte_list_memory w (take n lst) mem"
apply (induction lst arbitrary: w n mem)
apply (auto)
apply (rule funext)
apply (simp add:store_byte_list_memory_def)
apply (rule funext)
apply (auto)
subgoal for a lst w n mem x
apply (cases "n > 0")
defer
apply auto
apply (simp add:store_byte_list_memory_def)
apply (simp add:simp_take)
using split_new
apply force
done
done


(*

definition insert_one :: "(nat*byte) \<Rightarrow> memory \<Rightarrow> memory" where
"insert_one a mem = (\<lambda> p.
   if word_of_int (int (fst a)) = p then snd a else mem p)"

fun insertions  :: "(nat*byte) list \<Rightarrow> memory \<Rightarrow> memory"  where
 "insertions [] orig = orig"
|"insertions (a # t) orig = insertions t (insert_one a orig)"

definition ins_list  :: "w256 \<Rightarrow> byte list \<Rightarrow> (nat*byte) list"  where
"ins_list pos lst = map (\<lambda> i. (fst i+unat pos,snd i)) (enumerate 0 lst)"

lemma k1 : "snd (unat w, a) = a"
apply auto
done


fun modeq :: "(nat*byte) list \<Rightarrow> (nat*byte) list \<Rightarrow> bool" where
"modeq ((a1,b1)#l1) ((a2,b2)#l2) =
   (a1 mod (2^256) = a2 mod (2^256) \<and> b1 = b2 \<and> modeq l1 l2)"
| "modeq [] [] = True"
| "modeq _ _ = False"
*)

(*
lemma suc_mod :
  "Suc (unat (x::w256)) mod 2^256 =
   unat (word_of_int (int (Suc (unat x)))::w256)"
apply (subst unat_mod)
apply auto
done

lemma suc_mod2 :
   "Suc (unat (x::w256)) mod 2^256 = unat (x+1)"
apply (subst suc_mod)
apply auto
  by (metis add.commute uint_nat wi_hom_succ word_of_int_uint word_succ_p1)

lemma suc_mod3 :
   "Suc (unat (x::w256)) mod 2^256 =
    unat (x+1) mod 2^256"
apply (subst suc_mod2)
  by (metis (no_types, hide_lams) StoreByteList.unat_mod Word.word_of_nat unat_of_nat word_unat.norm_Rep)

lemma add_mod :
    "(a::nat) mod 2^256 = b mod 2^256 \<Longrightarrow>
     (x+a) mod 2^256 = (x+b) mod 2^256"
  using mod_add_cong by blast

lemma mod_plus :
"(x + Suc (unat (w::w256))) mod 2^256 =
 (x + unat (w + 1::w256)) mod 2^256"
apply (rule add_mod)
apply (rule suc_mod3)
done

lemma mapi_inc :
"modeq (map (\<lambda>i. (fst i + unat (w::w256), snd i)) (enumerate (Suc x) lst))
       (map (\<lambda>i. (fst i + unat (w+1), snd i)) (enumerate x lst))"
apply (induction lst arbitrary:w x)
apply (auto)
using mod_plus
apply force
done

lemma make_mod2 :
"a mod 2^256 = b mod 2^256 \<Longrightarrow>
 int a mod 2^256 = int b mod 2^256"
  by (metis Nat_Transfer.transfer_int_nat_functions(4) transfer_int_nat_numerals(3) zmod_int)

lemma make_mod :
"a mod 2^256 = b mod 2^256 \<Longrightarrow>
 (word_of_int (int b)::w256) =
 ( word_of_int (int a)::w256)"
using make_mod2 [of a b]
  by (metis find_mod int_word_uint word_of_int_def)


lemma insert_one_modeq :
   "a mod 2^256 = b mod 2^256 \<Longrightarrow>
   insert_one (a,v) mem = insert_one (b,v) mem"
apply (auto simp:insert_one_def)
using make_mod [of a b]
apply auto
done

lemma insertions_modeq :
  "modeq l1 l2 \<Longrightarrow>
   insertions l1 mem = insertions l2 mem"
apply (induction l1  arbitrary:mem rule:modeq.induct)
apply (auto)
subgoal for a1 b1 l1 a2 l2 mem
using insert_one_modeq [of a2 a1 b1 mem]
apply auto
done
done

lemma manage_aux :
"( store_byte_list_memory_old
            (w+1) lst (\<lambda>p. if w = p then a else mem p) =
  insertions
            (map
              (\<lambda>i. (fst i + unat (w+1), snd i))
              (enumerate 0 lst))
            (\<lambda>p. if w = p then a else mem p) ) \<Longrightarrow>
  insertions
        (map
          (\<lambda>i. (fst i + unat w,
                snd i))
          (enumerate (Suc 0) lst))
        (\<lambda>p. if w = p then a else mem p) =
       store_byte_list_memory_old
        (w + 1) lst
        (\<lambda>p. if w = p then a else mem p)"
apply auto
apply (rule insertions_modeq)
apply (auto simp:mapi_inc)
done

lemma manage :
  "insertions (ins_list w lst) mem =
   store_byte_list_memory_old w lst mem"
apply (induction lst arbitrary: w mem)
apply (auto simp:ins_list_def insert_one_def)
apply (subst k1)
using manage_aux
apply force
done
*)

(*
lemma insertions_as_set :
  "set l1 = set l2 \<Longrightarrow>
   (\<And>x v y v2.
       ((x,v) \<in> set l1 \<Longrightarrow>
       (y,v2) \<in> set l1 \<Longrightarrow>
       x mod 2^256 = y mod 2^256 \<Longrightarrow>
       v = v2)) \<Longrightarrow>
  insertions l1 mem = insertions l2 mem"
*)

(* commuting insertions *)

(*
lemma store_take :
 "store_byte_list_memory w (take (Suc n) (a # lst)) mem x =
  store_byte_list_memory w (a#take n lst) mem x"
apply (simp add:store_byte_list_memory_def)
done

lemma store_take2 :
 "n > 0 \<Longrightarrow>
  store_byte_list_memory w (take n (a # lst)) mem x =
  store_byte_list_memory w (a#take (n-1) lst) mem x"
using store_take [of w "n-1" a lst mem x]
apply auto
done
*)


(*
lemma store_byte_eq :
  "length lst < 2^256 \<Longrightarrow>
   store_byte_list_memory addr lst mem =
   store_byte_list_memory_old addr lst mem"
apply (induction lst arbitrary: addr mem)
apply (auto simp:store_byte_list_memory_def)

lemma store_byte_eq :
  "store_byte_list_memory addr lst mem =
   store_byte_list_memory_old addr (rev (take (2^256) (rev lst))) mem"
apply (induction lst arbitrary: addr mem)
apply (auto simp:store_byte_list_memory_def)
apply (rule funext)
apply auto
subgoal for a lst addr mem x
apply (cases "length lst < 2^256")

apply (auto)

*)

