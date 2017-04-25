theory StoreByteList

imports Main "hoare/Hoare"

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

end

