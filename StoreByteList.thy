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

(*
lemma mapi_inc2 :
"w < 2^256 \<Longrightarrow>
 map (\<lambda>i. (fst i + unat w, snd i)) (enumerate (Suc 0) lst) =
 map (\<lambda>i. (fst i + unat (w + 1), snd i)) (enumerate 0 lst)"
apply (induction lst arbitrary:w)
apply (auto)

lemma mieti :
"1 + unat ((2 ^ 256 - 1)::w256) = 0 \<Longrightarrow> False"
  by linarith

lemma mieti_list : 
"map (\<lambda>i. (fst i +
              unat ((2 ^ 256 - 1)::w256),
              snd i))
        (enumerate (Suc 0) [0::byte]) =
       enumerate 0 [0::byte] \<Longrightarrow>
     False"
apply auto
done

lemma tst :
 "(w::w256) = 2^256-1 \<Longrightarrow>
map (\<lambda>i. (fst i + unat w, snd i)) (enumerate (Suc 0) [a,b,c]) = asd \<and>
map (\<lambda>i. (fst i + unat (w+1), snd i)) (enumerate 0 [a,b,c]) = bsd"
apply auto

*)

fun modeq :: "(nat*byte) list \<Rightarrow> (nat*byte) list \<Rightarrow> bool" where
"modeq ((a1,b1)#l1) ((a2,b2)#l2) =
   (a1 mod (2^256) = a2 mod (2^256) \<and> b1 = b2 \<and> modeq l1 l2)"
| "modeq [] [] = True"
| "modeq _ _ = False"

lemma find_mod :
  "uint (word_of_int x::w256) = (x::int) mod 2^256"
apply (auto simp:uint_word_of_int)
done

lemma unat_mod [simp]:
  "unat (word_of_int (int x)::w256) = x mod 2^256"
apply (simp add: find_mod unat_def)
  by (metis (mono_tags, hide_lams) Divides.transfer_int_nat_functions(2) nat_int.Rep_inverse' of_nat_numeral)

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

lemma funext : "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
apply auto
done

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

(* apply (auto simp:store_byte_list_memory_def)*)





