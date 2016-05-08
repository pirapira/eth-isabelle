theory RLP

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym "byte" = "8 word"

datatype "tree" =
  Leaf "byte list" |
  Node "tree list"

fun BE_rev :: "nat \<Rightarrow> byte list"
where
"BE_rev 0 = []" |
"BE_rev n = (if n < 256 then [of_nat n] else
         (of_nat (n mod 256)) # BE_rev (n div 256))"

value "BE_rev 256"

definition BE :: "nat \<Rightarrow> byte list"
where
"BE n = rev (BE_rev n)"


value "BE 300"

fun BD_rev :: "byte list \<Rightarrow> nat"
where
"BD_rev [] = 0" |
"BD_rev (h # t) = 256 * (BD_rev t) + (unat h)"

lemma BD_rev_BE_rev [simp]: "BD_rev (BE_rev n) = n"
apply(induct n rule: BE_rev.induct)
apply(simp)
apply(auto)
  apply(simp add: Word.unat_word_ariths(1) Word.unat_of_nat)
apply(simp add: Word.unat_of_nat)
done

definition BD :: "byte list \<Rightarrow> nat"
where
"BD lst = BD_rev (rev lst)"

lemma BD_BE [simp]: "BD (BE n) = n"
by (simp add: BD_def BE_def)

fun "r_b" :: "byte list \<Rightarrow> byte list"
where
"r_b [] = [128]" |
"r_b [k] = (if k < 128 then [k] else [129, k])" | (* there was a mistake, putting 128 twice *)
"r_b lst =
   (if length lst < 56 then
      of_nat (128 + length lst) # lst
    else
      of_nat (183 + length(BE(length lst))) # (BE(length lst) @ lst))
"

value "r_b (map of_nat (upt 0 100))"

definition "read_n_bytes" :: "nat \<Rightarrow> byte list \<Rightarrow> (byte list  * (* rest *) byte list) option"
where
"read_n_bytes n lst =
  (if length lst \<ge> n then
     Some (take n lst, drop n lst)
   else None)
"

definition "de_r_b" :: "byte list \<Rightarrow> (byte list * (*rest*) byte list) option"
where
  "de_r_b ll =
  (case ll of
    [] \<Rightarrow> None
  | k # lst \<Rightarrow>
    (if k = 128 then
       Some ([], lst)
     else if k < 128 then
       Some ([k], lst)
     else if k < 184 then
       (let len = unat k - 128 in
       (if length lst \<ge> len then Some (take len lst, drop len lst)
                                         else None))
     else if k \<le> 192 then
      (case read_n_bytes (unat k - 183) lst of
         None \<Rightarrow> None
       | Some(be_bytes, x_and_rest) \<Rightarrow>
         read_n_bytes (BD be_bytes) x_and_rest
      )
     else 
       None
    )
  )"

  value "r_b (map of_nat (upt 0 10))"
  value "de_r_b (r_b (map of_nat (upt 0 10)))"


lemma encode_r_b_middle[simp] :
    "length vc < 54 \<Longrightarrow>
       de_r_b ((130 + of_nat (length vc)) # v # vb # vc @ tail) = Some (v # vb # vc, tail)"
apply(simp add: de_r_b_def word_less_nat_alt unat_word_ariths unat_of_nat)
apply(unat_arith)
apply(simp add: unat_of_nat)
done

lemma BE0[simp] : "(BE (n) = []) = (n = 0)"
apply(simp only: BE_def)
by(induct n rule: BE_rev.induct; simp)

lemma read_n_n[simp] : "read_n_bytes (length lst) (lst @ rest) = Some (lst, rest)"
apply(induction lst)
apply(simp add: read_n_bytes_def)+
done

lemma encode_r_b_last[simp] :
"length (BE (length (v # vb # vc))) \<le> 9 \<Longrightarrow>
       \<not> length vc < 54 \<Longrightarrow>
       de_r_b
        ((183 + of_nat (length (BE (Suc (Suc (length vc)))))) #
         BE (Suc (Suc (length vc))) @ v # vb # vc @ tail) =
       Some (v # vb # vc, tail)"
apply(simp add: de_r_b_def word_less_nat_alt unat_word_ariths unat_of_nat)
apply(auto)

apply(unat_arith)
apply(simp add: unat_of_nat)

apply(simp add: read_n_bytes_def)

apply(unat_arith)
apply(simp add: unat_of_nat)
done

lemma inv_r_b[simp] : "length(BE(length lst)) \<le> 9 \<Longrightarrow> de_r_b (r_b lst @ tail) = Some (lst, tail)"
apply(induction lst rule: r_b.induct)
apply(simp add: de_r_b_def)
apply(simp add: "r_b.simps")
apply(auto)
apply(simp add: de_r_b_def)
apply(simp add: de_r_b_def)
done

fun "RLP" :: "tree \<Rightarrow> byte list"
where
"RLP(Leaf l) = r_b l" |
"RLP(Node lst) =
  (let s = concat (map RLP lst) in
   let len_s = length s in
   (if len_s < 56 then
      of_nat (192 + len_s) # s
    else
      of_nat (247 + length (BE len_s)) # (BE len_s @ s) ))"

definition "RLP_nat" :: "nat \<Rightarrow> byte list"
where
"RLP_nat i = RLP (Leaf (BE i))"
      
text "TODO :: also define a decoder and say something"

end