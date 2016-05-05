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
"r_b [k] = (if k < 128 then [k] else [128, k])" |
"r_b lst =
   (if length lst < 56 then
      of_nat (128 + length lst) # lst
    else
      of_nat (183 + length(BE(length lst))) # (BE(length lst) @ lst))
"

value "r_b (map of_nat (upt 0 100))"

function "de_r_b" :: "byte list \<Rightarrow> (byte list * (*rest*) byte list) option"
where
  "de_r_b [] = None"
| "de_r_b (128 # r) = Some ([], r)"
| "k < 128 \<Longrightarrow> de_r_b (k # r) = Some ([k], r)"
| "128 < k \<Longrightarrow> k < 128 + 56 \<Longrightarrow>
    de_r_b (k # lst) = (if length lst \<ge> (unat k) then Some (take (unat k) lst, drop (unat k) lst)
                                         else None)"
apply(auto)
oops

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