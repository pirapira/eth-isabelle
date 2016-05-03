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

text "TODO :: also define a decoder and say something"

end