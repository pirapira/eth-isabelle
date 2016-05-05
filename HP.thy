theory HP

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym byte = "8 word"
type_synonym nibble = "4 word"

fun "HP_f" :: "bool \<Rightarrow> byte"
where
  "HP_f True  = 2"
| "HP_f False = 0"

value "HP_f False"

value "word_rcat"

fun "HP_raw" :: "nibble list \<Rightarrow> byte list"
where
  "HP_raw [] = []"
| "HP_raw [x] = [ucast x]"
| "HP_raw (a # b # rest) = (word_rcat [a, b]) # HP_raw rest"

definition "HP" :: "nibble list \<Rightarrow> bool \<Rightarrow> byte list"
where
"HP lst t =
  (if even (length lst) then
  (16 * (HP_f t)) # HP_raw lst
  else
  (16 * (1 + HP_f t) + ucast (hd lst)) # HP_raw (tl lst))
  "

value "HP [0, 1, 2, 3] True"

end