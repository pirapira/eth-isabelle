theory Memory

imports Main "~~/src/HOL/Word/Word"

begin

text "The memory model is a simple word-addressed byte array, says the yellow paper."
text "But I think I need to keep track of the usage, for the gas computation."

type_synonym "idx" = "256 word"
type_synonym "content" = "8 word"

record "memory" =
  map :: "idx \<Rightarrow> content"
  max_idx :: "idx"
  
text "The whitepaper specifies how the memory is initialized."

definition "initial_memory" :: "memory"
where
"initial_memory = \<lparr> map = (\<lambda> _. 0), max_idx = 0 \<rparr>"

value "initial_memory"

definition "write_word" :: "memory \<Rightarrow> idx \<Rightarrow> 256 word \<Rightarrow> memory option"
where
"write_word orig loc val =
(if loc + 31 \<le> loc then None else 
Some
\<lparr>
  map = (let (bytes :: content list) = (word_rsplit val) in
          ((((map orig)
            (loc := (bytes ! 0)))
            ((loc + 1) := (bytes ! 1)))
            ((loc + 2) := (bytes ! 2)))
            ((loc + 3) := (bytes ! 3))
        ),
  max_idx = max (loc + 31) (max_idx orig)
\<rparr>)
"

text "Is it free to use the last 32 bytes?  Because loc + 32 overflows."

end