theory KEC

imports Main "~~/src/HOL/Word/Word"

begin

text "KEC is supposed to take a byte sequence"
text "and to return a 256-bit hash."

text "Now following http://keccak.noekeon.org/Keccak-reference-3.0.pdf"

text "1.1.2 Padding rules"

text "If all lengths are determined at compilation time,"
text "I prefer to have everything as words."
text "If some lengths are determined at runtime,"
text "I might choose lists of bits."
text "Depending on this, the padding rules will have"
text "different types."

text "1.2 Keccak-f permutations"

text "Keccak-f[?] which variant will be used later?"

text "https://github.com/mjosaarinen/tiny_sha3/blob/master/sha3.c is more readable."

definition "rotl64 (x :: 64 word) n = (word_rotl n x :: 64 word)"

definition "(keccakf_randc :: 64 word list) = [
        0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
        0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
        0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
        0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
        0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
        0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
        0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
        0x8000000000008080, 0x0000000080000001, 0x8000000080008008
 ]"

definition "(keccakf_rotc :: nat list) = [
        1,  3,  6,  10, 15, 21, 28, 36, 45, 55, 2,  14,
        27, 41, 56, 8,  25, 43, 62, 18, 39, 61, 20, 44
]"

definition "(keccakf_piln :: nat list) = [
        10, 7,  11, 17, 18, 3, 5,  16, 8,  21, 24, 4,
        15, 23, 19, 13, 12, 2, 20, 14, 22, 9,  6,  1
]"


text "Somehow I need to model"
text "st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];"
text "where st is 25 times uint64_t."
text "Shall I model st as a list or something else?  Maybe a list."

definition "(theta1 (i :: nat) (st :: 64 word list) :: 64 word) =
  (st ! i) XOR
  (st ! (i + 5)) XOR
  (st ! (i + 10)) XOR
  (st ! (i + 15)) XOR
  (st ! (i + 20))"

definition "(theta_t (i :: nat) (bc :: 64 word list) :: 64word) =
  (bc ! ((i + 4) mod 5)) XOR (rotl64 (bc ! ((i + 1) mod 5)) 1)
  "

value "upt 0 5"
  
definition "((theta (st :: 64 word list)) :: 64 word list) =
  (let (bc :: 64 word list) = map (\<lambda> i. theta1 i st) (upt 0 5) in
  (let (t :: 64 word list) = map (\<lambda> i. theta_t i bc) (upt 0 5) in
  map (\<lambda> ji. (st ! ji) XOR (t ! (ji mod 5))) (upt 0 25)
  ))
  "
  
definition "st_test = [(1 :: 64 word), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
              14,
              15, 16, 17, 18, 19,
              20, 21, 22, 23, 24, 25]"
              
value "map (\<lambda> i. theta1 i st_test) (upt 0 5)"
value "theta st_test"

text "For Rho Pi transformation, I need an update function for the list."
value "[1,2,3][1 := 0]"

text "For a fixed i, Rho Pi maps (t, st) to (t, st)."
definition "(rho_pi_inner (i :: nat) (t_st :: 64 word \<times> 64 word list)
 :: (64 word \<times> 64 word list)) =
 (let j = keccakf_piln ! i in
  let bc = (snd t_st) ! j in
 (bc, (snd t_st)[j := rotl64 (fst t_st) (keccakf_rotc ! i)]))
 "
 
 value "rho_pi_inner 3 (0, st_test)"
 
definition "(rho_pi_changes (t_st :: 64 word \<times> 64 word list)
 :: (64 word \<times> 64 word list)) =
 foldr rho_pi_inner (upt 0 24) t_st
 "
 
definition "(rho_pi (st :: 64 word list) :: 64 word list) =
snd (rho_pi_changes (st ! 1, st))"
 
text "model chi"
text "model it as a map on st?  Or, a five-time iteration?"
text "Maybe, [0..4] [5..9] [10..14] and so on"

text "First an operation that works on slices of length five."
definition "(chi_for_j (st_slice :: 64 word list) :: 64 word list) =
  map (\<lambda> i. st_slice ! i XOR (NOT st_slice ! ((i + 1) mod 5)) XOR
            st_slice ! ((i + 2) mod 5)) (upt 0 5)
"

value "sublist st_test (set (upt 0 5))"

definition "(chi (st :: 64 word list) :: 64 word list) =
  concat (map (\<lambda> j. chi_for_j (sublist st (set (upt (j * 5) (j * 5 + 5))))) (upt 0 5))"

value "chi st_test"

text "model iota"

definition "(iota (r :: nat) (st :: 64 word list) :: 64 word list) =
  st[0 := st ! 0 XOR keccakf_randc ! r]"

text "model the content of the for-loop"

definition "(for_inner (r :: nat) (st :: 64 word list) :: 64 word list) =
(iota r (chi (rho_pi (theta st))))
"

definition "(keccakf_rounds :: nat) = 24"

definition "(keccakf (st :: 64 word list) :: 64 word list) =
  foldr for_inner (upt 0 keccakf_rounds) st"

value "keccakf st_test"

text "model sha3_init"
text "mdlen == 256 bit == 32 byte"
text "mdlen = 32, rsiz = 200 - 32 * 2 = 136"
definition "(mdlen :: nat) = 256 div 8"
definition "(rsiz :: nat) = 200 - mdlen * 2"


type_synonym "byte" = "8 word"

definition "(update_byte (i :: byte) (p :: nat) (st :: 64 word list)
:: 64 word list) =
st[p div 8 := (st ! (p div 8)) XOR ((ucast i) << (56 - 8 * (p mod 8))) ]
"

value "(3 :: nat) div 8"
value "update_byte 2 3 [0, 0, 0]" (* just remember big endian *)
value "(ucast (2 :: 8 word) :: 64 word) << (56 - 8 * (3 mod 8))"

text "model sha3_update"
text "recursion on the length of the input."
text "But which command shall I use?  primrec?"

primrec "sha3_update" :: 
"byte list (* input *) \<Rightarrow> nat (* p *)
\<Rightarrow> 64 word list (* st *) \<Rightarrow> (nat (* final p *) \<times> 64 word list)"
where
"sha3_update [] p st = (p, st)" |
"sha3_update (c # rest) pos st =
  (if (pos \<le> rsiz)
   then
     sha3_update rest (pos + 1) (update_byte c pos st) 
   else
     sha3_update rest 0 (keccakf (update_byte c pos st))
  )
"

value "sha3_update [1, 2, 3] 0 st_test"

text "model sha3_final"

definition "split" :: "64 word \<Rightarrow> byte list"
where
"split = word_rsplit"

value "split 30"

definition "sha3_final" :: "nat \<Rightarrow> 64 word list \<Rightarrow> byte list"
where
"sha3_final p st =
   (let st0 = update_byte 0x06 p st in
    let st1 = update_byte 0x80 (rsiz - 1) st0 in
    let st2 = take 4 (keccakf st1) in
    concat (map split st2))
"

text "model the whole sha3 function"

definition "(initial_st :: 64 word list) = concat (replicate 25 [0])"
value "initial_st"

definition "initial_pos" :: "nat"
where
"initial_pos = 0"

definition "sha3" :: "byte list \<Rightarrow> byte list"
where
"sha3 input =
   (let mid = sha3_update input initial_pos initial_st in
    sha3_final (fst mid) (snd mid))"
    
value "sha3 [0, 0, 0]"

end
