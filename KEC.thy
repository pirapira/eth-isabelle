(*
   Copyright 2016 Yoichi Hirai

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

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

text {* https://github.com/mjosaarinen/tiny\_sha3/blob/master/sha3.c is more readable. *}

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
  
definition "((theta (st :: 64 word list)) :: 64 word list) =
  (let (bc :: 64 word list) = map (\<lambda> i. theta1 i st) (upt 0 5) in
  (let (t :: 64 word list) = map (\<lambda> i. theta_t i bc) (upt 0 5) in
  map (\<lambda> ji. (st ! ji) XOR (t ! (ji mod 5))) (upt 0 25)
  ))
  "

definition "(st_test :: 64 word list) = 
 [6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9223372036854775808, 
0, 0, 0, 0, 0, 0, 0, 0]"

text "For Rho Pi transformation, I need an update function for the list."

text "For a fixed i, Rho Pi maps (t, st) to (t, st)."
definition "(rho_pi_inner (i :: nat) (t_st :: 64 word \<times> 64 word list)
 :: (64 word \<times> 64 word list)) =
 (let j = keccakf_piln ! i in
  let bc = (snd t_st) ! j in
 (bc, (snd t_st)[j := rotl64 (fst t_st) (keccakf_rotc ! i)]))
 "

definition "(rho_pi_changes (i :: nat) (t_st :: 64 word \<times> 64 word list)
 :: (64 word \<times> 64 word list)) =
 fold rho_pi_inner (upt 0 i) t_st
 "

definition "(rho_pi (st :: 64 word list) :: 64 word list) =
snd (rho_pi_changes 24 (st ! 1, st))"

text "model chi"
text "model it as a map on st?  Or, a five-time iteration?"
text "Maybe, [0..4] [5..9] [10..14] and so on"

text "First an operation that works on slices of length five."
definition "(chi_for_j (st_slice :: 64 word list) :: 64 word list) =
  map (\<lambda> i. (st_slice ! i) XOR ((NOT (st_slice ! ((i + 1) mod 5)))
            AND
            (st_slice ! ((i + 2) mod 5))))
            (upt 0 5)
"

definition "slice0 = (sublist (rho_pi (theta st_test)) (set (upt 0 5)))"

definition "(chi (st :: 64 word list) :: 64 word list) =
  concat (map (\<lambda> j. chi_for_j
                    (sublist st (set (upt (j * 5) (j * 5 + 5))))
                    )
                    (upt 0 5))"

text "model iota"

definition "(iota (r :: nat) (st :: 64 word list) :: 64 word list) =
  st[0 := st ! 0 XOR keccakf_randc ! r]"

text "model the content of the for-loop"

definition "(for_inner (r :: nat) (st :: 64 word list) :: 64 word list) =
(iota r (chi (rho_pi (theta st))))
"

definition "(keccakf_rounds :: nat) = 24"

type_synonym "byte" = "8 word"

definition "split" :: "64 word \<Rightarrow> byte list"
where
"split = word_rsplit"

definition "cat" :: "byte list \<Rightarrow> 64 word"
where "cat = word_rcat"

definition "invert_endian" :: "64 word \<Rightarrow> 64 word"
where
"invert_endian w = cat (rev (split w))"

definition "(keccakf (st :: 64 word list) :: 64 word list) =
   (fold for_inner (upt 0 keccakf_rounds) st)"

value "keccakf st_test"

text "model sha3_init"
text "mdlen == 256 bit == 32 byte"
text "mdlen = 32, rsiz = 200 - 32 * 2 = 136"
definition "(mdlen :: nat) = 256 div 8"
definition "(rsiz :: nat) = 200 - mdlen * 2"



definition "(update_byte (i :: byte) (p :: nat) (st :: 64 word list)
:: 64 word list) =
st[p div 8 := (st ! (p div 8)) XOR ((ucast i) << (8 * (p mod 8))) ]
"

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

value "split 30"

definition "keccack_final" :: "nat \<Rightarrow> 64 word list \<Rightarrow> byte list"
where
"keccack_final p st =
   (let st0 = update_byte 0x01 p st in
    let st1 = update_byte 0x80 (rsiz - 1) st0 in
    let st2 = take 4 (keccakf st1) in
    concat (map (\<lambda> x. rev (split x)) st2))
"

text "model the whole keccack function"

definition "(initial_st :: 64 word list) = concat (replicate 25 [0])"
value "initial_st"

definition "initial_pos" :: "nat"
where
"initial_pos = 0"

definition "keccak'" :: "byte list \<Rightarrow> byte list"
where
"keccak' input =
   (let mid = sha3_update input initial_pos initial_st in
    keccack_final (fst mid) (snd mid))"

value "keccak' []"

definition "keccak" :: "byte list \<Rightarrow> 256 word"
where
"keccak input = word_rcat (keccak' input)"

end
