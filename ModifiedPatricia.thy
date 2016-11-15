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

theory ModifiedPatricia

imports Main "./HP" "./RLP" "./KEC"

begin

text "the input value J, a set containing pairs of byte sequences."
text "This looks wrong, J is not a set but a sequence."

type_synonym "jott" = "(byte list \<times> byte list) list"

text "(159) type is not clear."

definition "MP_I0" :: "jott \<Rightarrow> nat \<Rightarrow> byte list"
where
"MP_I0 j i = fst (j ! i)"

definition "MP_I1" :: "jott \<Rightarrow> nat \<Rightarrow> byte list"
where
"MP_I1 j i = snd (j ! i)"

text "In the definition of c(J,i), the \\exists I : I \\in J is nonsense" 

text "MP_c and MP_n must be defined mutually recursively."
text "Doing it at once seems tiresome.  I start defining small pieces."

text "In the second line of (164), why do the indices start from 0?"
text "Maybe this should start from i."

text "I think it's very natural to define a tree as a datatype first"
text "and then say the tree encodes such and such jott."

text "If I'm going to do this, I need something more."
text "I need the decoding function of hex-prefixing encoding."

text "Well, there is this storage thing.  And this storage thing"
text "is going to be encoded into a Patricia tree."

text "storage => Patricia tree => hash"
text "This way of computation is necessary, the other way around is"
text "not supposed to happen anyway."

datatype "MPTree" =
  "MPLeaf" "nibble list" "byte list"
| "MPExt"  "nibble list" "MPTree"
| "MPBranch" "MPTree option list" (* always 16 elements*) "byte list"

text "In (164), when J is empty, the second choice is impossible"
text "just because the argmax does not work."

function MP_n :: "MPTree option (* None means empty *) \<Rightarrow> byte list"
and MP_c :: "MPTree \<Rightarrow> byte list"
where
  "MP_n None = []"
| "MP_n (Some t) =
    (let content = MP_c t in
     if length content < 32 then content
     else word_rsplit (keccack content))
  "
| "MP_c (MPLeaf I0 I1) = RLP(Node [Leaf (HP I0 True), Leaf (I1)])"
| "MP_c (MPExt I0part cont) =
    RLP(Node [Leaf (HP I0part False), Leaf (MP_n (Some cont))])"
| "MP_c (MPBranch subs content) =
    RLP(Node ((map (\<lambda> sub. Leaf (MP_n sub)) subs)@[Leaf content]))"
apply(auto)
apply(case_tac x)
apply(auto)
apply(case_tac b)
apply(auto)
done

text "I still need to encode storage as a MP tree."
text "Or, include an MP tree in the account state."

definition "TRIE" :: "MPTree option \<Rightarrow> 256 word"
where
"TRIE t = (case t of None \<Rightarrow> keccack([]) | Some tree \<Rightarrow> keccack(MP_c tree))"

end
