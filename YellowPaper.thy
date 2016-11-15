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

theory YellowPaper

imports Main "~~/src/HOL/Word/Word" "./KEC" "./ModifiedPatricia"

begin

type_synonym uint256 = "256 word"
type_synonym word32 = "32 word"

text "2. The Blockchain Paradigm"

text "The equations (1) until (4) are rather abstract."
text "Skipping them for now, hoping we can revisit them."

text "2.1. Value."

definition "Wei :: uint256 == 10 ^ 0"
definition "Szabo :: uint256 == 10 ^ 12"
definition "Finney :: uint256 == 10 ^ 15"
definition "Ether :: uint256 == 10 ^ 18"

text "Thanks to uint256, these values can be computed quickly."
value "Wei"
value "Szabo"
value "Finney"
value "Ether"

text "2.2. Which History?"
text "This aspect is not modelled."
text "I aim at modelling a linear history first."

text "3. Conventions"

text "Greek letters"
value "\<Upsilon>"
value "\<iota>"

text "Can I use bold characters as symbols?"

text "How to access slices of arrays?"
text "I think I will implement a notation like \<mu>[0..31]"

text "equation (5)"

definition "l == last"

text "4. Blocks, State and the Transactions"

text "4.1. World State"

text "State is a mapping from addresses to account states."

text "Now I have to choose if I model the account state
      as a byte sequence or a struct.  This is essentially
      about allowing invalid RLP or not.  I choose not."

type_synonym "address" = "160 word"

text "Shall I model the nonce as a natural number?"
text "Well, I'll just use uint256. -> (11) and (12) support this."

text "Shall I model the storage just as a hash or not."
text "Mathematically, there are many states that maps to"
text "a single hash, though it's hard to find more than one."
text "So I need to embed the whole storage here."
text "For the same reason, I record code not just the code hash."

type_synonym byte = "8 word"
type_synonym storage = "uint256 \<Rightarrow> uint256 option"

record "account_state" =
  Nonce :: "uint256"
  Balance :: "uint256"
  Storage :: "MPTree option" (* storing MPTree instead of the hash.
                         It's easier to compute the hash from the tree.*)
  Code :: "byte list"

type_synonym "state" = "address \<Rightarrow> account_state"

definition "codeHash" :: "account_state \<Rightarrow> uint256"
where
"codeHash as = keccack (Code as)"

definition "storageRoot" :: "account_state \<Rightarrow> uint256"
where
"storageRoot as = TRIE (Storage as)"

text "Question about text:"
text "not a 'physical' member of the account"
text "What does this mean?"

text "Model the world state."
text "Maybe not as a function but a MP Tree"
text "Or, list of pairs (address, account state)."
text "Or, maybe try this https://wwwmath.uni-muenster.de:16030/sev/projects/icf/icf-2010-01-20-outline.pdf"

text "But, when I analyze a contract, I don't need to know"
text "if there are only finitely many addresses."
text "So just a mapping is enough."

type_synonym "world_state" = "address \<Rightarrow> account_state"

text "TODO"
text "Model the world-state collapse function L_S"

text "(11) will be encoded in the types"
text "when the hash functions will be defined."

text "4.2. Transaction."

text "Appendix F. Signing Transactions"
text "I don't think this part is necessary for analyzing EVM programs."

end
