theory YellowPaper

imports Main "~~/src/HOL/Word/Word"

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
text "Well, I'll just use uint256."
text "If there is a program depending on the monotonicity of"
text "the nonce, at least I can point that out."

text "Shall I model the storage just as a hash or not."
text "Mathematically, there are many states that maps to"
text "a single hash, though it's hard to find more than one."
text "So I need to embed the whole storage here."
text "For the same reason, I record code not just the code hash."

type_synonym byte = "8 word"

record "account_state" =
  Nonce :: "uint256"
  Balance :: "uint256"
  StorageRoot :: "uint256" (* This should be changed. *)
  CodeHash :: "byte list"

type_synonym "state" = "address \<Rightarrow> account_state"

text "We do not model the Merkle Patricia tree for now"


end
