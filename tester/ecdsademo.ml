
open EccPrimitives
open Ecdh
open Ecdsa
open Extlib.ExtList

module DH = Ecdh (PrimeField)
module DSA = Ecdsa (PrimeField)
module F = PrimeField

let curve = PrimeField.lookup_curve "secp256k1"

let do_test () =
  let sk = Z.of_string_base 16 "45a915e4d060149eb4365960e6a7a45f334393093061116b197e3240065ff2d8" in
  let pk = F.multiply_point (F.get_g curve) sk curve in
  match pk with
  | Point (x,y) ->
    let str = Z.format "%x" x ^ Z.format "%x" y in
    let lst = Conv.byte_list_of_hex_string str in
    let addr_lst = List.drop 12 (Keccak.keccak' lst) in
    Printf.printf "hashing %s to %s\n" str (Conv.hex_string_of_byte_list "" addr_lst)
  | _ -> ()

let _ = do_test ()

(*
let (bob_pk, bob_sk) = DH.create_keys curve
let (alice_pk, alice_sk) = DH.create_keys curve

let sign_message msg sk =
  DSA.sign msg sk curve

let verify_signed_message msg sign pk_sender =
  if DSA.verify msg sign pk_sender curve then
    Printf.printf "message succesfully verified\n"
  else
    Printf.printf "Invalid signature\n"

let main = 
  let msg = "ECDSA demo!" in
  let signature = sign_message msg alice_sk in
    verify_signed_message msg signature alice_pk;

*)
