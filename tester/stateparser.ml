
open Yojson.Basic
open Keccak
open Evm
open Block
open VmTestParser

open EccPrimitives
open Ecdh
open Ecdsa
open Extlib.ExtList

module DH = Ecdh (PrimeField)
module DSA = Ecdsa (PrimeField)
module F = PrimeField

let curve = PrimeField.lookup_curve "secp256k1"

let secret_to_address str =
  let sk = Z.of_string_base 16 str in
  let pk = F.multiply_point (F.get_g curve) sk curve in
  match pk with
  | Point (x,y) ->
    let str = Z.format "%x" x ^ Z.format "%x" y in
    let lst = Conv.byte_list_of_hex_string str in
    let addr_lst = List.drop 12 (Keccak.keccak' lst) in
    Conv.hex_string_of_byte_list "0x" addr_lst
  | _ -> "???"

type tr =
  { target : Big_int.big_int option
  ; data : string
  ; gasLimit : Big_int.big_int
  ; gasPrice : Big_int.big_int
  ; address : Big_int.big_int
  ; nonce : Big_int.big_int
  ; value : Big_int.big_int
  }

let parse_tr (j : json) : tr =
  Util.(
    { target = (try Some (parse_address_from_field "to" j) with _ -> None)
    ; data = to_string (member "data" j)
    ; address = Big_int.big_int_of_string (secret_to_address (to_string (member "secretKey" j)))
    ; gasLimit = parse_big_int_from_field "gasLimit" j
    ; gasPrice = parse_big_int_from_field "gasPrice" j
    ; value = parse_big_int_from_field "value" j
    ; nonce = parse_big_int_from_field "nonce" j
    })

type test_case =
  { env : env
  ; tr : tr
  ; gas : string option
  ; logs : log list
  ; out : string option
  ; post : (string * account_state) list
  ; pre : (string * account_state) list
  }

let parse_test_case (j : json) : test_case =
  Util.(
  { env = parse_env (member "env" j)
  ; tr = parse_tr (member "transaction" j)
  ; gas =
      (try Some (to_string (member "gas" j))
       with Yojson.Basic.Util.Type_error _ -> None)
  ; logs =
      (try (List.map parse_log (to_list (member "logs" j)))
       with Yojson.Basic.Util.Type_error _ -> [])
  ; out =
      (try Some (to_string (member "out" j))
       with Yojson.Basic.Util.Type_error _ -> None)
  ; post = parse_states (to_assoc (member "post" j))
  ; pre = parse_states (to_assoc (member "pre" j))
  })


