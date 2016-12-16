open Evm

let pad_left (elm : 'a) (len : int) (orig : 'a list) =
  let remaining = len - List.length orig in
  let () = Printf.printf "padding: remaining: %d\n%!" remaining in
  let padding = BatList.make remaining elm in
  padding @ orig

let word256_of_big_int (b : Big_int.big_int) =
  let () = if BatBig_int.(lt_big_int b zero_big_int) then failwith "negative number cannot be turned into word256" else () in
  let binary : string = BatBig_int.to_string_in_binary b in
  (* should be a sequence of 0s and 1s *)
  let bl : bool list =
    List.map (fun (digit : char) ->
        match digit with
        | '0' -> false
        | '1' -> true
        | _ -> failwith "neither 0 or 1"
      ) (BatString.to_list binary)
    in
  let (h :: tl) = pad_left false 256 bl in
  Word256.W256 (h, tl)

let big_int_of_word256 (Word256.W256 (h, tl)) : Big_int.big_int =
  let bl = h :: tl in
  let nums : Big_int.big_int list = List.map (fun x -> if x then Big_int.unit_big_int else Big_int.zero_big_int) bl in
  List.fold_left (fun x y -> Big_int.(add_big_int y (mult_int_big_int 2 x))) Big_int.zero_big_int nums

let () =
  let x : Word256.word256 = Word256.W256 (true, []) in
  let open Big_int in
  Printf.printf "hello %s\n" (string_of_big_int (big_int_of_word256 (word256_of_big_int (BatBig_int.big_int_of_int (333)))))
