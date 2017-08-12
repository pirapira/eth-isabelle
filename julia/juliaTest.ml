
open Julia
open Parsr
open Lexr

open Lexing
open Printf

(* The following two functions comes from
 * https://github.com/realworldocaml/examples/tree/master/code/parsing-test
 * which is under UNLICENSE
 *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parsr.main Lexr.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | Parsr.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
  | a ->
    raise a

let rec value_to_string = function
 | FalseV -> "false"
 | TrueV -> "true"
 | IntV i -> Z.to_string i
 | StringV i -> "'" ^ Z.to_string i ^ "'"
 | ListV lst -> "[" ^ String.concat "," (List.map value_to_string lst) ^ "]"
 | FunctionV (id, _, _, _) -> "function " ^ Z.to_string id
 | BuiltinV _ -> "builtin"
 | GBuiltinV _ -> "state builtin"

let builtins = [
  "addu256", AddU256;
]

let init =
  List.fold_left (fun acc (k,v) -> Pmap.add (JuliaUtil.string_to_Z k) (BuiltinV v) acc) Julia.initial builtins

let builtins2 = [
  "mstore", MStore;
  "mstore8", MStore8;
  "mload", MLoad;
  "sstore", SStore;
  "sload", SLoad;
  "return", Return;
  "revert", Revert;
  "create", Create;
  "call", Call;
]

let init =
  List.fold_left (fun acc (k,v) -> Pmap.add (JuliaUtil.string_to_Z k) (GBuiltinV v) acc) init builtins2

let print_state l =
  Pmap.iter (fun k v -> prerr_endline (Z.to_string k ^ " -> " ^ value_to_string v)) l 

let print_memory mem sz = ()

let rec do_calc g l = function
 | st :: lst ->
    let l, g = match Julia.eval_statement g l st 100 with
     | Exit _ -> prerr_endline "<error>"; (l, g)
     | Normal (g,l,_) -> print_state l; print_memory g.memory g.memory_size; prerr_endline "<step>"; (l, g) in
    do_calc g l lst
 | [] -> prerr_endline "Exiting ..."

let main () =
  if Array.length Sys.argv < 2 then prerr_endline "need filename" else
  let lexbuf = Lexing.from_channel (open_in Sys.argv.(1)) in
  let lst = parse_with_error lexbuf in
  let _ = prerr_endline "Finished parsing" in
  do_calc {Julia.init_global with context=init; address=Z.of_int 1337} init lst

let _ =
  prerr_endline (Z.to_string (get_byte (Z.of_int 0) (Z.of_int 1234)));
  prerr_endline (Z.to_string (get_byte (Z.of_int 1) (Z.of_int 1234)));
  main ()

