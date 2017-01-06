open Ocamlbuild_plugin


(* The lines below are derived from
 * https://github.com/aantron/bisect_ppx/blob/d6a569bee855543077b46ceae05433b9a4e7b0e3/src/ocamlbuild/bisect_ppx_plugin.ml
 * which in the public domain.
 *)
let _tag_name = "coverage"
let _environment_variable = "BISECT_COVERAGE"
let _enable = "YES"

let handle_coverage () =
  if getenv ~default:"" _environment_variable <> _enable then
    mark_tag_used _tag_name
  else begin
    flag ["ocaml"; "compile"; _tag_name] (S [A "-package"; A "bisect_ppx"]);
    flag ["ocaml"; "link"; _tag_name] (S [A "-package"; A "bisect_ppx"])
  end

let dispatch' = function
  | After_rules -> handle_coverage ()
  | _ -> ()

let () = dispatch dispatch'
