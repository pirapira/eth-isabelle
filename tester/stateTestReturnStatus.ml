open Yojson.Basic
open StateTestLib

let main fn filter =
  let test : json = Yojson.Basic.from_file fn in
  let test_assoc : (string * json) list = Util.to_assoc test in
  let check a = match filter with None -> true | Some b -> a = b in
  let () =
    List.iter (fun (a,b) -> if check a then begin
                                match (run_test (a,b)) with
                                | TestResult.TestSuccess -> ()
                                | TestResult.TestSkipped -> ()
                                | TestResult.TestFailure -> exit 1
                              end
              ) test_assoc
  in
  ()

let _ =
  if Array.length Sys.argv = 2 then main Sys.argv.(1) None else
  if Array.length Sys.argv > 2 then main Sys.argv.(1) (Some Sys.argv.(2))
  (*
  for i = 1 to Array.length Sys.argv - 1 do
    main Sys.argv.(i)
  done*)
