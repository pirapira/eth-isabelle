let rec traverse (base : string) (f : string -> unit) : unit =
  let lst = BatSys.readdir base in
  Array.iter
    (fun filename ->
      let path = Filename.concat base filename in
      if BatSys.is_directory path then
        traverse path f
      else f path)
    lst
