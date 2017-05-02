(** [traverse base f] traverses the directory [base] recursively and runs [f file] on every [file] found with [.json] suffix. *)
val traverse : string -> (string -> unit) -> unit
