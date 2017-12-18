(** [to_list_allow_null] is similar to [Yojson.Basic.Util.to_list] but turns a null document into the empty list. *)
val to_list_allow_null : Yojson.Basic.json -> Yojson.Basic.json list
