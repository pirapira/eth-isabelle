let to_list_allow_null (j : Yojson.Basic.json) =
  if j = Yojson.Basic.(`Null) then []
  else Yojson.Basic.Util.to_list j
